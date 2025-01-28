#include <algorithm>
#include <cctype>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <vector>

extern "C" {
#include <lightning.h>
}

using namespace std;

struct S {
  string head;
  vector<shared_ptr<S>> rest;

  S(string h) : head(std::move(h)) {}
  S(string h, vector<shared_ptr<S>> r)
      : head(std::move(h)), rest(std::move(r)) {}

  string to_string() const {
    ostringstream oss;
    for (const auto &s : rest) {
      oss << s->to_string() << ' ';
    }
    oss << head;
    return oss.str();
  }
};

enum class TokenType { Atom, Op, Eof };

struct Token {
  TokenType type;
  string value;

  Token(TokenType t, string v = "") : type(t), value(std::move(v)) {}
};

class Lexer {
public:
  explicit Lexer(const string &input) {
    size_t i = 0;
    while (i < input.size()) {
      if (isspace(input[i])) {
        ++i;
        continue;
      }

      if (isdigit(input[i])) {
        size_t start = i;
        while (i < input.size() && isdigit(input[i]))
          ++i;
        tokens.emplace_back(TokenType::Atom, input.substr(start, i - start));
        continue;
      }

      if (isalnum(input[i])) {
        tokens.emplace_back(TokenType::Atom, string(1, input[i]));
        ++i;
        continue;
      }

      tokens.emplace_back(TokenType::Op, string(1, input[i]));
      ++i;
    }
    tokens.emplace_back(TokenType::Eof);
    reverse(tokens.begin(), tokens.end());
  }

  Token next() {
    if (tokens.empty())
      return {TokenType::Eof};
    Token token = tokens.back();
    tokens.pop_back();
    return token;
  }

  Token peek() const {
    if (tokens.empty())
      return {TokenType::Eof};
    return tokens.back();
  }

private:
  vector<Token> tokens;
};

shared_ptr<S> expr_bp(Lexer &lexer, int min_bp);

shared_ptr<S> expr(const string &input) {
  Lexer lexer(input);
  return expr_bp(lexer, 0);
}

pair<int, int> infix_binding_power(char op) {
  switch (op) {
  case '=':
    return {2, 1};
  case '?':
    return {4, 3};
  case '+':
  case '-':
    return {5, 6};
  case '*':
  case '/':
    return {7, 8};
  case '.':
    return {14, 13};
  default:
    return {-1, -1};
  }
}

int prefix_binding_power(char op) {
  switch (op) {
  case '+':
  case '-':
    return 9;
  case '(':
    return 15;
  default:
    return -1;
  }
}

int postfix_binding_power(char op) {
  switch (op) {
  case '!':
  case '[':
    return 11;
  case ')':
    return 12;
  default:
    return -1;
  }
}

shared_ptr<S> expr_bp(Lexer &lexer, int min_bp) {
  Token token = lexer.next();
  shared_ptr<S> lhs;

  if (token.type == TokenType::Atom) {
    lhs = make_shared<S>(token.value);
  } else if (token.type == TokenType::Op && token.value == "(") {
    lhs = expr_bp(lexer, 0);
  } else if (token.type == TokenType::Op) {
    int r_bp = prefix_binding_power(token.value[0]);
    auto rhs = expr_bp(lexer, r_bp);
    lhs = make_shared<S>(token.value, vector<shared_ptr<S>>{rhs});
  } else {
    throw runtime_error("Unexpected token");
  }

  while (true) {
    Token lookahead = lexer.peek();
    if (lookahead.type == TokenType::Eof)
      break;

    if (lookahead.type == TokenType::Op) {
      if (int l_bp = postfix_binding_power(lookahead.value[0]);
          l_bp >= min_bp) {
        lexer.next();
        lhs = make_shared<S>(lookahead.value, vector<shared_ptr<S>>{lhs});
        continue;
      }

      auto [l_bp, r_bp] = infix_binding_power(lookahead.value[0]);
      if (l_bp < min_bp)
        break;

      lexer.next();

      if (lookahead.value[0] == '?') {
        auto mhs = expr_bp(lexer, 0);
        auto rhs = expr_bp(lexer, r_bp);
        lhs = make_shared<S>(lookahead.value,
                             vector<shared_ptr<S>>{lhs, mhs, rhs});
      } else {
        auto rhs = expr_bp(lexer, r_bp);
        lhs = make_shared<S>(lookahead.value, vector<shared_ptr<S>>{lhs, rhs});
      }
    }
  }

  return lhs;
}

typedef int (*pifi)(int);
typedef int (*pifv)(void);

static jit_state_t *_jit;

void stack_push(int reg, int *sp) {
  jit_stxi_i(*sp, JIT_FP, reg);
  *sp += sizeof(int);
}

void stack_pop(int reg, int *sp) {
  *sp -= sizeof(int);
  jit_ldxi_i(reg, JIT_FP, *sp);
}

jit_node_t *compile_rpn(const char *expr) {
  jit_node_t *in, *fn;
  int stack_base, stack_ptr;

  fn = jit_note(NULL, 0);
  jit_prolog();
  in = jit_arg();
  stack_ptr = stack_base = jit_allocai(32 * sizeof(int));

  jit_getarg(JIT_R2, in);

  while (*expr) {
    char buf[32];
    int n;
    if (sscanf(expr, "%[0-9]%n", buf, &n)) {
      expr += n - 1;
      stack_push(JIT_R0, &stack_ptr);
      jit_movi(JIT_R0, atoi(buf));
    } else if (*expr == '+') {
      stack_pop(JIT_R1, &stack_ptr);
      jit_addr(JIT_R0, JIT_R1, JIT_R0);
    } else if (*expr == '-') {
      stack_pop(JIT_R1, &stack_ptr);
      jit_subr(JIT_R0, JIT_R1, JIT_R0);
    } else if (*expr == '*') {
      stack_pop(JIT_R1, &stack_ptr);
      jit_mulr(JIT_R0, JIT_R1, JIT_R0);
    } else if (*expr == '/') {
      stack_pop(JIT_R1, &stack_ptr);
      jit_divr(JIT_R0, JIT_R1, JIT_R0);
    } else if (*expr == '(' || *expr == ')' || *expr == ' ') {
      ++expr;
      continue;
    } else {
      fprintf(stderr, "cannot compile: %s\n", expr);
      abort();
    }
    ++expr;
  }
  jit_retr(JIT_R0);
  jit_epilog();
  return fn;
}

pifv eval(const string line) {
  _jit = jit_new_state();
  auto c_expr = compile_rpn(line.c_str());
  (void)jit_emit();
  auto eval = (pifv)jit_address(c_expr);
  jit_clear_state();
  return eval;
}

#include <cassert>
#include <iostream>

void test_single_digit() {
  assert(expr("3")->to_string() == "3");
  assert(expr("42")->to_string() == "42");
}

void test_simple_operations() {
  assert(expr("3 + 4")->to_string() == "3 4 +");
  assert(expr("10 - 5")->to_string() == "10 5 -");
  assert(expr("6 * 7")->to_string() == "6 7 *");
  assert(expr("8 / 2")->to_string() == "8 2 /");
}

void test_operator_precedence() {
  assert(expr("3 + 4 * 5")->to_string() == "3 4 5 * +");
  assert(expr("10 - 5 / 5")->to_string() == "10 5 5 / -");
  assert(expr("1 + 2 * 3 - 4 / 5")->to_string() == "1 2 3 * + 4 5 / -");
}

void test_parentheses() {
  assert(expr("(3 + 4) * 5")->to_string() == "3 4 + 5 *");
  assert(expr("(1 + 2) * (3 - 4)")->to_string() == "1 2 + 3 4 - *");
}

void test_nested_parentheses() {
  assert(expr("((3 + 4) * 5) / 2")->to_string() == "3 4 + 5 * 2 /");
  assert(expr("(1 + (2 * 3)) - (4 / (5 + 6))")->to_string() ==
         "1 2 3 * + 4 5 6 + / -");
}

void test_complex_expressions() {
  assert(expr("3 + 4 * 2 / (1 - 5) + 6")->to_string() ==
         "3 4 2 * 1 5 - / + 6 +");
  assert(expr("42 * (35 + 12) / (7 - 3) + 8")->to_string() ==
         "42 35 12 + * 7 3 - / 8 +");
}

void test_unary_operations() {
  assert(expr("-3")->to_string() == "3 -");
  assert(expr("+42")->to_string() == "42 +");
  assert(expr("-3 + 4")->to_string() == "3 - 4 +");
  assert(expr("-3 * (4 + 2)")->to_string() == "3 - 4 2 + *");
}

void test_edge_cases() {
  // Minimal input
  assert(expr("1")->to_string() == "1");

  // Extra spaces
  assert(expr("  3   + 4   ")->to_string() == "3 4 +");

  // Complex parentheses
  assert(expr("(((3)))")->to_string() == "3");
  assert(expr("(3 + (4 * (5)))")->to_string() == "3 4 5 * +");

  // Multiple operators in sequence
  assert(expr("3 + 4 - 5")->to_string() == "3 4 + 5 -");
  assert(expr("6 * 7 / 2")->to_string() == "6 7 * 2 /");

  // Invalid input should throw errors (commented out as assert does not catch
  // exceptions) try { expr("+"); assert(false); } catch (...) {} // Unary +
  // without operand try { expr("(3 + 4"); assert(false); } catch (...) {} //
  // Mismatched parentheses try { expr(")3 + 4("); assert(false); } catch (...)
  // {} // Invalid parentheses
}

void test_large_numbers() {
  assert(expr("123 + 456")->to_string() == "123 456 +");
  assert(expr("99999 * 88888")->to_string() == "99999 88888 *");
  assert(expr("1234567890 - 987654321")->to_string() ==
         "1234567890 987654321 -");
}

void test_no_operators() {
  assert(expr("123")->to_string() == "123");
  assert(expr("456 789")->to_string() == "456 789");
}

void test_postfix_operators() {
  assert(expr("3!")->to_string() == "3 !");
  assert(expr("(4 + 5)!")->to_string() == "4 5 + !");
}

int tests() {
  test_single_digit();
  test_simple_operations();
  test_operator_precedence();
  test_parentheses();
  test_nested_parentheses();
  test_complex_expressions();
  test_unary_operations();
  test_edge_cases();
  test_large_numbers();
  test_no_operators();
  test_postfix_operators();

  std::cout << "All tests passed!" << std::endl;
  return 0;
}
int main(int argc, char **argv) {
  /*tests();*/
  jit_node_t *c_expr;
  string line;
  init_jit(argv[0]);
  do {
    cout << "<rpn> ";
    getline(cin, line);
    auto result = expr(line);
    auto function = eval(result->to_string());
    cout << result->to_string() << " -> " << function() << endl;
  } while (line != "quit");

  finish_jit();
  return 0;
}
