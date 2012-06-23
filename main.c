#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <stdlib.h>

/*
 * 7/5/05
 * Fixed memory leak (when using GC) in strdup.
 * Removed useless atom table.
 * Added lots of comments.
 * Reformatting.
 * Dead code elimination.
 * Factored cascaded conditionals and replaced some with switch.
 * list_eq for pairs fixed.
 * Fixed parsing of binary operators.
 */

/*
 * #define COLLECT_GARBAGE
 * If you want to use the Boehm-Demers-Weiser garbage collector.
 *
 * Portability issues:
 * Assumes int is as long as a pointer.
 */

#if defined(COLLECT_GARBAGE)
#include "gc.h"
#include "gc_typed.h"
#endif

int current_char;

#if defined(COLLECT_GARBAGE)
void *allocate_memory(size_t n) {
	return GC_malloc(n);
}
#else
void *allocate_memory(size_t n) {
	return malloc(n);
}
#endif

char *duplicate_string(const char *s) {
    return strcpy(allocate_memory(strlen(s)+1),s);
}

int next_char() {
	return current_char = getchar();
}

void error_msg(char *a) {
    /* Potential buffer overflow */
    char line[1024];
    fgets(line,1024,stdin);
    fprintf(stderr,"Error: %s\nBefore: %s\n",a,line);
    exit(1);
}

typedef enum {
    COMB_ERROR,

    COMB_ATOM,
    COMB_COMB,
    COMB_PAIR,
    COMB_INTEGER,
    COMB_VAR
} comb_type;

typedef struct list {
    comb_type type;
    int value;
    char *var_name;
    struct list *head,*tail;
    char name;
} list;

/*
 * Convenience macros for list access.
 */
#define H(a) ((a)->head)
#define T(a) ((a)->tail)
#define TT(a) T(T(a))
#define TH(a) T(H(a))
#define HT(a) H(T(a))
#define HH(a) H(H(a))
#define TTH(a) T(TH(a))
#define HTH(a) H(TH(a))
#define THT(a) T(HT(a))
#define HHT(a) H(HT(a))
#define THTH(a) T(HTH(a))
#define HHTH(a) H(HTH(a))

int is_comb(list *);

list *make_list() {
    list *c = (list *)allocate_memory(sizeof(list));

    return c;
}

list *I;

/*
 * Remove redundant I combinator.
 */
list *elide(list *a) {
    return is_comb(a) && H(a)==I ? elide(T(a)) : a;
}

/*
 * Apply combinator a to b.
 * Ie. a b
 */
list *apply(list *a,list *b) {
    list *c = make_list();
    c->type = COMB_COMB;
    c->head = elide(a);
    c->tail = b; /* elide(b) */;

    return c;
}

/*
 * a b c
 */
list *apply2(list *a,list *b,list *c) {
    return apply(apply(a,b),c);
}

/*
 * a b c d
 */
list *apply3(list *a,list *b,list *c,list *d) {
    return apply(apply(apply(a,b),c),d);
}

list *make_atom(char a) {
    list *l;
    l = make_list();
    l->type = COMB_ATOM;
    l->name = a;

    return l;
}

list *make_var(const char *a) {
    list *l = make_list();
    l->type = COMB_VAR;
    l->var_name = duplicate_string(a);

    return l;
}

list *make_int(int a) {
    list *l = make_list();
    l->type = COMB_INTEGER;
    l->value = a;

    return l;
}

list *make_pair(list *a,list *b) {
    list *l = make_list();
    l->head = a;
    l->tail = b;
    l->type = COMB_PAIR;

    return l;
}

int is_atom(list *a) {
    return a->type==COMB_ATOM;
}

int is_int(list *a) {
    return a->type==COMB_INTEGER;
}

int is_var(list *a) {
    return a->type==COMB_VAR;
}

int is_comb(list *a) {
    return a->type==COMB_COMB;
}

int is_pair(list *a) {
    return a->type==COMB_PAIR;
}

int get_int(list *a) {
    if (!is_int(a)) {
	error_msg("Attempt to read non-int as int");
    }
    return a->value;
}

/*
 * Built in combinators.
 */
list *S,*K,*I;
list *plus;
list *pair;
list *head,*tail;
list *true,*false;
list *cond;
list *U,*Y;
list *nil,*equal,*times,*minus,*divide,*less,*lesseq,*or,*and,*not;
list *B,*C,*Sdash,*Bstar,*Cdash;

/*
 * A dictionary is a simple linked list structure that
 * maps C strings to void * pointers.
 */
typedef struct dictionary {
    struct dictionary *next;
    char *name;
    void *value;
} dictionary;

/*
 * Look up given key in dictionary. If doesn't exist
 * thenmake new entry with NULL value.
 */
void **lookup(dictionary **pointer,const char *name) {
    dictionary *p;
    for (p = *pointer; p!=NULL; p = p->next) {
	if (!strcmp(p->name,name)) {
	    return &p->value;
	}
    }
    p = (dictionary *)allocate_memory(sizeof(dictionary));
    p->next = *pointer;
    p->name = duplicate_string(name);
    p->value = NULL;
    *pointer = p;

    return &p->value;
}

/*
 * Test whether dictionary contains given string
 * as key.
 */
int contains(dictionary *pointer,char *name) {
    dictionary *p;
    for (p = pointer; p!=NULL; p = p->next) {
	if (!strcmp(p->name,name)) {
	    return 1;
	}
    }

    return 0;
}

/*
 * Lexer
 */
typedef enum {
    TOKEN_ERROR,

    TOKEN_IDENTIFIER,
    TOKEN_CONSTANT,

    TOKEN_LPAREN, TOKEN_RPAREN,
    TOKEN_NIL,
    TOKEN_EQUAL,

    /* Definitions */
    TOKEN_DEF, TOKEN_WHERE, TOKEN_SEMICOLON, TOKEN_PERIOD,

    /* List operations */
    TOKEN_COLON, TOKEN_HEAD, TOKEN_TAIL,

    /* Conditional */
    TOKEN_IF, TOKEN_THEN, TOKEN_ELSE,

    /* Arithmetic */
    TOKEN_PLUS, TOKEN_MINUS, TOKEN_TIMES, TOKEN_DIVIDE,

    /* Comparison */
    TOKEN_GREATER, TOKEN_LESS, TOKEN_GREATEREQ, TOKEN_LESSEQ,

    /* Logical */
    TOKEN_OR,TOKEN_AND,TOKEN_NOT, TOKEN_TRUE, TOKEN_FALSE, TOKEN_EOF
} token_type;

typedef struct {
    token_type type;
    union {
        char *string_value;
        token_type *token_value;
        int int_value;
    } value;
} token;

token *current_token;

token *make_token_string(int t,char *v) {
    token *tok = (token *)allocate_memory(sizeof(token));

    tok->type = t;
    tok->value.string_value = v;

    return tok;
}

token *make_token_token(int t,token_type *v) {
    token *tok = (token *)allocate_memory(sizeof(token));

    tok->type = t;
    tok->value.token_value = v;

    return tok;
}

token *make_token_int(int t,int v) {
    token *tok = (token *)allocate_memory(sizeof(token));

    tok->type = t;
    tok->value.int_value = v;

    return tok;
}

dictionary *keywords = 0;

/*
 * Parse either a keyword or an identifier.
 * First character should be alphabetic.
 */
token *lex_keyword_or_identifier() {
    /* Potential buffer overflow */
    char name[4096];
    int i = 0;

    name[i++] = (char)current_char;
    next_char();

    while (isalnum(current_char)) {
	name[i++] = (char)current_char;
	next_char();
    }

    name[i] = 0;
    if (contains(keywords,name)) {
	return make_token_token(*(token_type *)lookup(&keywords,name),0);
    }

    return make_token_string(TOKEN_IDENTIFIER,duplicate_string(name));
}

/*
 * Parse integer. First character should be
 * digit.
 */
int get_number() {
    /* Potential buffer overflow */
    char number[256],*p = number;

    while (isdigit(current_char)) {
	*p++ = (char)current_char;
	next_char();
    }
    *p = 0;

    return atoi(number);
}

token *lex_numeric_constant() {
    return make_token_int(TOKEN_CONSTANT,get_number());
}

/*
 * Parse various types of operator.
 */
token *lex_operator() {
    static char *op_chars = "()=.:;+-*/";
    char *p = index(op_chars,current_char);
    if (p!=NULL) {
	static int token_table[] = {
	    TOKEN_LPAREN, TOKEN_RPAREN,
	    TOKEN_EQUAL, TOKEN_PERIOD,
	    TOKEN_COLON, TOKEN_SEMICOLON,
	    TOKEN_PLUS, TOKEN_MINUS,
	    TOKEN_TIMES, TOKEN_DIVIDE
	};
	next_char();
	return make_token_int(token_table[p-op_chars],0);
    }

    if (current_char=='<') {
	if (next_char()=='=') {
	    next_char();
	    return make_token_int(TOKEN_LESSEQ,0);
	}
	return make_token_int(TOKEN_LESS,0);
    }
    if (current_char=='>') {
	if (next_char()=='=') {
	    next_char();
	    return make_token_int(TOKEN_GREATEREQ,0);
	}
	return make_token_int(TOKEN_GREATER,0);
    }
    error_msg("Unrecognised symbol");
}

void lex_white_space() {
    while (isspace(current_char)) {
	next_char();
    }
}

/*
 * Return next token in input.
 * Returns a keyword, identifier, number, operator
 * or end-of-file marker.
 */
token *lex() {
    lex_white_space();
    if (isalpha(current_char)) {
	return lex_keyword_or_identifier();
    } else if (isdigit(current_char)) {
	return lex_numeric_constant();
    } else if (current_char==EOF) {
	return make_token_int(TOKEN_EOF,0);
    } else {
	return lex_operator();
    }
}

/*
 * The parser code follows.
 * This is a simple recursive descent parser.
 * SASL doesn't need anything fancy.
 * Note that the grammar has been refactored slightly
 * from the BNF in the comments.
 */

list *parse_expr();

/*
 * Expect a specified single token in the parse stream.
 * E.g. after an 'if' we expect a 'then' and an 'else'
 */
void expect(int type,char *message) {
    if (current_token->type!=type) {
	error_msg(message);
    }
    current_token = lex();
}

/*
 * CONDEXPR := 'if' EXPR 'then' EXPR 'else' EXPR
 */
list *parse_condexpr() {
    list *a,*b,*c;
    expect(TOKEN_IF,"Expected 'if'");
    a = parse_expr();
    expect(TOKEN_THEN,"Missing 'then'");
    b = parse_expr();
    expect(TOKEN_ELSE,"Missing 'else'");
    c = parse_expr();

    return apply3(cond,a,b,c);
}

/*
 * NAME := identifier
 */
list *parse_name() {
    if (current_token->type==TOKEN_IDENTIFIER) {
	list *r = make_var(current_token->value.string_value);
	current_token = lex();

	return r;
    } else {
	error_msg("Expected a name");
    }
}

/*
 * ATOMIC := CONSTANT | IDENTIFIER | '(' EXPR ')' | 'true' | 'false' | 'nil' |
 *		'head' | 'tail' | 'not'
 */
list *parse_atomic() {
    list *r;
    switch (current_token->type) {
    case TOKEN_CONSTANT:
	r = make_int(current_token->value.int_value);
	current_token = lex();
	return r;
    case TOKEN_IDENTIFIER:
	r = make_var(current_token->value.string_value);
	current_token = lex();
	return r;
    case TOKEN_LPAREN:
	current_token = lex();
	r = parse_expr();
	expect(TOKEN_RPAREN,"Missing ')'");
	return r;
    case TOKEN_TRUE:
	current_token = lex();
	return true;
    case TOKEN_FALSE:
	current_token = lex();
	return false;
    case TOKEN_NIL:
	current_token = lex();
	return nil;
    case TOKEN_HEAD:
	current_token = lex();
	return head;
    case TOKEN_TAIL:
	current_token = lex();
	return tail;
    case TOKEN_NOT:
	current_token = lex();
	return not;
    default:
	error_msg("Parse error");
    }
}

list *parse_sequence(list *r,token_type token,list *(*type)(),list *op) {
    while (current_token->type==token) {
	current_token = lex();
	r = apply2(op,r,(*type)());
    }
    return r;
}

list *parse_rsequence(list *r,token_type token,list *(*type)(),list *op) {
    while (current_token->type==token) {
	current_token = lex();
	r = apply2(op,(*type)(),r);
    }
    return r;
}

/*
 * PRODUCT := ATOMIC { ('*' | '/') ATOMIC }
 */
list *parse_product() {
    list *r = parse_atomic(),*or;
    do {
	or = r;
	r = parse_sequence(r,TOKEN_TIMES,parse_atomic,times);
	r = parse_sequence(r,TOKEN_DIVIDE,parse_atomic,divide);
    } while (r!=or);
    return r;
}

/*
 * SUM := PRODUCT { ('+' | '-') PRODUCT }
 */
list *parse_sum() {
    list *r = parse_product(),*or;
    do {
	or = r;
	r = parse_sequence(r,TOKEN_PLUS,parse_product,plus);
	r = parse_sequence(r,TOKEN_MINUS,parse_product,minus);
    } while (r!=or);
    return r;
}

/*
 * COMPARISONEXPR := SUM { ('=' | '<' | '>' | '<=' | '>=') SUM }
 */
list *parse_comparisonexpr() {
    list *r = parse_sum(),*or;
    do {
	or = r;
	r = parse_sequence(r,TOKEN_EQUAL,parse_sum,equal);
	r = parse_sequence(r,TOKEN_LESS,parse_sum,less);
	r = parse_sequence(r,TOKEN_LESSEQ,parse_sum,lesseq);
	r = parse_rsequence(r,TOKEN_GREATER,parse_sum,less);
	r = parse_rsequence(r,TOKEN_GREATEREQ,parse_sum,lesseq);
    } while (r!=or);
    return r;
}

/*
 * LOGICALPRODUCT := COMPARISONEXPR { 'and' COMPARISONEXPR }
 */
list *parse_logicalproduct() {
    list *r = parse_comparisonexpr(),*or;
    r = parse_sequence(r,TOKEN_AND,parse_comparisonexpr,and);
    return r;
}

/*
 * LOGICALSUM := LOGICALPRODUCT { 'or' LOGICALPRODUCT }
 */
list *parse_logicalsum() {
    list *r = parse_logicalproduct();
    r = parse_sequence(r,TOKEN_OR,parse_logicalproduct,or);
    return r;
}

/*
 * COMBEXPR := LOGICALSUM { LOGICALSUM }
 */
list *parse_combexpr() {
    list *r = parse_logicalsum();
    for (;;) {
	/*
	 * Identify end of sequence of arguments to
	 * combinator.
	 */
	static char final[] = {
	    TOKEN_EOF, TOKEN_RPAREN, TOKEN_THEN,
	    TOKEN_ELSE, TOKEN_PERIOD, TOKEN_SEMICOLON,
	    TOKEN_WHERE, TOKEN_COLON, 0
	};
	if (index(final,current_token->type)) {
	    return r;
	}
	r = apply(r,parse_atomic());
    }
}

/*
 * LISTEXPR := COMBEXPR [ ':' LISTEXPR ]
 */
list *parse_listexpr() {
    list *r = parse_combexpr();
    r = parse_sequence(r,TOKEN_COLON,parse_listexpr,pair);
    return r;
}

list *parse_abstraction();
list *parse_recursive_abstraction(list *name);
list *abstract(list *var,list *expr);
int mutual_recursion(list *l);

void display(list *);

/*
 * This is the main expression parser.
 * This is also where recursive defintions (as well as mutually
 * recursive definitions) are identified.
 *
 * EXPR := (CONDEXPR | LISTEXPR)
 *	{ WHERE NAME ABSTRACTION ';' { NAME ABSTRACTION ';' } }
 */
list *parse_expr() {
    list *r,*abstraction;
    if (current_token->type==TOKEN_IF) {
	    return parse_condexpr();
    }
    r = parse_listexpr();
    for (;;) {
	if (current_token->type==TOKEN_WHERE) {
	    list *definitions = 0,*dstart;
	    list *name,*lhs,*rhs;

	    /*
	     * Get list of all definitions in this 'where' clause.
	     */
	    do {
		list *expr;
		current_token = lex();
		name = parse_name();
		expr = parse_abstraction();
		definitions = apply(apply(name,expr),definitions);
	    } while (current_token->type==TOKEN_SEMICOLON);

#if 0
	    /*
	     * Special case for single definition
	     * Buggy.
	     */
	    if (definitions && definitions->tail==0) {
		    /*
		     * Only one definition
		     */
		    r = abstract(definitions->head->head,r);
		    return apply(r,definitions->head->tail);
	    }
#endif

	    rhs = nil;
	    lhs = apply(K,r);
	    if (!mutual_recursion(definitions)) {
		while (definitions) {
		    rhs = apply(apply(pair,TH(definitions)),rhs);
		    lhs = apply(U,abstract(HH(definitions),lhs));
		    definitions = T(definitions);
		}
		return apply(lhs,rhs);
	    } else {
		/*
		 * Mutually recursive definitions.
		 */
		dstart = definitions;
		while (definitions) {
		    rhs = apply(apply(pair,TH(definitions)),rhs);
		    lhs = apply(U,abstract(HH(definitions),lhs));
		    definitions = T(definitions);
		}
		rhs = apply(K,rhs);
		definitions = dstart;
		while (definitions) {
		    rhs = apply(U,abstract(HH(definitions),rhs));
		    definitions = T(definitions);
		}
		rhs = apply(Y,rhs);
		return apply(lhs,rhs);
	    }

#if 0
	    /*
	     * Name of variable being defined.
	     * Not sure why I commented this out.
	     */
	    name = parse_name();
	    abstraction = parse_recursive_abstraction(name);
	    r = abstract(name,r);
	    return apply(r,abstraction);
#endif
	} else {
		return r;
	}
    }
    return r;
}

char get_atom(list *a) {
    if (!is_atom(a)) {
	error_msg("Attempt to read non-atom as atom");
    }
    return a->name;
}

const char *get_var(list *a) {
    if (!is_var(a)) {
	error_msg("Attempt to read non-var as var");
    }
    return a->var_name;
}

/*
 * Returns 1 if expression 'expr' contains reference to
 * any variable in the list 'var'.
 */
int depends_on(list *expr,list *var) {
    if (is_var(expr) && !strcmp(expr->var_name,var->var_name)) {
	return 1;
    }
    if (is_int(expr) || is_var(expr) || is_atom(expr)) {
	return 0;
    }
    return depends_on(H(expr),var) || depends_on(T(expr),var);
}

/*
 * Input is a list of pairs [(var_i,expr_i)].
 * Return 1 if any expr_i contains any var_i.
 */
int mutual_recursion(list *l) {
    list *p,*q = l;

    /*
     * For each expr...
     */
    while (q) {
	p = l;

	/*
	 * ...for each name...
	 */
	while (p) {
	    if (depends_on(TH(q),HH(p))) {
		return 1;
	    }
	    p = T(p);
	}
	q = T(q);
    }

    return 0;
}

list *abstract(list *var,list *expr) {
    if (is_var(expr) && !strcmp(expr->var_name,var->var_name)) {
	return I;
    }
    if (is_int(expr) || is_var(expr) || is_atom(expr)) {
	return apply(K,expr);
    }
    return apply(apply(S,abstract(var,H(expr))),abstract(var,T(expr)));
}

/*
 * RECURSIVEABSTRACTION := { NAME } '=' EXPR
 *
 * Note: Not currently used.
 */
list *parse_recursive_abstraction(list *name) {
    list *names,*expr;
    /*
     * Parse arguments.
     */
    names = nil;
    while (current_token->type!=TOKEN_EQUAL) {
	list *name = parse_name();
	names = apply(name,names);
    }
    /* 
     * Skip '='
     */
    current_token = lex();
    expr = parse_expr();
    while (names!=nil) {
	expr = abstract(names->head,expr);
	names = T(names);
    }

    if (depends_on(expr,name)) {
	expr = abstract(name,expr);
	return apply(Y,expr);
    }
    return expr;
}

/*
 * ABSTRACTION := { NAME } '=' EXPR
 */
list *parse_abstraction() {
    list *names,*expr;
    /*
     * Parse arguments.
     */
    names = nil;
    while (current_token->type!=TOKEN_EQUAL) {
	list *name = parse_name();
	names = apply(name,names);
    }
    /* 
     * Skip '='
     */
    current_token = lex();
    expr = parse_expr();
    while (names!=nil) {
	expr = abstract(names->head,expr);
	names = T(names);
    }
    return expr;
}

dictionary *defs = 0;

/*
 * DEF := NAME ABSTRACTION '.'
 */
void parse_def() {
    list **location;
    list *name = parse_name();
    list *expr;
    const char *var_name = get_var(name);
    location = (list **)lookup(&defs,var_name);

    expr = parse_abstraction();

    *location = expr;
    expect(TOKEN_PERIOD,"Expected '.' after 'def'");
}

list *stack_eval(list *);

void display(list *l) {
    switch (l->type) {
    case COMB_ATOM:
	putchar(get_atom(l));
	break;
    case COMB_INTEGER:
	printf("%d",get_int(l));
	break;
    case COMB_PAIR:
	putchar('[');
	display(stack_eval(l->head));
	l = T(l);
	while (is_pair(l)) {
	    putchar(',');
	    display(stack_eval(l->head));
	    l = T(l);
	}
	putchar(':');
	display(stack_eval(l));
	putchar(']');
	break;
    case COMB_VAR:
	printf("Var(%s)",get_var(l));
	break;
    default:
	display(l->head);
	putchar(' ');
	if (!is_comb(T(l))) {
	    display(T(l));
	} else {
	    putchar('(');
	    display(T(l));
	    putchar(')');
	}
    }
}

/*
 * Substitute variables stored in dictionary 'defs' in expressions.
 * Note: this is part of the compilation, not something
 * that happens at run time.
 */
list *substitute(list *expr) {
    if (is_comb(expr)) {
	expr->head = substitute(expr->head);
	expr->tail = substitute(expr->tail);
	return expr;
    } else if (is_var(expr)) {
	const char *s = get_var(expr);
	return *(list **)lookup(&defs,s);
    } else {
	return expr;
    }
}

int optimise(list *);

/*
 * PROGRAM := { DEF } EXPR
 */
list *parse_program() {
    list *expr;
    dictionary *d;
    while (current_token->type==TOKEN_DEF) {
	current_token = lex();
	parse_def();
    }
    expr = parse_expr();
    optimise(expr);
    for (d = defs; d; d = d->next) {
	optimise(d->value);
    }
    for (d = defs; d; d = d->next) {
	d->value = substitute(d->value);
    }
    expr = substitute(expr);
    return expr;
}

/*
 * Compare two lists for equality.
 */
int list_eq(list *a,list *b) {
    if (a->type!=b->type) {
	return 0;
    }
    switch (a->type) {
    case COMB_ATOM:
	return get_atom(a)==get_atom(b);
    case COMB_PAIR:
	return list_eq(H(a),H(b)) && list_eq(T(a),T(b));
    case COMB_COMB:
	error_msg("Can't compare unevaluated expressions");
    case COMB_INTEGER:
	return get_int(a)==get_int(b);
    }
    error_msg("Invalid equality comparison");
}

int list_lt(list *a,list *b) {
    if (a->type!=COMB_INTEGER || b->type!=COMB_INTEGER) {
	error_msg("Can't compare non-integers");
    }
    return get_int(a)<get_int(b);
}

int list_le(list *a,list *b) {
    if (a->type!=COMB_INTEGER || b->type!=COMB_INTEGER) {
	error_msg("Can't compare non-integers");
    }
    return get_int(a)<=get_int(b);
}

/*
 * Implements a->Ia
 * The extra I looks superfulous but has certain uses.
 */
void copy(list *a,list *b) {
    *a = is_atom(b) ? *apply(I,b) : *b;
}

/*
 * This implements a number of shortcuts that speed up reductions.
 * They look like reduction rules but note that they are executed
 * at compile time, not reduction time.
 */
int optimise(list *a) {
    int flag;
    do {
	flag = 0;

	/*
	 * S(Kf)(Kg) -> K(fg)
	 */
	if (is_comb(a)
	    && is_comb(H(a))
	    && is_comb(TH(a))
	    && is_comb(T(a))
	    && HH(a)==S
	    && HTH(a)==K
	    && HT(a)==K) {
		*a = *apply(K,apply(TTH(a),TT(a)));
		flag |= 1;
	}

	/*
	 * S(Kf)I -> f
	 */
	if (is_comb(a)
	    && is_comb(H(a))
	    && is_comb(TH(a))
	    && HH(a)==S
	    && HTH(a)==K
	    && T(a)==I) {
		copy(a,TTH(a));
		flag |= 1;
	}

	/*
	 * S(Kf)(Bgh) -> B*fgh
	 */
	if (is_comb(a)
	    && is_comb(H(a))
	    && is_comb(TH(a))
	    && is_comb(T(a))
	    && is_comb(HT(a))
	    && HH(a)==S
	    && HTH(a)==K
	    && HHT(a)==B) {
		*a = *apply3(Bstar,TTH(a),THT(a),TT(a));
		flag |= 1;
	}

	/*
	 * S(Kf)g->Bfg
	 */
	if (is_comb(a)
	    && is_comb(H(a))
	    && is_comb(TH(a))
	    && HH(a)==S
	    && HTH(a)==K) {
		*a = *apply2(B,TTH(a),T(a));
		flag |= 1;
	}

	/*
	 * S(Bfg)(Kh) -> C'fgh
	 */
	if (is_comb(a)
	    && is_comb(H(a))
	    && is_comb(TH(a))
	    && is_comb(HTH(a))
	    && is_comb(T(a))
	    && HH(a)==S
	    && HHTH(a)==B
	    && HT(a)==K) {
		*a = *apply3(Cdash,THTH(a),TTH(a),TT(a));
		flag |= 1;
	}

	/*
	 * Sf(Kg)->Cfg;
	 */
	if (is_comb(a)
	    && is_comb(H(a))
	    && is_comb(T(a))
	    && HH(a)==S
	    && HT(a)==K) {
		*a = *apply2(C,TH(a),TT(a));
		flag |= 1;
	}

	/*
	 * S(Bfg)h -> S'fgh
	 */
	if (is_comb(a)
	    && is_comb(H(a))
	    && is_comb(TH(a))
	    && is_comb(HTH(a))
	    && HH(a)==S
	    && HHTH(a)==B) {
		*a = *apply3(Sdash,THTH(a),TTH(a),T(a));
		flag |= 1;
	}
	if (is_comb(a)) {
	    flag |= optimise(H(a)) | optimise(T(a));
	}
    } while (flag);

    return 0;
}

/*
 * Core combinatorial reduction engine.
 * This is where program execution takes place.
 */
list *stack_eval(list *a) {
    list *stack[1024],*result;
    int sp = 0;
    int i;

    stack[sp] = a;

    /*
     * Reduction phase
     */
    while (1) {
	if (is_comb(stack[sp])) {
	    /*
	     * 'Unpack' top of stack until it is an atom
	     */
	    list *a = stack[sp];
	    ++sp;
	    stack[sp] = H(a);
	    stack[sp-1] = T(a);
	    continue;
	} else if (sp>=1) {
	    char combinator = stack[sp]->name;
	    list *a = stack[sp-1];
	    switch (combinator) {
	    case 'I':
		--sp;
		continue;
	    case 'h':
		--sp;
		a = stack_eval(a);
		if (!is_pair(a)) {
		    error_msg("head needs a list");
		}
		stack[sp] = H(a);
		continue;
	    case 'Y':
		--sp;
		stack[sp] = apply(a,apply(Y,a));
		continue;
	    case '!':
		--sp;
		stack[sp] = a==true ? false : true;
		continue;
	    case 't':
		--sp;
		a = stack_eval(a);
		if (!is_pair(a)) {
		    error_msg("tail needs a list");
		}
		stack[sp] = T(a);
		continue;
	    default:
		if (sp>=2) {
		    list *b = stack[sp-2];
		    switch (combinator) {
		    case 'K':
			sp -= 2;
			stack[sp] = a;
			continue;
		    case ':':
			sp -= 2;
			stack[sp] = make_pair(a,b);
			continue;
		    case 'U':
			stack[sp] = a;
			stack[sp-1] = apply(head,b);
			stack[sp-2] = apply(tail,b);
			continue;
		    case '+':
			a = stack_eval(a);
			b = stack_eval(b);
			sp -= 2;
			stack[sp] = make_int(get_int(a)+get_int(b));
			continue;
		    case '-':
			a = stack_eval(a);
			b = stack_eval(b);
			sp -= 2;
			stack[sp] = make_int(get_int(a)-get_int(b));
			continue;
		    case '*':
			a = stack_eval(a);
			b = stack_eval(b);
			sp -= 2;
			stack[sp] = make_int(get_int(a)*get_int(b));
			continue;
		    case '/':
			a = stack_eval(a);
			b = stack_eval(b);
			sp -= 2;
			stack[sp] = make_int(get_int(a)/get_int(b));
			continue;
		    case '=':
			a = stack_eval(a);
			b = stack_eval(b);
			sp -= 2;
			stack[sp] = list_eq(a,b) ? true : false;
			continue;
		    case '<':
			a = stack_eval(a);
			b = stack_eval(b);
			sp -= 2;
			stack[sp] = list_lt(a,b) ? true : false;
			continue;
		    case 'l':
			a = stack_eval(a);
			b = stack_eval(b);
			sp -= 2;
			stack[sp] = list_le(a,b) ? true : false;
			continue;
		    case '|':
			a = stack_eval(a);
			sp -= 2;
			stack[sp] = (a==true || stack_eval(b)==true) ? true : false;
			continue;
		    case '&':
			a = stack_eval(a);
			sp -= 2;
			stack[sp] = (a==false || stack_eval(b)==false) ? false : true;
			continue;
		    default:
			if (sp>=3) {
			    list *c = stack[sp-3];
			    switch (combinator) {
			    case 'S':
				--sp;
				stack[sp] = a;
				stack[sp-1] = c;
				stack[sp-2] = apply(b,c);
				continue;
			    case 'B':
				sp -= 2;
				stack[sp] = a;
				stack[sp-1] = apply(b,c);
				continue;
			    case 'C':
				--sp;
				stack[sp] = a;
				stack[sp-1] = c;
				stack[sp-2] = b;
				continue;
			    case '?':
				a = stack_eval(a);
				sp -= 3;
				if (a==false) {
				    stack[sp] = c;
				} else if (a==true) {
				    stack[sp] = b;
				} else {
				    error_msg("'cond' expects 'true' or 'false'");
				}
				continue;
			    default:
				if (sp>=4) {
				    list *d = stack[sp-4];
				    switch (combinator) {
				    case 's':
					sp -= 2;
					stack[sp] = a;
					stack[sp-1] = apply(b,d);
					stack[sp-2] = apply(c,d);
					continue;
				    case 'b':
					sp -= 3;
					stack[sp] = a;
					stack[sp-1] = apply(b,apply(c,d));
					continue;
				    case 'c':
					sp -= 2;
					stack[sp] = a;
					stack[sp-1] = apply(b,d);
					stack[sp-2] = c;
					continue;
				    }
				}
			    }
			}
		    }
		}
	    }
	}
	break;
    }


    /*
     * Reassemble result
     */
    result = stack[sp--];
    for (i = sp; i>=0; --i) {
	result = apply(result,stack[i]);
    }
    
    /*
     * If we've evaluated to a combinator expression we should overwrite it.
     * But we musn't copy atoms as they are unique.
     */
    if (is_comb(a) && !is_atom(result)) {
	*a = *result;
	return a;
    } else {
	return result;
    }
}

/*
 * All of the combinators
 */
void constants() {
    S	    = make_atom('S');
    K	    = make_atom('K');
    I	    = make_atom('I');
    plus    = make_atom('+');
    times   = make_atom('*');
    minus   = make_atom('-');
    divide  = make_atom('/');
    pair    = make_atom(':');
    head    = make_atom('h');
    tail    = make_atom('t');
    true    = make_atom('T');
    false   = make_atom('F');
    cond    = make_atom('?');
    U	    = make_atom('U');
    Y	    = make_atom('Y');
    nil	    = make_atom('n');
    equal   = make_atom('=');
    less    = make_atom('<');
    lesseq  = make_atom('l');
    and	    = make_atom('&');
    or	    = make_atom('|');
    not	    = make_atom('!');
    B	    = make_atom('B');
    C	    = make_atom('C');
    Sdash   = make_atom('s');
    Bstar   = make_atom('b');
    Cdash   = make_atom('c');
}

void make_keywords() {
    *lookup(&keywords,"def")	= (void *)TOKEN_DEF;
    *lookup(&keywords,"if")	= (void *)TOKEN_IF;
    *lookup(&keywords,"then")	= (void *)TOKEN_THEN;
    *lookup(&keywords,"else")	= (void *)TOKEN_ELSE;
    *lookup(&keywords,"where")	= (void *)TOKEN_WHERE;
    *lookup(&keywords,"true")	= (void *)TOKEN_TRUE;
    *lookup(&keywords,"false")	= (void *)TOKEN_FALSE;
    *lookup(&keywords,"nil")	= (void *)TOKEN_NIL;
    *lookup(&keywords,"hd")	= (void *)TOKEN_HEAD;
    *lookup(&keywords,"tl")	= (void *)TOKEN_TAIL;
    *lookup(&keywords,"or")	= (void *)TOKEN_OR;
    *lookup(&keywords,"and")	= (void *)TOKEN_AND;
    *lookup(&keywords,"not")	= (void *)TOKEN_NOT;
}

int main(int argc,char **argv) {
    list *t;

    constants();
    make_keywords();

    next_char();
    current_token = lex();
    t = parse_program();
    t = stack_eval(t);
    display(t);
    printf("\n");

    return 0;
}
