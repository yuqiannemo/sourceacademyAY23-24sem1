/*

CS1101S Lecture L11: CSE Machine

This program contains a CSE machine for a simple
functional programming language, including:
* literal values: numbers, booleans, strings
* conditional statements and expressions
* sequences and blocks
* simple functions (body consists of a single 
                    return statement)

Examples at the end of the program
*/

function evaluate(program) { 
    let C = list(make_block(program));
    let S = null;
    let E = the_global_environment;
    while (! is_null(C)) {
        display_control(C);
        display_stash(S);   
        display_environment(E);
        const command = head(C);
        C = tail(C);
        
        // expressions and statements
        if (is_literal(command)) {
            S = pair(literal_value(command), S);
        } else if (is_binary_operator_combination(command)) {
            C = pair(first_operand(command),
                 pair(second_operand(command),
                  pair(make_binary_operator_instruction(
                   operator_symbol(command)),
                   C)));
        } else if (is_unary_operator_combination(command)) {
            C = pair(first_operand(command),
                  pair(make_unary_operator_instruction(
                   operator_symbol(command)),
                   C));
        } else if (is_sequence(command)) {
            const body = sequence_statements(command);
            C = is_null(body)
                ? pair(make_literal(undefined), C)
                : is_null(tail(body))
                ? pair(head(body), C)
                : pair(head(body),
                    pair(make_pop_instruction(),
                      pair(make_sequence(tail(body)),
                        C)));
        } else if (is_conditional(command)) {
            C = pair(conditional_predicate(command),
                  pair(make_branch_instruction(
                         conditional_consequent(command),
                         conditional_alternative(command)),
                    C));
        } else if (is_block(command)) {
            const locals = scan_out_declarations(
                             block_body(command));
            const unassigneds = list_of_unassigned(locals);
            C = pair(block_body(command),
                  pair(make_env_instruction(E),
                    C));
            E = extend_environment(locals, unassigneds, E);
        } else if (is_function_declaration(command)) {
            C = pair(function_decl_to_constant_decl(command),
                     C);
        } else if (is_declaration(command)) {
            C = pair(make_assignment(
                       declaration_symbol(command),
                       declaration_value_expression(command)),
                     C);
        } else if (is_name(command)) {
            S = pair(lookup_symbol_value(
                         symbol_of_name(command),
                         E),
                     S);
        } else if (is_assignment(command)) {
            C = pair(assignment_value_expression(command),
                  pair(make_assign_instruction(
                         assignment_symbol(command)),
                       C));
        } else if (is_lambda_expression(command)) {
            S = pair(
                  is_return_statement(lambda_body(command))
                  ? make_simple_function(
                      lambda_parameter_symbols(command),
                      return_expression(lambda_body(command)),
                      E)
                  : make_complex_function(
                      lambda_parameter_symbols(command),
                      make_sequence(
                        list(
                          lambda_body(command),
                          make_return_statement(
                            make_literal(undefined)))),
                      E),
                  S);
        } else if (is_application(command)) {
            const arg_exprs = arg_expressions(command);
            C = pair(function_expression(command),
                  append(arg_exprs, 
                    pair(make_call_instruction(
                           length(arg_exprs)), C)));
                           
        } else if (is_logical_composition(command)) {
            C = pair(
                  logical_symbol(command) === "&&"
                  ? make_conditional_expression(
                      logical_composition_first_component(
                        command),
                      logical_composition_second_component(
                        command),
                      make_literal(false))
                  : make_conditional_expression(
                      logical_composition_first_component(command),
                      make_literal(true),
                      logical_composition_second_component(command)),
                C);
        } else if (is_return_statement(command)) {
            C = pair(return_expression(command),
                  pair(make_return_instruction(),
                    C));
        } else if (is_while_loop(command)) {
            C = pair(
                  make_conditional_statement(
                    while_loop_predicate(command),
                    make_sequence(
                      list(while_loop_body(command),
                           command)),
                    make_sequence(null)),
                  C);
        } else if (is_for_loop(command)) {
            C = pair(
                  make_block(
                    make_sequence(
                      list(
                        for_loop_init(command),
                        make_while_loop(
                          for_loop_predicate(command),
                          make_sequence(
                            list(
                              for_loop_body(command),
                              for_loop_update(command)
                              )))))), C);
         } else if (is_array_expression(command)) {
             const array_expressions = array_elements(command);
             C = append(array_expressions,
                   pair(make_array_instruction(
                          length(array_expressions)),
                        C));
         } else if (is_array_access(command)) {
             C = pair(array_access_array_expression(command),
                   pair(array_access_index_expression(command),
                     pair(make_array_access_instruction(),
                        C)));         
         } else if (is_array_assignment(command)) {
             const access = 
                 array_assignment_access(command);
             C = pair(array_access_array_expression(access),
                   pair(array_access_index_expression(access),
                     pair(array_assignment_value_expression(
                            command),
                       pair(make_array_assignment_instruction(),
                         C)))); 
                        
        // machine instructions
        } else if (is_pop_instruction(command)) {
            S = tail(S);
        } else if (is_binary_operator_instruction(command)) {
            S = pair(apply_binary(operator_instruction_symbol(command),
                                  head(tail(S)), head(S)),
                 tail(tail(S)));
        } else if (is_unary_operator_instruction(command)) {
            S = pair(apply_unary(operator_instruction_symbol(command),
                       head(S)),
                 tail(S));
        } else if (is_branch_instruction(command)) {
            C = pair(is_truthy(head(S))
                     ? branch_instruction_consequent(command)
                     : branch_instruction_alternative(command),
                     C);
            S = tail(S);
        } else if (is_assign_instruction(command)) {
            assign_symbol_value(
               assign_instruction_symbol(command), 
               head(S),
               E);
        } else if (is_env_instruction(command)) {
            E = env_instruction_environment(command);
        } else if (is_call_instruction(command)) {
            const arity = call_instruction_arity(command);
            let args = null;
            let n = arity;
            while (n > 0) {
                args = pair(head(S), args);
                S = tail(S);
                n = n - 1;
            }
            const fun = head(S);
            S = tail(S);
            if (is_primitive_function(fun)) {
                S = pair(apply_primitive_function(fun, args),
                      S);
            } else if (is_simple_function(fun)) {
                C = pair(function_body(fun), 
                      pair(make_env_instruction(E),
                        C));
                E = extend_environment(
                       function_parameters(fun), 
                       args, 
                       function_environment(fun));
            } else { // it's a complex function
                C = pair(function_body(fun), 
                      pair(make_marker(),
                        pair(make_env_instruction(E),
                          C)));
                E = extend_environment(
                       function_parameters(fun), 
                       args, 
                       function_environment(fun));
            }
        } else if (is_return_instruction(command)) {
            if (is_marker(head(C))) {
                C = tail(C);
            } else {
                C = pair(command, tail(C));
            }
        } else if (is_array_instruction(command)) {
            const arr = [];
            const size = array_instruction_size(command);
            for (let i = size - 1; i >= 0; i = i - 1) {
                arr[i] = head(S);
                S = tail(S);
            }
            S = pair(arr, S);
        } else if (is_array_access_instruction(command)) {
            const index = head(S);
            const array = head(tail(S));
            S = pair(array[index], tail(tail(S)));
        } else if (is_array_assignment_instruction(command)) {
            const val = head(S);
            const index = head(tail(S));
            const array = head(tail(tail(S)));
            array[index] = val;
            S = pair(val, tail(tail(tail(S))));
        } else {
           error(command, "unknown command:");
        }
    }
    return head(S); 
}

// scan_out_declarations and list_of_unassigned
// (SICP JS 4.1.1)

function scan_out_declarations(component) {
    return is_sequence(component)
           ? accumulate(append,
                        null,
                        map(scan_out_declarations,
                            sequence_statements(component)))
           : is_declaration(component)
           ? list(declaration_symbol(component))
           : null;
}

function list_of_unassigned(symbols) {
    return map(symbol => "*unassigned*", symbols);
}

function apply_binary(operator, op1, op2) {
    return operator === "+"
           ? op1 + op2
           : operator === "-"
           ? op1 - op2 
           : operator === "*" 
           ? op1 * op2 
           : operator === "/" 
           ? op1 / op2
           : operator === "%" 
           ? math_pow(op1, op2)
           : operator === "<" 
           ? op1 < op2
           : operator === ">" 
           ? op1 > op2
           : operator === "<=" 
           ? op1 <= op2
           : operator === ">=" 
           ? op1 >= op2
           : operator === "===" 
           ? op1 === op2
           : operator === "!==" 
           ? op1 !== op2
           : error(operator, "Unknown operator");
}

function apply_unary(operator, op) {
    return operator === "-unary"
           ? - op
           : operator === "!"
           ? ! op
           : error(operator, "Unknown operator");
}
//
// syntax functions (SICP JS 4.1.2)
//

function is_tagged_list(component, the_tag) {
    return is_pair(component) && head(component) === the_tag;
}

// literals

function is_literal(component) {
    return is_tagged_list(component, "literal");
}
function literal_value(component) {    
    return head(tail(component));
}
function make_literal(val) {
    return list("literal", val);
}

// names

function is_name(component) {
    return is_tagged_list(component, "name");
}
function make_name(symbol) {
    return list("name", symbol);
}
function symbol_of_name(component) {
    return head(tail(component));
}

// operator combinations

function is_operator_combination(component) {	    
    return is_unary_operator_combination(component) ||
           is_binary_operator_combination(component);
}
function is_unary_operator_combination(component) {	    
    return is_tagged_list(component, "unary_operator_combination");
}
function is_binary_operator_combination(component) {	    
    return is_tagged_list(component, "binary_operator_combination");
}
function operator_symbol(component) {
    return list_ref(component, 1);
}
function first_operand(component) {
    return list_ref(component, 2);
}
function second_operand(component) {
    return list_ref(component, 3);
}

// sequences

function is_sequence(stmt) {
   return is_tagged_list(stmt, "sequence");
}
function sequence_statements(stmt) {   
   return head(tail(stmt));
}
function make_sequence(stmts) {   
   return list("sequence", stmts);
}

// conditionals 

function is_conditional(component) {
    return is_tagged_list(component, "conditional_expression") ||
           is_tagged_list(component, "conditional_statement");
}
function conditional_predicate(component) {
   return list_ref(component, 1);
}
function conditional_consequent(component) {
   return list_ref(component, 2);
}
function conditional_alternative(component) {
   return list_ref(component, 3);
}
function make_conditional_expression(pred, cons, alt) {
    return list("conditional_expression", pred, cons, alt);
}
function make_conditional_statement(pred, cons, alt) {
    return list("conditional_statement", pred, cons, alt);
}

// blocks 

function is_block(component) {
    return is_tagged_list(component, "block");
}
function block_body(component) {
    return head(tail(component));
}
function make_block(statement) {
    return list("block", statement);
}

// declarations 

function is_declaration(component) {
    return is_tagged_list(component, "constant_declaration") ||
           is_tagged_list(component, "variable_declaration") ||
           is_tagged_list(component, "function_declaration");
}
function declaration_symbol(component) {
    return symbol_of_name(head(tail(component)));
}
function declaration_value_expression(component) {
    return head(tail(tail(component)));
}
function make_constant_declaration(name, value_expression) {
    return list("constant_declaration", name, value_expression);
}

// assignments 

function is_assignment(component) {
    return is_tagged_list(component, "assignment");
}
function assignment_symbol(component) {
    return head(tail(head(tail(component))));
}
function assignment_value_expression(component) {
    return head(tail(tail(component)));
}
function make_assignment(symbol, expression) {
    return list("assignment", 
                make_name(symbol),
                expression);
}

// lambda expressions

function is_lambda_expression(component) {
    return is_tagged_list(component, "lambda_expression");
}
function lambda_parameter_symbols(component) {
    return map(symbol_of_name, head(tail(component)));
}
function lambda_body(component) {
    return head(tail(tail(component)));
}

function make_lambda_expression(parameters, body) {
    return list("lambda_expression", parameters, body);
}

// function declarations 

function is_function_declaration(component) {	    
    return is_tagged_list(component, "function_declaration");
}
function function_declaration_name(component) {
    return list_ref(component, 1);
}
function function_declaration_parameters(component) {
    return list_ref(component, 2);
}
function function_declaration_body(component) {
    return list_ref(component, 3);
}
function function_decl_to_constant_decl(component) {
    return make_constant_declaration(
               function_declaration_name(component),
               make_lambda_expression(
                   function_declaration_parameters(component),
                   function_declaration_body(component)));
}

// applications

function is_application(comp) {
   return is_tagged_list(comp, "application");
}
function function_expression(comp) {
   return head(tail(comp));
}
function arg_expressions(comp) {
   return head(tail(tail(comp)));
}

// return statements

function is_return_statement(component) {
   return is_tagged_list(component, "return_statement");
}
function return_expression(component) {
   return head(tail(component));
}
function make_return_statement(expression) {
    return list("return_statement", expression);
}

// logical compositions

function is_logical_composition(comp) {
    return is_tagged_list(comp, "logical_composition");
}
function logical_symbol(comp) {
    return list_ref(comp, 1);
}
function logical_composition_first_component(comp) {
    return list_ref(comp, 2);
}
function logical_composition_second_component(comp) {
    return list_ref(comp, 3);
}

// while loops

function is_while_loop(comp) {
    return is_tagged_list(comp, "while_loop");
}
function while_loop_predicate(comp) {
    return list_ref(comp, 1);
}
function while_loop_body(comp) {
    return list_ref(comp, 2);
}
function make_while_loop(pred, body) {
    return list("while_loop", pred, body);
}

// for loops 

function is_for_loop(component) {
    return is_tagged_list(component, "for_loop");
}
function for_loop_init(comp) {
    return list_ref(comp, 1);
}
function for_loop_predicate(comp) {
    return list_ref(comp, 2);
}
function for_loop_update(comp) {
    return list_ref(comp, 3);
}
function for_loop_body(comp) {
    return list_ref(comp, 4);
}

// array expressions

function is_array_expression(expr) {
    return is_tagged_list(expr, "array_expression");
}
function array_elements(expr) {
    return head(tail(expr));
}

// object access

function is_array_access(expr) {
    return is_tagged_list(expr, "object_access");
}
function array_access_array_expression(expr) {
    return list_ref(expr, 1);
}
function array_access_index_expression(expr) {
    return list_ref(expr, 2);
}

// array access

function is_array_assignment(expr) {
    return is_tagged_list(expr, "object_assignment");
}
function array_assignment_access(expr) {
    return list_ref(expr, 1);
}
function array_assignment_value_expression(expr) {
    return list_ref(expr, 2);
}

//
// CSE machine instructions
//

// operators instructions

function is_binary_operator_instruction(component) {	    
    return is_tagged_list(component, "binop");
}
function is_unary_operator_instruction(component) {	    
    return is_tagged_list(component, "unop");
}
function operator_instruction_symbol(component) {
    return list_ref(component, 1);
}
function make_binary_operator_instruction(symbol) {
    return list("binop", symbol);
}
function make_unary_operator_instruction(symbol) {
    return list("unop", symbol);
}

// assign instructions

function is_assign_instruction(component) {
    return is_tagged_list(component, "asgn");
}
function assign_instruction_symbol(component) {
    return head(tail(component));
}
function make_assign_instruction(symbol) {
    return list("asgn", symbol);
}

// pop instructions

function is_pop_instruction(component) {	    
    return is_tagged_list(component, "pop");
}
function make_pop_instruction() {
    return list("pop");
}

// branch instructions

function is_branch_instruction(component) {
    return is_tagged_list(component, "branch");
}
function branch_instruction_consequent(component) {
   return list_ref(component, 1);
}
function branch_instruction_alternative(component) {
   return list_ref(component, 2);
}
function make_branch_instruction(consequent, alternative) {
    return list("branch", consequent, alternative);
}

// environment instructions

function is_env_instruction(component) {
    return is_tagged_list(component, "env");
}
function env_instruction_environment(component) {
   return list_ref(component, 1);
}
function make_env_instruction(environment) {
    return list("env", environment);
}

// call instructions

function is_call_instruction(component) {
    return is_tagged_list(component, "call");
}
function call_instruction_arity(component) {
   return list_ref(component, 1);
}
function make_call_instruction(arity) {
    return list("call", arity);
}

// marker

function is_marker(component) {
    return is_tagged_list(component, "marker");
}
function make_marker() {
    return list("marker");
}

// return instructions

function is_return_instruction(component) {	    
    return is_tagged_list(component, "return");
}
function make_return_instruction() {
    return list("return");
}

// array instructions

function is_array_instruction(component) {	    
    return is_tagged_list(component, "array");
}
function array_instruction_size(component) {
    return list_ref(component, 1);
}
function make_array_instruction(size) {
    return list("array", size);
}

// array access instructions

function is_array_access_instruction(component) {	    
    return is_tagged_list(
             component, 
             "array_access_instruction");
}
function make_array_access_instruction() {
    return list("array_access_instruction");
}

// array assignment instructions

function is_array_assignment_instruction(component) {	    
    return is_tagged_list(
             component, 
             "array_assignment_instruction");
}
function make_array_assignment_instruction() {
    return list("array_assignment_instruction");
}

//
// evaluator data structures (SICP JS 4.1.3)
//

// Booleans

function is_truthy(x) {
    return is_boolean(x) 
           ? x
           : error(x, "boolean expected, received");
}

// function objects

function make_simple_function(parameters, body, env) {
    return list("simple_function", parameters, body, env);
}
function is_simple_function(f) {
    return is_tagged_list(f, "simple_function");
}
function make_complex_function(parameters, body, env) {
    return list("complex_function", parameters, body, env);
}
function is_complex_function(f) {
    return is_tagged_list(f, "complex_function");
}
function function_parameters(f) { return list_ref(f, 1); }

function function_body(f) { return list_ref(f, 2); }

function function_environment(f) { return list_ref(f, 3); }

//
// environments
//

function enclosing_environment(env) { return tail(env); }

function first_frame(env) { return head(env); }

const the_empty_environment = null;

function make_frame(symbols, values) { return pair(symbols, values); }

function frame_symbols(frame) { return head(frame); }

function frame_values(frame) { return tail(frame); }

function extend_environment(symbols, vals, base_env) {
    return length(symbols) === length(vals)
           ? pair(make_frame(symbols, vals), base_env)
           : length(symbols) < length(vals)
           ? error("too many arguments supplied: " + 
                   stringify(symbols) + ", " + 
                   stringify(vals))
           : error("too few arguments supplied: " + 
                   stringify(symbols) + ", " + 
                   stringify(vals));
}

function lookup_symbol_value(symbol, env) {
    function env_loop(env) {
        function scan(symbols, vals) {
            return is_null(symbols)
                   ? env_loop(enclosing_environment(env))
                   : symbol === head(symbols)
                   ? head(vals)
                   : scan(tail(symbols), tail(vals));
        }
        if (env === the_empty_environment) {
            error(symbol, "unbound name");
        } else {
            const frame = first_frame(env);
            return scan(frame_symbols(frame), frame_values(frame));
        }
    }
    return env_loop(env);
}

function assign_symbol_value(symbol, val, env) {
    function env_loop(env) {
        function scan(symbols, vals) {
            return is_null(symbols)
                   ? env_loop(enclosing_environment(env))
                   : symbol === head(symbols)
                   ? set_head(vals, val)
                   : scan(tail(symbols), tail(vals));
        } 
        if (env === the_empty_environment) {
            error(symbol, "unbound name -- assignment");
        } else {
            const frame = first_frame(env);
            return scan(frame_symbols(frame), frame_values(frame));
        }
    }
    return env_loop(env);
}

// global environment (SICP JS 4.1.4)

function is_primitive_function(fun) {
    return is_tagged_list(fun, "primitive");
}

function primitive_implementation(fun) { return head(tail(fun)); }

const primitive_functions = list(
       list("head",    head             ),
       list("tail",    tail             ),
       list("pair",    pair             ),
       list("list",    list             ),
       list("is_null", is_null          ),
       list("display", display          ),
       list("error",   error            ),
       list("math_abs", math_sin        ),
       list("parse",    parse           ),
       list("math_pow",math_pow         )
       );
const primitive_function_symbols =
    map(head, primitive_functions);
const primitive_function_objects =
    map(fun => list("primitive", head(tail(fun))),
        primitive_functions);

const primitive_constants = list(list("undefined", undefined),
                                 list("Infinity",  Infinity),
                                 list("math_PI",   math_PI),
                                 list("math_E",    math_E),
                                 list("NaN",       NaN)
                                );
const primitive_constant_symbols =
    map(c => head(c), primitive_constants);
const primitive_constant_values =
    map(c => head(tail(c)), primitive_constants);

function apply_primitive_function(fun, arglist) {
    return apply_in_underlying_javascript(
               primitive_implementation(fun), arglist);
}

function setup_environment() {
    return extend_environment(append(primitive_function_symbols,
                                     primitive_constant_symbols),
                              append(primitive_function_objects, 
                                     primitive_constant_values),
                              the_empty_environment);
}

const the_global_environment = setup_environment();
const the_global_frame = head(the_global_environment);

//
// testing
//

function display_control(C) {
    display("", "***     control     ***                      ");
    for_each(command => 
                 is_literal(command) ||
                 is_call_instruction(command) ||
                 is_pop_instruction(command) ||
                 is_binary_operator_instruction(command) ||
                 is_unary_operator_instruction(command) ||
                 is_assign_instruction(command)
                 ? display_list(command)
                 : display_list(list(head(command), "...")), 
             C);
    display("", "                                             ");
}

function display_stash(S) {
    display("", "***      stash      ***                      ");
    for_each(value => 
             is_simple_function(value)
             ? display_list(list("simple_function",
                                 function_parameters(value),
                                 "<body not displayed>",
                                 "<environment not displayed>"))
             : is_complex_function(value)
             ? display_list(list("complex_function",
                                 function_parameters(value),
                                 "<body not displayed>",
                                 "<environment not displayed>"))
             : display_list(value),
             S);
    display("", "                                             ");
}

function display_environment(E) {
    display("", "***   environment   ***                      ");
    for_each(frame => {
                 if (frame === the_global_frame) {
                     display("", "<global frame not displayed>                 ");
                 } else {
                     display_list(head(frame), "names: ");
                     display_list(
                         map(value => 
                            is_simple_function(value)
                            ? list("simple_function",
                                   function_parameters(value),
                                   "<body not displayed>",
                                   "<environment not displayed>")
                            : is_complex_function(value)
                            ? list("complex_function",
                                   function_parameters(value),
                                   "<body not displayed>",
                                   "<environment not displayed>")
                            : value,
                            tail(frame)), 
                        "values:");
                }
    }, E);
    display("", "                                             ");
}

function parse_and_evaluate(string) {
    return evaluate(parse(string));
}

//parse_and_evaluate("1;");

//parse_and_evaluate("undefined;");

//parse_and_evaluate("'hello';");

//parse_and_evaluate("1 + 2;");

//parse_and_evaluate("- 4;");

//parse_and_evaluate("! true;");

//parse_and_evaluate("'hello' + 'world';");

//parse_and_evaluate("1; 2; 3;");

//parse_and_evaluate("if (true) { 1; } else { 2; }");

//parse_and_evaluate("true ? 1 : 2;");

//parse_and_evaluate("math_PI;");

//parse_and_evaluate("const x = 1 + 2; x;");

//parse_and_evaluate("const x = 1; { const x = 2; x; } x;");

//parse_and_evaluate("math_pow(2, 3);");

/*
parse_and_evaluate(`
function factorial(n) {
    return n === 1
           ? 1
           : n * factorial(n - 1);
}
factorial(5);`);
*/

/*
parse_and_evaluate(`
const n = 1000000;
function factorial(n) {
    return n === 1
           ? 1
           : factorial(n - 1) * n;
}
factorial(5) + n;`);
*/

/*
parse_and_evaluate(`
function f(x) {
    const y = 1;
    return x + y;
}
f(2);
`);
*/

/*
parse_and_evaluate(`
function f(b) {
    if (b) {
        return 1;
    }
    2 + 3;
    return 4;
}
f(true);
`);
*/

/*
parse_and_evaluate(`
let result = 1;
let i = 5;
while (i > 0) {
    result = result * i;
    i = i - 1;
}
result;
`);
*/

/*
parse_and_evaluate(`
let result = 1;
for (let i = 5; i > 0; i = i - 1) {
    result = result * i;
}
result;
`);
*/

/*
parse_and_evaluate(`
const a = [10, 20, 30];
a;
`);
*/

/*
parse_and_evaluate(`
const a = [10, 20, 30];
a[0] = 40;
a;
`);
*/

parse_and_evaluate(`
function f(x) {
    12;
}
f(49);
`);