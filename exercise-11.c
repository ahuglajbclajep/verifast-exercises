#include <stdlib.h>
#include <assert.h>

struct node {
    int value;
    struct node* next;
};
typedef struct node node_t;

struct stack {
    node_t* head;
};
typedef struct stack stack_t;

/*@
inductive int_list = int_list_nil | int_list_cons(int, int_list);

fixpoint int int_list_head(int_list list) {
    switch (list) {
        case int_list_nil: return 0;
        case int_list_cons(x, xs): return x;
    }
}

fixpoint int_list int_list_tail(int_list list) {
    switch (list) {
        case int_list_nil: return int_list_nil;
        case int_list_cons(x, xs): return xs;
    }
}

fixpoint int int_list_sum(int_list list) {
    switch (list) {
        case int_list_nil: return 0;
        case int_list_cons(x, xs): return x + int_list_sum(xs);
    }
}

predicate nodes(node_t* node, int_list value_list) =
    !node ? value_list == int_list_nil : node->value |-> ?value &*&
    node->next |-> ?next &*& malloc_block_node(node) &*&
    nodes(next, ?xs) &*& value_list == int_list_cons(value, xs);

predicate stack(stack_t* stack, int_list value_list) =
    stack->head |-> ?head &*& malloc_block_stack(stack) &*& nodes(head, value_list);
@*/

stack_t* create_stack()
    //@ requires true;
    //@ ensures  stack(result, int_list_nil);
{
    stack_t* stack = malloc(sizeof(stack_t));
    if (!stack) abort();
    stack->head = 0;
    //@ close nodes(0, int_list_nil);
    //@ close stack(stack, int_list_nil);

    return stack;
}

void stack_push(stack_t* stack, int value)
    //@ requires stack(stack, ?value_list);
    //@ ensures  stack(stack, int_list_cons(value, value_list));
{
    node_t* new_node = malloc(sizeof(node_t));
    if (!new_node) abort();
    new_node->value = value;

    //@ open stack(stack, value_list);
    new_node->next = stack->head;
    stack->head = new_node;
    //@ close nodes(new_node, int_list_cons(value, value_list));
    //@ close stack(stack, int_list_cons(value, value_list));
}

int stack_pop(stack_t* stack)
    //@ requires stack(stack, ?value_list) &*& value_list != int_list_nil;
    //@ ensures  stack(stack, int_list_tail(value_list)) &*& result == int_list_head(value_list);
{
    //@ open stack(stack, value_list);
    node_t* head = stack->head;
    //@ open nodes(head, value_list);
    int value = head->value;

    stack->head = head->next;
    free(head);
    //@ close stack(stack, int_list_tail(value_list));

    return value;
}

void stack_dispose(stack_t* stack)
    //@ requires stack(stack, int_list_nil);
    //@ ensures  true;
{
    //@ open stack(stack, int_list_nil);
    //@ open nodes(_, _);
    free(stack);
}

int nodes_get_sum(node_t* node)
    //@ requires nodes(node, ?value_list);
    //@ ensures  nodes(node, value_list) &*& result == int_list_sum(value_list);
{
    int sum = 0;
    //@ open nodes(node, value_list);
    if (node) {
        sum = nodes_get_sum(node->next);
        sum += node->value;
    }
    //@ close nodes(node, value_list);

    return sum;
}

int stack_get_sum(stack_t* stack)
    //@ requires stack(stack, ?value_list);
    //@ ensures  stack(stack, value_list) &*& result == int_list_sum(value_list);
{
    //@ open stack(stack, value_list);
    return nodes_get_sum(stack->head);
    //@ close stack(stack, value_list);
}

int main()
    //@ requires true;
    //@ ensures  true;
{
    stack_t* stack = create_stack();
    stack_push(stack, 10);
    stack_push(stack, 20);

    int sum = stack_get_sum(stack);
    assert(sum == 30);

    int result1 = stack_pop(stack);
    assert(result1 == 20);

    int result2 = stack_pop(stack);
    assert(result2 == 10);

    stack_dispose(stack);

    return 0;
}
