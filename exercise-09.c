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

/*
int stack_pop(stack_t* stack)
    //@ requires stack(stack, ?size) &*& 0 < size;
    //@ ensures  stack(stack, size -1);
{
    //@ open stack(stack, size);
    node_t* head = stack->head;
    //@ open nodes(head, size);
    int value = head->value;

    stack->head = head->next;
    free(head);
    //@ close stack(stack, size - 1);

    return value;
}
*/

void stack_dispose(stack_t* stack)
    //@ requires stack(stack, int_list_nil);
    //@ ensures  true;
{
    //@ open stack(stack, int_list_nil);
    //@ open nodes(_, _);
    free(stack);
}

int main()
    //@ requires true;
    //@ ensures  true;
{
    stack_t* stack = create_stack();
    stack_push(stack, 10);
    stack_push(stack, 20);
/*
    int result1 = stack_pop(stack);
    assert(result1 == 20);

    int result2 = stack_pop(stack);
    assert(result2 == 10);
*/
    stack_dispose(stack);

    return 0;
}
