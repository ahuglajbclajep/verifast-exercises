#include "stdlib.h"
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
predicate nodes(node_t* node, int size) =
    !node ? size == 0 : 0 < size &*&
    node->value |-> ?value &*& node->next |-> ?next &*&
    malloc_block_node(node) &*& nodes(next, size - 1);

predicate stack(stack_t* stack, int size) =
    0 <= size &*& stack->head |-> ?head &*&
    malloc_block_stack(stack) &*& nodes(head, size);
@*/

stack_t* create_stack()
{
    stack_t* stack = malloc(sizeof(stack_t));
    if (!stack) abort();
    stack->head = 0;

    return stack;
}

void stack_push(stack_t* stack, int value)
{
    node_t* new_node = malloc(sizeof(node_t));
    if (!new_node) abort();
    new_node->value = value;
    new_node->next = stack->head;
    stack->head = new_node;
}

int stack_pop(stack_t* stack)
{
    node_t* head = stack->head;
    int value = head->value;

    stack->head = head->next;
    free(head);

    return value;
}

void stack_dispose(stack_t* stack)
{
    free(stack);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    stack_t* stack = create_stack();
    stack_push(stack, 10);
    stack_push(stack, 20);
    assert(stack_pop(stack) == 20);
    assert(stack_pop(stack) == 10);
    stack_dispose(stack);

    return 0;
}
