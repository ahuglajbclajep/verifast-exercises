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

stack_t* create_stack()
{
    stack_t* stack = malloc(sizeof(stack_t));
    if (!stack) abort();
    stack->head = 0;

    return stack;
}

void stack_push(stack_t* stack, int value)
{
    node_t* n = malloc(sizeof(node_t));
    if (!n) abort();
    n->value = value;
    n->next = stack->head;
    stack->head = n;
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
{
    stack_t* s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    assert(stack_pop(s) == 20);
    assert(stack_pop(s) == 10);
    stack_dispose(s);

    return 0;
}
