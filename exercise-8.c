#include "stdlib.h"
#include <stdbool.h>

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
    //@ requires true;
    //@ ensures  stack(result, 0);
{
    stack_t* stack = malloc(sizeof(stack_t));
    if (!stack) abort();
    stack->head = 0;
    //@ close nodes(0, 0);
    //@ close stack(stack, 0);

    return stack;
}

void stack_push(stack_t* stack, int value)
    //@ requires stack(stack, ?size);
    //@ ensures  stack(stack, size + 1);
{
    node_t* new_node = malloc(sizeof(node_t));
    if (!new_node) abort();
    new_node->value = value;

    //@ open stack(stack, size);
    new_node->next = stack->head;
    stack->head = new_node;
    //@ close nodes(new_node, size + 1);
    //@ close stack(stack, size + 1);
}

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

void stack_popn(stack_t* stack, int n)
    //@ requires stack(stack, ?size) &*& 0 <= n &*& n <= size;
    //@ ensures  stack(stack, size - n);
{
    int cnt = 0;
    while (cnt < n)
        //@ invariant stack(stack, size - cnt);
    {
        stack_pop(stack);
        cnt++;
    }
}

void stack_dispose(stack_t* stack)
    //@ requires stack(stack, _);
    //@ ensures  true;
{
    //@ open stack(stack, _);
    node_t* node = stack->head;
    while (node)
        //@ invariant nodes(node, _);
    {
        //@ open nodes(node, _);
        node_t* next = node->next;
        free(node);
        node = next;
    }
    //@ open nodes(0, _);
    free(stack);
}

bool stack_is_empty(stack_t* stack)
    //@ requires stack(stack, ?size);
    //@ ensures  stack(stack, size) &*& result == (size == 0);
{
    //@ open stack(stack, size);
    node_t* head = stack->head;

    //@ open nodes(head, size);
    return stack->head == 0;
    //@ close nodes(head, size);
    //@ close stack(stack, size);
}

int nodes_get_sum(node_t* node)
    //@ requires nodes(node, ?size);
    //@ ensures  nodes(node, size);
{
    int sum = 0;
    if (node) {
        //@ open nodes(node, size);
        sum = nodes_get_sum(node->next);
        sum += node->value;
        //@ close nodes(node, size);
    }

    return sum;
}

int stack_get_sum(stack_t* stack)
    //@ requires stack(stack, ?size);
    //@ ensures  stack(stack, size);
{
    //@ open stack(stack, size);
    return nodes_get_sum(stack->head);
    //@ close stack(stack, size);
}

int main()
    //@ requires true;
    //@ ensures  true;
{
    stack_t* stack = create_stack();
    stack_push(stack, 10);
    stack_push(stack, 20);
    stack_pop(stack);
    stack_pop(stack);
    stack_dispose(stack);

    return 0;
}
