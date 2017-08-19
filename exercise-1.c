#include "stdlib.h"

struct account {
    int balance;
};
typedef struct account account_t;

account_t* create_account()
    //@ requires true;
    //@ ensures  result->balance |-> _ &*& malloc_block_account(result);
{
    account_t* tmp = malloc(sizeof(account_t));
    if (!tmp) abort();
    tmp->balance = 0;

    return tmp;
}

void account_set_balance(account_t* my_account, int new_balance)
    //@ requires my_account->balance |-> _;
    //@ ensures  my_account->balance |-> new_balance;
{
    my_account->balance = new_balance;
}

void dispose_account(account_t* my_account)
    //@ requires my_account->balance |-> _ &*& malloc_block_account(my_account);
    //@ ensures  true;
{
    free(my_account);
}

int main()
    //@ requires true;
    //@ ensures  true;
{
    account_t* my_account = create_account();
    account_set_balance(my_account, 5);
    dispose_account(my_account);

    return 0;
}
