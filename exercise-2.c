#include "stdlib.h"
#include <assert.h>

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

int account_get_balance(account_t* my_account)
    //@ requires my_account->balance |-> ?the_balance;
    //@ ensures  my_account->balance |-> the_balance &*& result == the_balance;
{
    return my_account->balance;
}

void account_set_balance(account_t* my_account, int new_balance)
    //@ requires my_account->balance |-> _;
    //@ ensures  my_account->balance |-> new_balance;
{
    my_account->balance = new_balance;
}

void account_deposit(account_t* my_account, int amount)
    //@ requires my_account->balance |-> ?the_balance &*& 0 <= amount;
    //@ ensures  my_account->balance |-> the_balance + amount;
{
    my_account->balance += amount;
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
    account_deposit(my_account, 10);
    int tmp = account_get_balance(my_account);
    assert(tmp == 15);
    dispose_account(my_account);

    return 0;
}
