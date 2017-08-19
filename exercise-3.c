#include "stdlib.h"
#include <assert.h>

struct account {
    int balance;
    int limit;
};
typedef struct account account_t;

account_t* create_account(int limit)
    //@ requires limit <= 0;
    //@ ensures  result->balance |-> _ &*& result->limit |-> limit &*& malloc_block_account(result);
{
    account_t* tmp = malloc(sizeof(account_t));
    if (!tmp) abort();
    tmp->balance = 0;
    tmp->limit = limit;

    return tmp;
}

int account_get_balance(account_t* my_account)
    //@ requires my_account->balance |-> ?the_balance;
    //@ ensures  my_account->balance |-> the_balance &*& result == the_balance;
{
    return my_account->balance;
}

void account_deposit(account_t* my_account, int amount)
    //@ requires my_account->balance |-> ?the_balance;
    //@ ensures  my_account->balance |-> the_balance + amount;
{
    my_account->balance += amount;
}

int account_withdraw(account_t* my_account, int amount);

void dispose_account(account_t* my_account)
    //@ requires my_account->balance |-> _ &*& my_account->limit |-> _ &*& malloc_block_account(my_account);
    //@ ensures  true;
{
    free(my_account);
}

int main()
    //@ requires true;
    //@ ensures  true;
{
    account_t* my_account = create_account(-100);
    account_deposit(my_account, 200);

    int w1 = account_withdraw(my_account, 50);
    assert(w1 == 50);

    int b1 = account_get_balance(my_account);
    assert(b1 == 150);

    int w2 = account_withdraw(my_account, 300);
    assert(w2 == 250);

    int b2 = account_get_balance(my_account);
    assert(b2 == -100);

    dispose_account(my_account);

    return 0;
}
