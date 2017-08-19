#include "stdlib.h"

struct account {
    int balance;
};
typedef struct account account_t;

account_t* account_creation()
    //@ requires true;
    //@ ensures  true;
{
    return malloc(sizeof(account_t));
}

void account_set_balance(account_t* my_account, int new_balance)
    //@ requires my_account->balance |-> _;
    //@ ensures  my_account->balance |-> new_balance;
{
    my_account->balance = new_balance;
}

void account_disposal(account_t* my_account)
    //@ requires true;
    //@ ensures  true;
{
    free(my_account);
}

int main()
    //@ requires true;
    //@ ensures  true;
{
    account_t* my_account = account_creation();
    if (!my_account) abort();
    account_set_balance(my_account, 5);
    account_disposal(my_account);

    return 0;
}
