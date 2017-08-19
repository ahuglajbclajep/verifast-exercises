#include "stdlib.h"

struct account {
    int balance;
};
typedef struct account account_t;

void account_set_balance(account_t* my_account, int new_balance)
    //@ requires account_balance(my_account, _);
    //@ ensures true;
{
    my_account->balance = new_balance;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    account_t* my_account = malloc(sizeof(account_t));
    if (!my_account) abort();
    account_set_balance(my_account, 5);
    free(my_account);

    return 0;
}
