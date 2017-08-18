#include "stdlib.h"

struct account {
    int balance;
};
typedef struct account account_t;

int main()
    //@ requires true;
    //@ ensures true;
{
    account_t *myAccount = malloc(sizeof(account_t));
    if (myAccount == 0) { abort(); }
    myAccount->balance = 5;
    free(myAccount);
    return 0;
}
