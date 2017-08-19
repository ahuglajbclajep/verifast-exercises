/*
 * This code can be compiled with gcc, but it fails to run.
 * `free()` for local variables can be detected by VeriFast.
 */

#include "stdlib.h"

struct account {
    int balance;
};
typedef struct account account_t;

int main()
    //@ requires true;
    //@ ensures true;
{
    account_t my_account_local;
    account_t* my_account = &my_account_local;
    my_account->balance = 5;  // pass
    free(my_account);  // error

    return 0;
}
