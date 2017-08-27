#include <assert.h>
#include "account.h"

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
