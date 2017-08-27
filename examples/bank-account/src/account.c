#include "account.h"
#include <stdlib.h>

account_t* create_account(int limit)
    //@ requires limit <= 0;
    //@ ensures  account_pred(result, 0, limit);
{
    account_t* the_account = malloc(sizeof(account_t));
    if (!the_account) abort();
    the_account->balance = 0;
    the_account->limit = limit;
    //@ close account_pred(the_account, 0, limit);

    return the_account;
}

int account_get_balance(account_t* my_account)
    //@ requires account_pred(my_account, ?balance, ?limit);
    //@ ensures  account_pred(my_account, balance, limit) &*& result == balance;
{
    //@ open account_pred(my_account, balance, limit);
    return my_account->balance;
    //@ close account_pred(my_account, balance, limit);
}

void account_deposit(account_t* my_account, int amount)
    //@ requires 0 <= amount &*& account_pred(my_account, ?balance, ?limit);
    //@ ensures  account_pred(my_account, balance + amount, limit);
{
    //@ open account_pred(my_account, balance, limit);
    my_account->balance += amount;
    //@ close account_pred(my_account, balance + amount, limit);
}

int account_withdraw(account_t* my_account, int amount)
    //@ requires 0 <= amount &*& account_pred(my_account, ?balance, ?limit);
    /*@ ensures  account_pred(my_account, balance - result, limit) &*&
            result == (balance - amount < limit ? balance - limit : amount); @*/
{
    //@ open account_pred(my_account, balance, limit);
    int withdrawal_amount = my_account->balance - amount < my_account->limit ?
        my_account->balance - my_account->limit : amount;
    my_account->balance -= withdrawal_amount;
    //@ close account_pred(my_account, balance - withdrawal_amount, limit);

    return withdrawal_amount;
}

void dispose_account(account_t* my_account)
    //@ requires account_pred(my_account, _, _);
    //@ ensures  true;
{
    //@ open account_pred(my_account, _, _);
    free(my_account);
}
