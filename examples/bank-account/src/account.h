#ifndef ACCOUNT_H
#define ACCOUNT_H

struct account {
    int balance;
    int limit;
};
typedef struct account account_t;

/*@
predicate account_pred(account_t* the_account, int the_balance, int the_limit) =
    the_account->balance |-> the_balance &*& the_account->limit |-> the_limit &*&
    malloc_block_account(the_account);
@*/

account_t* create_account(int limit);
    //@ requires limit <= 0;
    //@ ensures  account_pred(result, 0, limit);

int account_get_balance(account_t* my_account);
    //@ requires account_pred(my_account, ?balance, ?limit);
    //@ ensures  account_pred(my_account, balance, limit) &*& result == balance;

void account_deposit(account_t* my_account, int amount);
    //@ requires 0 <= amount &*& account_pred(my_account, ?balance, ?limit);
    //@ ensures  account_pred(my_account, balance + amount, limit);

int account_withdraw(account_t* my_account, int amount);
    //@ requires 0 <= amount &*& account_pred(my_account, ?balance, ?limit);
    /*@ ensures  account_pred(my_account, balance - result, limit) &*&
            result == (balance - amount < limit ? balance - limit : amount); @*/

void dispose_account(account_t* my_account);
    //@ requires account_pred(my_account, _, _);
    //@ ensures  true;

#endif
