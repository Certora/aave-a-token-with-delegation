/*
    This is a specification file for the verification of delegation invariants
    of AaveTokenV3.sol smart contract using the Certora prover. 
    For more information, visit: https://www.certora.com/

    This file is run with scripts/verifyGeneral.sh
    On a version with some minimal code modifications 
    AaveTokenV3HarnessStorage.sol

    Sanity check results: https://prover.certora.com/output/67509/8cee7c95432ede6b3f9f/?anonymousKey=78d297585a2b2edc38f6c513e0ce12df10e47b82
*/

import "base_token_v3.spec";

using SymbolicLendingPoolL1 as _SymbolicLendingPoolL1;
definition RAY() returns uint256 = 10^27;


methods {
    //    function _SymbolicLendingPoolL1.getReserveNormalizedIncome(address) external returns (uint256)  => index();
    //function _.rayMul(uint256 a,uint256 b) internal => rayMul_MI(a,b) expect uint256 ALL;
    //function _.rayDiv(uint256 a,uint256 b) internal => rayDiv_MI(a,b) expect uint256 ALL;

    //function _.getIncentivesController() external => CONSTANT;
    //function _.UNDERLYING_ASSET_ADDRESS() external => CONSTANT;
    
    // called by AToken.sol::224. A method of IPool.
    function _.finalizeTransfer(address, address, address, uint256, uint256, uint256) external => NONDET;

    // called from: IncentivizedERC20.sol::29.
    function _.getACLManager() external => NONDET;

    // called from: IncentivizedERC20.sol::30.
    function _.isPoolAdmin(address) external => NONDET;

    // called from: IncentivizedERC20.sol::76.
    function _.ADDRESSES_PROVIDER() external => NONDET;

    // called from: IncentivizedERC20.sol::207. A method of incentivesControllerLocal.
    function _.handleAction(address,uint256,uint256) external => NONDET;

    // getPool() returns address => ALWAYS(100);
    //    function _.getPool() external returns address => NONDET;
    //function _.getPool() external => NONDET;
    
    // A method of Ipool
    // can this contract change the pool
    //function _.getReserveData(address) external => CONSTANT;
    //function _.claimAllRewards(address[],address) external => NONDET;

    // called in MetaTxHelpers.sol::27.
    //function _.isValidSignature(bytes32, bytes) external => NONDET;
}


ghost index() returns uint256 {
    axiom index()==RAY();
}
ghost rayMul_MI(mathint , mathint) returns uint256 {
    axiom forall mathint x. forall mathint y. to_mathint(rayMul_MI(x,y)) == x ;
}
ghost rayDiv_MI(mathint , mathint) returns uint256 {
    axiom forall mathint x. forall mathint y. to_mathint(rayDiv_MI(x,y)) == x ;
}


/**
    Ghosts
*/

// sum of all user balances
ghost mathint sumBalances {
    init_state axiom sumBalances == 0;
}

// tracking voting delegation status for each address
ghost mapping(address => bool) isDelegatingVoting {
    init_state axiom forall address a. isDelegatingVoting[a] == false;
}

// tracking voting delegation status for each address
ghost mapping(address => bool) isDelegatingProposition {
    init_state axiom forall address a. isDelegatingProposition[a] == false;
}

// sum of all voting delegated balances
ghost mathint sumDelegatedBalancesV {
    init_state axiom sumDelegatedBalancesV == 0;
}

// sum of all proposition undelegated balances
ghost mathint sumUndelegatedBalancesV {
    init_state axiom sumUndelegatedBalancesV == 0;
}

// sum of all proposition delegated balances
ghost mathint sumDelegatedBalancesP {
    init_state axiom sumDelegatedBalancesP == 0;
}

// sum of all voting undelegated balances
ghost mathint sumUndelegatedBalancesP {
    init_state axiom sumUndelegatedBalancesP == 0;
}

// token balances of each address
ghost mapping(address => mathint) balances {
    init_state axiom forall address a. balances[a] == 0;
}

/*

    Hooks

*/


/*

    This hook updates the sum of delegated and undelegated balances on each change of delegation state.
    If the user moves from not delegating to delegating, their balance is moved from undelegated to delegating,
    and etc.

*/
hook Sstore _userState[KEY address user].delegationMode ATokenWithDelegation_Harness.DelegationMode new_state (ATokenWithDelegation_Harness.DelegationMode old_state) STORAGE {
    
    bool willDelegateP = !DELEGATING_PROPOSITION(old_state) && DELEGATING_PROPOSITION(new_state);
    bool wasDelegatingP = DELEGATING_PROPOSITION(old_state) && !DELEGATING_PROPOSITION(new_state);
 
    // we cannot use if statements inside hooks, hence the ternary operator
    sumUndelegatedBalancesP = willDelegateP ? (sumUndelegatedBalancesP - balances[user]) : sumUndelegatedBalancesP;
    sumUndelegatedBalancesP = wasDelegatingP ? (sumUndelegatedBalancesP + balances[user]) : sumUndelegatedBalancesP;
    sumDelegatedBalancesP = willDelegateP ? (sumDelegatedBalancesP + balances[user]) : sumDelegatedBalancesP;
    sumDelegatedBalancesP = wasDelegatingP ? (sumDelegatedBalancesP - balances[user]) : sumDelegatedBalancesP;
    
    // change the delegating state only if a change is stored

    isDelegatingProposition[user] = new_state == old_state
        ? isDelegatingProposition[user]
        : new_state == PROPOSITION_DELEGATED() || new_state == FULL_POWER_DELEGATED();

    
    bool willDelegateV = !DELEGATING_VOTING(old_state) && DELEGATING_VOTING(new_state);
    bool wasDelegatingV = DELEGATING_VOTING(old_state) && !DELEGATING_VOTING(new_state);
    sumUndelegatedBalancesV = willDelegateV ? (sumUndelegatedBalancesV - balances[user]) : sumUndelegatedBalancesV;
    sumUndelegatedBalancesV = wasDelegatingV ? (sumUndelegatedBalancesV + balances[user]) : sumUndelegatedBalancesV;
    sumDelegatedBalancesV = willDelegateV ? (sumDelegatedBalancesV + balances[user]) : sumDelegatedBalancesV;
    sumDelegatedBalancesV = wasDelegatingV ? (sumDelegatedBalancesV - balances[user]) : sumDelegatedBalancesV;
    
    // change the delegating state only if a change is stored

    isDelegatingVoting[user] = new_state == old_state
        ? isDelegatingVoting[user]
        : new_state == VOTING_DELEGATED() || new_state == FULL_POWER_DELEGATED();
}


/*

    This hook updates the sum of delegated and undelegated balances on each change of user balance.
    Depending on the delegation state, either the delegated or the undelegated balance get updated.

*/
hook Sstore _userState[KEY address user].balance uint120 balance (uint120 old_balance) STORAGE {
    balances[user] = balances[user] - old_balance + balance;
    // we cannot use if statements inside hooks, hence the ternary operator
    sumDelegatedBalancesV = isDelegatingVoting[user] 
        ? sumDelegatedBalancesV + to_mathint(balance) - to_mathint(old_balance)
        : sumDelegatedBalancesV;
    sumUndelegatedBalancesV = !isDelegatingVoting[user] 
        ? sumUndelegatedBalancesV + to_mathint(balance) - to_mathint(old_balance)
        : sumUndelegatedBalancesV;
    sumDelegatedBalancesP = isDelegatingProposition[user] 
        ? sumDelegatedBalancesP + to_mathint(balance) - to_mathint(old_balance)
        : sumDelegatedBalancesP;
    sumUndelegatedBalancesP = !isDelegatingProposition[user] 
        ? sumUndelegatedBalancesP + to_mathint(balance) - to_mathint(old_balance)
        : sumUndelegatedBalancesP;

}

/*
    @Rule

    @Description:
        User's delegation flag is switched on iff user is delegating to an address
        other than his own own or 0

    @Notes:


    @Link:

*/
invariant delegateCorrectness(address user)
/* ((getVotingDelegate(user) == user || getVotingDelegate(user) == 0) <=> !getDelegatingVoting(user))
   &&*/
    ((getPropositionDelegate(user) == user || getPropositionDelegate(user) == 0) <=> !getDelegatingProposition(user));

/*
    @Rule

    @Description:
        Sum of delegated voting balances and undelegated balances is equal to total supply

    @Notes:


    @Link:

*/
invariant sumOfVBalancesCorrectness() sumDelegatedBalancesV + sumUndelegatedBalancesV == to_mathint(scaledTotalSupply());

/*
    @Rule

    @Description:
        Sum of delegated proposition balances and undelegated balances is equal to total supply

    @Notes:


    @Link:

*/
invariant sumOfPBalancesCorrectness() sumDelegatedBalancesP + sumUndelegatedBalancesP == to_mathint(scaledTotalSupply());

/*
    @Rule

    @Description:
       Transfers don't change voting delegation state

    @Notes:


    @Link:

*/
rule transferDoesntChangeDelegationMode() {
    env e;
    address from; address to; address charlie;
    require (charlie != from && charlie != to);
    uint amount;

    ATokenWithDelegation_Harness.DelegationMode stateFromBefore = getDelegationMode(from);
    ATokenWithDelegation_Harness.DelegationMode stateToBefore = getDelegationMode(to);
    ATokenWithDelegation_Harness.DelegationMode stateCharlieBefore = getDelegationMode(charlie);
    
    bool testFromBefore = isDelegatingVoting[from];
    bool testToBefore = isDelegatingVoting[to];

    transferFrom(e, from, to, amount);

    ATokenWithDelegation_Harness.DelegationMode stateFromAfter = getDelegationMode(from);
    ATokenWithDelegation_Harness.DelegationMode stateToAfter = getDelegationMode(to);
    bool testFromAfter = isDelegatingVoting[from];
    bool testToAfter = isDelegatingVoting[to];

    assert testFromBefore == testFromAfter && testToBefore == testToAfter;
    assert getDelegationMode(charlie) == stateCharlieBefore;
}
