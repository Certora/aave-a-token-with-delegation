/*
    This is a specification file for the verification of general ERC20
    features of AaveTokenV3.sol smart contract using the Certora prover. 
    For more information, visit: https://www.certora.com/

    This file is run with scripts/erc20.sh
    On the token harness AaveTokenV3Harness.sol

    Sanity run:
    https://prover.certora.com/output/67509/a5d16a31a49b9c9a7b71/?anonymousKey=bd108549122fd97450428a26c4ed52458793b898
*/

import "base_token_v3.spec";

using SymbolicLendingPoolL1 as _SymbolicLendingPoolL1;
using DummyERC20_aTokenUnderlying as Underlying;
definition RAY() returns uint256 = 10^27;

function doesntChangeBalance(method f) returns bool {
    return f.selector != sig:transfer(address,uint256).selector &&
        f.selector != sig:transferFrom(address,address,uint256).selector;
}

methods {
    function _SymbolicLendingPoolL1.getReserveNormalizedIncome(address) external returns (uint256) envfree;
    //function _SymbolicLendingPoolL1.getReserveNormalizedIncome(address) external returns (uint256)  => index();
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

    

/*
    @Rule


    @Description:
        Token transfer works correctly. Balances are updated if not reverted. 
        If reverted then the transfer amount was too high, or the recipient is 0.

    @Formula:
        {
            balanceFromBefore = balanceOf(msg.sender)
            balanceToBefore = balanceOf(to)
        }
        <
            transfer(to, amount)
        >
        {
            lastReverted => to = 0 || amount > balanceOf(msg.sender)
            !lastReverted => balanceOf(to) = balanceToBefore + amount &&
                            balanceOf(msg.sender) = balanceFromBefore - amount
        }

    @Notes:
        This rule fails on tokens with a blacklist function, like USDC and USDT.
        The prover finds a counterexample of a reverted transfer to a blacklisted address or a transfer in a paused state.

    @Link:

*/

// nissan: remove this rule becaue we have integrityTransfer in AToken spec
/*
rule transferCorrect(address to, uint256 amount) {
    env e;
    require e.msg.value == 0 && e.msg.sender != 0;
    uint256 fromBalanceBefore = balanceOf(e.msg.sender);
    uint256 toBalanceBefore = balanceOf(to);
    require fromBalanceBefore + toBalanceBefore < AAVE_MAX_SUPPLY() / 100;
    
    // proven elsewhere
    address v_delegateTo = getVotingDelegate(to);
    mathint dvbTo = getDelegatedVotingBalance(v_delegateTo);
    require dvbTo >= balanceOf(to) / DELEGATED_POWER_DIVIDER() && 
        dvbTo < SCALED_MAX_SUPPLY() - amount / DELEGATED_POWER_DIVIDER();
    address p_delegateTo = getPropositionDelegate(to);
    mathint pvbTo = getDelegatedPropositionBalance(p_delegateTo);
    require pvbTo >= balanceOf(to) / DELEGATED_POWER_DIVIDER() && 
        pvbTo < SCALED_MAX_SUPPLY() - amount / DELEGATED_POWER_DIVIDER();

    // proven elsewhere
    address v_delegateFrom = getVotingDelegate(e.msg.sender);
    address p_delegateFrom = getPropositionDelegate(e.msg.sender);
    mathint dvbFrom = getDelegatedVotingBalance(v_delegateFrom);
    mathint pvbFrom = getDelegatedPropositionBalance(p_delegateFrom);
    require dvbFrom >= balanceOf(e.msg.sender) / DELEGATED_POWER_DIVIDER();
    require pvbFrom >= balanceOf(e.msg.sender) / DELEGATED_POWER_DIVIDER();

    require validDelegationMode(e.msg.sender) && validDelegationMode(to);
    require ! ( (getDelegatingVoting(to) && v_delegateTo == to) ||
                (getDelegatingProposition(to) && p_delegateTo == to));
    require validDelegationMode(p_delegateFrom) && validDelegationMode(p_delegateTo);
    require validDelegationMode(v_delegateFrom) && validDelegationMode(v_delegateTo);

    // to not overcomplicate the constraints on dvbTo and dvbFrom
    require v_delegateFrom != v_delegateTo && p_delegateFrom != p_delegateTo;

    transfer@withrevert(e, to, amount);
    bool reverted = lastReverted;
    if (!reverted) {
        if (e.msg.sender == to) {
            assert balanceOf(e.msg.sender) == fromBalanceBefore;
        } else {
            assert to_mathint(balanceOf(e.msg.sender)) == fromBalanceBefore - amount;
            assert to_mathint(balanceOf(to)) == toBalanceBefore + amount;
        }
    } else {
        assert amount > fromBalanceBefore || to == 0;
    }
}
*/


/*
    @Rule


    @Description:
        Test that transferFrom works correctly. Balances are updated if not reverted. 
        If reverted, it means the transfer amount was too high, or the recipient is 0

    @Formula:
        {
            balanceFromBefore = balanceOf(from)
            balanceToBefore = balanceOf(to)
        }
        <
            transferFrom(from, to, amount)
        >
        {
            lastreverted => to = 0 || amount > balanceOf(from)
            !lastreverted => balanceOf(to) = balanceToBefore + amount &&
                            balanceOf(from) = balanceFromBefore - amount
        }

    @Notes:
        This rule fails on tokens with a blacklist and or pause function, like USDC and USDT.
        The prover finds a counterexample of a reverted transfer to a blacklisted address or a transfer in a paused state.

    @Link:

*/

rule transferFromCorrect(address from, address to, uint256 amount) {
    //nissan: I added the requirement that index==1 for this rule.
    require (_SymbolicLendingPoolL1.getReserveNormalizedIncome(Underlying) == RAY());
    
    env e;
    require e.msg.value == 0;
    uint256 fromBalanceBefore = balanceOf(from);
    uint256 toBalanceBefore = balanceOf(to);
    uint256 allowanceBefore = allowance(from, e.msg.sender);
    require fromBalanceBefore + toBalanceBefore < to_mathint(AAVE_MAX_SUPPLY());

    transferFrom(e, from, to, amount);

    assert from != to =>
        to_mathint(balanceOf(from)) == fromBalanceBefore - amount &&
        to_mathint(balanceOf(to)) == toBalanceBefore + amount &&
        (to_mathint(allowance(from, e.msg.sender)) == allowanceBefore - amount ||
         allowance(from, e.msg.sender) == max_uint256);
}

/*
    @Rule

    @Description:
        Balance of address 0 is always 0

    @Formula:
        { balanceOf[0] = 0 }

    @Notes:


    @Link:

*/
/*
invariant ZeroAddressNoBalance()
    balanceOf(0) == 0;
*/


/*
    @Rule

    @Description:
        Contract calls don't change token total supply.

    @Formula:
        {
            supplyBefore = totalSupply()
        }
        < f(e, args)>
        {
            supplyAfter = totalSupply()
            supplyBefore == supplyAfter
        }

    @Notes:
        This rule should fail for any token that has functions that change totalSupply(), like mint() and burn().
        It's still important to run the rule and see if it fails in functions that _aren't_ supposed to modify totalSupply()

    @Link:

*/
rule NoChangeTotalSupply(method f)
    filtered {f ->
        f.selector != sig:burn(address,address,uint256,uint256).selector &&
        f.selector != sig:mint(address,address,uint256,uint256).selector &&
        f.selector != sig:mintToTreasury(uint256,uint256).selector
        }
{
    //    require f.selector != sig:burn(uint256).selector && f.selector != sig:mint(address, uint256).selector;
    env e;
    uint256 totalSupplyBefore = scaledTotalSupply(e);
    calldataarg args;
    f(e, args);
    assert scaledTotalSupply(e) == totalSupplyBefore;
}

/*
 The two rules cover the same ground as NoChangeTotalSupply.
 
 The split into two rules is in order to make the burn/mint features of a tested token even more obvious
*/
// nissan: The following two rules are not relevant for Atoken-With-Delegation hence removed
/*
rule noBurningTokens(method f) {
    uint256 totalSupplyBefore = totalSupply();
    env e;
    calldataarg args;
    f(e, args);
    assert totalSupply() >= totalSupplyBefore;
}

rule noMintingTokens(method f) {
    uint256 totalSupplyBefore = totalSupply();
    env e;
    calldataarg args;
    f(e, args);
    assert totalSupply() <= totalSupplyBefore;
}
*/

/*
    @Rule

    @Description:
        Allowance changes correctly as a result of calls to approve, transfer, increaseAllowance, decreaseAllowance

    @Formula:
        {
            allowanceBefore = allowance(from, spender)
        }
        <
            f(e, args)
        >
        {
            f.selector = approve(spender, amount) => allowance(from, spender) = amount
            f.selector = transferFrom(from, spender, amount) => allowance(from, spender) = allowanceBefore - amount
            f.selector = decreaseAllowance(spender, delta) => allowance(from, spender) = allowanceBefore - delta
            f.selector = increaseAllowance(spender, delta) => allowance(from, spender) = allowanceBefore + delta
            generic f.selector => allowance(from, spender) == allowanceBefore
        }

    @Notes:
        Some ERC20 tokens have functions like permit() that change allowance via a signature. 
        The rule will fail on such functions.

    @Link:

*/
rule ChangingAllowance(method f, address from, address spender) {
    uint256 allowanceBefore = allowance(from, spender);
    env e;
    if (f.selector == sig:approve(address, uint256).selector) {
        address spender_;
        uint256 amount;
        approve(e, spender_, amount);
        if (from == e.msg.sender && spender == spender_) {
            assert allowance(from, spender) == amount;
        } else {
            assert allowance(from, spender) == allowanceBefore;
        }
    } else if (f.selector == sig:transferFrom(address,address,uint256).selector) {
        address from_;
        address to;
        uint256 amount;
        transferFrom(e, from_, to, amount);
        mathint allowanceAfter = allowance(from, spender);
        if (from == from_ && spender == e.msg.sender) {
            assert from == to || allowanceBefore == max_uint256 || allowanceAfter == allowanceBefore - amount;
        } else {
            assert allowance(from, spender) == allowanceBefore;
        }
    } else if (f.selector == sig:decreaseAllowance(address, uint256).selector) {
        address spender_;
        uint256 amount;
        require amount <= allowanceBefore;
        decreaseAllowance(e, spender_, amount);
        if (from == e.msg.sender && spender == spender_) {
            assert to_mathint(allowance(from, spender)) == allowanceBefore - amount;
        } else {
            assert allowance(from, spender) == allowanceBefore;
        }
    } else if (f.selector == sig:increaseAllowance(address, uint256).selector) {
        address spender_;
        uint256 amount;
        require amount + allowanceBefore < max_uint256;
        increaseAllowance(e, spender_, amount);
        if (from == e.msg.sender && spender == spender_) {
            assert to_mathint(allowance(from, spender)) == allowanceBefore + amount;
        } else {
            assert allowance(from, spender) == allowanceBefore;
        }
    } 
    else
    {
        calldataarg args;
        f(e, args);
        assert allowance(from, spender) == allowanceBefore ||
            f.selector == sig:permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector;
    }
}

/*
    @Rule

    @Description:
        Transfer from a to b doesn't change the sum of their balances

    @Formula:
        {
            balancesBefore = balanceOf(msg.sender) + balanceOf(b)
        }
        <
            transfer(b, amount)
        >
        {
            balancesBefore == balanceOf(msg.sender) + balanceOf(b)
        }

    @Notes:

    @Link:

*/
//nissan: changed from balanceOf to scaledBalanceOf. First it's more relevant to ERC20, second
//        I'm getting time-out
rule TransferSumOfFromAndToBalancesStaySame(address to, uint256 amount) {
    env e;
    mathint sum = scaledBalanceOf(e.msg.sender) + scaledBalanceOf(to);
    require sum < max_uint256;
    transfer(e, to, amount); 
    assert scaledBalanceOf(e.msg.sender) + scaledBalanceOf(to) == sum;
}

/*
    @Rule

    @Description:
        Transfer using transferFrom() from a to b doesn't change the sum of their balances

    @Formula:
        {
            balancesBefore = balanceOf(a) + balanceOf(b)
        }
        <
            transferFrom(a, b)
        >
        {
            balancesBefore == balanceOf(a) + balanceOf(b)
        }

    @Notes:

    @Link:

*/
//nissan: changed from balanceOf to scaledBalanceOf. First it's more relevant to ERC20, second
//        I'm getting time-out
rule TransferFromSumOfFromAndToBalancesStaySame(address from, address to, uint256 amount) {
    env e;
    mathint sum = scaledBalanceOf(from) + scaledBalanceOf(to);
    require sum < max_uint256;
    transferFrom(e, from, to, amount); 
    assert scaledBalanceOf(from) + scaledBalanceOf(to) == sum;
}

/*
    @Rule

    @Description:
        Transfer from msg.sender to alice doesn't change the balance of other addresses

    @Formula:
        {
            balanceBefore = balanceOf(bob)
        }
        <
            transfer(alice, amount)
        >
        {
            balanceOf(bob) == balanceBefore
        }

    @Notes:

    @Link:

*/
rule TransferDoesntChangeOtherBalance(address to, uint256 amount, address other) {
    env e;
    require other != e.msg.sender;
    require other != to && other != currentContract;
    uint256 balanceBefore = balanceOf(other);
    transfer(e, to, amount); 
    assert balanceBefore == balanceOf(other);
}

/*
    @Rule

    @Description:
        Transfer from alice to bob using transferFrom doesn't change the balance of other addresses

    @Formula:
        {
            balanceBefore = balanceOf(charlie)
        }
        <
            transferFrom(alice, bob, amount)
        >
        {
            balanceOf(charlie) = balanceBefore
        }

    @Notes:

    @Link:

*/
rule TransferFromDoesntChangeOtherBalance(address from, address to, uint256 amount, address other) {
    env e;
    require other != from;
    require other != to;
    uint256 balanceBefore = balanceOf(other);
    transferFrom(e, from, to, amount); 
    assert balanceBefore == balanceOf(other);
}

/*
    @Rule

    @Description:
        Balance of an address, who is not a sender or a recipient in transfer functions, doesn't decrease 
        as a result of contract calls

    @Formula:
        {
            balanceBefore = balanceOf(charlie)
        }
        <
            f(e, args)
        >
        {
            f.selector != transfer && f.selector != transferFrom => balanceOf(charlie) == balanceBefore
        }

    @Notes:
        USDC token has functions like transferWithAuthorization that use a signed message for allowance. 
        FTT token has a burnFrom that lets an approved spender to burn owner's token.
        Certora prover finds these counterexamples to this rule.
        In general, the rule will fail on all functions other than transfer/transferFrom that change a balance of an address.

    @Link:

*/
rule OtherBalanceOnlyGoesUp(address other, method f)
    filtered {f ->
        f.selector != sig:burn(address,address,uint256,uint256).selector &&
        f.selector != sig:transferOnLiquidation(address,address,uint256).selector
        }
{
    
    env e;
    require other != currentContract;
    uint256 balanceBefore = scaledBalanceOf(e,other);

    if (f.selector == sig:transferFrom(address, address, uint256).selector) {
        address from;
        address to;
        uint256 amount;
        require(other != from);
        require balanceOf(from) + balanceBefore < max_uint256;
        transferFrom(e, from, to, amount);
    } else if (f.selector == sig:transfer(address, uint256).selector) {
        require other != e.msg.sender;
        require balanceOf(e.msg.sender) + balanceBefore < max_uint256;
        calldataarg args;
        f(e, args);
    } else {
        require other != e.msg.sender;
        calldataarg args;
        f(e, args);
    }

    assert scaledBalanceOf(e,other) >= balanceBefore;
}

// nissan: The following rule doesn't apply to AToken
/*
rule noRebasing(method f, address alice) {
    env e;
    calldataarg args;

    require doesntChangeBalance(f);
    
    uint256 balanceBefore = balanceOf(alice);
    f(e, args);
    uint256 balanceAfter = balanceOf(alice);
    assert balanceBefore == balanceAfter;
}
*/
