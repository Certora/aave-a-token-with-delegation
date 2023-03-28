// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import 'forge-std/Test.sol';
import {IPool, ATokenWithDelegation} from '../src/contracts/ATokenWithDelegation.sol';
import {IGovernancePowerDelegationToken} from 'aave-token-v3/interfaces/IGovernancePowerDelegationToken.sol';
import {DelegationState} from 'aave-token-v3/DelegationAwareBalance.sol';

contract PoolMock {
  address public constant ADDRESSES_PROVIDER = address(12351);
}

contract DelegationBaseTest is Test, ATokenWithDelegation {
  uint256 constant INDEX = 1e27;
  uint256 constant AMOUNT = 100 ether;

  constructor() ATokenWithDelegation(IPool(address(new PoolMock()))) {}

  enum DelegationType {
    VOTING,
    PROPOSITION,
    FULL_POWER
  }

  modifier mintAmount(address caller) {
    _mintAmount(caller);
    _;
  }

  // prepare a state where delegator is delegating full power to receiver
  modifier prepareDelegationToReceiver(address delegator, address receiver) {
    // set up delegator delegation balances
    _delegatedBalances[delegator].delegationState = DelegationState.FULL_POWER_DELEGATED;

    // set up receiver delegation balances
    _delegatedBalances[receiver].delegatedVotingBalance = uint72(
      _userState[delegator].balance / POWER_SCALE_FACTOR
    );
    _delegatedBalances[receiver].delegatedPropositionBalance = uint72(
      _userState[delegator].balance / POWER_SCALE_FACTOR
    );

    _votingDelegatee[delegator] = receiver;
    _propositionDelegatee[delegator] = receiver;

    _;
  }

  modifier prepareDelegationByTypeToReceiver(
    address delegator,
    address receiver,
    IGovernancePowerDelegationToken.GovernancePowerType delegationType
  ) {
    // set up receiver delegation balances
    if (delegationType == IGovernancePowerDelegationToken.GovernancePowerType.VOTING) {
      _delegatedBalances[delegator].delegationState = DelegationState.VOTING_DELEGATED;

      _delegatedBalances[receiver].delegatedVotingBalance = uint72(
        _userState[delegator].balance / POWER_SCALE_FACTOR
      );
      _votingDelegatee[delegator] = receiver;
    } else {
      _delegatedBalances[delegator].delegationState = DelegationState.PROPOSITION_DELEGATED;

      _delegatedBalances[receiver].delegatedPropositionBalance = uint72(
        _userState[delegator].balance / POWER_SCALE_FACTOR
      );

      _propositionDelegatee[delegator] = receiver;
    }

    _;
  }

  modifier validateNoChangesInDelegation(address user) {
    address beforeVotingDelegatee = _votingDelegatee[user];
    address beforePropositionDelegatee = _propositionDelegatee[user];
    uint104 beforeDelegationVotingPowerOfUser = _getDelegationBalanceByType(
      user,
      IGovernancePowerDelegationToken.GovernancePowerType.VOTING
    );
    uint104 beforeDelegationPropositionPowerOfUser = _getDelegationBalanceByType(
      user,
      IGovernancePowerDelegationToken.GovernancePowerType.PROPOSITION
    );
    DelegationState delegationStateBefore = _delegatedBalances[user].delegationState;

    _;

    address afterVotingDelegatee = _votingDelegatee[user];
    address afterPropositionDelegatee = _propositionDelegatee[user];
    uint104 afterDelegationVotingPowerOfUser = _getDelegationBalanceByType(
      user,
      IGovernancePowerDelegationToken.GovernancePowerType.VOTING
    );
    uint104 afterDelegationPropositionPowerOfUser = _getDelegationBalanceByType(
      user,
      IGovernancePowerDelegationToken.GovernancePowerType.PROPOSITION
    );
    DelegationState delegationStateAfter = _delegatedBalances[user].delegationState;

    assertEq(beforeVotingDelegatee, afterVotingDelegatee);
    assertEq(beforePropositionDelegatee, afterPropositionDelegatee);
    assertEq(beforeDelegationVotingPowerOfUser, afterDelegationVotingPowerOfUser);
    assertEq(beforeDelegationPropositionPowerOfUser, afterDelegationPropositionPowerOfUser);
    assertEq(uint8(delegationStateBefore), uint8(delegationStateAfter));
  }

  modifier validateNoChangesInVotingDelegatee(address user) {
    address beforeDelegatee = _votingDelegatee[user];
    _;
    address afterDelegatee = _votingDelegatee[user];

    assertEq(beforeDelegatee, afterDelegatee);
  }

  modifier validateNoChangesInPropositionDelegatee(address user) {
    address beforeDelegatee = _propositionDelegatee[user];
    _;
    address afterDelegatee = _propositionDelegatee[user];

    assertEq(beforeDelegatee, afterDelegatee);
  }

  // validates no changes happened in delegation balance for a user and delegation type
  modifier validateNoChangesInDelegationBalanceByType(
    address user,
    IGovernancePowerDelegationToken.GovernancePowerType delegationType
  ) {
    uint104 beforeDelegationPowerOfUser = _getDelegationBalanceByType(user, delegationType);

    _;

    uint104 afterDelegationPowerOfUser = _getDelegationBalanceByType(user, delegationType);

    // ----------------------------- VALIDATIONS ----------------------------------------------
    assertEq(beforeDelegationPowerOfUser, afterDelegationPowerOfUser);
  }

  modifier validateNoChangesInDelegationState(address user) {
    DelegationState delegationStateBefore = _delegatedBalances[user].delegationState;
    _;
    DelegationState delegationStateAfter = _delegatedBalances[user].delegationState;

    assertEq(uint8(delegationStateBefore), uint8(delegationStateAfter));
  }

  modifier validateUserTokenBalance(address user) {
    uint128 beforeDelegationActualBalanceOfDelegator = _getHolderActualBalance(user);

    _;
    uint128 afterDelegationActualBalanceOfDelegator = _getHolderActualBalance(user);

    // ----------------------------- VALIDATIONS ----------------------------------------------
    // actual a token balance should not have changed
    assertEq(beforeDelegationActualBalanceOfDelegator, afterDelegationActualBalanceOfDelegator);
  }

  // check that delegation power of delegator has been removed from delegation recipient
  modifier validateDelegationRemoved(
    address delegator,
    address delegationRecipient,
    IGovernancePowerDelegationToken.GovernancePowerType delegationType
  ) {
    uint128 beforeDelegationActualBalanceOfDelegator = _getHolderActualBalance(delegator);
    uint72 beforeDelegationPowerOfDelegator = _getDelegationBalanceByType(
      delegator,
      delegationType
    );
    uint72 beforeDelegationPowerOfDelegationRecipient = _getDelegationBalanceByType(
      delegationRecipient,
      delegationType
    );

    _;

    uint72 afterDelegationPowerOfDelegator = _getDelegationBalanceByType(delegator, delegationType);
    uint72 afterDelegationPowerOfDelegationRecipient = _getDelegationBalanceByType(
      delegationRecipient,
      delegationType
    );

    assertEq(beforeDelegationPowerOfDelegator, afterDelegationPowerOfDelegator);
    assertEq(
      afterDelegationPowerOfDelegationRecipient,
      beforeDelegationPowerOfDelegationRecipient -
        uint72(beforeDelegationActualBalanceOfDelegator / POWER_SCALE_FACTOR)
    );
  }

  // validates that the balance of delegator is now being delegated to recipient
  modifier validateDelegationPower(
    address delegator,
    address delegationRecipient,
    IGovernancePowerDelegationToken.GovernancePowerType delegationType
  ) {
    uint128 beforeDelegationActualBalanceOfDelegator = _getHolderActualBalance(delegator);
    uint72 beforeDelegationPowerOfDelegator = _getDelegationBalanceByType(
      delegator,
      delegationType
    );
    uint72 beforeDelegationPowerOfDelegationRecipient = _getDelegationBalanceByType(
      delegationRecipient,
      delegationType
    );

    _;

    uint72 afterDelegationPowerOfDelegator = _getDelegationBalanceByType(delegator, delegationType);
    uint72 afterDelegationPowerOfDelegationRecipient = _getDelegationBalanceByType(
      delegationRecipient,
      delegationType
    );

    // balance of delegator moved to delegation recipient
    assertEq(beforeDelegationPowerOfDelegator, afterDelegationPowerOfDelegator);
    assertEq(
      afterDelegationPowerOfDelegationRecipient,
      beforeDelegationPowerOfDelegationRecipient +
        uint72(beforeDelegationActualBalanceOfDelegator / POWER_SCALE_FACTOR)
    );
  }

  // validates that delegator delegation state changes accordingly
  modifier validateDelegationState(
    address delegator,
    address delegationRecipient,
    DelegationType delegationType
  ) {
    DelegationState beforeDelegationStateOfDelegationRecipient = _getDelegationState(
      delegationRecipient
    );

    _;

    DelegationState afterDelegationStateOfDelegator = _getDelegationState(delegator);
    DelegationState afterDelegationStateOfDelegationRecipient = _getDelegationState(
      delegationRecipient
    );

    // ----------------------------- VALIDATIONS ----------------------------------------------
    if (delegationType == DelegationType.FULL_POWER) {
      assertEq(uint8(afterDelegationStateOfDelegator), uint8(DelegationState.FULL_POWER_DELEGATED));
    } else if (delegationType == DelegationType.VOTING) {
      assertEq(uint8(afterDelegationStateOfDelegator), uint8(DelegationState.VOTING_DELEGATED));
    } else {
      assertEq(
        uint8(afterDelegationStateOfDelegator),
        uint8(DelegationState.PROPOSITION_DELEGATED)
      );
    }
    assertEq(
      uint8(beforeDelegationStateOfDelegationRecipient),
      uint8(afterDelegationStateOfDelegationRecipient)
    );
  }

  modifier validateDelegationReceiver(
    address delegator,
    address delegationReceiver,
    IGovernancePowerDelegationToken.GovernancePowerType delegationType
  ) {
    _;
    if (delegationType == IGovernancePowerDelegationToken.GovernancePowerType.VOTING) {
      assertEq(_votingDelegatee[delegator], delegationReceiver);
    } else {
      assertEq(_propositionDelegatee[delegator], delegationReceiver);
    }
  }

  function _getHolderActualBalance(address holder) internal view returns (uint128) {
    return _userState[holder].balance;
  }

  function _getDelegationBalanceByType(
    address holder,
    IGovernancePowerDelegationToken.GovernancePowerType delegationType
  ) internal view returns (uint72) {
    if (delegationType == IGovernancePowerDelegationToken.GovernancePowerType.VOTING) {
      return _delegatedBalances[holder].delegatedVotingBalance;
    } else {
      return _delegatedBalances[holder].delegatedPropositionBalance;
    }
  }

  function _getDelegationState(address holder) internal view returns (DelegationState) {
    return _delegatedBalances[holder].delegationState;
  }

  function _mintAmount(address receiver) internal {
    hoax(address(POOL));
    this.mint(receiver, receiver, AMOUNT, INDEX);
  }
}
