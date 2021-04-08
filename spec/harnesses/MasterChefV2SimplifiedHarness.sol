pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

import "./MasterChefV2Harness.sol";

contract MasterChefV2SimplifiedHarness is MasterChefV2Harness {
    ////////////////////////////////////////////////////////////////////////////
    //                         Constructors and inits                         //
    ////////////////////////////////////////////////////////////////////////////
    constructor(IMasterChef _MASTER_CHEF, IERC20 _sushi, uint256 _MASTER_PID)
                    MasterChefV2Harness(_MASTER_CHEF, _sushi, _MASTER_PID) public { }

    ////////////////////////////////////////////////////////////////////////////
    //                           Overrided Methods                            //
    ////////////////////////////////////////////////////////////////////////////

    mapping(uint256 => mapping(uint64 => mapping( uint256 => uint256))) symbolicSushiReward; // random number
    function calculateSushiReward(uint256 blocks, uint64 poolAllocPoint) public override returns (uint256) {
        return symbolicSushiReward[blocks][poolAllocPoint][totalAllocPoint];
    }

    mapping(uint256 => mapping(uint256 => uint256)) symbolicSushiPerShare; // random number
    function calculateSushiPerShare(uint256 sushiReward, uint256 lpSupply) public override returns (uint128) {
        return (sushiReward.mul(ACC_SUSHI_PRECISION) / lpSupply).to128();
    }
}