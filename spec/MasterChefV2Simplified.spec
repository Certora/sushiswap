/*
 * This is a specification file for MasterChefV2's formal verification
 * using the Certora prover.
 *
 * Run this file with scripts/_runMasterChefV2Simplified.sh
 */

// Declaration of contracts used in the sepc 
using DummyERC20A as tokenA
using DummyERC20B as tokenB
using DummySUSHI as sushiToken

/*
 * Declaration of methods that are used in the rules.
 * envfree indicate that the method is not dependent on the environment (msg.value, msg.sender).
 * Methods that are not declared here are assumed to be dependent on env.
 */
methods {
	// Getters for the internals
	userInfoAmount(uint256 pid, address user) returns (uint256) envfree 
	userInfoRewardDebt(uint256 pid, address user) returns (int256) envfree 
	userLpTokenBalanceOf(uint256 pid, address user) returns (uint256) envfree // NOT USED

	poolInfoAccSushiPerShare(uint256 pid) returns (uint128) envfree
	poolInfoLastRewardBlock(uint256 pid) returns (uint64) envfree
	poolInfoAllocPoint(uint256 pid) returns (uint64) envfree
	totalAllocPoint() returns (uint256) envfree

	lpToken(uint256 pid) returns (address) envfree
	rewarder(uint256 pid) returns (address) envfree

	// overrided methods
	sushiPerBlock() returns (uint256 amount)

	// ERC20 
	balanceOf(address) => DISPATCHER(true) 
	totalSupply() => DISPATCHER(true)
	transferFrom(address from, address to, uint256 amount) => DISPATCHER(true)
	transfer(address to, uint256 amount) => DISPATCHER(true)
	approve(address t, uint256 amount) => NONDET
	permit(address owner, address spender, uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s) => NONDET
	
	// General Helpers
	compare(int256 x, int256 y) returns (bool) envfree // Helper to check <= for int256
	intEquality(int256 x, int256 y) returns (bool) envfree // Helper to check int equality
	compareUint128(uint128 x, uint128 y) returns (bool) envfree // Helper to check >= for uint128 // NOT USED
	intDeltaOne(int256 x, int256 y) returns (bool) envfree // Helper to allow a difference of 1 for int256
	sub(uint256 a, int256 b) returns (int256) envfree // NOT USED
	sub(int256 a, int256 b) returns (int256) envfree // NOT USED
	sub(uint256 a, uint256 b) returns (int256) envfree // NOT USED
	mul(uint256 a, uint256 b) returns (uint256) envfree // NOT USED

	// Helper Invariant Functions
	poolLength() returns (uint256) envfree
	lpTokenLength() returns (uint256) envfree // NOT USED
	rewarderLength() returns (uint256) envfree // NOT USED

	// SUSHI token
	SUSHI() returns (address) envfree // NOT USED
	sushiToken.balanceOf(address) returns (uint256) // NOT USED

	// Dummy ERC20
	tokenA.balanceOf(address) returns (uint256) // NOT USED
	tokenB.balanceOf(address) returns (uint256) // NOT USED

	// Rewarder
	// SIG_ON_SUSHI_REWARD = 0xbb6cc2ef; // onSushiReward(uint256,address,uint256)
	0xbb6cc2ef => NONDET

	// MasterChefV1
	deposit(uint256 pid, uint256 amount) => NONDET

	lpSupply(uint256 pid) returns (uint256) envfree
}

// Constants

definition MAX_UINT64() returns uint64 = 0xFFFFFFFFFFFFFFFF;

definition MAX_UINT256() returns uint256 =
	0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;

// Rules

// Timing out
// https://vaas-stg.certora.com/output/98097/41b11683b81631cc4414/?anonymousKey=e62ded94bb532c4a1f6bda0187caed62ae2283f8
// Fails with a simplified ratio
rule correctEffectOfChangeToAllocPoint(uint256 pid, address user,
									   uint256 allocPoint, bool overwrite) {
	env e1;
	env e2;
	env e3;

	require e2.block.number >= e1.block.number;
	require e3.block.number >= e2.block.number;

	uint256 _pendingSushi = pendingSushi(e1, pid, user);

	updatePool(e2, pid);

	address rewarder;
	set(e2, pid, allocPoint, rewarder, overwrite);

	uint256 pendingSushi_ = pendingSushi(e3, pid, user);

	assert(pendingSushi_ >= _pendingSushi, 
	       "The effect of changing allocPoint is incorrect");
}

// Passing
// https://vaas-stg.certora.com/output/98097/dae7846ec701c26a71f1/?anonymousKey=b93a6af989f37e9a2acae07e373e65fd2355fa2a
rule depositThenWithdraw(uint256 pid, address user, uint256 amount, address to) {
	env e;

	require e.msg.sender == to;

	uint256 _userInfoAmount = userInfoAmount(pid, user);
	int256 _userInfoRewardDebt = userInfoRewardDebt(pid, user);

	deposit(e, pid, amount, to);
	withdraw(e, pid, amount, to);

	uint256 userInfoAmount_ = userInfoAmount(pid, user);
	int256 userInfoRewardDebt_ = userInfoRewardDebt(pid, user);

	assert(_userInfoAmount == userInfoAmount_, "user amount changed");
	assert(intEquality(_userInfoRewardDebt, userInfoRewardDebt_),
		   "user reward debt changed");
}

// Timing out 
// https://vaas-stg.certora.com/output/98097/c446b7baea6d299bb2d8/?anonymousKey=abd7ca8f951ec0abbef2c26171a5dcebbfb9af7a
rule orderOfOperationWithdrawAndHarvest(uint256 pid, uint256 amount, address user) {
	env e;
	storage initStorage = lastStorage;

	// call withdraw then harvest
	withdraw(e, pid, amount, user);
	harvest(e, pid, user);

	uint128 splitScenarioAccSushiPerShare = poolInfoAccSushiPerShare(pid);
	uint64 splitScenarioLastRewardBlock = poolInfoLastRewardBlock(pid);
	uint64 splitScenarioAllocPoint = poolInfoAllocPoint(pid);

	uint256 splitScenarioUserInfoAmount = userInfoAmount(pid, user);
	int256 splitScenarioUserInfoRewardDebt = userInfoRewardDebt(pid, user);

	// call harvest then withdraw at initStorage
	harvest(e, pid, user) at initStorage;
	withdraw(e, pid, amount, user);

	uint128 finalScenarioAccSushiPerShare = poolInfoAccSushiPerShare(pid);
	uint64 finalScenarioLastRewardBlock = poolInfoLastRewardBlock(pid);
	uint64 finalScenarioAllocPoint = poolInfoAllocPoint(pid);

	uint256 finalScenarioUserInfoAmount = userInfoAmount(pid, user);
	int256 finalScenarioUserInfoRewardDebt = userInfoRewardDebt(pid, user);

	assert(splitScenarioAccSushiPerShare == finalScenarioAccSushiPerShare, "finalScenarioAccSushiPerShare");
	assert(splitScenarioLastRewardBlock == finalScenarioLastRewardBlock, "finalScenarioLastRewardBlock");
	assert(splitScenarioAllocPoint == splitScenarioAllocPoint, "splitScenarioAllocPoint");

	assert(splitScenarioUserInfoAmount == finalScenarioUserInfoAmount, "finalScenarioUserInfoAmount");
	assert(intDeltaOne(splitScenarioUserInfoRewardDebt, finalScenarioUserInfoRewardDebt), "finalScenarioUserInfoRewardDebt");
}

// Failing
// https://vaas-stg.certora.com/output/98097/1a888f1e502f677501d4/?anonymousKey=4603d0052c2365caef50afafdf031c762f4eeca1
rule additivityOfDepositOnRewardDebt(uint256 pid, uint256 x, uint256 y, address to) {
	env e;
	storage initStorage = lastStorage;

	deposit(e, pid, x, to);
	deposit(e, pid, y, to);

	int256 splitScenarioUserRewardDebt = userInfoRewardDebt(pid, to);

	require x + y <= MAX_UINT256();
	uint256 sum = x + y;
	deposit(e, pid, sum, to) at initStorage;
	
	int256 sumScenarioUserRewardDebt = userInfoRewardDebt(pid, to);

	assert(intEquality(splitScenarioUserRewardDebt, sumScenarioUserRewardDebt), 
		   "deposit is not additive on rewardDebt");
}

// Failing
// https://vaas-stg.certora.com/output/98097/1ccb51a4f1e3c9dfd5eb/?anonymousKey=30c3b98329bd7cad9f2aeebce2127e62bece2848
rule additivityOfWithdrawOnRewardDebt(uint256 pid, uint256 x, uint256 y, address to) {
	env e;
	storage initStorage = lastStorage;

	withdraw(e, pid, x, to);
	withdraw(e, pid, y, to);

	int256 splitScenarioUserRewardDebt = userInfoRewardDebt(pid, to);

	require x + y <= MAX_UINT256();
	uint256 sum = x + y;
	withdraw(e, pid, sum, to) at initStorage;
	
	int256 sumScenarioUserRewardDebt = userInfoRewardDebt(pid, to);

	assert(intEquality(splitScenarioUserRewardDebt, sumScenarioUserRewardDebt), 
		   "withdraw is not additive on rewardDebt");
}

// Failing
// https://vaas-stg.certora.com/output/98097/6d54e7014b96a2ee3453/?anonymousKey=4649d0a54dce4634bb0ba527da86c4fbea267d0a
// No revert information
rule updatePoolRevert(uint256 pid) {
	env e;

	require e.msg.value == 0;
	require lpToken(pid) == tokenA || lpToken(pid) == tokenB;
	require pid < poolLength();
    require e.block.number <= MAX_UINT64();
	require totalAllocPoint() != 0;
	require (e.block.number - poolInfoLastRewardBlock(pid)) * sushiPerBlock(e) <= MAX_UINT256();
	require (e.block.number - poolInfoLastRewardBlock(pid)) * sushiPerBlock(e) * poolInfoAllocPoint(pid) <= MAX_UINT256();

	uint128 sushiPerShare = calculateSushiPerShare(e, 
							calculateSushiReward(e, (e.block.number - poolInfoLastRewardBlock(pid)),
							poolInfoAllocPoint(pid)), lpSupply(pid)); 

	require poolInfoAccSushiPerShare(pid) + sushiPerShare <= MAX_UINT256();
	
	updatePool@withrevert(e, pid);
	bool succ = !lastReverted;

	assert(succ, "updatePoolReverted");
}

// Failing
// https://vaas-stg.certora.com/output/98097/d39dc3437fc9539cc5e6/?anonymousKey=350f42d8ced67961e4d4fddd681bd27373d5e2e4
// might have to assume additivity for updatePoolAdditive for calculateSushiReward to make this pass
rule updatePoolAdditive(uint256 pid) {
	env e1;
	env e2;

	require poolInfoLastRewardBlock(pid) < e1.block.number && e1.block.number < e2.block.number;

	storage initStorage = lastStorage;

	updatePool(e1, pid);
	updatePool(e2, pid);

	uint128 splitScenarioAccSushiPerShare = poolInfoAccSushiPerShare(pid);
	uint64 splitScenarioLastRewardBlock = poolInfoLastRewardBlock(pid);
	uint64 splitScenarioAllocPoint = poolInfoAllocPoint(pid);

	updatePool(e2, pid) at initStorage;

	uint128 finalScenarioAccSushiPerShare = poolInfoAccSushiPerShare(pid);
	uint64 finalScenarioLastRewardBlock = poolInfoLastRewardBlock(pid);
	uint64 finalScenarioAllocPoint = poolInfoAllocPoint(pid);

	assert(splitScenarioAccSushiPerShare == finalScenarioAccSushiPerShare, "finalScenarioAccSushiPerShare");
	assert(splitScenarioLastRewardBlock == finalScenarioLastRewardBlock, "finalScenarioLastRewardBlock");
	assert(splitScenarioAllocPoint == splitScenarioAllocPoint, "splitScenarioAllocPoint");
}