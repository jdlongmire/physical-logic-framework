// Lean compiler output
// Module: PhysicalLogicFramework.FeasibilityRatio
// Imports: Init Mathlib.Data.Nat.Basic Mathlib.Data.Finset.Basic Mathlib.Data.Fintype.Basic Mathlib.Data.Fintype.Prod Mathlib.GroupTheory.Perm.Basic Mathlib.Data.Fintype.Perm Mathlib.Tactic.NormNum Mathlib.GroupTheory.Perm.Cycle.Type
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l_LFT_trans__12;
lean_object* l_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equiv_swapCore___at___Equiv_swap___at___LFT_trans__01_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Equiv_trans___redArg(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_PhysicalLogicFramework_FeasibilityRatio_0__LFT_factorial_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_trans__01;
static lean_object* l_LFT_cycle__012___closed__1;
static lean_object* l_LFT_trans__01___closed__0;
static lean_object* l_LFT_cycle__021___closed__0;
LEAN_EXPORT lean_object* l___private_PhysicalLogicFramework_FeasibilityRatio_0__LFT_factorial_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_LFT_inversionCount___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_MaxInformationEntropy___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Equiv_swap___at___LFT_trans__01_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Equiv_instFintype___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_id__3;
static lean_object* l_LFT_trans__01___closed__1;
LEAN_EXPORT lean_object* l_LFT_cycle__012;
static lean_object* l_LFT_cycle__012___closed__0;
LEAN_EXPORT lean_object* l_Equiv_swap___at___LFT_trans__01_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_factorial(lean_object*);
LEAN_EXPORT lean_object* l_LFT_LFTConstraintThreshold(lean_object*);
static lean_object* l_LFT_id__3___closed__0;
LEAN_EXPORT uint8_t l_LFT_ValidArrangements___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equiv_swapCore___at___Equiv_swap___at___LFT_trans__01_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_inversionCount(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_LFT_trans__02___closed__1;
LEAN_EXPORT lean_object* l_LFT_LFTConstraintThreshold___boxed(lean_object*);
LEAN_EXPORT lean_object* l_LFT_ValidArrangements(lean_object*);
static lean_object* l_LFT_trans__02___closed__0;
LEAN_EXPORT lean_object* l_LFT_cycle__021;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_LFT_trans__12___closed__0;
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_factorial___boxed(lean_object*);
LEAN_EXPORT lean_object* l_LFT_inversionCount___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_Equiv_refl(lean_object*);
LEAN_EXPORT lean_object* l___private_PhysicalLogicFramework_FeasibilityRatio_0__LFT_factorial_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_ValidArrangements___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_TotalArrangements___boxed(lean_object*);
LEAN_EXPORT lean_object* l_LFT_trans__02;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_PhysicalLogicFramework_FeasibilityRatio_0__LFT_factorial_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_MaxInformationEntropy(lean_object*);
LEAN_EXPORT lean_object* l_LFT_TotalArrangements(lean_object*);
LEAN_EXPORT lean_object* l_Equiv_swap___at___LFT_trans__01_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_factorial(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 1)
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(1u);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
x_7 = lean_nat_add(x_6, x_5);
x_8 = l_LFT_factorial(x_6);
lean_dec(x_6);
x_9 = lean_nat_mul(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_LFT_factorial___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_LFT_factorial(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LFT_TotalArrangements(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_LFT_factorial(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LFT_TotalArrangements___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_LFT_TotalArrangements(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_LFT_inversionCount___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
lean_inc_ref(x_6);
x_7 = lean_apply_1(x_6, x_4);
x_8 = lean_apply_1(x_6, x_3);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_LFT_inversionCount(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l_LFT_inversionCount___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_List_finRange(x_1);
lean_inc(x_4);
x_5 = l_Multiset_product___redArg(x_4, x_4);
x_6 = l_Multiset_filter___redArg(x_3, x_5);
x_7 = l_List_lengthTR___redArg(x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_LFT_inversionCount___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_LFT_inversionCount___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LFT_MaxInformationEntropy(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
x_4 = lean_nat_mul(x_1, x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_shiftr(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LFT_MaxInformationEntropy___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_LFT_MaxInformationEntropy(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LFT_LFTConstraintThreshold(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 1)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = lean_nat_dec_eq(x_5, x_2);
if (x_6 == 1)
{
lean_dec(x_5);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_nat_sub(x_5, x_4);
lean_dec(x_5);
x_8 = lean_nat_dec_eq(x_7, x_2);
if (x_8 == 1)
{
lean_dec(x_7);
return x_4;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_nat_sub(x_7, x_4);
lean_dec(x_7);
x_10 = lean_nat_dec_eq(x_9, x_2);
if (x_10 == 1)
{
lean_dec(x_9);
return x_4;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_nat_sub(x_9, x_4);
lean_dec(x_9);
x_12 = lean_nat_dec_eq(x_11, x_2);
if (x_12 == 1)
{
lean_object* x_13; 
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(3u);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_14 = lean_nat_sub(x_11, x_4);
lean_dec(x_11);
x_15 = lean_unsigned_to_nat(5u);
x_16 = lean_nat_add(x_14, x_15);
x_17 = l_LFT_MaxInformationEntropy(x_16);
x_18 = lean_unsigned_to_nat(4u);
x_19 = lean_nat_add(x_14, x_18);
lean_dec(x_14);
x_20 = lean_nat_mul(x_16, x_19);
lean_dec(x_19);
lean_dec(x_16);
x_21 = lean_unsigned_to_nat(6u);
x_22 = lean_nat_div(x_20, x_21);
lean_dec(x_20);
x_23 = lean_nat_dec_le(x_17, x_22);
if (x_23 == 0)
{
lean_dec(x_17);
return x_22;
}
else
{
lean_dec(x_22);
return x_17;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_LFT_LFTConstraintThreshold___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_LFT_LFTConstraintThreshold(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_LFT_ValidArrangements___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_3 = l_LFT_inversionCount(x_1, x_2);
x_4 = l_LFT_LFTConstraintThreshold(x_1);
lean_dec(x_1);
x_5 = lean_nat_dec_le(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_LFT_ValidArrangements(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_LFT_ValidArrangements___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = l_List_finRange(x_1);
x_4 = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_3);
lean_inc_ref(x_4);
x_5 = l_Equiv_instFintype___redArg(x_4, x_4, x_3, x_3);
x_6 = l_Multiset_filter___redArg(x_2, x_5);
x_7 = l_List_lengthTR___redArg(x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_LFT_ValidArrangements___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_LFT_ValidArrangements___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_PhysicalLogicFramework_FeasibilityRatio_0__LFT_factorial_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_dec_ref(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_PhysicalLogicFramework_FeasibilityRatio_0__LFT_factorial_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_PhysicalLogicFramework_FeasibilityRatio_0__LFT_factorial_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_PhysicalLogicFramework_FeasibilityRatio_0__LFT_factorial_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_PhysicalLogicFramework_FeasibilityRatio_0__LFT_factorial_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_PhysicalLogicFramework_FeasibilityRatio_0__LFT_factorial_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_PhysicalLogicFramework_FeasibilityRatio_0__LFT_factorial_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_LFT_id__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Equiv_refl(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_LFT_id__3() {
_start:
{
lean_object* x_1; 
x_1 = l_LFT_id__3___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Equiv_swapCore___at___Equiv_swap___at___LFT_trans__01_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_3, x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_3, x_2);
if (x_5 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_inc(x_1);
return x_1;
}
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Equiv_swap___at___LFT_trans__01_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Equiv_swapCore___at___Equiv_swap___at___LFT_trans__01_spec__0_spec__0(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Equiv_swap___at___LFT_trans__01_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Equiv_swap___at___LFT_trans__01_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_LFT_trans__01___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LFT_trans__01___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LFT_trans__01() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_LFT_trans__01___closed__0;
x_2 = l_LFT_trans__01___closed__1;
x_3 = l_Equiv_swap___at___LFT_trans__01_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Equiv_swapCore___at___Equiv_swap___at___LFT_trans__01_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Equiv_swapCore___at___Equiv_swap___at___LFT_trans__01_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Equiv_swap___at___LFT_trans__01_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Equiv_swap___at___LFT_trans__01_spec__0___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_LFT_trans__02___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LFT_trans__02___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_LFT_trans__02___closed__0;
x_2 = l_LFT_trans__01___closed__0;
x_3 = l_Equiv_swap___at___LFT_trans__01_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LFT_trans__02() {
_start:
{
lean_object* x_1; 
x_1 = l_LFT_trans__02___closed__1;
return x_1;
}
}
static lean_object* _init_l_LFT_trans__12___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_LFT_trans__02___closed__0;
x_2 = l_LFT_trans__01___closed__1;
x_3 = l_Equiv_swap___at___LFT_trans__01_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LFT_trans__12() {
_start:
{
lean_object* x_1; 
x_1 = l_LFT_trans__12___closed__0;
return x_1;
}
}
static lean_object* _init_l_LFT_cycle__012___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_LFT_trans__01___closed__1;
x_2 = l_LFT_trans__01___closed__0;
x_3 = l_Equiv_swap___at___LFT_trans__01_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LFT_cycle__012___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_LFT_cycle__012___closed__0;
x_2 = l_LFT_trans__12___closed__0;
x_3 = l_Equiv_trans___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LFT_cycle__012() {
_start:
{
lean_object* x_1; 
x_1 = l_LFT_cycle__012___closed__1;
return x_1;
}
}
static lean_object* _init_l_LFT_cycle__021___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_LFT_trans__02___closed__1;
x_2 = l_LFT_cycle__012___closed__0;
x_3 = l_Equiv_trans___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LFT_cycle__021() {
_start:
{
lean_object* x_1; 
x_1 = l_LFT_cycle__021___closed__0;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Finset_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Prod(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_GroupTheory_Perm_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Perm(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_NormNum(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_GroupTheory_Perm_Cycle_Type(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PhysicalLogicFramework_FeasibilityRatio(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fintype_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fintype_Prod(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_GroupTheory_Perm_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fintype_Perm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_NormNum(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_GroupTheory_Perm_Cycle_Type(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_LFT_id__3___closed__0 = _init_l_LFT_id__3___closed__0();
lean_mark_persistent(l_LFT_id__3___closed__0);
l_LFT_id__3 = _init_l_LFT_id__3();
lean_mark_persistent(l_LFT_id__3);
l_LFT_trans__01___closed__0 = _init_l_LFT_trans__01___closed__0();
lean_mark_persistent(l_LFT_trans__01___closed__0);
l_LFT_trans__01___closed__1 = _init_l_LFT_trans__01___closed__1();
lean_mark_persistent(l_LFT_trans__01___closed__1);
l_LFT_trans__01 = _init_l_LFT_trans__01();
lean_mark_persistent(l_LFT_trans__01);
l_LFT_trans__02___closed__0 = _init_l_LFT_trans__02___closed__0();
lean_mark_persistent(l_LFT_trans__02___closed__0);
l_LFT_trans__02___closed__1 = _init_l_LFT_trans__02___closed__1();
lean_mark_persistent(l_LFT_trans__02___closed__1);
l_LFT_trans__02 = _init_l_LFT_trans__02();
lean_mark_persistent(l_LFT_trans__02);
l_LFT_trans__12___closed__0 = _init_l_LFT_trans__12___closed__0();
lean_mark_persistent(l_LFT_trans__12___closed__0);
l_LFT_trans__12 = _init_l_LFT_trans__12();
lean_mark_persistent(l_LFT_trans__12);
l_LFT_cycle__012___closed__0 = _init_l_LFT_cycle__012___closed__0();
lean_mark_persistent(l_LFT_cycle__012___closed__0);
l_LFT_cycle__012___closed__1 = _init_l_LFT_cycle__012___closed__1();
lean_mark_persistent(l_LFT_cycle__012___closed__1);
l_LFT_cycle__012 = _init_l_LFT_cycle__012();
lean_mark_persistent(l_LFT_cycle__012);
l_LFT_cycle__021___closed__0 = _init_l_LFT_cycle__021___closed__0();
lean_mark_persistent(l_LFT_cycle__021___closed__0);
l_LFT_cycle__021 = _init_l_LFT_cycle__021();
lean_mark_persistent(l_LFT_cycle__021);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
