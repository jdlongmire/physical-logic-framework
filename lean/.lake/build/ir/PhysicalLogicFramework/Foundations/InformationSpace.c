// Lean compiler output
// Module: PhysicalLogicFramework.Foundations.InformationSpace
// Imports: Init PhysicalLogicFramework.Foundations.ThreeFundamentalLaws Mathlib.GroupTheory.Perm.Basic Mathlib.Data.Fintype.Perm Mathlib.Analysis.SpecialFunctions.Log.Basic
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
LEAN_EXPORT uint8_t l_LFT_ConstraintValid_inversionCount___lam__0(lean_object*, lean_object*);
lean_object* l_Multiset_filter___redArg(lean_object*, lean_object*);
static lean_object* l_LFT_instGroupSymmetricGroup___closed__0;
LEAN_EXPORT lean_object* l_LFT_instGroupSymmetricGroup___boxed(lean_object*);
LEAN_EXPORT lean_object* l_LFT_instGroupSymmetricGroup(lean_object*);
lean_object* l_Equiv_instFintype___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_instFintypeSymmetricGroup(lean_object*);
lean_object* l_Equiv_Perm_permGroup(lean_object*);
LEAN_EXPORT lean_object* l_LFT_ConstraintValid_inversionCount(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_FiniteProjection(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Multiset_product___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_canonicalI2PS;
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* l_LFT_InformationPoint_component(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_ConstraintValid_inversionCount___lam__0___boxed(lean_object*, lean_object*);
static lean_object* _init_l_LFT_instGroupSymmetricGroup___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Equiv_Perm_permGroup(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_LFT_instGroupSymmetricGroup(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_LFT_instGroupSymmetricGroup___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_LFT_instGroupSymmetricGroup___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_LFT_instGroupSymmetricGroup(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LFT_instFintypeSymmetricGroup(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_List_finRange(x_1);
lean_inc(x_3);
lean_inc_ref(x_2);
x_4 = l_Equiv_instFintype___redArg(x_2, x_2, x_3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LFT_InformationPoint_component(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_LFT_canonicalI2PS() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_LFT_FiniteProjection(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_LFT_ConstraintValid_inversionCount___lam__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_LFT_ConstraintValid_inversionCount(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l_LFT_ConstraintValid_inversionCount___lam__0___boxed), 2, 1);
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
LEAN_EXPORT lean_object* l_LFT_ConstraintValid_inversionCount___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_LFT_ConstraintValid_inversionCount___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_PhysicalLogicFramework_Foundations_ThreeFundamentalLaws(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_GroupTheory_Perm_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Perm(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PhysicalLogicFramework_Foundations_InformationSpace(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PhysicalLogicFramework_Foundations_ThreeFundamentalLaws(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_GroupTheory_Perm_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fintype_Perm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_LFT_instGroupSymmetricGroup___closed__0 = _init_l_LFT_instGroupSymmetricGroup___closed__0();
lean_mark_persistent(l_LFT_instGroupSymmetricGroup___closed__0);
l_LFT_canonicalI2PS = _init_l_LFT_canonicalI2PS();
lean_mark_persistent(l_LFT_canonicalI2PS);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
