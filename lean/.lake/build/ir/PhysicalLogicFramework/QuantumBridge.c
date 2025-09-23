// Lean compiler output
// Module: PhysicalLogicFramework.QuantumBridge
// Imports: Init PhysicalLogicFramework.PermutationGeometry Mathlib.Data.Nat.Basic
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
LEAN_EXPORT lean_object* l_LFT_BornProbability(lean_object*);
LEAN_EXPORT lean_object* l_LFT_InversionCountObservable(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_ConstraintEntanglement(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_cast___at___Rat_ofScientific_spec__0(lean_object*);
lean_object* l_LFT_inversionCount(lean_object*, lean_object*);
lean_object* l_LFT_ValidArrangements(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
static lean_object* l_LFT_BornProbability___closed__0;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* _init_l_LFT_BornProbability___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Nat_cast___at___Rat_ofScientific_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LFT_BornProbability(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_LFT_BornProbability___closed__0;
x_3 = l_LFT_ValidArrangements(x_1);
x_4 = l_Nat_cast___at___Rat_ofScientific_spec__0(x_3);
x_5 = l_Rat_div(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_LFT_InversionCountObservable(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LFT_inversionCount(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LFT_ConstraintEntanglement(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_4 = l_LFT_inversionCount(x_1, x_3);
x_5 = l_LFT_inversionCount(x_1, x_2);
x_6 = lean_nat_dec_le(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_nat_sub(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_nat_sub(x_5, x_4);
lean_dec(x_4);
lean_dec(x_5);
return x_8;
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_PhysicalLogicFramework_PermutationGeometry(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PhysicalLogicFramework_QuantumBridge(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PhysicalLogicFramework_PermutationGeometry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_LFT_BornProbability___closed__0 = _init_l_LFT_BornProbability___closed__0();
lean_mark_persistent(l_LFT_BornProbability___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
