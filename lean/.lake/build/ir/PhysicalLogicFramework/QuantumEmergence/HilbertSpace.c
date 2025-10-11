// Lean compiler output
// Module: PhysicalLogicFramework.QuantumEmergence.HilbertSpace
// Imports: Init PhysicalLogicFramework.QuantumEmergence.BellInequality_Fixed Mathlib.Analysis.InnerProductSpace.Basic Mathlib.Topology.MetricSpace.Basic Mathlib.Order.CompleteLattice.Basic Mathlib.Data.Real.Basic Mathlib.Data.Complex.Basic
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
LEAN_EXPORT lean_object* l_LFT_QuantumEmergence_projection__complement(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_403_;
LEAN_EXPORT lean_object* l_LFT_QuantumEmergence_projection__complement___redArg(lean_object*, lean_object*);
lean_object* l_NormedAddCommGroup_toNormedAddGroup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_LFT_QuantumEmergence_born__probability___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_QuantumEmergence_born__probability(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_npowRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_QuantumEmergence_projection__complement___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_QuantumEmergence_born__probability___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LFT_QuantumEmergence_projection__complement___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_LFT_QuantumEmergence_projection__complement___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_NormedAddCommGroup_toNormedAddGroup___redArg(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lean_alloc_closure((void*)(l_LFT_QuantumEmergence_projection__complement___redArg___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_LFT_QuantumEmergence_projection__complement(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_LFT_QuantumEmergence_projection__complement___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LFT_QuantumEmergence_born__probability___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LFT_QuantumEmergence_born__probability___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_alloc_closure((void*)(l_LFT_QuantumEmergence_born__probability___redArg___lam__0), 2, 0);
x_7 = lean_apply_1(x_3, x_2);
x_8 = lean_apply_1(x_5, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_403_;
x_11 = l_npowRec___redArg(x_10, x_6, x_9, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_LFT_QuantumEmergence_born__probability(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_LFT_QuantumEmergence_born__probability___redArg(x_2, x_3, x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_PhysicalLogicFramework_QuantumEmergence_BellInequality__Fixed(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_InnerProductSpace_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_MetricSpace_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Order_CompleteLattice_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Complex_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PhysicalLogicFramework_QuantumEmergence_HilbertSpace(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PhysicalLogicFramework_QuantumEmergence_BellInequality__Fixed(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_InnerProductSpace_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_MetricSpace_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Order_CompleteLattice_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Complex_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
