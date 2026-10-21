/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.CategoryTheory.CondensedInternalBarResolution
public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat

/-! # Injectivity of internal homogeneous functions

Source: the internal homogeneous-function helper for paragraph (3) of the main-20261015
six-functors direct-image proof; Stacks Tags 015Z, 03EV and 03EO
(blueprint: lem-sfb-internal-homogeneous-functions-injective).

The free module and internal Hom are the recorded constructions. A normalized model
retains the diagonal action formula on every profinite slice, without choosing data
from a mere existence statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace Profinite.CondensedAction

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
variable (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The existing internal sheaf Hom from the actual free module on G^(n+1), read through
 the section-module equivalence. Thus a section is a linear map on the whole slice.
Source: Stacks 03EO and the homogeneous-function helper
(blueprint: lem-sfb-internal-homogeneous-functions-injective). -/
abbrev homogeneousHom (J : ActionModule R G) (n : ℕ) :=
  SheafOfModules.homObj.{u + 1, u, u + 1, u + 1}
    ((InternalAbelianSheafModule.sectionModuleFunctor
      (coherentTopology Profinite.{u}) R.X).obj
        (CondensedBar.freeParameter ⟨R.X⟩ (CondensedBar.power G (n + 1))))
    ((InternalAbelianSheafModule.sectionModuleFunctor
      (coherentTopology Profinite.{u}) R.X).obj J.module)

/-- Evaluate an actual internal-Hom section at a generalized tuple over T → S, using
its slice component and the canonical generator of the free internal module.
Source: Stacks 03EO, slice interpretation of internal Hom
(blueprint: lem-sfb-internal-homogeneous-functions-injective). -/
def homogeneousEvaluate (J : ActionModule R G) (n : ℕ) (S : Profinite.{u})
    (c : (homogeneousHom R G J n).val.obj (op S))
    (T : Profinite.{u}) (f : T ⟶ S) (x : Fin (n + 1) → C(T, G)) :
    sectionModule R J.module T :=
  (c.app (op (Over.mk f))).hom (InternalBar.generator R G (n + 1) T x)

/-- A normalized model of H_n(J). Its underlying object is the specified internal Hom,
up to the displayed identification, and its action is fixed on every generalized tuple.
This records the meaning of "equip with the homogeneous action", without assuming
existence or selecting an unspecified object.
Source: the homogeneous-function helper, displayed action formula
(blueprint: lem-sfb-internal-homogeneous-functions-injective). -/
structure HomogeneousFunctions (J : ActionModule R G) (n : ℕ) where
  /-- The internal equivariant module. -/
  object : ActionModule R G
  /-- The underlying module is Hom_A(A[G^(n+1)], UJ). -/
  internalHom :
    (InternalAbelianSheafModule.sectionModuleFunctor
      (coherentTopology Profinite.{u}) R.X).obj object.module ≅ homogeneousHom R G J n
  /-- The diagonal action formula holds on all profinite base changes T → S. -/
  action : ∀ (S : Profinite.{u}) (g : C(S, G)) (c : sectionModule R object.module S)
    (T : Profinite.{u}) (f : T ⟶ S) (x : Fin (n + 1) → C(T, G)),
    homogeneousEvaluate R G J n S
      ((internalHom.hom.val.app (op S)).hom (object.act S g c)) T f x =
    J.act T (g.comp f.hom.hom)
      (homogeneousEvaluate R G J n S ((internalHom.hom.val.app (op S)).hom c) T f
        (fun i ↦ (g.comp f.hom.hom)⁻¹ * x i))

/-- For every nonnegative degree, the specified homogeneous internal function module
exists and is injective in the actual category of internal equivariant modules whenever
UJ is injective as an internal module. No projectivity, discreteness or finiteness is used.

Source: the homogeneous-function helper for paragraph (3) of the main-20261015
six-functors direct-image proof; Stacks Tags 015Z, 03EV and 03EO
(blueprint: lem-sfb-internal-homogeneous-functions-injective).

Proof:
1. Use the section-module equivalence to work with the same internal modules as sheaves
of section modules. Tensor and internal Hom are identified by their universal properties;
Hom sections are maps on the entire slice, not just functions on ordinary points.
2. Put P = A[G^n], also for n = 0. The free-module adjunction identifies it with the
sheafification of the representable-indexed direct sum of copies of A. Stacks 03EV,
lem-pc-sites-modules-j-shriek-flat, makes P flat, so P tensor - preserves monomorphisms.
3. If i : N → M is an equivariant monomorphism, its sectionwise kernel is an invariant
subsheaf. Its inclusion is zero by monicity, so the underlying map Ui is monic.
4. Given h : N → H_n(J), evaluate at (1,t_1,...,t_n) on every slice. Free linear
extension and the tensor-Hom adjunction give alpha : P tensor UN → UJ.
5. Injectivity of UJ extends alpha along P tensor Ui to beta : P tensor UM → UJ.
6. Define b(m)(g_0,...,g_n) to be g_0 acting on
beta([g_0^(-1)g_1,...,g_0^(-1)g_n] tensor (g_0^(-1) acting on m)). All operations commute
with restriction and are linear in m; free extension and tensor-Hom transposition make
this an internal linear map. The same slice construction defines the displayed
homogeneous action itself: restrict g to the slice, translate the tuple by its inverse,
then apply the coefficient action. The action and naturality laws follow from those of J.
7. The identities k(k^(-1)g_0) = g_0 and (k^(-1)g_0)^(-1) = g_0^(-1)k prove
b(km) = k b(m) on every slice, so b is equivariant.
8. The extension identity for beta and equivariance of h give b(i(x)) = h(x) on all
local free generators. Hence every map extends along every equivariant monomorphism,
which is exactly CategoryTheory.Injective. This includes the empty test, zero modules,
the zero ring, trivial G and n = 0; no sectionwise injectivity of J(S) is claimed.
-/
theorem homogeneous_functions_injective (J : ActionModule R G) [Injective J.module]
    (n : ℕ) : ∃ H : HomogeneousFunctions R G J n, Injective H.object := by
  sorry

end Profinite.CondensedAction
