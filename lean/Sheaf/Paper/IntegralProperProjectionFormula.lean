/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.Paper.ModuleObjectProjectionMap
public import Sheaf.Paper.LocalizingClosure
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Sheaf.Paper.ProjectionMateExact
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.SixFunctors.IntegralTensorInverseImage
import Sheaf.Paper.RingedProjectionFirstShift
import Sheaf.Algebra.Homology.KFlat
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Paper.IntegralProperBaseChange
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.Paper.LocalizingClosureExistence
import Sheaf.Paper.ModuleRingedToposDerivedComparison
import Sheaf.Paper.UnboundedLocalizingPullback
import Sheaf.SixFunctors.ProperImageLocalizingProper
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# The integral proper projection formula

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-pf-adic/
sk-thm-sf-pf-adic-projection.md, clauses (1)--(2)
(blueprint: det-thm-sf-pf-adic-projection).

All operations are the ordinary unbounded module-object derived operations.
The localizing closures use ambient small sums and the constant-model
constructibility predicate recorded by sk-def-sfb-constructible.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The bounded integral proper projection formula, tensor closure of the localizing
categories on every standing scheme, and the projection formula on those closures.
Source: blueprint sk-thm-sf-pf-adic-projection, clauses (1)--(2)
(blueprint: det-thm-sf-pf-adic-projection).

Proof:
1. The standing schemes are qcqs by lem-weil-pbc-qcqs-over-affine.
The integral coefficient comparison det-def-localizing-closure-ctf-equals-bc
identifies Dctf with Dbc. det-def-localizing-closure-existence supplies the
ambient sums and the minimal localizing closures.
2. det-thm-sfb-proper-base-change-integral(3) proves the bounded assertion:
reduce the canonical mate modulo uniformizer powers, use the finite proper
projection formula, and use derived completeness and Nakayama on its cone.
3. For a bounded constructible K, tensor with K is exact and preserves ambient
sums. sk-lem-int-tensor shows that it takes bounded constructible generators
to generators. Minimality of the closure extends this to any second input
in the closure, using sk-def-sfb-derived-tensor-hom and the K-flat tensor.
4. Fix that second input. The full subcategory of first inputs whose tensor
lies in the closure is again localizing. It contains the generators by step 3,
and hence the whole closure. This proves tensor closure for every T.
5. det-proper-base-change-unbounded-pullback and det-proper-image-localizing-proper
restrict pullback and proper direct image to these closures and show that they
preserve sums. Together with step 4 these give exact, sum-preserving functors
on both sides of the projection map, separately in each variable.
6. lem-pd-module-ringed-topos-derived-comparison carries the specified adjunction,
its counit and K-flat tensor comparison to their ringed-topos counterparts.
lem-weil-pbc-adjunction-shift-compatibility-unique and
lem-sf-triangulated-right-adjoint give the compatible exact right adjoint.
lem-weil-pbc-ringed-projection-mate-exact and lem-sfb-ringed-projection-first-shift
give naturality and shift compatibility in the second and first variables,
including the connecting square of every distinguished triangle.
7. Fix bounded constructible L. The map is invertible on bounded constructible
K by step 2; sk-lem-sf-determination extends invertibility to every K in its
localizing closure, using the exactness and sum preservation of step 5.
8. Fix any such K. Apply sk-lem-sf-determination again, now in L, using step 7
on the bounded constructible generators of Y. This proves the final assertion.
-/
theorem integralProperProjectionFormula (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] :
    (∀ (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)))
      (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) Y L →
      IsIso (moduleObjectProjectionMap (Profinite.padicIntegersRingObj ℓ E.val) p K L)) ∧
    (∀ (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))]
      (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) T))),
      localizingClosure
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) T) K →
      localizingClosure
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) T) L →
      localizingClosure
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) T)
        (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) T).obj K).obj L)) ∧
    (∀ (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)))
      (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y))),
      localizingClosure
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X) K →
      localizingClosure
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) Y) L →
      IsIso (moduleObjectProjectionMap (Profinite.padicIntegersRingObj ℓ E.val) p K L)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
