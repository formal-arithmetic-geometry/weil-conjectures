/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.Paper.CoefficientFiniteDescentHom
import Sheaf.Paper.CoefficientFiniteDescentLisse
import Sheaf.Paper.CoefficientHeartGeneration
import Sheaf.Paper.CoefficientHeartTriangulated
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Sheaf.SixFunctors.ScalarSixPullback

/-!
# Finite coefficient descent of bounded constructible objects

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-objects.md and its proof
(blueprint: det-lem-coefficient-finite-descent-objects).

The constructibility convention is the finite constant local model convention of
`det-def-sfb-constructible-tor-amplitude`. The scalar extensions are the specified left
derived functors on the unbounded categories of internal modules over pulled-back
condensed rings. Isomorphisms are in these ambient derived categories.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Every bounded constructible algebraic-closure coefficient complex has a finite-field
model, and every such model remains a model after any finite enlargement of the field.
Source: blueprint main-20261015, sk-thm-sfb-qlbar-two-colimit,
sk-lem-coefficient-finite-descent-objects.md, both assertions
(blueprint: det-lem-coefficient-finite-descent-objects).

Proof plan, following the node's five steps:
1. A standing scheme is Noetherian: Spec k is Noetherian and finite type preserves this
(lem-weil-pbc-finite-type-over-noetherian). Its locally closed strata are Noetherian and
qcqs, so the hypotheses of lisse descent and finite constructible generation hold.
2. Models persist by lem-sfb-extend-subfield-constructible and the transitivity comparison
of def-sfb-derived-extend-comp-iso. Scalar extensions are exact by lem-sfb-subfield-flat,
lem-sfb-qlbar-flat and the right exact tensor adjunction sk-def-sfb-change-of-scalars.
The exact-functor identification of sk-def-sfb-derived-categories and
lem-weil-pbc-exact-functor-derived-factorization makes these specified derived functors
termwise, triangulated and compatible with shifts. Thus shifts of models are models by
det-cor-coefficient-heart-ii-triangulated. Finite composita put any two models over a common
field (def-weil-finite-subextension-directed-set). This proves the second assertion.
3. For a triangle A → K → B → A[1], put models of A and B over a common E. Transport the
connecting map to their extensions. By det-lem-coefficient-finite-descent-hom (3), with
r = 1, it is represented over some finite F containing E. Complete that representative to
a triangle B_F → A_F[1] → C_F → B_F[1] using TR1 of def-weil-triangulated-category.
Two inverse rotations give A_F → C_F[-1] → B_F → A_F[1], with the original connecting map
and no sign change. Set K_F = C_F[-1]; triangulated closure puts it in Dbc(X,F). After
scalar extension, rotate to compare connecting maps. TR3 and lem-sf-triangle-morphism-iso
give an isomorphism to the given triangle. Hence K descends. Rotation also gives descent
of cones between descended objects.
4. For a generator a_!L[n] of det-cor-coefficient-heart-ii-generation, its locally closed
stratum is qcqs by step 1. Apply det-lem-coefficient-finite-descent-lisse (1) there to get
L_E. The converse generation assertion puts a_!L_E[n] in Dbc(X,E).
The identification in def-sfb-derived-extend-to-qlbar is the same condensed inclusion on
both schemes. Thus det-prop-scalar-six-pullback (2), including the closed immersion factor,
and shift compatibility identify its extension with a_!L[n].
5. Apply the finite generating sequence of det-cor-coefficient-heart-ii-generation to K.
Induct through it using step 4 for generators, step 3 for cones, step 2 for common fields
and shifts, and composition for isomorphisms. Zero has its zero model over the base field,
also a rank-zero generator. Finitely many choices and composita yield one finite field E;
no infinite enlargement occurs. -/
theorem coefficient_finite_descent_objects
    (k : Type u) [Field k] (p ℓ : ℕ) [CharP k p] [Fact ℓ.Prime]
    (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X,
      ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
        (K_E : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E) X),
        Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K_E.obj ≅ K.obj)) ∧
    (∀ (K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X)
      (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (K_E : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E) X),
      Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K_E.obj ≅ K.obj) →
      ∀ (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F),
        constantModelBoundedConstructible (Profinite.continuousMapRingObj F) X
          ((derivedExtendScalarsSubfield X ℓ h).obj K_E.obj) ∧
        Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ F).obj
          ((derivedExtendScalarsSubfield X ℓ h).obj K_E.obj) ≅ K.obj)) :=
  sorry

end AlgebraicGeometry.ProEtale
