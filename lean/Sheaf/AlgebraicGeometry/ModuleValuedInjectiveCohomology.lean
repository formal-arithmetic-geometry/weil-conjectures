/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Comparison of the two encodings of injective module sheaves

Source: Stacks Project, Cohomology on Sites, Tag 03FD.
(blueprint: new-module-valued-injective-cohomology-comparison)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- An injective module-valued sheaf has an injective constant-ring module representative,
whose right-derived abelian evaluation computes the same cohomology.
Source: Stacks Project, Tag 03FD, proof, second paragraph.
(blueprint: new-module-valued-injective-cohomology-comparison)

Proof: Regard a module-valued sheaf as a module over the constant ring sheaf.
On each object, its scalar action is initially an action of the constant ring
presheaf. Sheafifying the action extends it uniquely to the constant ring sheaf:
locally constant scalars act locally, and sheaf uniqueness glues these actions.
Conversely, restriction along the constant presheaf gives the original module
structure. These constructions are inverse on objects and morphisms and preserve
underlying abelian sheaves. The resulting equivalence preserves injective objects.
Use the ring equivalence between the single and double universe lifts of ZMod r
to obtain a representative over the displayed constant ring sheaf. The constant
integer sheaf represents evaluation at the terminal etale object X
by the constant-sheaf adjunction. Applying this representation to an injective
resolution identifies the cohomology of its evaluation complex with the Ext groups
`Sheaf.H`, in every degree, including degree zero. Compose this identification
with the isomorphism of underlying abelian sheaves supplied by the equivalence.
The equivalence also covers r = 0, the zero module, and the empty scheme. -/
theorem moduleValued_injective_cohomology_comparison (X : Scheme.{u}) (r : ℕ)
    (J : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Injective J] :
    ∃ I : SheafOfModules.{u + 1}
      ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} (ULift.{u} (ZMod r))))),
      Injective I ∧ ∀ q : ℕ, Nonempty
        (Sheaf.H
          ((sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
              AddCommGrpCat.{u + 1})).obj J) q ≃+
          (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
            (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
              (Opposite.op (Scheme.Etale.mk (𝟙 X)))).rightDerived q).obj
            ((SheafOfModules.toSheaf _).obj I))) := by sorry

end AlgebraicGeometry.Etale
