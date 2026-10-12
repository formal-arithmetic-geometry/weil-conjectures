/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf

/-! # Cohomology comparison with affine etale neighborhoods

Source: Stacks Project, Tag 0A51, affine case of the proof.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- Cohomology on a closed subscheme of an affine scheme is a filtered colimit of
cohomology on etale neighborhoods, for a torsion sheaf of modules. There is no
injectivity hypothesis and no restriction on the degree.

Source: Stacks Project, Tag 0A51, first paragraph of the proof; Tags 09YQ and 09ZI.
(blueprint: lem-weil-pbc-affine-closed-etale-neighborhood-comparison)

Proof: present X as Spec B and Z as Spec B/K. The pair henselization is the filtered
colimit of etale B-algebras whose quotient by K is B/K. Take a small cofinal directed
presentation of these neighborhoods. The inverse images of J to their spectra give
compatible sheaves and hence a diagram H of their abelian cohomology groups.
Continuity (09YQ) identifies its colimit with the cohomology on the henselization.
Gabber comparison (09ZI) identifies this with the closed fibre cohomology, since
inverse image preserves torsion. Inverse-image composition
(lem-weil-pbc-inverse-image-composition) and compatibility with forgetting
coefficients (lemma-weil-pbc-etale-pullback-forget-modules)
identify the closed fibre sheaf with i inverse image J.
Transport the continuity cocone along this comparison to obtain c and e. The
neighborhood structure maps v are etale by construction. No acyclicity is used:
the same argument applies in degree zero and to noninjective torsion sheaves.
-/
theorem Etale.affine_closed_etale_neighborhood_comparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}} [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionSheaf J] (q : ℕ) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
      (Y : I → Scheme.{u}) (v : ∀ a, Y a ⟶ X),
      (∀ a, Etale (v a)) ∧
      ∃ (H : I ⥤ AddCommGrpCat.{u + 1}) (c : Cocone H),
        Nonempty (IsColimit c) ∧
        Nonempty (AddCommGrpCat.of (Sheaf.H
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((i)^*[ModuleCat.{u + 1} Λ].obj J)) q) ≅ c.pt) ∧
        ∀ a, Nonempty (H.obj a ≅ AddCommGrpCat.of (Sheaf.H
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((v a)^*[ModuleCat.{u + 1} Λ].obj J)) q)) := by
  sorry

end AlgebraicGeometry
