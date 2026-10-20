/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.CategoryTheory.RingedCompletionUnit
public import Sheaf.Paper.ExtendedLocalizationCech
public import Mathlib.Algebra.Homology.Additive
import Sheaf.Paper.RestrictedCoefficientHomComplex
import Sheaf.Algebra.Homology.BilinearHomComplex
import WeilConjectures.Algebra.Homology.HomComplexProjections
import Sheaf.Paper.RestrictedCoefficientHom

/-! # Augmentation evaluation in coefficient Hom complexes

Source: Stacks Project, Algebraization, Tag 099I, final displayed composite.
(blueprint: lem-weil-pbc-coefficient-hom-augmentation).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option maxHeartbeats 800000 in
-- The sectionwise formula compares the two scalar actions and the product projections.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Augmentation evaluation lifts to a natural B-linear map of coefficient Hom complexes.
Source: Stacks Project, Algebraization, Tag 099I, final displayed composite.
(blueprint: lem-weil-pbc-coefficient-hom-augmentation).

Proof: construct the coefficient internal Hom H with its precomposition B-action and
its explicit augmentation-evaluation maps. Apply the product Hom-complex construction
to H, and normalize its restriction comparison by its product projections. For m in
M^n, define the projection at source degree p to be zero if p is not zero. At p=0,
use the B-linear evaluation map associated to delta^0, followed by eta^n. The product
universal property supplies the degree-n map. The Hom differential on a projection is
d_I h - (-1)^n h d_L. The p=0 equation is eta's chain-map equation; the p=-1 term
vanishes by delta d_L=0; all other projections are zero. Thus these degree maps form
a chain map. Eta's naturality gives naturality in M. Restrict and precompose with u.
The augmentation equation identifies the resulting cochain with
x -> epsilon(x) eta(m), which is evaluation-at-one inverse followed by precomposition
with epsilon. Equality of all product projections proves the stated chain identity.
No quasi-isomorphism or K-injectivity hypothesis is needed.
-/
theorem exists_coefficientHom_augmentation
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (K : ringedSiteComplex R) (ε : K ⟶ ringedSiteRingComplex R)
    (L : ringedSiteComplex B) (δ : L ⟶ ringedSiteRingComplex B)
    (T : ringedSiteComplex R ⥤ ringedSiteComplex R)
    (η : 𝟭 (ringedSiteComplex R) ⟶ T) :
    let r := SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
    let rc := r.mapHomologicalComplex (.up ℤ)
    let σ : ringedSiteRingComplex R ⟶ rc.obj (ringedSiteRingComplex B) :=
      (HomologicalComplex.single _ (.up ℤ) 0).map
          (SheafOfModules.LocalizationCech.unitMap φ) ≫
        (HomologicalComplex.singleMapHomologicalComplex r (.up ℤ) 0).inv.app
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    ∀ (u : K ⟶ rc.obj L), u ≫ rc.map δ = ε ≫ σ →
      ∃ G : ringedSiteComplex R ⥤ ringedSiteComplex B,
        ∃ c : G ⋙ rc ≅ (homComplexFunctor (R := R)).obj (op (rc.obj L)),
          ∃ β : 𝟭 (ringedSiteComplex B) ⟶ rc ⋙ T ⋙ G,
            ∀ M : ringedSiteComplex B,
              rc.map (β.app M) ≫ c.hom.app (T.obj (rc.obj M)) ≫
                  ((homComplexFunctor (R := R)).map u.op).app (T.obj (rc.obj M)) =
                (by
                  change rc.obj M ⟶
                    ((homComplexFunctor (R := R)).obj (op K)).obj (T.obj (rc.obj M))
                  exact η.app (rc.obj M) ≫
                    (ringedHomUnitEvaluationIso R (T.obj (rc.obj M))).inv ≫
                    ((homComplexFunctor (R := R)).map ε.op).app (T.obj (rc.obj M))) := by
  sorry

end CategoryTheory
