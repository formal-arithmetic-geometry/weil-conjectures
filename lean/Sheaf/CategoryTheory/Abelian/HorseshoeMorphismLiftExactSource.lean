/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLift

/-!
# Horseshoe morphism lifts from exact augmented source complexes

Source: the classical horseshoe comparison argument, using Stacks Project, Tags 0136 and
013R; the Cartan--Eilenberg construction of Tag 015I motivates its application
(blueprint: lem-weil-pbc-horseshoe-morphism-lift-exact-source).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveResolution

/-- Prescribed endpoint maps from exact augmented complexes into a target horseshoe
extend to a compatible middle map. The source terms need not be injective.
Augmentations are chain maps from `single₀`; their quasi-isomorphism conditions mean
exactness of the augmented sequences, including monicity of the degree-zero augmentation.
Natural-number indexing represents the displayed nonnegative-degree complexes.
The target horseshoe data use the same declarations and equations as
`exists_horseshoe_morphism_lift`.

Source: the classical horseshoe comparison calculation, using Stacks Project, Tags 0136
and 013R, in the setting of the Cartan--Eilenberg construction of Tag 015I
(blueprint: lem-weil-pbc-horseshoe-morphism-lift-exact-source).

Proof:
1. By lem-weil-pbc-ses-injective-kernel-splits, split the target row in each degree,
   choosing a section sigma' of beta'. Extend phiA^n across the source monomorphism
   i^n into JA^n by injectivity (def-sp-injective-resolutions), obtaining t^n.
   Set chi^n = alpha'^n t^n + sigma'^n phiC^n p^n in ordinary composition order.
   Then chi i = alpha' phiA and beta' chi = phiC p.
2. By row exactness in the abelian category (def-sp-abelian), the differential defect
   D = d' chi - chi d factors uniquely as D^n = alpha'^{n+1} E^n p^n.
   The identity d' D = -D d gives d' E + E d = 0. Likewise the augmentation defect
   w = chi^0 sB - sB' b factors as alpha'^0 e g, with E^0 sC = d' e.
3. Adjoin S.X₃ in degree -1 to XC via sC. This complex is acyclic by source augmented
   exactness. The maps u^{-1} = e and u^n = (-1)^n E^n form a chain map into the
   bounded-below injective complex with degree m term JA^{m+1} and differential d'.
   Apply lem-weil-pbc-acyclic-map-to-injective-nullhomotopy (Tag 013R). Its homotopy
   h has h^{-1} = 0; k^n = (-1)^n h^n satisfies e = k^0 sC and
   E^n = d' k^n - k^{n+1} d.
4. Set phiB^n = chi^n - alpha'^n k^n p^n. These identities kill the differential
   and augmentation defects. The zero composites beta' alpha' and p i preserve
   both outer squares. Thus phiB is the required augmented middle chain map. -/
theorem exists_horseshoe_morphism_lift_exact_source
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T : ShortComplex C) (hS : S.ShortExact) (hT : T.ShortExact) (F : S ⟶ T)
    (XA XB XC : CochainComplex C ℕ)
    (sA : (CochainComplex.single₀ C).obj S.X₁ ⟶ XA)
    (sB : (CochainComplex.single₀ C).obj S.X₂ ⟶ XB)
    (sC : (CochainComplex.single₀ C).obj S.X₃ ⟶ XC)
    [QuasiIso sA] [QuasiIso sB] [QuasiIso sC]
    (i : XA ⟶ XB) (p : XB ⟶ XC) (hip : i ≫ p = 0)
    (hi : sA ≫ i = (CochainComplex.single₀ C).map S.f ≫ sB)
    (hp : sB ≫ p = (CochainComplex.single₀ C).map S.g ≫ sC)
    (hexact : ∀ n : ℕ,
      ((ShortComplex.mk i p hip).map
        (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (JA : InjectiveResolution T.X₁) (JB : InjectiveResolution T.X₂)
    (JC : InjectiveResolution T.X₃)
    (α' : JA.cocomplex ⟶ JB.cocomplex) (β' : JB.cocomplex ⟶ JC.cocomplex)
    (hαβ' : α' ≫ β' = 0)
    (hα' : JA.ι ≫ α' = (CochainComplex.single₀ C).map T.f ≫ JB.ι)
    (hβ' : JB.ι ≫ β' = (CochainComplex.single₀ C).map T.g ≫ JC.ι)
    (hexact' : ∀ n : ℕ,
      ((ShortComplex.mk α' β' hαβ').map
        (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (φA : XA ⟶ JA.cocomplex) (φC : XC ⟶ JC.cocomplex)
    (hφA : sA ≫ φA = (CochainComplex.single₀ C).map F.τ₁ ≫ JA.ι)
    (hφC : sC ≫ φC = (CochainComplex.single₀ C).map F.τ₃ ≫ JC.ι) :
    ∃ φB : XB ⟶ JB.cocomplex,
      sB ≫ φB = (CochainComplex.single₀ C).map F.τ₂ ≫ JB.ι ∧
      i ≫ φB = φA ≫ α' ∧ φB ≫ β' = p ≫ φC := by
  sorry

end CategoryTheory.InjectiveResolution
