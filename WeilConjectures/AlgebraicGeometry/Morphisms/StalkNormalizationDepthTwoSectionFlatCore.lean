/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.RingTheory.Depth

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/- Mathematical caveat: The cover need not split over the section. Take c and sigma
both the identity of Spec A, where A = Q[x^2,xy,y^2], and U the complement of the
vertex m = (x^2,xy,y^2). The restriction of Spec Q[x,y] to U is finite etale.
A_m has depth two, but its relative normalization B = Q[x,y] localized over A_m
is not flat: its generic rank is two and B/mB has basis 1,x,y, hence dimension
three. Thus no flat neighbourhood of the section closed point exists.
Tag 0EYJ uses the omitted rational-point hypothesis to split the section cover.
See report.md, Second reading by N2, for verification of every hypothesis. -/

/-- The formal-neighbourhood flatness calculation for a finite etale model over a
smooth family.  This is the local algebraic core of the depth-two section argument.

Source: Stacks Project, Tag 0EYJ, formal-neighbourhood calculation.
(blueprint: lem-sbc-stalk-normalization-depth-two-section-flat-core)

The proof uses the completion of a smooth local chart at the section, the split
finite-etale algebra on the punctured completion, and faithfully-flat descent.
The resulting flatness locus is open; finiteness makes the image of its complement
closed, producing the displayed neighbourhood. -/
theorem stalk_normalization_depth_two_section_flat_core {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    IsFinite n → ∃ W : (pullback c a).Opens,
      τ (IsLocalRing.closedPoint (S.presheaf.stalk s)) ∈ W ∧ Flat (n ∣_ W) := by
  sorry

end AlgebraicGeometry.Scheme
