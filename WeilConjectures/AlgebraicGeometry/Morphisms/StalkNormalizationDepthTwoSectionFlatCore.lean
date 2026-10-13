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
public import Mathlib.AlgebraicGeometry.Fiber

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/- Mathematical caveat: the Tag 0EYJ input is the rational point of the cover over the
section, recorded as `hsplit`: the pullback of the cover along `σ` is completely decomposed
over `σ⁻¹(c⁻¹U) = U`. Fibre density of `c⁻¹U` in the fibre over `s` (cf. `hclosed` in
`flat_of_smooth_local_depth_two_finite_extension`) cannot serve instead: as `s ∉ U`, the
open `c⁻¹U` misses that fibre, which contains `σ s`, so such a hypothesis is contradictory.
Without `hsplit` the statement is false. Take c and sigma
both the identity of Spec A, where A = Q[x^2,xy,y^2], and U the complement of the
vertex m = (x^2,xy,y^2). The restriction of Spec Q[x,y] to U is finite etale.
A_m has depth two, but its relative normalization B = Q[x,y] localized over A_m
is not flat: its generic rank is two and B/mB has basis 1,x,y, hence dimension
three. Thus no flat neighbourhood of the section closed point exists. There the cover is
connected of degree two over `σ⁻¹U = U`, so `hsplit` fails. -/

/-- The formal-neighbourhood flatness calculation for a finite etale model over a
smooth family.  This is the local algebraic core of the depth-two section argument.

Source: Stacks Project, Tag 0EYJ, formal-neighbourhood calculation.
(blueprint: lem-sbc-stalk-normalization-depth-two-section-flat-core)

The proof uses the completion of a smooth local chart at the section, the
finite-etale algebra on the punctured completion (split by `hsplit` and Tag 0EY6),
and faithfully-flat descent.
The resulting flatness locus is open; finiteness makes the image of its complement
closed, producing the displayed neighbourhood. -/
theorem stalk_normalization_depth_two_section_flat_core {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) (hs : s ∉ U)
    (hsplit : ∃ (ι : Type u) (_ : Finite ι)
      (e : pullback PA.obj.hom (σ ∣_ (c ⁻¹ᵁ U)) ≅
        ∐ fun _ : ι ↦ (σ ⁻¹ᵁ c ⁻¹ᵁ U).toScheme),
      e.hom ≫ Sigma.desc (fun _ ↦ 𝟙 _) = pullback.snd _ _)
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
