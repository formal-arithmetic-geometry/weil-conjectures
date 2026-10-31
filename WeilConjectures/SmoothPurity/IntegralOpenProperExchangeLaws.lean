/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOpenProperExchange
public import WeilConjectures.AlgebraicGeometry.CondensedOpenProperPasting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp

/-! # Invertibility and pasting of integral open-proper exchange

Source: Stacks Project, more-etale.tex, Tag 0F7H and
`lemma-shriek-proper-and-open-compose`, `lemma-shriek-proper-and-open-compose-horizontal`;
Bhatt--Scholze, Lemmas 6.1.13 and 6.5.9(2); derived Nakayama, Stacks Tag 0G1U
(blueprint: lem-pur-integral-open-proper-exchange-laws).

The five statements use the recorded integral mate, on the ordinary unbounded
internal-module derived categories. The coherence equations are componentwise
natural-transformation equalities before any further proper pushforward.

## Main statements

- `integralOpenProperExchange_isIso`: invertibility on constructible finite-Tor inputs.
- `integralOpenProperExchange_horizontal`: pasting along open immersions.
- `integralOpenProperExchange_vertical`: pasting along proper maps.
- `integralOpenProperExchange_proper_id`: identity proper maps.
- `integralOpenProperExchange_open_id`: identity open immersions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CondensedOpenProper

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hple : p ≠ ell)
  (k : Type u) [Field k] (hk : ringChar k = p)
  (E : PadicAlgCl.FiniteIntermediateField ell)
  (hΛ : IsAdmissibleCoefficient (Profinite.padicIntegersRingObj ell E.1))

/-- Invertibility on bounded constructible inputs of finite Tor amplitude.
Source: Stacks Tag 0F7H, Bhatt--Scholze 6.1.13 and 6.5.9(2), Stacks Tag 0G1U
(blueprint: lem-pur-integral-open-proper-exchange-laws).

Proof:
1. Integral constructibility gives derived completeness of L
   (lem-sfb-internal-integral-criterion-forward). Internal integral direct images preserve
   it (lem-sfb-internal-integral-direct-image-limits), and quasi-compact open extensions
   preserve limits and commute with uniformizer reduction
   (det-cor-int-compactness-ii-extension-zero, Bhatt--Scholze 6.1.13).
   Hence both endpoints and the cone of the exchange map are derived complete.
2. The endpoint and mate comparison
   (lem-pur-integral-open-proper-mate-reduction) identifies each uniformizer reduction
   with the finite constant-coefficient mate, compatibly with the specified adjunctions.
3. At the first quotient, integral constructibility gives bounded constructibility and
   finite Tor amplitude. The finite module-object/ordinary equivalence and the finite
   constructibility comparison (lem-sf-module-object-ordinary-coefficient-equivalence,
   lem-pe-finite-coefficient-model-comparison) supply the ordinary predicates.
   ReductionOpenEtaleOrigin (lem-fix-reduction-open-etale-origin) gives an etale origin.
   Torsion proper/open interchange (lem-amb-unbounded-proper-open-interchange and
   lem-cbc-proper-open-interchange-coherence) and its site-mate comparison
   (lem-sp-proper-open-coefficient-mate) make this reduced mate invertible.
4. Derived Nakayama (sk-lem-pe-derived-nakayama, Tag 0G1U) kills the complete cone,
   proving invertibility of the integral map.
5. For the coherence clauses, the normalized open/proper pasting theorem
   (lem-zl-condensed-open-proper-pasting) and mate pasting
   (lem-weil-pbc-mate-pasting) identify the mate of the outer square with the pasted
   mates. The inserted comparisons are exactly the canonical open and direct-image
   compositors. Identity squares use their canonical unit comparisons. These equations
   already hold before any outer proper image.
-/
theorem integralOpenProperExchange_isIso
    {U V X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (v : V ⟶ X) (j : U ⟶ Y) (f : X ⟶ Y) (fV : V ⟶ U)
    [IsOpenImmersion v.left] [QuasiCompact v.left]
    [IsOpenImmersion j.left] [QuasiCompact j.left] [IsProper f.left]
    (sq : IsPullback v.left fV.left f.left j.left)
    (L : ConstantModelConstructibleFiniteTor (Profinite.padicIntegersRingObj ell E.1) V.left) :
    IsIso (integralOpenProperExchange p ell hple k hk E hΛ v j f fV sq L.obj) := by
  sorry

/-- Horizontal pasting along the two successive open immersions.
Source: Stacks, more-etale.tex, `lemma-shriek-proper-and-open-compose-horizontal`.
(blueprint: lem-pur-integral-open-proper-exchange-laws).

Proof (node step 5):
1. Each exchange map is the `u_! ⊣ u^*` adjunct of `RpV_*(η_v) ≫ ρ⁻¹`, where `ρ` is the
   canonical open restriction of derived direct image; this is the `Γ_Q` of the normalized
   open/proper pasting statement (lem-zl-condensed-open-proper-pasting, clause (b)).
2. The restriction maps `ρ` of the two squares paste to the `ρ` of the outer square, with
   the restriction compositor `pComp` inserted; `jComp` is by definition the conjugate of
   `pComp` under the open adjunctions, and `jComp` for the top row is likewise.
3. Mate pasting (lem-weil-pbc-mate-pasting; Mathlib `mateEquiv_hcomp`) turns the pasted
   restriction square into the displayed composite: the intermediate open unit and counit
   cancel by the triangle identities.
4. The equality holds in the ambient derived category, before any outer proper image.
-/
theorem integralOpenProperExchange_horizontal
    {V W X U Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (v₁ : V ⟶ W) (v₂ : W ⟶ X) (j₁ : U ⟶ Z) (j₂ : Z ⟶ Y)
    (f₀ : V ⟶ U) (f₁ : W ⟶ Z) (f₂ : X ⟶ Y)
    [IsOpenImmersion v₁.left] [QuasiCompact v₁.left]
    [IsOpenImmersion v₂.left] [QuasiCompact v₂.left]
    [IsOpenImmersion j₁.left] [QuasiCompact j₁.left]
    [IsOpenImmersion j₂.left] [QuasiCompact j₂.left]
    [IsProper f₁.left] [IsProper f₂.left]
    (sq₁ : IsPullback v₁.left f₀.left f₁.left j₁.left)
    (sq₂ : IsPullback v₂.left f₁.left f₂.left j₂.left)
    (L : D (Profinite.padicIntegersRingObj ell E.1) V.left) :
    @integralOpenProperExchange p ell _ _ hple k _ hk E hΛ U V X Y
        _ _ _ _ _ _ _ _ _ _ _ _
        (v₁ ≫ v₂) (j₁ ≫ j₂) f₂ f₀
        (inferInstanceAs (IsOpenImmersion (v₁.left ≫ v₂.left)))
        (inferInstanceAs (QuasiCompact (v₁.left ≫ v₂.left)))
        (inferInstanceAs (IsOpenImmersion (j₁.left ≫ j₂.left)))
        (inferInstanceAs (QuasiCompact (j₁.left ≫ j₂.left)))
        inferInstance (sq₁.paste_horiz sq₂) L =
      (jComp (Profinite.padicIntegersRingObj ell E.1) j₁.left j₂.left).inv.app
          ((R (Profinite.padicIntegersRingObj ell E.1) f₀.left).obj L) ≫
        (J (Profinite.padicIntegersRingObj ell E.1) j₂.left).map
          (integralOpenProperExchange p ell hple k hk E hΛ v₁ j₁ f₁ f₀ sq₁ L) ≫
        integralOpenProperExchange p ell hple k hk E hΛ v₂ j₂ f₂ f₁ sq₂
          ((J (Profinite.padicIntegersRingObj ell E.1) v₁.left).obj L) ≫
        (R (Profinite.padicIntegersRingObj ell E.1) f₂.left).map
          ((jComp (Profinite.padicIntegersRingObj ell E.1) v₁.left v₂.left).hom.app L) := by
  sorry

/-- Vertical pasting along the two successive proper maps.
Source: Stacks, more-etale.tex, `lemma-shriek-proper-and-open-compose`.
(blueprint: lem-pur-integral-open-proper-exchange-laws).

Proof (node step 5):
1. Each exchange map is the `u_! ⊣ u^*` adjunct of `RpV_*(η_v) ≫ ρ⁻¹`, the `Γ_Q` of
   lem-zl-condensed-open-proper-pasting, clause (b).
2. The open restrictions `ρ` of the two squares paste vertically to the outer `ρ` once the
   direct-image compositor is inserted; the compositor `rightDerivedLowerStarComp` of
   lem-weil-derived-direct-image-composition is the conjugate of the pullback compositor.
3. Mate pasting (lem-weil-pbc-mate-pasting; Mathlib `mateEquiv_vcomp`) and naturality of
   the compositor give the displayed composite; the middle open unit of `j` cancels.
4. The equality holds in the ambient derived category, before any outer proper image.
-/
theorem integralOpenProperExchange_vertical
    {V X U Y W Z : Over (Spec (.of k))}
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (v : V ⟶ X) (j : U ⟶ Y) (i : W ⟶ Z)
    (f : X ⟶ Y) (fV : V ⟶ U) (g : Y ⟶ Z) (gU : U ⟶ W)
    [IsOpenImmersion v.left] [QuasiCompact v.left]
    [IsOpenImmersion j.left] [QuasiCompact j.left]
    [IsOpenImmersion i.left] [QuasiCompact i.left]
    [IsProper f.left] [IsProper g.left]
    (sq₁ : IsPullback v.left fV.left f.left j.left)
    (sq₂ : IsPullback j.left gU.left g.left i.left)
    (L : D (Profinite.padicIntegersRingObj ell E.1) V.left) :
    @integralOpenProperExchange p ell _ _ hple k _ hk E hΛ W V X Z
        _ _ _ _ _ _ _ _ _ _ _ _ v i (f ≫ g) (fV ≫ gU)
        inferInstance inferInstance inferInstance inferInstance
        (inferInstanceAs (IsProper (f.left ≫ g.left))) (sq₁.paste_vert sq₂) L =
      (J (Profinite.padicIntegersRingObj ell E.1) i.left).map
          ((rightDerivedLowerStarComp
            (Profinite.padicIntegersRingObj ell E.1) fV.left gU.left).inv.app L) ≫
        integralOpenProperExchange p ell hple k hk E hΛ j i g gU sq₂
          ((R (Profinite.padicIntegersRingObj ell E.1) fV.left).obj L) ≫
        (R (Profinite.padicIntegersRingObj ell E.1) g.left).map
          (integralOpenProperExchange p ell hple k hk E hΛ v j f fV sq₁ L) ≫
        (rightDerivedLowerStarComp (Profinite.padicIntegersRingObj ell E.1) f.left g.left).hom.app
          ((J (Profinite.padicIntegersRingObj ell E.1) v.left).obj L) := by
  sorry

/-- Identity proper maps give the identity exchange under the direct-image unitors.
Source: Stacks, more-etale.tex, open/proper exchange and its identity normalization.
(blueprint: lem-pur-integral-open-proper-exchange-laws).

Proof (node step 5, identity square):
1. For `f = 𝟙`, the open restriction `ρ` of the identity square is the identity after the
   identity comparisons `rId` (conjugate of `pId`), by its normalization.
2. The adjunct of `R(𝟙)(η_v L) ≫ ρ⁻¹` is then `v_!(rId) ≫ rId⁻¹`, since the adjunct of
   `η_v` is the identity (triangle identity of `v_! ⊣ v^*`), and naturality of `rId`.
3. The equality holds before any outer proper image.
-/
theorem integralOpenProperExchange_proper_id
    {V X : Over (Spec (.of k))}
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (v : V ⟶ X) [IsOpenImmersion v.left] [QuasiCompact v.left]
    (sq : IsPullback v.left (𝟙 V.left) (𝟙 X.left) v.left)
    (L : D (Profinite.padicIntegersRingObj ell E.1) V.left) :
    integralOpenProperExchange p ell hple k hk E hΛ v v (𝟙 X) (𝟙 V) sq L =
      (J (Profinite.padicIntegersRingObj ell E.1) v.left).map
          ((rId (Profinite.padicIntegersRingObj ell E.1) V.left).hom.app L) ≫
        (rId (Profinite.padicIntegersRingObj ell E.1) X.left).inv.app
          ((J (Profinite.padicIntegersRingObj ell E.1) v.left).obj L) := by
  sorry

/-- Identity open immersions give the identity exchange under the open unitors.
Source: Stacks, more-etale.tex, open/proper exchange and its identity normalization.
(blueprint: lem-pur-integral-open-proper-exchange-laws).

Proof (node step 5, identity square):
1. For `u = v = 𝟙`, `jId` is the left-adjoint uniqueness iso for `𝟙_! ⊣ 𝟙^*` against the
   identity adjunction, normalized by `pId`; `ρ` of the square is the identity modulo `pId`.
2. Transposing `Rf_*(η_𝟙 L) ≫ ρ⁻¹` along `𝟙_! ⊣ 𝟙^*` gives `jId ≫ Rf_*(jId⁻¹)` by the
   definition of `leftAdjointUniq` and naturality of `jId`.
3. The equality holds before any outer proper image.
-/
theorem integralOpenProperExchange_open_id
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsProper f.left]
    (sq : IsPullback (𝟙 X.left) f.left f.left (𝟙 Y.left))
    (L : D (Profinite.padicIntegersRingObj ell E.1) X.left) :
    integralOpenProperExchange p ell hple k hk E hΛ (𝟙 X) (𝟙 Y) f f sq L =
      (jId (Profinite.padicIntegersRingObj ell E.1) Y.left).hom.app
          ((R (Profinite.padicIntegersRingObj ell E.1) f.left).obj L) ≫
        (R (Profinite.padicIntegersRingObj ell E.1) f.left).map
          ((jId (Profinite.padicIntegersRingObj ell E.1) X.left).inv.app L) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
