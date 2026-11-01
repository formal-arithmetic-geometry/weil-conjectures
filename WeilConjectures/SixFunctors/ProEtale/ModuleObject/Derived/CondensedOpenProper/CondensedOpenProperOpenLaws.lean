/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperOpenCoherence

/-! # Open exchange laws for condensed modules

Part (a) of the open/proper pasting lemma, together with the normalization of the ambient
exchange: the invertible open units, the normalized open exchange `B` on every Cartesian
open square, its identity and pasting laws, and the open compositor laws.
Source: latest blueprint sk-thm-sf-comp-composition.proof.md, Canonicity and associativity
and Base change paragraphs (blueprint: new-zl-condensed-open-proper-open-laws).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
/-- The open half of `Pasting`: units, normalized open exchange and their laws (part (a)),
and the ambient exchange normalization.
Source: latest blueprint sk-thm-sf-comp-composition.proof.md
(blueprint: new-zl-condensed-open-proper-open-laws). -/
structure OpenLaws where
  /-- The specified invertible open units. -/
  units : OpenUnits Λ
  /-- Normalized open exchange on every Cartesian open square, without quasi-compactness. -/
  B : ∀ {U' U W' W : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ W'}
    {j : U ⟶ W} {b : W' ⟶ W} [IsOpenImmersion j] [IsOpenImmersion j'],
    IsPullback a j' j b → (J Λ j ⋙ P Λ b ≅ P Λ a ⋙ J Λ j')
  /-- B is the inverse of exactly the specified unit--square--counit transformation. -/
  B_normalized : ∀ {U' U W' W : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ W'}
    {j : U ⟶ W} {b : W' ⟶ W} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback a j' j b), (B sq).inv = openMap Λ sq.toCommSq
  /-- Identity vertical maps give the canonical identity exchange. -/
  B_id : ∀ {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j]
    (sq : IsPullback (𝟙 U) j j (𝟙 W)) (K : D Λ U),
    (B sq).hom.app K = (pId Λ W).hom.app ((J Λ j).obj K) ≫
      (J Λ j).map ((pId Λ U).inv.app K)
  /-- Identity opens give the canonical identity exchange. -/
  B_open_id : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sq : IsPullback f (𝟙 X) (𝟙 Y) f) (K : D Λ Y),
    (B sq).hom.app K = (P Λ f).map ((jId Λ Y).hom.app K) ≫
      (jId Λ X).inv.app ((P Λ f).obj K)
  /-- Cartesian pasting along successive arbitrary base maps. -/
  B_vertical : ∀ {U₀ U₁ U₂ W₀ W₁ W₂ : Scheme.{u}}
    {a₁ : U₁ ⟶ U₀} {a₂ : U₂ ⟶ U₁} {b₁ : W₁ ⟶ W₀} {b₂ : W₂ ⟶ W₁}
    {j₀ : U₀ ⟶ W₀} {j₁ : U₁ ⟶ W₁} {j₂ : U₂ ⟶ W₂}
    [IsOpenImmersion j₀] [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (q₁ : IsPullback a₁ j₁ j₀ b₁) (q₂ : IsPullback a₂ j₂ j₁ b₂)
    (q : IsPullback (a₂ ≫ a₁) j₂ j₀ (b₂ ≫ b₁)) (K : D Λ U₀),
    (B q).hom.app K =
      (pComp Λ b₂ b₁).hom.app ((J Λ j₀).obj K) ≫
      (P Λ b₂).map ((B q₁).hom.app K) ≫
      (B q₂).hom.app ((P Λ a₁).obj K) ≫
      (J Λ j₂).map ((pComp Λ a₂ a₁).inv.app K)
  /-- Cartesian pasting along successive opens. -/
  B_horizontal : ∀ {U U' V V' W W' : Scheme.{u}}
    {a : U' ⟶ U} {b : V' ⟶ V} {c : W' ⟶ W}
    {j : U ⟶ V} {j' : U' ⟶ V'} {i : V ⟶ W} {i' : V' ⟶ W'}
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion i] [IsOpenImmersion i']
    (q₁ : IsPullback a j' j b) (q₂ : IsPullback b i' i c)
    (q : IsPullback a (j' ≫ i') (j ≫ i) c) (K : D Λ U),
    (B q).hom.app K =
      (P Λ c).map ((jComp Λ j i).inv.app K) ≫
      (B q₂).hom.app ((J Λ j).obj K) ≫
      (J Λ i').map ((B q₁).hom.app K) ≫
      (jComp Λ j' i').hom.app ((P Λ a).obj K)
  /-- Associativity of the specified open compositors. -/
  j_assoc : ∀ {X₀ X₁ X₂ X₃ : Scheme.{u}}
    (j : X₀ ⟶ X₁) (i : X₁ ⟶ X₂) (k : X₂ ⟶ X₃)
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion k] (K : D Λ X₀),
    (J Λ k).map ((jComp Λ j i).hom.app K) ≫
      (jComp Λ (j ≫ i) k).hom.app K ≫ (jCongr Λ (Category.assoc j i k)).hom.app K =
      (jComp Λ i k).hom.app ((J Λ j).obj K) ≫ (jComp Λ j (i ≫ k)).hom.app K
  /-- Both open-compositor unit equations. -/
  j_unit : ∀ {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j] (K : D Λ U),
    ((jComp Λ (𝟙 U) j).hom.app K ≫ (jCongr Λ (Category.id_comp j)).hom.app K =
      (J Λ j).map ((jId Λ U).hom.app K)) ∧
    ((jComp Λ j (𝟙 W)).hom.app K ≫ (jCongr Λ (Category.comp_id j)).hom.app K =
      (jId Λ W).hom.app ((J Λ j).obj K))
  /-- The exact-model ambient mate equals the recorded total-left-derived ambient mate. -/
  exchange_normalized : ∀ {U W Y Z : Scheme.{u}}
    {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    (sq : ChosenCartesianSquare j p r i) (K : D Λ W),
    (condensedAmbientExchange Λ sq).app K ≫
        (R Λ p).map ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).hom.app K) =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ i).hom.app ((R Λ r).obj K) ≫
        (derivedDirectImageOpenRestriction Λ sq.toCommSq).app K

/-- Open units, normalized open exchange and the open compositor laws.
Source: latest blueprint sk-thm-sf-comp-composition.proof.md, Canonicity and associativity
and Base change paragraphs (blueprint: new-zl-condensed-open-proper-open-laws).

Proof:
1. Transport internal modules over `p_T^*Λ` to modules over the section-ring sheaf, with
pullback, direct image, open extension and their specified adjunctions; exact diagram
descent transports units, counits and their equations to unbounded derived categories.
Pullback and open extension are exact, so `P f = D(f^*)` and `J j = D(j_!)`.
2. Arbitrary-scheme condensed open base change shows that `openMap` (unit, square
comparison, counit) is invertible on every Cartesian open square, without
quasi-compactness; let `B` be its inverse, so `B_normalized` holds by definition. The
transported ringed-site normalization gives invertible open units equal to the derived
open-adjunction unit.
3. The coefficient maps are isomorphisms, so module direct-image coherence applies and
open compositors are the conjugates of the canonical pullback compositors. Both adjoints
of an identity, binary-pasting or triple-composition diagram of open comparisons are the
same restriction comparison with the same units inserted; mate pasting and the triangle
identities give `B_id`, `B_open_id`, `B_vertical`, `B_horizontal`, `j_assoc`, `j_unit`.
4. On a chosen Cartesian square the exact-model open restriction and the total left
derived ambient exchange are mates of the same pullback-square comparison under the
identification `leftDerivedUpperStarIsoMapDerivedCategory`; this is `exchange_normalized`. -/
theorem condensedOpenProperOpenLaws (_hΛ : IsAdmissibleCoefficient Λ) :
    Nonempty (OpenLaws Λ) := by
  obtain ⟨basic⟩ := condensedOpenProperOpenBasic Λ _hΛ
  obtain ⟨coh⟩ := condensedOpenProperOpenCoherence Λ _hΛ basic
  refine ⟨{ units := basic.units
            B := basic.B
            B_normalized := basic.B_normalized
            B_id := coh.B_id
            B_open_id := coh.B_open_id
            B_vertical := coh.B_vertical
            B_horizontal := coh.B_horizontal
            j_assoc := coh.j_assoc
            j_unit := coh.j_unit
            exchange_normalized := coh.exchange_normalized }⟩


end AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper
