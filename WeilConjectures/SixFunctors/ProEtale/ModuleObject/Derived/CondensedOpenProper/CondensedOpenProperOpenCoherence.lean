/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperOpenBasic

/-! # Coherence of normalized open exchange

Identity, pasting, compositor, and ambient-exchange equations for the canonical basic data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
structure OpenLawsCoherence (basic : OpenLawsBasic Λ) : Prop where
  B_id : ∀ {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j]
    (sq : IsPullback (𝟙 U) j j (𝟙 W)) (K : D Λ U),
    (basic.B sq).hom.app K = (pId Λ W).hom.app ((J Λ j).obj K) ≫
      (J Λ j).map ((pId Λ U).inv.app K)
  B_open_id : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sq : IsPullback f (𝟙 X) (𝟙 Y) f) (K : D Λ Y),
    (basic.B sq).hom.app K = (P Λ f).map ((jId Λ Y).hom.app K) ≫
      (jId Λ X).inv.app ((P Λ f).obj K)
  B_vertical : ∀ {U₀ U₁ U₂ W₀ W₁ W₂ : Scheme.{u}}
    {a₁ : U₁ ⟶ U₀} {a₂ : U₂ ⟶ U₁} {b₁ : W₁ ⟶ W₀} {b₂ : W₂ ⟶ W₁}
    {j₀ : U₀ ⟶ W₀} {j₁ : U₁ ⟶ W₁} {j₂ : U₂ ⟶ W₂}
    [IsOpenImmersion j₀] [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (q₁ : IsPullback a₁ j₁ j₀ b₁) (q₂ : IsPullback a₂ j₂ j₁ b₂)
    (q : IsPullback (a₂ ≫ a₁) j₂ j₀ (b₂ ≫ b₁)) (K : D Λ U₀),
    (basic.B q).hom.app K =
      (pComp Λ b₂ b₁).hom.app ((J Λ j₀).obj K) ≫
      (P Λ b₂).map ((basic.B q₁).hom.app K) ≫
      (basic.B q₂).hom.app ((P Λ a₁).obj K) ≫
      (J Λ j₂).map ((pComp Λ a₂ a₁).inv.app K)
  B_horizontal : ∀ {U U' V V' W W' : Scheme.{u}}
    {a : U' ⟶ U} {b : V' ⟶ V} {c : W' ⟶ W}
    {j : U ⟶ V} {j' : U' ⟶ V'} {i : V ⟶ W} {i' : V' ⟶ W'}
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion i] [IsOpenImmersion i']
    (q₁ : IsPullback a j' j b) (q₂ : IsPullback b i' i c)
    (q : IsPullback a (j' ≫ i') (j ≫ i) c) (K : D Λ U),
    (basic.B q).hom.app K =
      (P Λ c).map ((jComp Λ j i).inv.app K) ≫
      (basic.B q₂).hom.app ((J Λ j).obj K) ≫
      (J Λ i').map ((basic.B q₁).hom.app K) ≫
      (jComp Λ j' i').hom.app ((P Λ a).obj K)
  j_assoc : ∀ {X₀ X₁ X₂ X₃ : Scheme.{u}}
    (j : X₀ ⟶ X₁) (i : X₁ ⟶ X₂) (k : X₂ ⟶ X₃)
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion k] (K : D Λ X₀),
    (J Λ k).map ((jComp Λ j i).hom.app K) ≫
      (jComp Λ (j ≫ i) k).hom.app K ≫ (jCongr Λ (Category.assoc j i k)).hom.app K =
      (jComp Λ i k).hom.app ((J Λ j).obj K) ≫ (jComp Λ j (i ≫ k)).hom.app K
  j_unit : ∀ {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j] (K : D Λ U),
    ((jComp Λ (𝟙 U) j).hom.app K ≫ (jCongr Λ (Category.id_comp j)).hom.app K =
      (J Λ j).map ((jId Λ U).hom.app K)) ∧
    ((jComp Λ j (𝟙 W)).hom.app K ≫ (jCongr Λ (Category.comp_id j)).hom.app K =
      (jId Λ W).hom.app ((J Λ j).obj K))
  exchange_normalized : ∀ {U W Y Z : Scheme.{u}}
    {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    (sq : ChosenCartesianSquare j p r i) (K : D Λ W),
    (condensedAmbientExchange Λ sq).app K ≫
        (R Λ p).map ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).hom.app K) =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ i).hom.app ((R Λ r).obj K) ≫
        (derivedDirectImageOpenRestriction Λ sq.toCommSq).app K

/-- The coherence laws for the normalized basic open exchange package.
Source: latest blueprint sk-thm-sf-comp-composition.proof.md, Canonicity and associativity
and Base change paragraphs (blueprint: new-zl-condensed-open-proper-coherence).

Proof:
1. There is no arbitrary choice of comparisons in `basic`: `units_normalized` identifies
its units with `canonicalOpenUnits`, and `B_normalized` identifies the inverse of every `B`
with the specified `openMap`. An isomorphism is determined by its inverse, so it suffices to
calculate the canonical mate; these calculations apply to every `basic` satisfying the two
normalizations.
2. The coefficient maps are isomorphisms, so module direct-image coherence applies. Under
exact derived passage the pullback compositors remain `pComp`; the open compositors `jComp`
are their conjugates under the specified derived open adjunctions. The same passage preserves
units, counits, the square comparison, functor composition and the triangle identities.
3. For identity vertical maps, the restriction-square comparison is the identity after
inserting `pId`. Take its open-adjunction mate and cancel the adjacent unit and counit by the
triangle identities. Inverting gives the displayed `B_id` formula. For identity opens do the
same calculation with the identity open adjunction, whose comparison is `jId`; cancellation
then gives `B_open_id` with the displayed `jId` and its inverse.
4. For two vertically pasted Cartesian squares, the outer restriction comparison equals
the composite of the two inner restriction comparisons, conjugated by the two `pComp`s.
Mate pasting carries this equality to the composite of their open mates. Invert it and use
`B_normalized` on all three squares. The outer target compositor is `pComp b₂ b₁`, the
middle factors are the two `B`s, and the source compositor is the inverse of `pComp a₂ a₁`;
these are precisely the four factors of `B_vertical`, in their stated order.
5. For two horizontally pasted squares use the composite open adjunctions. Mate pasting
identifies the outer mate with the two inner mates; the comparisons between composite and
single open adjoints are exactly `jComp`. Inverting yields `B_horizontal`, with the inverse
upper open compositor first and the lower open compositor last. For three successive opens,
both composites of `jComp` have, by conjugation, the same restriction compositor: pullback
associativity makes their mates equal. Injectivity of the mate correspondence gives `j_assoc`,
including transport by `jCongr`. With an identity open the pullback unit equations and the
triangle identities give the two equalities of `j_unit` by the same argument.
6. On a chosen Cartesian square, conjugate the exact-model open restriction and the total
left-derived ambient exchange by `leftDerivedUpperStarIsoMapDerivedCategory`. Both are mates
of the same pullback-square comparison with the same unit and counit inserted. Naturality of
this identification and injectivity of mates identify the two transformations; evaluating
at `K` gives the two sides of `exchange_normalized`. Collect the seven resulting laws in
`OpenLawsCoherence`.
(blueprint: new-zl-condensed-open-proper-coherence) -/
theorem condensedOpenProperOpenCoherence (_hΛ : IsAdmissibleCoefficient Λ)
    (basic : OpenLawsBasic Λ) : Nonempty (OpenLawsCoherence Λ basic) := by sorry
end AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper
