/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientDerivedFunctorAPI
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalCoefficientQbarAffineExchange
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry Scheme
/-- The finite-subextension-valued algebraic-closure branch of rational proper closed exchange.
Source: Hemo--Richarz--Scholbach, Proposition 5.2, Lemma 5.3(1), Lemma 7.9 and
Theorem 7.7.
(blueprint: lem-sp-original-coefficient-closed-rational-heart-qbar)

Proof: apply the affine-local closed-exchange reduction
`originalCoefficientClosedExchangeAffineLocal` to the coefficient `padicAlgClRingObj ell`,
with target `Z₂.left`, structure map `Z₂.hom`, proper map `h.left` and closed
immersion `i.left`. Its affine hypothesis is `originalCoefficientQbarAffineExchange` on every
affine target where `ell` is invertible. The square identities of the canonical pullback
square are propositions, so the conclusion is the displayed global exchange. -/
theorem originalCoefficientClosedRationalHeartQbar
    (ell : ℕ) [Fact ell.Prime]
    (S : Scheme.{u}) (hell : IsUnit (ell : Γ(S, ⊤)))
    {Z₁ Z₂ C : Over S}
    [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
    [LocallyOfFiniteType Z₂.hom] [QuasiCompact Z₂.hom]
    (h : Z₁ ⟶ Z₂) [IsProper h.left]
    (i : C ⟶ Z₂) [IsClosedImmersion i.left]
    (hc : ∃ (U : Scheme.{u}) (j : U ⟶ Z₂.left),
      IsOpenImmersion j ∧ QuasiCompact j ∧ Set.range i.left.base = (Set.range j.base)ᶜ)
    (M : Mod (Sheaf (ProEt.topology Z₁.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) Z₁.left))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ell) Z₁.left) M) :
    IsIso ((refinementAmbientExchange (Profinite.padicAlgClRingObj ell)
      (g' := pullback.fst h.left i.left) (f' := pullback.snd h.left i.left)
      (f := h.left) (g := i.left)
      { w := pullback.condition, isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).app
      ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  refine originalCoefficientClosedExchangeAffineLocal ell (Profinite.padicAlgClRingObj ell)
    ?_ S hell Z₂.hom h.left i.left hc M hM
  intro Y _ hY X C f _ i _ hc M hM
  exact originalCoefficientQbarAffineExchange ell Y hY X C f i hc M hM

end AlgebraicGeometry.ProEtale.CondensedRing
