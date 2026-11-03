/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientDerivedFunctorAPI
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientDerivedFunctorAPI
import WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalIntegralFiniteQuotientMateTransport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStarDerived
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange

/-! # Proper closed exchange for ordinary finite quotients

Source: Bhatt--Scholze, Lemma 6.7.5 and Section 6.1.
(blueprint: lem-sp-original-integral-closed-finite-quotient-exchange)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open AlgebraicGeometry Scheme

private theorem finiteCoefficientExchangeIsIso
    (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [DiscreteTopology T] [Finite T]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} [IsProper f]
    (sq : ChosenCartesianSquare g' f' f g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)))
    (hK : boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj T) X) K) :
    IsIso ((refinementAmbientExchange (Profinite.continuousMapRingObj T) sq).app K) := by
  have horigin := (isEtaleOrigin_of_isConstructible T hK).plusEtaleOrigin
  have hbc : IsIso ((ProEtale.derivedBaseChangeMap
      (ModuleCat.{u + 1} (ULift.{u + 1} T)) sq.toCommSq).app
        ((finiteCoefficientDerivedEquivalence X T).functor.obj K)) :=
    ProEtale.isIso_derivedBaseChangeMap_app_of_isProper (ULift.{u + 1} T)
      (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)
      _ horigin
  have hmap : IsIso ((finiteCoefficientDerivedEquivalence Y' T).functor.map
      ((refinementAmbientExchange (Profinite.continuousMapRingObj T) sq).app K)) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Arrow.isoMk (originalFiniteCoefficientExchangeSource T (f := f) (g := g) K)
        (originalFiniteCoefficientExchangeTarget T (f' := f') (g' := g') K)
        (originalFiniteCoefficientExchangeComparison T sq K).symm)).2 hbc
  exact isIso_of_reflects_iso _ (finiteCoefficientDerivedEquivalence Y' T).functor

/-- The ordinary finite-quotient part of integral closed exchange.

Source: Bhatt--Scholze, Lemma 6.7.5, Section 6.1, Lemma 6.1.3 and Corollary 6.1.5;
Hemo--Richarz--Scholbach, Propositions 5.1 and 7.6 and Theorem 7.7.
(blueprint: lem-sp-original-integral-closed-finite-quotient-exchange).

Proof in words. At level n use ordinary extension of scalars along the actual quotient
map O_E -> O_E/ell^(n+1). Right exactness of tensor gives a canonical isomorphism from
its scalar restriction to the displayed ordinary cokernel. Constructibility over the
quotient follows from integral cokernel closure and the quotient coefficient presentation
lemma. Place this finite coefficient module in degree zero. Its image in ordinary
finite-module sheaves is bounded constructible, so the published finite coefficient
origin theorem supplies bounded-below etale origin. The published pro-etale consequence
of torsion etale proper base change makes its ordinary finite-module exchange invertible.
The finite coefficient model comparison identifies this map with the specified condensed
exchange. The scalar restriction comparison then identifies the latter with the integral
exchange on the scalar restriction. Finally commute exact restriction with the single
functor and use naturality along the proved cokernel isomorphism. The two comparisons are
map identities with fixed, constructed endpoint isomorphisms; neither assumes exchange
invertibility. This uses no integral reconstruction. Empty schemes, zero quotients and
the first positive exponent are covered by the same constructions. -/
theorem originalIntegralClosedFiniteQuotientExchange
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E]
    (S : Scheme.{u}) (hell : IsUnit (ell : Γ(S, ⊤)))
    {Z₁ Z₂ C : Over S}
    [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
    [LocallyOfFiniteType Z₂.hom] [QuasiCompact Z₂.hom]
    (h : Z₁ ⟶ Z₂) [IsProper h.left]
    (i : C ⟶ Z₂) [IsClosedImmersion i.left]
    (hc : ∃ (U : Scheme.{u}) (j : U ⟶ Z₂.left),
      IsOpenImmersion j ∧ QuasiCompact j ∧
        Set.range i.left.base = (Set.range j.base)ᶜ)
    (M : Mod (Sheaf (ProEt.topology Z₁.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) Z₁.left))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) Z₁.left) M) :
    ∀ n : ℕ, IsIso ((refinementAmbientExchange (Profinite.padicIntegersRingObj ell E)
      (g' := pullback.fst h.left i.left) (f' := pullback.snd h.left i.left)
      (f := h.left) (g := i.left)
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).app ((DerivedCategory.singleFunctor _ 0).obj
          (cokernel (ell ^ (n + 1) • 𝟙 M)))) := by
  intro n
  let N := originalIntegralFiniteQuotientModule ell E Z₁.left M n
  let T := PadicAlgCl.integersModPow ell E (n + 1)
  let a := Profinite.padicIntegersRingObjToIntegersModPow.{u} ell E (n + 1)
  let K := (DerivedCategory.singleFunctor _ 0).obj N
  let sq : ChosenCartesianSquare (pullback.fst h.left i.left)
      (pullback.snd h.left i.left) h.left i.left :=
    { w := pullback.condition
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
  obtain ⟨hN, ⟨eN⟩⟩ := originalIntegralFiniteQuotientPresentation ell E Z₁.left M hM n
  have hK : boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj T) Z₁.left) K :=
    boundedConstructible_singleFunctor_zero_obj _ N hN
  have : IsIso ((refinementAmbientExchange (Profinite.continuousMapRingObj T) sq).app K) :=
    finiteCoefficientExchangeIsIso T sq K hK
  have hmap : IsIso (D(Mod.comap (coefficientMap a C.left)).map
      ((refinementAmbientExchange (Profinite.continuousMapRingObj T) sq).app K)) :=
    inferInstance
  have hres : IsIso ((refinementAmbientExchange (Profinite.padicIntegersRingObj ell E) sq).app
      (D(Mod.comap (coefficientMap a Z₁.left)).obj K)) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Arrow.isoMk (originalIntegralRestrictionExchangeSource a
          (f := h.left) (g := i.left) K)
        (originalIntegralRestrictionExchangeTarget a
          (f' := pullback.snd h.left i.left) (g' := pullback.fst h.left i.left) K)
        (originalIntegralFiniteQuotientMateTransport a sq K).symm)).2 hmap
  let e : D(Mod.comap (coefficientMap a Z₁.left)).obj K ≅
      (DerivedCategory.singleFunctor _ 0).obj (cokernel (ell ^ (n + 1) • 𝟙 M)) :=
    ((Mod.comap (coefficientMap a Z₁.left)).mapDerivedCategorySingleFunctor 0).app N ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso eN
  exact (NatTrans.isIso_app_iff_of_iso
    (refinementAmbientExchange (Profinite.padicIntegersRingObj ell E) sq) e).1 hres

end AlgebraicGeometry.ProEtale.CondensedRing
