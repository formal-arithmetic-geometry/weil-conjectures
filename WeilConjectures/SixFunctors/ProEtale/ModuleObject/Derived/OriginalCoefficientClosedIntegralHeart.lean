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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalIntegralOrdinaryQuotientReconstruction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalIntegralClosedFiniteQuotientExchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorShifts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.KFlatDerivedAdjunctionTransportShifts
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import WeilConjectures.CategoryTheory.DerivedCategory.ProductsMapDerivedCategory

/-! # Integral coefficient proper closed exchange in degree zero

Source: `def-exchange-projection`, original-coefficient proper closed-exchange
step of the compactification-independence calculation.
(blueprint: lem-sp-original-coefficient-closed-integral-heart)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open AlgebraicGeometry Scheme

private theorem exchangeAdjunctionShift
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {U V : Scheme.{u}} (h : U ⟶ V) :
    Adjunction.CommShift
      (F := moduleObjectDerivedPullback R h) (G := moduleObjectDerivedPushforward R h)
      (derivedUpperStarLowerStarAdjunction R h) ℤ := by
  exact (kflat_derived_adjunction_transport_shifts (Mon.mk R) h).2.2

private theorem exchangeShift
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {V W V' W' : Scheme.{u}} {f : V ⟶ W} {g : W' ⟶ W}
    {f' : V' ⟶ W'} {g' : V' ⟶ V}
    (sq : ChosenCartesianSquare g' f' f g) :
    NatTrans.CommShift
      (F₁ := moduleObjectDerivedPushforward R f ⋙ moduleObjectDerivedPullback R g)
      (F₂ := moduleObjectDerivedPullback R g' ⋙ moduleObjectDerivedPushforward R f')
      (refinementAmbientExchange R sq) ℤ := by
  have := exchangeAdjunctionShift R f
  have := exchangeAdjunctionShift R f'
  have : NatTrans.CommShift
      (modulePullbackSquareComparison R f g g' f' sq.toCommSq.w.symm).hom ℤ := by
    constructor
    intro n
    ext K
    exact (module_pullback_square_shift R f g g' f' sq.toCommSq.w.symm K n).symm
  unfold refinementAmbientExchange
  rw [coefficientDerivedAdjunction_eq, coefficientDerivedAdjunction_eq,
    coefficientAmbientSquare_eq, coefficientIsoTransThree_eq]
  exact NatTrans.CommShift.mateEquiv
    (G := moduleObjectDerivedPullback R g) (H := moduleObjectDerivedPullback R g')
    (L₁ := moduleObjectDerivedPullback R f) (R₁ := moduleObjectDerivedPushforward R f)
    (L₂ := moduleObjectDerivedPullback R f') (R₂ := moduleObjectDerivedPushforward R f')
    (derivedUpperStarLowerStarAdjunction R f)
    (derivedUpperStarLowerStarAdjunction R f')
    (TwoSquare.mk _ _ _ _
      (modulePullbackSquareComparison R f g g' f' sq.toCommSq.w.symm).hom)

private theorem moduleProductsExact
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (X : Scheme.{u}) :
    HasExactLimitsOfShape (Discrete ℕ)
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) := by
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) (condensedRingObj R X)
  let B : Sheaf (ProEt.topology X) RingCat.{u + 1} :=
    (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (ProEt.topology X) (condensedRingObj R X))
  have : HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{u + 1} B) :=
    Scheme.ProEt.products_exact.{u, u, 0} X B ℕ
  exact HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ) e.symm

private theorem immersionPullbackProducts
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsImmersion f] :
    PreservesLimitsOfShape (Discrete ℕ) (moduleObjectDerivedPullback R f) := by
  have := (Scheme.proEtale_immersion_inverseImage_preservesLimits f).2.1
  have := preservesSmallestLimits_of_preservesLimits
    (Scheme.proEtaleSheafInverseImage f Ab.{u + 1})
  have : PreservesLimitsOfShape (Discrete ℕ) (ProEtale.upperStar Ab.{u + 1} f) :=
    preservesLimitsOfShape_of_natIso
      ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).leftAdjointUniq
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f))
  let B := condensedRingObj R X
  let L := ProEtale.upperStar Ab.{u + 1} f
  have : PreservesLimitsOfShape (Discrete ℕ) (L.mapMod B) := by
    let V : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (L.obj B) ⥤
        Sheaf (ProEt.topology Y) Ab.{u + 1} := Mod.forget (L.obj B)
    have : PreservesLimitsOfShape (Discrete ℕ) (L.mapMod B ⋙ V) :=
      inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ) (Mod.forget B ⋙ L))
    have : ReflectsLimitsOfShape (Discrete ℕ) V :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    exact preservesLimitsOfShape_of_reflects_of_preserves (L.mapMod B) V
  have : PreservesLimitsOfShape (Discrete ℕ) (upperStar R f) :=
    preservesLimitsOfShape_of_natIso (Functor.isoWhiskerLeft
      (L.mapMod B) (Mod.extendScalarsIsoComapInv (condensedPullbackHom R f))).symm
  have := moduleProductsExact R X
  have := moduleProductsExact R Y
  have : PreservesLimitsOfShape (Discrete ℕ) (upperStar R f).mapDerivedCategory :=
    Functor.preservesLimitsOfShape_discrete_mapDerivedCategory _
  exact preservesLimitsOfShape_of_natIso (modulePullbackExactComparison R f).symm

private theorem isoLocus_countableProducts
    {A B : Type*} [Category A] [Category B] (F G : A ⥤ B)
    [PreservesLimitsOfShape (Discrete ℕ) F]
    [PreservesLimitsOfShape (Discrete ℕ) G] (τ : F ⟶ G) :
    τ.isoLocus.IsClosedUnderLimitsOfShape (Discrete ℕ) := by
  constructor
  rintro X ⟨p⟩
  have (j : Discrete ℕ) : IsIso ((Functor.whiskerLeft p.diag τ).app j) :=
    p.prop_diag_obj j
  have : IsIso (Functor.whiskerLeft p.diag τ) := NatIso.isIso_of_isIso_app _
  let hF := isLimitOfPreserves F p.isLimit
  let hG := isLimitOfPreserves G p.isLimit
  let e := IsLimit.conePointsIsoOfNatIso hF hG
    (asIso (Functor.whiskerLeft p.diag τ))
  have he : τ.app X = e.hom := by
    apply hG.hom_ext
    intro j
    change τ.app X ≫ G.map (p.π.app j) = _
    rw [← τ.naturality]
    exact (IsLimit.conePointsIsoOfNatIso_hom_comp hF hG
      (asIso (Functor.whiskerLeft p.diag τ)) j).symm
  change IsIso (τ.app X)
  rw [he]
  infer_instance

/-- Integral coefficient proper closed exchange in degree zero.

Source: `def-exchange-projection`, compactification-independence calculation,
original-coefficient proper closed-exchange step, reduced to the heart.

Proof: Work on affine opens V of Z₂. The quasi-compact complementary open
in hc remains quasi-compact on V, so i_V is a constructible closed immersion.
Its pro-étale inverse image is computed on lifted w-contractible affine tests;
this description preserves limits. On each constructible stratum write M
locally by a finite matrix of integral coefficient sections. On a
w-contractible affine test these are continuous functions from its extremally
disconnected component space into O_E. The finite presentation is complete for
the uniformizer: solve its compatible finite quotient presentation equations
pointwise in the compact spaces O_E^r, then use projectivity of the extremally
disconnected space to choose a continuous solution. This proves both separation
and reconstruction by the ordinary quotients M/π^n M. Their transitions are
epimorphisms, and the replete pro-étale topos identifies this limit with the
derived limit of the degree-zero quotients. Exact open/closed localization and
limit preservation of the corresponding pro-étale extensions reassemble the
finite stratification, proving M[0] = Rlim (M/π^n M)[0]. Each ordinary quotient
has finite-coefficient constructible étale origin, by transporting its local
finite presentations on the same strata. This assertion is about ordinary
quotients and does not assert constructibility of all derived reductions.
Proper direct image preserves the derived limit by its derived adjunction.
Constructible closed pullback preserves it by lifted-test evaluation and exact
products. Apply finite torsion proper base change to each ordinary quotient,
then take the compatible limit. Restriction of coefficient scalars identifies
the finite-level pullbacks and pushforwards with the ordinary integral ones.
For the map compatibility expand the unit, pullback compositor and counit
of the mate. The tensor/evaluation coefficient comparisons commute with each
of these factors, hence with their composite and quotient transition maps.
Thus the limit is the specified ambient exchange, rather than an unspecified
isomorphism between the same objects. Conservative lifted tests and the
inverse images of the affine cover of Z₂ give the global assertion. Empty
tests, strata and zero modules use the same formulas.
References: Bhatt--Scholze Section 6.1 and Lemma 6.7.5; Hemo--Richarz--Scholbach
Propositions 5.1 and 7.6 and Theorem 7.7. The finite-presentation reconstruction
uses compact integral presentation equations on the extremally disconnected
tests of the current condensed coefficient model.
(blueprint: lem-sp-original-coefficient-closed-integral-heart) -/
theorem originalCoefficientClosedIntegralHeart
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E]
    (Λ : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (hΛ : Λ = ⟨Profinite.padicIntegersRingObj ell E⟩)
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
      (condensedRingObj Λ.X Z₁.left))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ.X Z₁.left) M) :
    IsIso ((refinementAmbientExchange Λ.X
      (g' := pullback.fst h.left i.left) (f' := pullback.snd h.left i.left)
      (f := h.left) (g := i.left)
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).app ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  subst Λ
  have hquot := originalIntegralClosedFiniteQuotientExchange ell E S hell h i hc M hM
  let R := Profinite.padicIntegersRingObj ell E
  let F := moduleObjectDerivedPushforward R h.left ⋙ moduleObjectDerivedPullback R i.left
  let G := moduleObjectDerivedPullback R (pullback.fst h.left i.left) ⋙
    moduleObjectDerivedPushforward R (pullback.snd h.left i.left)
  let sq : ChosenCartesianSquare (pullback.fst h.left i.left)
      (pullback.snd h.left i.left) h.left i.left :=
    { w := pullback.condition
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
  let τ : F ⟶ G := refinementAmbientExchange R sq
  have := immersionPullbackProducts R i.left
  have := immersionPullbackProducts R (pullback.fst h.left i.left)
  have : PreservesLimitsOfSize.{0, 0} (moduleObjectDerivedPushforward R h.left) :=
    (derivedUpperStarLowerStarAdjunction R h.left).rightAdjoint_preservesLimits
  have : PreservesLimitsOfSize.{0, 0}
      (moduleObjectDerivedPushforward R (pullback.snd h.left i.left)) :=
    (derivedUpperStarLowerStarAdjunction R
      (pullback.snd h.left i.left)).rightAdjoint_preservesLimits
  have : PreservesLimitsOfShape (Discrete ℕ) F := inferInstance
  have : PreservesLimitsOfShape (Discrete ℕ) G := inferInstance
  have := (module_derived_functors_exact_and_comparison_shifts R h.left).2.1
  have := (module_derived_functors_exact_and_comparison_shifts R i.left).1
  have := (module_derived_functors_exact_and_comparison_shifts R
    (pullback.fst h.left i.left)).1
  have := (module_derived_functors_exact_and_comparison_shifts R
    (pullback.snd h.left i.left)).2.1
  have : F.IsTriangulated := inferInstance
  have : G.IsTriangulated := inferInstance
  have : NatTrans.CommShift τ ℤ := exchangeShift R sq
  have : τ.isoLocus.IsClosedUnderLimitsOfShape (Discrete ℕ) :=
    isoLocus_countableProducts F G τ
  exact originalIntegralOrdinaryQuotientReconstruction ell E Z₁.left M hM τ.isoLocus hquot

end AlgebraicGeometry.ProEtale.CondensedRing
