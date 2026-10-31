/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.AlgebraicGeometry.CondensedIsomorphismSquareExchange
import WeilConjectures.SixFunctors.FrobeniusSquareCartesian
import WeilConjectures.CategoryTheory.ExactDerivedCohomologyCoherence
import WeilConjectures.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.AlgebraicGeometry.ExactDerivedTransformation
import WeilConjectures.CategoryTheory.Triangulated.TExactFixedPairHeartCohomology
public import WeilConjectures.CategoryTheory.ExactDerivedAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf
import WeilConjectures.CategoryTheory.InverseMateEquivalence

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.CondensedShriekBoundedQcqs
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Condensed open extension, cohomology and local Frobenius

Source: latest blueprint, sec-deligne-laumon-general/sk-prop-wgen-relative-line/
lem-zl-morphism-open-closed-reduction.proof.md, Part 2
(blueprint: lem-zl-condensed-open-extension-local).

The comparison uses the chosen compactification and the existing trivial-open comparison.
Weil cohomology is transported by the normalized exact-derived homology comparison.
All module and derived categories are the ordinary condensed-coefficient categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u vC vD uC uD wC wD uV vV

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.OpenExtensionLocal

/-- Localize an exact commutation isomorphism termwise, using the canonical compositors.
Source: Part 2, exact extension by zero and its Frobenius square
(blueprint: lem-zl-condensed-open-extension-local). -/
def derivedExchange {C : Type uC} {E : Type uD} [Category.{vC} C] [Category.{vD} E]
    [Abelian C] [Abelian E] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} E]
    (J : C ⥤ E) (P : C ⥤ C) (Q : E ⥤ E)
    [J.Additive] [P.Additive] [Q.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (β : J ⋙ Q ≅ P ⋙ J) :
    J.mapDerivedCategory ⋙ Q.mapDerivedCategory ≅
      P.mapDerivedCategory ⋙ J.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso J Q).symm ≪≫
    Functor.mapDerivedCategoryNatIso β ≪≫ Functor.mapDerivedCategoryCompIso P J

section AbstractCohomology

variable {C : Type uC} {E : Type uD} [Category.{vC} C] [Category.{vD} E]
  [Abelian C] [Abelian E] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} E]
  (J : C ⥤ E) (P : C ⥤ C) (Q : E ⥤ E)
  [J.Additive] [P.Additive] [Q.Additive]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]

/-- Cohomology of a strict pair, through the normalized exact-derived comparison.
Source: Part 2, Weil cohomology of exact extension
(blueprint: lem-zl-condensed-open-extension-local). -/
def pairCohomology (r : ℤ) :=
  IsoAlgebra.mapOfNatIso (P.mapDerivedCategoryHomologyFunctorIso r)

/-- The natural Weil cohomology comparison with its prescribed underlying map.
This is the exact carrier-equality clause written before specialization to module objects.
Source: Part 2, cohomological compatibility
(blueprint: lem-zl-condensed-open-extension-local). -/
def ExactWeilCohomology (β : J ⋙ Q ≅ P ⋙ J) (r : ℤ) : Prop :=
  ∃ e : IsoAlgebra.mapOfNatIso (derivedExchange J P Q β) ⋙ pairCohomology Q r ≅
      pairCohomology P r ⋙ IsoAlgebra.mapOfNatIso β,
    ∀ K : IsoAlgebra P.mapDerivedCategory,
      (e.hom.app K).hom.f = (J.mapDerivedCategoryHomologyFunctorIso r).inv.app K.carrier

/-- Transport the induced Weil structure across the specified derived comparison.
Source: Part 2, the Weil structure on the compactification functor
(blueprint: lem-zl-condensed-open-extension-local). -/
def transportDerivedPair (β : J ⋙ Q ≅ P ⋙ J)
    (K : IsoAlgebra P.mapDerivedCategory) (L : DerivedCategory E)
    (c : L ≅ J.mapDerivedCategory.obj K.carrier) :=
  IsoAlgebra.mk L
    (Q.mapDerivedCategory.mapIso c ≪≫
      ((IsoAlgebra.mapOfNatIso (derivedExchange J P Q β)).obj K).str ≪≫ c.symm)

/-- The compact-support cohomology comparison, with its canonical carrier formula.
The arbitrary-looking L is accompanied by the specified comparison c; no map or Weil
structure is assumed as free data in the specialization to compact support.
Source: Part 2, cohomology after the compactification comparison
(blueprint: lem-zl-condensed-open-extension-local). -/
def CompactWeilCohomology (β : J ⋙ Q ≅ P ⋙ J)
    (K : IsoAlgebra P.mapDerivedCategory) (L : DerivedCategory E)
    (c : L ≅ J.mapDerivedCategory.obj K.carrier) (r : ℤ) : Prop :=
  ∃ e : (pairCohomology Q r).obj (transportDerivedPair J P Q β K L c) ≅
      (IsoAlgebra.mapOfNatIso β).obj ((pairCohomology P r).obj K),
    e.hom.hom.f = (DerivedCategory.homologyFunctor E r).map c.hom ≫
      (J.mapDerivedCategoryHomologyFunctorIso r).inv.app K.carrier

end AbstractCohomology

/-- Cohomology of an ambient strict Weil pair with its canonical module Weil structure.
Source: Part 2, cohomological compatibility
(blueprint: lem-zl-condensed-open-extension-local). -/
def weilCohomology (ℓ : ℕ) [Fact ℓ.Prime] {T : Scheme.{u}} (a : T ≅ T) (r : ℤ) :=
  pairCohomology (upperStar (Profinite.padicAlgClRingObj ℓ) a.hom) r

variable (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  (U₀ X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]

/-- Finite type is stable under the specified geometric base change.
Source: the separated finite-type setting of Part 2
(blueprint: lem-zl-condensed-open-extension-local). -/
instance geometricFiniteType (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] :
    LocallyOfFiniteType ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj T₀).hom :=
  inferInstanceAs (LocallyOfFiniteType
    (pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Quasi-compactness is stable under the specified geometric base change.
Source: the finite-type setting of Part 2
(blueprint: lem-zl-condensed-open-extension-local). -/
instance geometricQuasiCompact (T₀ : Over (Spec (.of D.k₀)))
    [QuasiCompact T₀.hom] :
    QuasiCompact ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj T₀).hom :=
  inferInstanceAs (QuasiCompact
    (pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Separatedness is stable under the specified geometric base change.
Source: the separated setting of Part 2
(blueprint: lem-zl-condensed-open-extension-local). -/
instance geometricSeparated (T₀ : Over (Spec (.of D.k₀)))
    [IsSeparated T₀.hom] :
    IsSeparated ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj T₀).hom :=
  inferInstanceAs (IsSeparated
    (pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Openness is stable under the specified geometric base change.
Source: Part 2, the geometric base change of j₀
(blueprint: lem-zl-condensed-open-extension-local). -/
instance geometricOpen : IsOpenImmersion (((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left) :=
  MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j₀ inferInstance

/-- The actual inverse-image square of the geometric Frobenius automorphisms.
Source: Part 2, j g_U = g_X j
(blueprint: lem-zl-condensed-open-extension-local).
Proof: both composites have first pullback projection j₀ and second projection followed
by Spec of the inverse q-power field automorphism. Pullback uniqueness proves the equality. -/
theorem frobenius_square :
    CommSq (D.geometricFrobenius U₀).hom (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)
      (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)
        (D.geometricFrobenius X₀).hom := by
  exact ⟨(D.frobenius_square_cartesian U₀ X₀ j₀).2.2.2.2.1⟩

/-- The specified pullback-square isomorphism; its inverse mate fixes the open exchange.
Source: Part 2, inverse-image composition comparisons
(blueprint: lem-zl-condensed-open-extension-local). -/
def pullbackSquare :=
  upperStarSquareComparison (Profinite.padicAlgClRingObj ℓ) (frobenius_square D U₀ X₀ j₀)

/-- The canonical inverse mate, with no choice of a comparison map.
Source: Part 2, open Frobenius exchange
(blueprint: lem-zl-condensed-open-extension-local). -/
def inverseMate :=
  ((mateEquiv
    (openImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ)
      (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left))
    (openImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ)
      (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left))).symm
    (TwoSquare.mk _ _ _ _ (pullbackSquare D ℓ U₀ X₀ j₀).inv)).natTrans

/-- Invertibility of the specified inverse mate, including the empty and identity opens.
Source: Part 2, open Frobenius exchange
(blueprint: lem-zl-condensed-open-extension-local).
Proof: apply condensed_isomorphism_square_open_exchange to frobenius_square. Its horizontal
maps are the geometric Frobenius automorphisms; the mate equation identifies its map
with inverseMate. No nonemptiness hypothesis enters the argument. -/
theorem inverseMate_isIso : IsIso (inverseMate D ℓ U₀ X₀ j₀) := by
  letI : (upperStar (Profinite.padicAlgClRingObj ℓ)
      (D.geometricFrobenius U₀).hom).IsEquivalence := by infer_instance
  letI : (upperStar (Profinite.padicAlgClRingObj ℓ)
      (D.geometricFrobenius X₀).hom).IsEquivalence := by infer_instance
  exact isIso_inverseMate_of_equivalences
    (openImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ)
      (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left))
    (openImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ)
      (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left))
    (pullbackSquare D ℓ U₀ X₀ j₀).symm

/-- Exchange in the direction g_X^* j_! to j_! g_U^*, with its specified inverse mate.
Source: Part 2, induced Weil structure
(blueprint: lem-zl-condensed-open-extension-local). -/
def moduleExchange :=
  (@asIso _ _ _ _ (inverseMate D ℓ U₀ X₀ j₀)
    (inverseMate_isIso D ℓ U₀ X₀ j₀)).symm

/-- The localized termwise Frobenius exchange.
Source: Part 2, induced derived Weil structure
(blueprint: lem-zl-condensed-open-extension-local). -/
def derivedModuleExchange :=
  derivedExchange
    (openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
      (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left))
    (upperStar (Profinite.padicAlgClRingObj ℓ) (D.geometricFrobenius U₀).hom)
    (upperStar (Profinite.padicAlgClRingObj ℓ) (D.geometricFrobenius X₀).hom)
    (moduleExchange D ℓ U₀ X₀ j₀)

/-- Module extension by zero with its induced Weil structure beta followed by j_!(theta).
Source: Part 2, exact extension of Weil sheaves
(blueprint: lem-zl-condensed-open-extension-local). -/
def weilExtension := IsoAlgebra.mapOfNatIso (moduleExchange D ℓ U₀ X₀ j₀)

/-- Termwise derived extension with its induced strict Weil structure.
Source: Part 2, induced Weil structures
(blueprint: lem-zl-condensed-open-extension-local). -/
def derivedWeilExtension := IsoAlgebra.mapOfNatIso (derivedModuleExchange D ℓ U₀ X₀ j₀)


/-- Weil pullback along the open, using the inverse-image composition square.
Source: Part 2, the canonical open adjunction
(blueprint: lem-zl-condensed-open-extension-local). -/
def weilPullback := IsoAlgebra.mapOfNatIso (pullbackSquare D ℓ U₀ X₀ j₀).symm

/-- Termwise derived Weil pullback along the open.
Source: Part 2, the canonical derived open adjunction
(blueprint: lem-zl-condensed-open-extension-local). -/
def derivedWeilPullback :=
  IsoAlgebra.mapOfNatIso (derivedExchange
    (upperStar (Profinite.padicAlgClRingObj ℓ)
      (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left))
    (upperStar (Profinite.padicAlgClRingObj ℓ) (D.geometricFrobenius X₀).hom)
    (upperStar (Profinite.padicAlgClRingObj ℓ) (D.geometricFrobenius U₀).hom)
    (pullbackSquare D ℓ U₀ X₀ j₀).symm)

/-- A lift of the specified adjunction to Weil pairs with unchanged unit and counit.
This predicate expresses the two carrier equalities in abstract categories, so their
specialization does not unfold the entire concrete condensed module constructions.
Source: Part 2, normalized open unit and counit
(blueprint: lem-zl-condensed-open-extension-local). -/
def WeilAdjunctionCompatible {C : Type uC} {E : Type uD}
    [Category.{vC} C] [Category.{vD} E]
    {J : C ⥤ E} {R : E ⥤ C} {P : C ⥤ C} {Q : E ⥤ E}
    (a : J ⊣ R) (β : J ⋙ Q ≅ P ⋙ J) (α : R ⋙ P ≅ Q ⋙ R) : Prop :=
  ∃ w : IsoAlgebra.mapOfNatIso β ⊣ IsoAlgebra.mapOfNatIso α,
    (∀ K, (w.unit.app K).hom.f = a.unit.app K.carrier) ∧
    (∀ M, (w.counit.app M).hom.f = a.counit.app M.carrier)

/-- The ordinary and localized open adjunction maps are Weil morphisms with precisely
 their original carriers, as expressed by WeilAdjunctionCompatible.
Source: Part 2, normalized open unit and counit
(blueprint: lem-zl-condensed-open-extension-local).
Proof: the inverse-mate equation and adjunction triangles identify equivariance of an
arrow with equivariance of its transpose. Thus the original Hom bijection restricts to
Weil intertwiners, preserving the original unit and counit. Localize termwise using the
standard exact-functor comparisons. The same mate calculation proves equivariance of
the localized unit and counit; their carriers are the localized original maps. -/
theorem condensed_open_extension_weil_adjunction (_hℓ : ℓ ≠ D.p) :
    WeilAdjunctionCompatible
      (openImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ)
        (((Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left))
      (moduleExchange D ℓ U₀ X₀ j₀) (pullbackSquare D ℓ U₀ X₀ j₀).symm ∧
    WeilAdjunctionCompatible
      (openImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ)
        (((Over.pullback
          (Spec.map (CommRingCat.ofHom
            (algebraMap D.k₀ D.k)))).map j₀).left)).mapExactDerivedCategory
      (derivedModuleExchange D ℓ U₀ X₀ j₀)
      (derivedExchange
        (upperStar (Profinite.padicAlgClRingObj ℓ)
          (((Over.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left))
        (upperStar (Profinite.padicAlgClRingObj ℓ) (D.geometricFrobenius X₀).hom)
        (upperStar (Profinite.padicAlgClRingObj ℓ) (D.geometricFrobenius U₀).hom)
        (pullbackSquare D ℓ U₀ X₀ j₀).symm) := by
  sorry

/-- The closure has the characteristic specified by the finite-field datum.
Source: the finite-field setting of Part 2
(blueprint: lem-zl-condensed-open-extension-local).
Proof: the cardinality q=p^a with a positive and p prime implies characteristic p for k₀.
The algebra embedding into its algebraic closure preserves characteristic. -/
theorem closure_characteristic : ringChar D.k = D.p := by
  letI := Fintype.ofFinite D.k₀
  have hcard : Fintype.card D.k₀ = D.q := by
    rw [Fintype.card_eq_nat_card]
    exact D.card_base
  have hzero : (D.q : D.k₀) = 0 := by
    rw [← hcard]
    exact FiniteField.cast_card_eq_zero D.k₀
  have hpowa : (D.p : D.k₀) ^ D.a = 0 := by
    rw [← Nat.cast_pow, ← D.cardinality_eq, hzero]
  have hp0 : (D.p : D.k₀) = 0 := eq_zero_of_pow_eq_zero hpowa
  have hk₀ : ringChar D.k₀ = D.p :=
    CharP.ringChar_of_prime_eq_zero D.prime hp0
  exact (Algebra.ringChar_eq D.k₀ D.k).symm.trans hk₀

/-- The prime-characteristic instance required by the published compactification functor.
Source: the finite-field setting of Part 2
(blueprint: lem-zl-condensed-open-extension-local). -/
instance closureCharacteristicPrime : Fact (ringChar D.k).Prime :=
  ⟨(closure_characteristic D).symm ▸ D.prime⟩

/-- The coefficient characteristic separation in the published compactification interface.
Source: the ell different from p setting of Part 2
(blueprint: lem-zl-condensed-open-extension-local). -/
instance closureCharacteristicDifferent [Fact (ℓ ≠ D.p)] : Fact (ringChar D.k ≠ ℓ) :=
  ⟨fun h ↦ (Fact.out : ℓ ≠ D.p) (h.symm.trans (closure_characteristic D))⟩

/-- The chosen compact-support comparison, after inclusion into the ambient derived category.
Source: Part 2, compare the chosen compactification with (j, identity)
(blueprint: lem-zl-condensed-open-extension-local). -/
def comparison [Fact (ℓ ≠ D.p)] :=
  Functor.isoWhiskerRight
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀))
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (D.geometricFiber X₀).left)).ι ≪≫
    boundedConstructibleOpenImmersionLowerShriekCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀)

/-- The derived natural isomorphism for the chosen compact-support functor.
The specified representative of this isomorphism is comparison, constructed from the
published compactification-independence and termwise-open comparison maps.
Source: Part 2, Rj_! is termwise exact extension by zero
(blueprint: lem-zl-condensed-open-extension-local).
Proof: the open is quasi-compact since X is Noetherian. Thus (j, identity) is a
compactification, also when U is empty. Compactification independence compares the chosen
compactification with this one. The derived identity pushforward and exact module-extension
factorization identify the latter with termwise j_!. Compose these natural isomorphisms;
this is comparison. The inverse-mate square supplies its induced Weil structures. -/
theorem condensed_open_extension [Fact (ℓ ≠ D.p)] :
    Nonempty
      (boundedConstructibleLowerShriek ℓ
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀) ⋙
        (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber X₀).left)).ι ≅
        (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber U₀).left)).ι ⋙
        (openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
          (((Over.pullback
            (Spec.map (CommRingCat.ofHom
              (algebraMap D.k₀ D.k)))).map j₀).left)).mapDerivedCategory) := by
  exact ⟨comparison D ℓ U₀ X₀ j₀⟩

/-- Half-lines, bounded constructibility and the exact Weil-heart restriction.
Source: Part 2, exact extension and cohomological compatibility
(blueprint: lem-zl-condensed-open-extension-local).
Proof: module extension is exact. Its termwise localization commutes with cohomology by
exactDerivedCohomologyCoherence. Vanishing in either half-line is therefore preserved.
Extend a finite stratification by the complementary closed stratum, on which the sheaf is
zero; the same finite scalar local models work on the open. This proves constructibility.
The inverse-mate comparison moduleExchange gives the induced Weil functor, and exactness
of its underlying module functor gives preservation of kernels and cokernels of Weil maps.
The comparison with the trivial compactification transfers these assertions to Rj_!.
Empty and identity immersions require no separate hypotheses. -/
theorem condensed_open_extension_exact (_hℓ : ℓ ≠ D.p) :
    PreservesFiniteLimits (weilExtension D ℓ U₀ X₀ j₀) ∧
    PreservesFiniteColimits (weilExtension D ℓ U₀ X₀ j₀) ∧
    (∀ F : WeilConjectures.CondensedModule.Modules ℓ (D.geometricFiber U₀).left,
      IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber U₀).left) F →
      IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber X₀).left)
        ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
          (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)).obj F)) ∧
    (∀ K : DerivedCategory
        (WeilConjectures.CondensedModule.Modules ℓ (D.geometricFiber U₀).left),
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber U₀).left) K →
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber X₀).left)
        ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
          (((Over.pullback
        (Spec.map (CommRingCat.ofHom
              (algebraMap D.k₀ D.k)))).map j₀).left)).mapDerivedCategory.obj K)) ∧
    (∀ (K : DerivedCategory
        (WeilConjectures.CondensedModule.Modules ℓ (D.geometricFiber U₀).left)) (n : ℤ),
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber U₀).left) K →
      (K.IsLE n → ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
        (((Over.pullback
        (Spec.map (CommRingCat.ofHom
              (algebraMap D.k₀ D.k)))).map j₀).left)).mapDerivedCategory.obj K).IsLE n) ∧
      (K.IsGE n → ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
        (((Over.pullback
        (Spec.map (CommRingCat.ofHom
              (algebraMap D.k₀ D.k)))).map j₀).left)).mapDerivedCategory.obj K).IsGE n)) := by
  sorry


/-- Natural Weil isomorphisms between cohomology of extension and extension of cohomology.
Their carriers are precisely the inverse normalized exact-derived cohomology comparison.
Source: Part 2, cohomological compatibility
(blueprint: lem-zl-condensed-open-extension-local).
Proof: apply exactDerivedCohomologyCoherence to module extension and Frobenius pullback.
The derived exchange is the localization of moduleExchange, so this coherence equation
is exactly the equivariance of the homology comparison. Naturality gives the natural
Weil isomorphism; inverse components give its inverse. Restrict to bounded constructible
objects, using condensed_open_extension_exact, and transport across comparison for Rj_!.
This is also the fixed-pair cohomology calculation of
lem-zl-texact-fixed-pair-heart-cohomology, carried out in the module realization of the heart. -/
theorem condensed_open_extension_cohomology (_hℓ : ℓ ≠ D.p) (r : ℤ) :
    ExactWeilCohomology
      (openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
        (((Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left))
      (upperStar (Profinite.padicAlgClRingObj ℓ) (D.geometricFrobenius U₀).hom)
      (upperStar (Profinite.padicAlgClRingObj ℓ) (D.geometricFrobenius X₀).hom)
      (moduleExchange D ℓ U₀ X₀ j₀) r := by
  sorry

/-- Evaluate the actual adjunction unit through a specified inverse-image compositor.
Source: Part 2, the on-open fiber unit
(blueprint: lem-zl-condensed-open-extension-local). -/
def evaluatedUnit {C : Type uC} {E : Type uD} {V : Type uV}
    [Category.{vC} C] [Category.{vD} E] [Category.{vV} V]
    {J : C ⥤ E} {R : E ⥤ C} (a : J ⊣ R)
    (A : C ⥤ V) (B : E ⥤ V) (c : B ≅ R ⋙ A) (F : C) :
    A.obj F ⟶ B.obj (J.obj F) :=
  A.map (a.unit.app F) ≫ c.inv.app (J.obj F)

/-- Evaluate the canonical open unit at a geometric point before specializing the open.
This has the specified inverse-image compositor and ordinary unit, with an abstract immersion j.
Source: Part 2, on-open fiber identification
(blueprint: lem-zl-condensed-open-extension-local). -/
def moduleFibreUnit (k : Type u) [Field k] [IsSepClosed k]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : WeilConjectures.CondensedModule.Modules ℓ U) (z : Spec (.of k) ⟶ U) :=
  evaluatedUnit
    (openImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ) j)
    (upperStar (Profinite.padicAlgClRingObj ℓ) z ⋙ pointSections ℓ k)
    (upperStar (Profinite.padicAlgClRingObj ℓ) (z ≫ j) ⋙ pointSections ℓ k)
    (Functor.isoWhiskerRight (upperStarComp (Profinite.padicAlgClRingObj ℓ) z j)
      (pointSections ℓ k) ≪≫ Functor.associator _ _ _) F

/-- Canonical on-open fiber identification and intertwining of the actual local operators.
The equality hx only changes from the composite point to the specified equal point y.
All maps in this predicate are the ordinary unit and the existing local-return operators.
Source: Part 2, same fibers and local geometric Frobenius
(blueprint: lem-zl-condensed-open-extension-local). -/
def PointwiseOpenComparison {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (a : U ⟶ U) (b : X ⟶ X)
    (β : openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j ⋙
        upperStar (Profinite.padicAlgClRingObj ℓ) b ≅
      upperStar (Profinite.padicAlgClRingObj ℓ) a ⋙
        openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j)
    (F : WeilConjectures.condensedWeilModules (Profinite.padicAlgClRingObj ℓ) a)
    (z : Spec (.of D.k) ⟶ U) (y : Spec (.of D.k) ⟶ X) (hx : z ≫ j = y)
    (n : ℕ)
    (hy : y ≫ WeilConjectures.localPositivePower b n =
      WeilConjectures.localPositivePower (WeilConjectures.frobeniusPointIso D).hom n ≫ y) :
    Prop :=
  ∃ hret : z ≫ WeilConjectures.localPositivePower a n =
      WeilConjectures.localPositivePower (WeilConjectures.frobeniusPointIso D).hom n ≫ z,
    ∃ e : WeilConjectures.CondensedModule.fibre ℓ D F.carrier z ≅
        WeilConjectures.CondensedModule.fibre ℓ D
          ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj F.carrier) y,
      e.hom = moduleFibreUnit ℓ D.k j F.carrier z ≫ eqToHom
        (congrArg (WeilConjectures.CondensedModule.fibre ℓ D
          ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj F.carrier)) hx) ∧
      WeilConjectures.CondensedModule.operator ℓ D a F.carrier F.str z n hret ≫ e.hom =
        e.hom ≫ WeilConjectures.CondensedModule.operator ℓ D b
          ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj F.carrier)
          ((IsoAlgebra.mapOfNatIso β).obj F).str y n hy

/-- Same or zero fibres, the same residue fields, and the actual geometric local operators.
The return exponent on both sides is the degree of the image closed point minus one,
following the existing positive-power convention.
Source: Part 2, same stalks on the open and zero stalks elsewhere
(blueprint: lem-zl-condensed-open-extension-local).
Proof: internal/sectionwise transport and the ring-sheaf open base-change theorem identify
pullback of j_! with extension from the pulled-back open. Above a geometric point this open
is the identity or empty. The first case is the adjunction unit, giving moduleFibreUnit; in the
second case extension is zero, including its value on the empty object by the sheaf axiom.
The inverse-mate triangle identity says that the open unit is a Weil morphism. Iterate it
d times and apply the same return and inverse-image compositors on both sides. This proves
the displayed intertwining for the canonical operators, without using stalk conservativity.
An open immersion identifies local rings and hence residue fields, so d is unchanged.
The constructible finite-rank local model gives finite dimension of the evaluated fibre;
outside the open this also follows from its vanishing.
This proof also covers the zero sheaf, the empty open and the identity immersion. -/
theorem condensed_open_extension_fibres (_hℓ : ℓ ≠ D.p) :
    (∀ u : U₀.left, IsIso (j₀.left.residueFieldMap u)) ∧
    (∀ (F : WeilConjectures.condensedWeilModules (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFrobenius U₀).hom)
      (_hF : IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber U₀).left) F.carrier)
      (x : {x : X₀.left // x ∈ closedPoints X₀.left})
      (ι : X₀.left.residueField x.val →+* D.k)
      (hι : ι.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k),
      FiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))
        (WeilConjectures.CondensedModule.fibre ℓ D
          ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
            (((Over.pullback
              (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)).obj F.carrier)
          (WeilConjectures.localClosedPoint D X₀ x ι hι)) ∧
      (x.val ∉ Set.range j₀.left →
        IsZero (WeilConjectures.CondensedModule.fibre ℓ D
          ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
            (((Over.pullback
              (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)).obj F.carrier)
          (WeilConjectures.localClosedPoint D X₀ x ι hι))) ∧
      (∀ (z : Spec (.of D.k) ⟶ (D.geometricFiber U₀).left)
        (_hz : z ≫ (D.geometricFiber U₀).hom = 𝟙 _)
        (hx : z ≫ ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left =
          WeilConjectures.localClosedPoint D X₀ x ι hι),
        PointwiseOpenComparison D ℓ
          (((Over.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)
          (D.geometricFrobenius U₀).hom (D.geometricFrobenius X₀).hom
          (moduleExchange D ℓ U₀ X₀ j₀) F z
          (WeilConjectures.localClosedPoint D X₀ x ι hι) hx
          (WeilConjectures.localClosedPointDegree D X₀ x - 1)
          (WeilConjectures.localClosedPoint_return D X₀ x ι hι))) := by
  sorry


variable [Fact (ℓ ≠ D.p)]

/-- The compact-support strict pair, transported through the specified comparison.
The data are the canonical compactification functor and its concrete comparison, not an
arbitrary functor or a chosen Weil structure.
Source: Part 2, induced Weil structure on Rj_!
(blueprint: lem-zl-condensed-open-extension-local). -/
def compactWeilObject
    (K : IsoAlgebra (StrictWeil.action (Profinite.padicAlgClRingObj ℓ)
      (D.geometricFrobenius U₀)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (D.geometricFiber U₀).left) K.carrier) :=
  transportDerivedPair
    (openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
      (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left))
    (upperStar (Profinite.padicAlgClRingObj ℓ) (D.geometricFrobenius U₀).hom)
    (upperStar (Profinite.padicAlgClRingObj ℓ) (D.geometricFrobenius X₀).hom)
    (moduleExchange D ℓ U₀ X₀ j₀) K
    (((boundedConstructibleLowerShriek ℓ
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀)).obj
        ⟨K.carrier, hK⟩).obj)
    ((comparison D ℓ U₀ X₀ j₀).app ⟨K.carrier, hK⟩)

/-- Rj_! has the same natural Weil cohomology comparison, with its canonical carrier map.
Source: Part 2, cohomological compatibility for compact support
(blueprint: lem-zl-condensed-open-extension-local).
Proof: compare the chosen compactification to (j, identity) using comparison. Its target
is the termwise extension. The definition compactWeilObject transports exactly the induced
Weil structure, so comparison is equivariant. Compose its homology with the natural Weil
isomorphism condensed_open_extension_cohomology. This gives the displayed carrier and
naturality. The half-line and constructibility conclusions transfer along the same comparison. -/
theorem condensed_open_extension_compact_cohomology
    (K : IsoAlgebra (StrictWeil.action (Profinite.padicAlgClRingObj ℓ)
      (D.geometricFrobenius U₀)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (D.geometricFiber U₀).left) K.carrier) (r : ℤ) :
    CompactWeilCohomology
      (openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
        (((Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left))
      (upperStar (Profinite.padicAlgClRingObj ℓ) (D.geometricFrobenius U₀).hom)
      (upperStar (Profinite.padicAlgClRingObj ℓ) (D.geometricFrobenius X₀).hom)
      (moduleExchange D ℓ U₀ X₀ j₀) K
      (((boundedConstructibleLowerShriek ℓ
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀)).obj
          ⟨K.carrier, hK⟩).obj)
      ((comparison D ℓ U₀ X₀ j₀).app ⟨K.carrier, hK⟩) r := by
  sorry

/-- The canonical open adjunction for the compactification functor, transported from the
restriction of the localized module adjunction by the specified compactification comparison.
Source: Part 2, canonical open unit and counit
(blueprint: lem-zl-condensed-open-extension-local). -/
def compactOpenAdjunction :=
  (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj ℓ) ℓ
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀)).ofNatIsoLeft
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀)).symm

/-- The derived comparison identifies both adjunction maps, with their exact formulas.
Source: Part 2, canonical open unit and counit
(blueprint: lem-zl-condensed-open-extension-local).
Proof: localize the module adjunction with the exact-functor factorization comparisons.
Restriction along the fully faithful bounded-constructible inclusions retains its unit
and counit. Transport by the trivial-compactification comparison gives eta followed by
j^*(c inverse), and c followed by epsilon, respectively. These are the displayed formulas.
The inverse-mate definition of exchange makes the transpose of every equivariant map
equivariant, so the unit and counit are Weil maps as well. -/
theorem condensed_open_extension_adjunction :
    (∀ K,
      (compactOpenAdjunction D ℓ U₀ X₀ j₀).unit.app K =
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀)).unit.app
            K ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀)).map
            ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
              ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀)).inv.app
                K)) ∧
    (∀ M,
      (compactOpenAdjunction D ℓ U₀ X₀ j₀).counit.app M =
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀)).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀)).obj M) ≫
          (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
            (Profinite.padicAlgClRingObj ℓ) ℓ
            ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
              j₀)).counit.app M) := by
  constructor
  · intro K
    rfl
  · intro M
    rfl

/-- Both cohomological half-lines are preserved by the chosen compact-support functor.
Bounded constructibility is retained by its codomain, the recorded full subcategory.
Source: Part 2, t-exact extension by zero
(blueprint: lem-zl-condensed-open-extension-local).
Proof: comparison identifies the chosen compactification functor with exact termwise
extension. Its homology is extension of the original homology by the normalized comparison.
Zero cohomology remains zero, proving both assertions in every integer degree. -/
theorem condensed_open_extension_compact_exact
    (K : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (D.geometricFiber U₀).left)) (n : ℤ) :
    (K.obj.IsLE n →
      ((boundedConstructibleLowerShriek ℓ
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀)).obj
          K).obj.IsLE n) ∧
    (K.obj.IsGE n →
      ((boundedConstructibleLowerShriek ℓ
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀)).obj
          K).obj.IsGE n) := by
  let J := openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
    (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)
  let L := boundedConstructibleOpenImmersionLowerShriek
    (Profinite.padicAlgClRingObj ℓ) ℓ
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀)
  constructor
  · intro h
    letI : K.obj.IsLE n := h
    have hdirect : (L.obj K).obj.IsLE n := by
      change (J.mapDerivedCategory.obj K.obj).IsLE n
      exact J.isLE_mapDerivedCategory_obj K.obj n
    letI : DerivedCategory.TStructure.t.IsLE
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber X₀).left)).ι.obj (L.obj K)) n := by
      exact hdirect
    exact DerivedCategory.TStructure.t.isLE_of_iso
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber X₀).left)).ι.mapIso
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl
          ℓ (((Over.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀))).app K).symm) n
  · intro h
    letI : K.obj.IsGE n := h
    have hdirect : (L.obj K).obj.IsGE n := by
      change (J.mapDerivedCategory.obj K.obj).IsGE n
      exact J.isGE_mapDerivedCategory_obj K.obj n
    letI : DerivedCategory.TStructure.t.IsGE
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber X₀).left)).ι.obj (L.obj K)) n := by
      exact hdirect
    exact DerivedCategory.TStructure.t.isGE_of_iso
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber X₀).left)).ι.mapIso
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl
          ℓ (((Over.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀))).app K).symm) n

end AlgebraicGeometry.ProEtale.CondensedRing.OpenExtensionLocal
