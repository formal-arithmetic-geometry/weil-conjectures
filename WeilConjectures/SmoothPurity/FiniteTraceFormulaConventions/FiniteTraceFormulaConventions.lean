/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFiniteCohomologyComplexes
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Ring.Shrink
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteConstructibleEncoding
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteDerivedCoefficientData
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Compactification.CommonDenseRefinement
import WeilConjectures.AlgebraicGeometry.Compactification.DenseRefinementMorphisms
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
import WeilConjectures.CategoryTheory.ZetaWeil.SectionRingGlobalSections
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndSurjective
import WeilConjectures.WeilObject.Sheaf.StalkFiniteFree
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.RingTheory.Finiteness.Basic

/-! # Trace-formula conventions for arbitrary finite primary coefficients

Source: latest blueprint, def-trf-coefficient-conventions, with the binding correction
of Wei Yang, Zulip #1441, item 27 (2026-11-02)
(blueprint: def-trf-coefficient-conventions).

A finite commutative ring killed by a positive power of ell is the coefficient ring.
The DVR quotients are a distinguished family for integral reduction only. Native ordinary
module-derived categories, their full bounded constructible and finite-Tor subcategories,
and the actual compactification lower shriek are used throughout.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor

attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver
attribute [local instance] coefficientProfiniteEssentiallySmall

set_option maxHeartbeats 1600000 in
-- The finite coefficient equivalence identifies two derived module categories.
private theorem finiteAmbientEndpoints
    (B : Type) [CommRing B] [Finite B] [TopologicalSpace B]
    [DiscreteTopology B] [IsTopologicalRing B]
    {V W V' W' : Scheme.{u}} {f : V ⟶ W} {g : W' ⟶ W}
    {f' : V' ⟶ W'} {g' : V' ⟶ V} [IsProper f] [IsProper f']
    (sq : ChosenCartesianSquare g' f' f g)
    (N : DerivedCategory (FiniteDiscreteInternalModules B V))
    (hN : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj B) V) N) :
    Nonempty (
      (coefficientDerivedUpperStar (Profinite.continuousMapRingObj B) g).obj
          ((coefficientDerivedLowerStar (Profinite.continuousMapRingObj B) f).obj N) ≅
      (coefficientDerivedLowerStar (Profinite.continuousMapRingObj B) f').obj
          ((coefficientDerivedUpperStar (Profinite.continuousMapRingObj B) g').obj N)) := by
  classical
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} B
  let := heR
  obtain ⟨G, hG, hforget⟩ := internalModuleAb_equivalence (ULift.{u + 1} B)
  let := hG
  let E := finiteDiscreteCoefficientEquivalence B eR G hforget
  let J := (E V).inverse.mapDerivedCategory.obj N
  have hJ : DerivedCategory.TStructure.t.bounded J :=
    (E V).inverse.bounded_mapDerivedCategory_obj hN.1
  have hH (m : ℤ) : ProEtale.IsConstructible (ULift.{u + 1} B)
      ((DerivedCategory.homologyFunctor _ m).obj J) := by
    apply ProEtale.isConstructible_of_iso
      (((E V).inverse.mapDerivedCategoryHomologyFunctorIso m).app N)
    exact finiteDiscreteCoefficient_constructible B eR G hforget V _ (hN.2 m)
  obtain ⟨L, hL, ⟨eL⟩⟩ := ProEtale.DerivedCategory.boundedConstructible_of_homology
    (ULift.{u + 1} B) hJ (fun m ↦
      ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
        (ULift.{u + 1} B) (hH m))
  let Lplus : FiniteDiscreteEtalePlus B V := ⟨L, hL.1.1⟩
  let F := fun T : Scheme.{u} ↦ finiteDiscreteRealization B T (E T)
  let e : (F V).obj Lplus ≅ N := by
    dsimp only [F]
    unfold finiteDiscreteRealization
    exact (E V).functor.mapDerivedCategory.mapIso eL ≪≫
      (E V).mapDerivedCategory.counitIso.app N
  obtain ⟨P⟩ := finiteDiscreteCoefficient_derivedComparisonData B eR G hforget
  let Q := P.toComparisonData B
  let R := Profinite.continuousMapRingObj B
  have : IsIso (Etale.baseChange (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq.toCommSq) :=
    Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring
      (ULift.{u + 1} B) isAddTorsion_of_finite
        (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)
  let a := (coefficientDerivedUpperStar R g).mapIso ((Q.pushforward f).app Lplus).symm
  let b := ((Q.pullback g).app
    ((R+(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f)).obj Lplus)).symm
  let c := (F W').mapIso
    ((asIso (Etale.baseChange (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq.toCommSq)).app Lplus)
  let d := (Q.pushforward f').app
    ((D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g')).obj Lplus)
  let t := (coefficientDerivedLowerStar R f').mapIso ((Q.pullback g').app Lplus)
  exact ⟨(coefficientDerivedUpperStar R g).mapIso
      ((coefficientDerivedLowerStar R f).mapIso e.symm) ≪≫
    a ≪≫ b ≪≫ c ≪≫ d ≪≫ t ≪≫
    (coefficientDerivedLowerStar R f').mapIso
      ((coefficientDerivedUpperStar R g').mapIso e)⟩


-- The source lemma only exposes the Noetherian special case; its construction
-- needs exactly quasi-compactness of the open immersion.
private theorem qcOpenConstructible
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j] [QuasiCompact j]
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U))
    (hM : IsConstructibleModuleObject (condensedRingObj R U) M) :
    IsConstructibleModuleObject (condensedRingObj R V)
      ((openImmersionLowerShriek R j).obj M) := by
  obtain ⟨SU, hSU⟩ := hM
  obtain ⟨Z, i, _, hij⟩ : ∃ (Z : Scheme.{u}) (i : Z ⟶ V), IsClosedImmersion i ∧
      Set.range i.base = (Set.range j.base)ᶜ :=
    ⟨_, j.closedComplement, inferInstance, j.range_closedComplement⟩
  refine ⟨Stratification.openClosed j i hij SU (Stratification.trivial _), fun k ↦ ?_⟩
  change IsLocallyFinitelyPresented
      ((Sum.rec (motive := fun s ↦ Sum.elim SU.domain
          (Stratification.trivial Z).domain s ⟶ V)
        (fun l ↦ SU.immersion l ≫ j)
        (fun l ↦ (Stratification.trivial Z).immersion l ≫ i)
        (finSumFinEquiv.symm k))^*[Ab.{u + 1}].obj (condensedRingObj R V))
      (((Sum.rec (motive := fun s ↦ Sum.elim SU.domain
          (Stratification.trivial Z).domain s ⟶ V)
        (fun l ↦ SU.immersion l ≫ j)
        (fun l ↦ (Stratification.trivial Z).immersion l ≫ i)
        (finSumFinEquiv.symm k))^*[Ab.{u + 1}].mapMod (condensedRingObj R V)).obj
          ((openImmersionLowerShriek R j).obj M))
  generalize finSumFinEquiv.symm k = s
  rcases s with l | l
  · exact isLocallyFinitelyPresented_mapMod_comp_openImmersionLowerShriek_obj R j _ M (hSU l)
  · refine isLocallyFinitelyPresented_mapMod_openImmersionLowerShriek_obj_of_disjoint
      R j _ ?_ M
    dsimp only
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact disjoint_compl_right.mono_right ((Set.image_subset_range _ _).trans hij.le)

/-- Quasi-compact open extension preserves the generic bounded constructibility predicate.

Source: `def-exchange-projection`, closed-complement calculation, preservation of the
constructible input under open extension by zero.
(blueprint: def-trf-coefficient-conventions).

Proof: choose the finite constructible stratification of each cohomology module on U.
Quasi-compactness of the open makes the images of its constructible strata constructible
in V. Concatenate that stratification with the trivial stratification of the reduced
closed complement. On each open stratum the pullback of extension by zero is the original
module, so its local finite presentation is preserved by the composition comparison.
On the closed stratum it is zero by disjoint-support vanishing, and zero has a finite
presentation of rank zero. Thus every extended cohomology module is constructible.
The exact extension functor preserves boundedness and identifies its cohomology with
extension of the original cohomology, proving the derived assertion. This works for
empty opens or complements, the zero coefficient ring, and the identity immersion. -/
private theorem boundedConstructible_openExtension_of_quasiCompact
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategory
      (Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U)))
    (hK : boundedConstructible (condensedRingObj R U) K) :
    boundedConstructible (condensedRingObj R V)
      ((openImmersionLowerShriek R j).mapDerivedCategory.obj K) := by
  refine ⟨(openImmersionLowerShriek R j).bounded_mapDerivedCategory_obj hK.1, ?_⟩
  intro m
  apply IsConstructibleModuleObject.of_iso
    (((openImmersionLowerShriek R j).mapDerivedCategoryHomologyFunctorIso m).app K)
  exact qcOpenConstructible R j _ (hK.2 m)


private theorem finiteRefinementMap_isIso
    (B : Type) [CommRing B] [Finite B] [TopologicalSpace B]
    [DiscreteTopology B] [IsTopologicalRing B]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj B) X)))
    (hK : boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj B) X) K) :
    IsIso (localizingRefinementMap (Profinite.continuousMapRingObj B) r K) := by
  let Λ := Profinite.continuousMapRingObj.{u} B
  have : QuasiCompact c.obj.obj.i := c.obj.property
  have : QuasiCompact d.obj.obj.i := d.obj.property
  let i := c.obj.obj.i.closedComplement
  let h := r.hom.hom.hom
  let J := (openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory
  have hdis : Disjoint (Set.range d.obj.obj.i.base)
      (Set.range (pullback.fst h i).base) := by
    rw [Set.disjoint_left]
    rintro x ⟨y, rfl⟩ ⟨z, hz⟩
    have him : h.base (d.obj.obj.i.base y) ∈ Set.range c.obj.obj.i.base :=
      ⟨y, (congrArg (fun v : X ⟶ c.obj.obj.Z ↦ v.base y) r.hom.hom.i_hom).symm⟩
    have hcm : h.base (d.obj.obj.i.base y) ∈ Set.range i.base := by
      rw [← hz]
      exact ⟨(pullback.snd h i).base z,
        (congrArg (fun v : pullback h i ⟶ c.obj.obj.Z ↦ v.base z)
          (pullback.condition (f := h) (g := i))).symm⟩
    rw [Scheme.Hom.range_closedComplement] at hcm
    exact hcm him
  have hz := isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint
    Λ d.obj.obj.i (pullback.fst h i) hdis K
  have hzout := ((lowerStar Λ (pullback.snd h i)).rightDerivedFunctor).map_isZero hz
  have hN := boundedConstructible_openExtension_of_quasiCompact Λ d.obj.obj.i K hK
  obtain ⟨e⟩ := finiteAmbientEndpoints B
    (f := h) (g := i) (g' := pullback.fst h i) (f' := pullback.snd h i)
    { w := pullback.condition
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ } (J.obj K) hN
  have hztgt := hzout.of_iso e
  have hij : IsCompl (Set.range i.base) (Set.range c.obj.obj.i.base) := by
    dsimp only [i]
    rw [Scheme.Hom.range_closedComplement]
    exact isCompl_compl.symm
  apply (jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl Λ i
    c.obj.obj.i hij).isIso_of_pairFunctor (localizingRefinementMap Λ r K)
  · apply (NatIso.isIso_map_iff
      (leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.i) _).2
    let a := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i
    let ρ := (refinementOpenRestriction Λ r.hom.hom).app (J.obj K)
    have : IsIso ρ := by
      have := refinementOpenRestriction_isIso Λ r
      dsimp only [ρ]
      infer_instance
    have he := localizingRefinementMap_normalized Λ r K
    have : IsIso (a.unit.app K ≫
        (upperStar Λ c.obj.obj.i).mapDerivedCategory.map
          (localizingRefinementMap Λ r K) ≫ ρ) := by
      rw [he]
      infer_instance
    have : IsIso ((upperStar Λ c.obj.obj.i).mapDerivedCategory.map
        (localizingRefinementMap Λ r K) ≫ ρ) :=
      IsIso.of_isIso_comp_left (a.unit.app K) _
    exact IsIso.of_isIso_comp_right _ ρ
  · have hzsrc := isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint
      Λ c.obj.obj.i i hij.symm.disjoint K
    exact hzsrc.isIso hztgt _

private theorem finiteRefinementComponent_isIso
    (B : Type) [CommRing B] [Finite B] [TopologicalSpace B]
    [DiscreteTopology B] [IsTopologicalRing B]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj B) X)))
    (hK : boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj B) X) K) :
    IsIso (compactificationRefinementComponent (Profinite.continuousMapRingObj B) r K) := by
  let Λ := Profinite.continuousMapRingObj.{u} B
  have := finiteRefinementMap_isIso B r K hK
  unfold compactificationRefinementComponent
  exact isIso_map_comp_natIso (lowerStar Λ c.obj.obj.g).rightDerivedFunctor
    (lowerStar Λ r.hom.hom.hom).rightDerivedFunctor
    (lowerStar Λ (r.hom.hom.hom ≫ c.obj.obj.g)).rightDerivedFunctor
    (lowerStar Λ d.obj.obj.g).rightDerivedFunctor
    (refinementDerivedLowerStarComp Λ r.hom.hom.hom c.obj.obj.g)
    (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ r.hom.hom.hom_g))
    ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K)
    (localizingRefinementMap Λ r K)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem finiteRefinementComponent_naturality
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (a : K ⟶ L) :
    (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).map a ≫
        compactificationRefinementComponent Λ r L =
      compactificationRefinementComponent Λ r K ≫
        (rightDerivedLowerShriekOfCompactification Λ d.obj.obj).map a := by
  let eta : (openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory ⟶
      (openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory ⋙
        (lowerStar Λ r.hom.hom.hom).rightDerivedFunctor :=
    { app := fun K ↦ localizingRefinementMap Λ r K
      naturality := fun _ _ a ↦ refinementMap_naturality Λ r a }
  let τ := Functor.whiskerRight eta (lowerStar Λ c.obj.obj.g).rightDerivedFunctor ≫
    (Functor.associator (openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory
      (lowerStar Λ r.hom.hom.hom).rightDerivedFunctor
      (lowerStar Λ c.obj.obj.g).rightDerivedFunctor).hom ≫
    Functor.whiskerLeft (openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory
      ((refinementDerivedLowerStarComp Λ r.hom.hom.hom c.obj.obj.g).inv ≫
        (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ r.hom.hom.hom_g)).hom)
  simpa only [τ, eta, compactificationRefinementComponent, compactificationLocalizingCandidate,
    rightDerivedLowerShriekOfCompactification, Functor.comp_map, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp, ObjectProperty.ι_obj, ObjectProperty.ι_map] using τ.naturality a

end AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures

/-- The global finite-field datum, a prime different from its characteristic prime,
any finite commutative ell-primary ring, and a separated finite-type base scheme.
No coefficient extension, uniformizer, flatness or projective dimension is assumed.
Source: latest blueprint, def-trf-coefficient-conventions, and Wei Yang #1441, item 27
(blueprint: def-trf-coefficient-conventions). -/
structure FiniteTraceFormulaConventions where
  datum : FiniteFieldDatum.{u}
  ell : ℕ
  [ell_prime : Fact ell.Prime]
  ell_ne : ell ≠ datum.p
  A : Type u
  [commRing : CommRing A]
  [finite : Finite A]
  primary : ∃ N : ℕ, 1 ≤ N ∧ (ell ^ N : ℕ) • (1 : A) = 0
  X₀ : Over (Spec (.of datum.k₀))
  [finite_type : LocallyOfFiniteType X₀.hom]
  [quasi_compact : QuasiCompact X₀.hom]
  [separated : IsSeparated X₀.hom]

attribute [instance] FiniteTraceFormulaConventions.ell_prime
  FiniteTraceFormulaConventions.commRing FiniteTraceFormulaConventions.finite
  FiniteTraceFormulaConventions.finite_type FiniteTraceFormulaConventions.quasi_compact
  FiniteTraceFormulaConventions.separated

namespace FiniteTraceFormulaConventions

/-- The geometric base change, including its structure morphism to Spec k.
Source: latest blueprint, X = X₀ ×_{k₀} k
(blueprint: def-trf-coefficient-conventions). -/
abbrev geometricScheme (T : FiniteTraceFormulaConventions.{u}) :=
  T.datum.geometricFiber T.X₀

/-- The discrete condensed ring A. Shrinking only supplies the Type 0 presentation
required by the upstream continuous-map API; Shrink.ringEquiv retains the original A.
Source: latest blueprint, A as a discrete condensed ring
(blueprint: def-trf-coefficient-conventions). -/
abbrev coefficients (T : FiniteTraceFormulaConventions.{u}) :=
  letI : TopologicalSpace (Shrink.{0} T.A) := ⊥
  letI : DiscreteTopology (Shrink.{0} T.A) := ⟨rfl⟩
  Profinite.continuousMapRingObj.{u} (Shrink.{0} T.A)

/-- The commutative multiplication on the discrete condensed coefficient ring.
Source: latest blueprint, the ring structure of A
(blueprint: def-trf-coefficient-conventions). -/
instance coefficients_comm (T : FiniteTraceFormulaConventions.{u}) :
    IsCommMonObj T.coefficients := by
  let : TopologicalSpace (Shrink.{0} T.A) := ⊥
  let : DiscreteTopology (Shrink.{0} T.A) := ⟨rfl⟩
  exact Profinite.isCommMonObj_continuousMapRingObj _

/-- A_Y = p_Y^* A, using the existing monoidal coefficient pullback.
Source: latest blueprint, pulled-back coefficients
(blueprint: def-trf-coefficient-conventions). -/
abbrev coefficientSheaf (T : FiniteTraceFormulaConventions.{u}) (Y : Scheme.{u}) :=
  condensedRingObj T.coefficients Y

/-- The canonical finite-coefficient comparison with ordinary constant-ring module sheaves.
This also applies when A is a DVR quotient; the same constant-section map normalizes it.
Source: latest blueprint, finite discrete coefficients and integral-reduction agreement
(blueprint: def-trf-coefficient-conventions). -/
abbrev finiteModelComparison (T : FiniteTraceFormulaConventions.{u}) (Y : Scheme.{u}) :=
  letI : TopologicalSpace (Shrink.{0} T.A) := ⊥
  letI : DiscreteTopology (Shrink.{0} T.A) := ⟨rfl⟩
  finiteCoefficientDerivedEquivalence Y (Shrink.{0} T.A)

/-- The ordinary unbounded derived category of A_Y-module objects.
Source: latest blueprint, ordinary module-derived categories
(blueprint: def-trf-coefficient-conventions). -/
abbrev Complexes (T : FiniteTraceFormulaConventions.{u}) (Y : Scheme.{u}) :=
  DerivedCategory
    (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (T.coefficientSheaf Y))

/-- The recorded bounded constructible property, with all ambient derived morphisms.
For finite discrete coefficients local finite presentation means locally constant finite
module stalks on a finite locally closed constructible stratification.
Source: latest blueprint, D^b_c(Y,A)
(blueprint: def-trf-coefficient-conventions). -/
abbrev constructible (T : FiniteTraceFormulaConventions.{u}) (Y : Scheme.{u}) :=
  boundedConstructible (T.coefficientSheaf Y)

/-- The additional finite-Tor condition, with no identification with D^b_c.
Source: latest blueprint, D^b_ctf(Y,A)
(blueprint: def-trf-coefficient-conventions). -/
abbrev constructibleFiniteTor (T : FiniteTraceFormulaConventions.{u}) (Y : Scheme.{u}) :=
  condensedConstructibleFiniteTor T.coefficients Y

/-- Ordinary coefficient complexes with bounded finite cohomology.
Source: latest blueprint, D^b_fin(A)
(blueprint: def-trf-coefficient-conventions). -/
abbrev finiteCohomology (T : FiniteTraceFormulaConventions.{u}) :=
  DerivedCategory.pointFiniteCohomology (ULift.{u + 1} T.A)

/-- Constant sections, with the canonical ring equivalences that undo the size changes.
Source: latest blueprint, the canonical A-action by constant sections
(blueprint: def-trf-coefficient-conventions). -/
def constantScalars (T : FiniteTraceFormulaConventions.{u}) :
    ULift.{u + 1} T.A →+* Γ T.coefficients :=
  letI : TopologicalSpace (Shrink.{0} T.A) := ⊥
  letI : DiscreteTopology (Shrink.{0} T.A) := ⟨rfl⟩
  (Profinite.continuousMapConstRingHom (Shrink.{0} T.A)).comp
    ((Shrink.ringEquiv.{0} T.A : Shrink.{0} T.A ≃+* T.A).symm.toRingHom.comp
      (ULift.ringEquiv : ULift.{u + 1} T.A ≃+* T.A).toRingHom)

/-- Derived terminal evaluation with precisely the constant-section A-action.
This is the recorded point-section functor followed by exact scalar restriction.
Source: latest blueprint, Fib_s
(blueprint: def-trf-coefficient-conventions). -/
def pointFiber (T : FiniteTraceFormulaConventions.{u}) :
    T.Complexes (Spec (.of T.datum.k)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} T.A)) :=
  (condensedRingCoefficientSections T.coefficients
    (Spec (.of T.datum.k))).rightDerivedFunctor ⋙
      (ModuleCat.restrictScalars T.constantScalars :
        ModuleCat.{u + 1} (Γ T.coefficients) ⥤
          ModuleCat.{u + 1} (ULift.{u + 1} T.A)).mapDerivedCategory

set_option maxHeartbeats 1600000 in
-- The finite-coefficient comparison imports enlarge the point-section instance search.
set_option synthInstance.maxHeartbeats 200000 in
/-- Evaluation of bounded constructible point complexes has bounded finite cohomology.
Source: latest blueprint, Fib_s : D^b_c(s,A) -> D^b_fin(A)
(blueprint: def-trf-coefficient-conventions).
Proof: the geometric point is algebraically closed, so every cover of its final object
splits and terminal evaluation is exact. A constructible sheaf is locally a finite
A-module; pulling a trivialization back along a section makes it globally such a module.
Thus evaluation commutes with cohomology, preserves its finite support and has finite
cohomology modules. The constant-section action is unchanged by the two ring equivalences.
No DVR quotient, self-injectivity or finite projective dimension is used. -/
theorem pointFiber_finite (T : FiniteTraceFormulaConventions.{u})
    (K : (T.constructible (Spec (.of T.datum.k))).FullSubcategory) :
    T.finiteCohomology (T.pointFiber.obj K.obj) := by
  classical
  let : IsAlgClosed T.datum.k := IsAlgClosure.isAlgClosed T.datum.k₀
  let S := Spec (.of T.datum.k)
  let F := condensedRingCoefficientSections T.coefficients S
  let G : ModuleCat.{u + 1} (Γ T.coefficients) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} T.A) := ModuleCat.restrictScalars T.constantScalars
  let : PreservesFiniteLimits F := (finite_point_sections_exact T.coefficients T.datum.k).1
  let : PreservesFiniteColimits F := (finite_point_sections_exact T.coefficients T.datum.k).2
  let H := F ⋙ G
  let : PreservesFiniteColimits G := inferInstance
  let hH : PreservesFiniteColimits H := comp_preservesFiniteColimits F G
  let : PreservesColimitsOfShape WalkingParallelPair H :=
    @PreservesFiniteColimits.preservesFiniteColimits _ _ _ _ H hH WalkingParallelPair _ _
  have finite_regular : Finite (H.obj (Mod.regular (T.coefficientSheaf S))) := by
    let : TopologicalSpace (Shrink.{0} T.A) := ⊥
    let : DiscreteTopology (Shrink.{0} T.A) := ⟨rfl⟩
    have : Finite (Γ T.coefficients) :=
      Finite.of_surjective _ (Profinite.continuousMapConstRingHom_surjective (Shrink.{0} T.A))
    let U := upperStarFromPoint S
    let := Functor.additive_of_preserves_binary_products U
    have h := InternalAbelianSheafModule.globalMapFunctor_bijective U
      (Functor.FullyFaithful.ofFullyFaithful U) T.coefficients
    have : Finite (Γ (T.coefficientSheaf S)) := Finite.of_surjective _ h.2
    exact Finite.of_surjective _ Mod.regularEndRingHom_surjective
  have finite_sections (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (T.coefficientSheaf S)) (hM : IsConstructibleModuleObject (T.coefficientSheaf S) M) :
      Finite (H.obj M) := by
    have hp := isFinitelyPresented_upperStar_of_isConstructibleModuleObject
      T.coefficients (Field.toIsField T.datum.k) IsField.isSepClosed_toField hM (𝟙 S)
    have hp' := hp.of_iso ((upperStarId T.coefficients S).app M)
    obtain ⟨n, m, f, ⟨e⟩⟩ := hp'
    let : PreservesColimit (parallelPair f 0) H :=
      PreservesColimitsOfShape.preservesColimit
    have : HasCokernel (H.map f) :=
      HasColimit.mk ⟨_, ModuleCat.cokernelIsColimit (H.map f)⟩
    let b := H.mapBiproduct (fun _ : Fin n ↦ Mod.regular (T.coefficientSheaf S)) ≪≫
      ModuleCat.biproductIsoPi (fun _ : Fin n ↦ H.obj (Mod.regular (T.coefficientSheaf S)))
    have : Module.Finite (ULift.{u + 1} T.A)
        (H.obj (Mod.finiteFree (T.coefficientSheaf S) n)) :=
      Module.Finite.equiv b.toLinearEquiv.symm
    have : Module.Finite (ULift.{u + 1} T.A)
        (cokernel (H.map f) : ModuleCat.{u + 1} (ULift.{u + 1} T.A)) :=
      Module.Finite.equiv (ModuleCat.cokernelIsoRangeQuotient (H.map f)).toLinearEquiv.symm
    have : Module.Finite (ULift.{u + 1} T.A)
        (H.obj M) :=
      Module.Finite.equiv (H.mapIso e ≪≫ PreservesCokernel.iso H f).toLinearEquiv.symm
    exact Module.finite_of_finite (ULift.{u + 1} T.A)
  let e (i : ℤ) :=
    G.mapIso ((F.rightDerivedFunctorHomologyFunctorIso i).app K.obj) ≪≫
      (G.mapDerivedCategoryHomologyFunctorIso i).app (F.rightDerivedFunctor.obj K.obj)
  obtain ⟨⟨a, b, hz⟩, hc⟩ := (mem_boundedConstructible_iff _ _).mp K.property
  constructor
  · refine ⟨Finset.Icc a b, fun i hi ↦ ?_⟩
    have hi' : i < a ∨ b < i := by simpa only [Finset.mem_Icc, not_and_or, not_le] using hi
    exact IsZero.of_iso (H.map_isZero (hz i hi')) (e i).symm
  · intro i
    exact (e i).toLinearEquiv.toEquiv.finite_iff.mp (finite_sections _ (hc i))

/-- The specified point fibre with its finite ordinary coefficient codomain.
Source: latest blueprint, Fib_s on bounded constructible objects
(blueprint: def-trf-coefficient-conventions). -/
def boundedPointFiber (T : FiniteTraceFormulaConventions.{u}) :=
  T.finiteCohomology.lift
    ((T.constructible (Spec (.of T.datum.k))).ι ⋙ T.pointFiber) T.pointFiber_finite

/-- The recorded derived module pullback along any scheme morphism.
Source: latest blueprint, derived pullback
(blueprint: def-trf-coefficient-conventions). -/
abbrev pullback (T : FiniteTraceFormulaConventions.{u})
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) :=
  (upperStar T.coefficients f).leftDerivedFunctor

/-- The actual relative derived tensor product on ordinary module-derived categories.
Source: latest blueprint, derived tensor
(blueprint: def-trf-coefficient-conventions). -/
abbrev tensor (T : FiniteTraceFormulaConventions.{u}) (Y : Scheme.{u}) :=
  derivedTensor T.coefficients Y

/-- The actual derived internal Hom, contravariant in its first variable.
Source: latest blueprint, derived internal Hom
(blueprint: def-trf-coefficient-conventions). -/
abbrev internalHom (T : FiniteTraceFormulaConventions.{u}) (Y : Scheme.{u}) :=
  derivedHom T.coefficients Y

/-- Ordinary cohomology sheaves in every integer degree.
Source: latest blueprint, H^i
(blueprint: def-trf-coefficient-conventions). -/
abbrev cohomologySheaf (T : FiniteTraceFormulaConventions.{u})
    (Y : Scheme.{u}) (i : ℤ) :=
  DerivedCategory.homologyFunctor
    (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (T.coefficientSheaf Y)) i

/-- RΓ_c(X,-) = Fib_s(Ra_X! -), using exact open extension and proper derived image.
The compactification specifies the representative of the existing lower shriek.
The scalar action is exactly restriction along constantScalars, as for pointFiber.
Source: latest blueprint, the RΓ_c display
(blueprint: def-trf-coefficient-conventions). -/
def compactSupportComplex (T : FiniteTraceFormulaConventions.{u})
    (c : Compactification T.geometricScheme.hom) :
    T.Complexes T.geometricScheme.left ⥤
      DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} T.A)) :=
  condensedRingCompactCoefficientComplex T.coefficients c ⋙
    (ModuleCat.restrictScalars T.constantScalars :
        ModuleCat.{u + 1} (Γ T.coefficients) ⥤
          ModuleCat.{u + 1} (ULift.{u + 1} T.A)).mapDerivedCategory

/-- The compact-support functor with its bounded constructible source.
Source: latest blueprint, K in D^b_c(X,A) in the compact-support display
(blueprint: def-trf-coefficient-conventions). -/
abbrev constructibleCompactSupport (T : FiniteTraceFormulaConventions.{u})
    (c : Compactification T.geometricScheme.hom) :=
  (T.constructible T.geometricScheme.left).ι ⋙ T.compactSupportComplex c

/-- The compactification comparisons are uniquely specified by the canonical refinement
maps, including for inputs without finite Tor amplitude. They are therefore data fixed
by the geometry, rather than arbitrary isomorphisms between coefficient complexes.
Source: latest blueprint, the specified compactification comparisons
(blueprint: def-trf-coefficient-conventions).
Proof: compare exact extension by zero followed by proper derived image along a common
dense refinement. The refinement arrow is the open-adjunction unit mate followed by the
canonical derived compositor, namely compactificationRefinementComponent. For finite
discrete coefficients it is invertible on bounded constructible inputs by finite-ring
etale descent and proper/open interchange. Point evaluation and constant scalar
restriction preserve these maps and their inverses. Common dense refinements exist,
and any two are dominated by a third; equality of the refined open-unit maps proves
independence and uniqueness. The same calculation gives identity and cocycle. This
argument does not require the input to be perfect over Z/ell^N or A to be self-injective. -/
theorem compactSupportComparisons_unique (T : FiniteTraceFormulaConventions.{u}) :
    ∃! phi : ∀ c d : Compactification.BoundaryCompactification T.geometricScheme.hom,
      T.constructibleCompactSupport c.obj.obj ≅ T.constructibleCompactSupport d.obj.obj,
      ∀ (c d : Compactification.BoundaryCompactification T.geometricScheme.hom)
        (e : Compactification.DenseBoundaryCompactification T.geometricScheme.hom)
        (hc : e.obj ⟶ c) (hd : e.obj ⟶ d)
        (K : (T.constructible T.geometricScheme.left).FullSubcategory),
        (phi c d).hom.app K ≫
            T.pointFiber.map (compactificationRefinementComponent T.coefficients hd K.obj) =
          T.pointFiber.map (compactificationRefinementComponent T.coefficients hc K.obj) := by
  classical
  let : TopologicalSpace (Shrink.{0} T.A) := ⊥
  let : DiscreteTopology (Shrink.{0} T.A) := ⟨rfl⟩
  have hΛ : IsLocalizingAdmissibleCoefficient T.ell T.coefficients := by
    refine Or.inl ⟨Shrink.{0} T.A, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, ?_, ⟨Iso.refl _⟩⟩
    obtain ⟨n, _, hn⟩ := T.primary
    refine ⟨n, fun a ↦ ?_⟩
    have hn' : (T.ell ^ n : Shrink.{0} T.A) = 0 := by
      apply (Shrink.ringEquiv.{0} T.A).injective
      simpa only [map_pow, map_natCast, map_zero, nsmul_eq_mul, _root_.mul_one,
        Nat.cast_pow] using hn
    rw [nsmul_eq_mul, Nat.cast_pow, hn', zero_mul]
  let f := T.geometricScheme.hom
  have : LocallyOfFiniteType f := by
    dsimp [f, geometricScheme, FiniteFieldDatum.geometricFiber]
    infer_instance
  have : QuasiCompact f := by
    dsimp [f, geometricScheme, FiniteFieldDatum.geometricFiber]
    infer_instance
  have : IsSeparated f := by
    dsimp [f, geometricScheme, FiniteFieldDatum.geometricFiber]
    infer_instance
  let P (c : Compactification.BoundaryCompactification f) : Prop :=
    IsSchemeTheoreticallyDominant c.obj.obj.i
  let F (c : Compactification.BoundaryCompactification f) :=
    T.constructibleCompactSupport c.obj.obj
  let ρ {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c) : F c ⟶ F d :=
    { app := fun K ↦ T.pointFiber.map
        (compactificationRefinementComponent T.coefficients r K.obj)
      naturality := by
        intro K L a
        change T.pointFiber.map
            ((rightDerivedLowerShriekOfCompactification T.coefficients c.obj.obj).map a.hom) ≫
            T.pointFiber.map (compactificationRefinementComponent T.coefficients r L.obj) =
          T.pointFiber.map (compactificationRefinementComponent T.coefficients r K.obj) ≫
            T.pointFiber.map
              ((rightDerivedLowerShriekOfCompactification T.coefficients d.obj.obj).map a.hom)
        rw [← T.pointFiber.map_comp, ← T.pointFiber.map_comp]
        exact congrArg T.pointFiber.map
          (finiteRefinementComponent_naturality T.coefficients r a.hom) }
  have hcomp {c d e : Compactification.BoundaryCompactification f}
      (r : d ⟶ c) (s : e ⟶ d) : ρ (s ≫ r) = ρ r ≫ ρ s := by
    ext K
    change T.pointFiber.map _ = T.pointFiber.map _ ≫ T.pointFiber.map _
    rw [← T.pointFiber.map_comp, refinementComponent_comp T.coefficients T.ell hΛ]
  have hiso {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c) :
      IsIso (ρ r) := by
    have (K : (T.constructible T.geometricScheme.left).FullSubcategory) :
        IsIso ((ρ r).app K) := by
      have := finiteRefinementComponent_isIso (Shrink.{0} T.A) r K.obj K.property
      change IsIso (T.pointFiber.map _)
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  have hcommon (c d : Compactification.BoundaryCompactification f) :
      ∃ e : Compactification.BoundaryCompactification f,
        P e ∧ Nonempty (e ⟶ c) ∧ Nonempty (e ⟶ d) := by
    rcases Compactification.exists_common_dense_refinement.{u, u} f c.obj.obj d.obj.obj with
      ⟨_, _, hqc, hd, _, _, _, _, _, _, _, h₁, h₂, _⟩
    let e : Compactification.BoundaryCompactification f :=
      ⟨⟨Compactification.inf c.obj.obj d.obj.obj, hqc⟩⟩
    refine ⟨e, hd, ⟨?_⟩, ⟨?_⟩⟩
    · exact ⟨ObjectProperty.homMk (Compactification.infFst c.obj.obj d.obj.obj), h₁⟩
    · exact ⟨ObjectProperty.homMk (Compactification.infSnd c.obj.obj d.obj.obj), h₂⟩
  have hthin {d : Compactification.BoundaryCompactification f} (hd : P d)
      (c : Compactification.BoundaryCompactification f) : Subsingleton (d ⟶ c) := by
    constructor
    intro a b
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    apply Compactification.Refinement.ext
    exact ((denseCompactification_refinement_morphisms d.obj c.obj hd
      a.hom.hom.hom a.hom.hom.hom_g a.hom.hom.i_hom).2.2
        b.hom.hom.hom b.hom.hom.hom_g b.hom.hom.i_hom).symm
  obtain ⟨φ, hn, _, _⟩ := comparisons_of_refinements P F ρ
    (fun r s ↦ hcomp r s) (fun _ r ↦ hiso r) hcommon hthin
  refine ⟨φ, ?_, ?_⟩
  · intro c d e hc hd K
    exact congrArg (fun t ↦ t.app K) (hn c d e.obj e.property hc hd)
  · intro ψ hψ
    funext c d
    obtain ⟨e, he, ⟨hc⟩, ⟨hd⟩⟩ := hcommon c d
    let e' : Compactification.DenseBoundaryCompactification f := ⟨e, he⟩
    apply Iso.ext
    ext K
    let : IsIso (ρ hd) := hiso hd
    let : IsIso ((ρ hd).app K) := NatIso.isIso_app_of_isIso (ρ hd) K
    apply (cancel_mono ((ρ hd).app K)).1
    exact (hψ c d e' hc hd K).trans
      (congrArg (fun t ↦ t.app K) (hn c d e he hc hd)).symm

/-- The unique common-refinement-normalized compactification comparison.
Only the proof is postponed: the characterization determines the whole family uniquely.
Source: latest blueprint, specified compactification comparisons
(blueprint: def-trf-coefficient-conventions). -/
def compactSupportComparison (T : FiniteTraceFormulaConventions.{u})
    (c d : Compactification.BoundaryCompactification T.geometricScheme.hom) :
    T.constructibleCompactSupport c.obj.obj ≅ T.constructibleCompactSupport d.obj.obj :=
  T.compactSupportComparisons_unique.exists.choose c d

/-- H_c^i is ordinary cohomology of the specified compact-support coefficient complex.
Source: latest blueprint, the H_c display
(blueprint: def-trf-coefficient-conventions). -/
def compactSupportCohomology (T : FiniteTraceFormulaConventions.{u})
    (c : Compactification T.geometricScheme.hom) (i : ℤ) :=
  T.compactSupportComplex c ⋙ DerivedCategory.homologyFunctor _ i

/-- The distinguished DVR-quotient family, used only when making integral reductions.
The extension lies inside the fixed PadicAlgCl; the uniformizer condition and positive
level are explicit. None of these data occurs in FiniteTraceFormulaConventions.
Source: latest blueprint, A_{E,n} = O_E / pi_E^n
(blueprint: def-trf-coefficient-conventions). -/
abbrev integralReductionRing (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (pi : {x : PadicAlgCl.integers ell E //
      Ideal.span {x} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E)})
    (n : ℕ+) :=
  PadicAlgCl.integers ell E ⧸ (Ideal.span {pi.val}) ^ (n : ℕ)

end FiniteTraceFormulaConventions
end WeilConjectures
