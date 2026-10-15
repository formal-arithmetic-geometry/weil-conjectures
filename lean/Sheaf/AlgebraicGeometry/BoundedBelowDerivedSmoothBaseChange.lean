/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
import Sheaf.AlgebraicGeometry.BoundedBelowTruncationCriterion
import Sheaf.AlgebraicGeometry.BoundedAllowableTorsionSmoothBaseChange
import Sheaf.AlgebraicGeometry.AllowableTorsionInverseImage
import Sheaf.AlgebraicGeometry.QcqsHigherImagesPrimeTorsion

/-!
# Bounded-below derived smooth base change

Source: blueprint, sec-smooth-base-change, sk-rem-rest, order 1440
(blueprint: sbc-thm-bounded-below-derived-smooth-base-change).

The conclusion includes membership of both images in the full allowable-torsion
subcategory as well as invertibility of the specified canonical exchange arrow.
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory

private lemma allowable_iso {Z : Scheme.{u}} {P : Set ℕ}
    {F G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}} (i : F ≅ G)
    (hF : allowableTorsionSheafProperty Z P F) : allowableTorsionSheafProperty Z P G := by
  intro Ω _ _ s x
  let j := (Scheme.pointSmallEtale s).sheafFiber.mapIso i
  obtain ⟨n, hn, hp, hx⟩ := hF Ω s (j.inv.hom x)
  refine ⟨n, hn, hp, ?_⟩
  have he : j.hom.hom (j.inv.hom x) = x := by
    change (j.inv ≫ j.hom).hom x = x
    simp
  rw [← he, ← map_nsmul, hx, map_zero]

private lemma allowable_zero {Z : Scheme.{u}} {P : Set ℕ}
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : Limits.IsZero F) :
    allowableTorsionSheafProperty Z P F := by
  intro Ω _ _ s x
  have : ((Scheme.pointSmallEtale s).sheafFiber
      (A := AddCommGrpCat.{u + 1})).IsLeftAdjoint :=
    ((Scheme.pointSmallEtale s).skyscraperSheafAdjunction
      (A := AddCommGrpCat.{u + 1})).isLeftAdjoint
  have : ((Scheme.pointSmallEtale s).sheafFiber
      (A := AddCommGrpCat.{u + 1})).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have hz := (Scheme.pointSmallEtale s).sheafFiber.map_isZero hF
  have hx : x = 0 := AddCommGrpCat.isZero_iff_subsingleton.mp hz |>.elim _ _
  refine ⟨1, by omega, ?_, by simp [hx]⟩
  intro p hp hd
  exact False.elim (hp.ne_one (Nat.dvd_one.mp hd))

private lemma abelian_exchange_naturality
    {X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T}
    {f : X ⟶ S} {g : T ⟶ S} (sq : ChosenCartesianSquare h e f g)
    {K L : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (v : K ⟶ L) :
    D(upperStar AddCommGrpCat.{u + 1} f).map
        (R(lowerStar AddCommGrpCat.{u + 1} g).map v) ≫
      abelianDerivedBaseChangeArrow sq L = abelianDerivedBaseChangeArrow sq K ≫
        R(lowerStar AddCommGrpCat.{u + 1} h).map
          (D(upperStar AddCommGrpCat.{u + 1} e).map v) := by
  exact (abelianDerivedBaseChangeTransformation sq).naturality v

private lemma rightDerived_isGE {U V : Scheme.{u}} (g : U ⟶ V)
    (K : DerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (a : ℤ) [K.IsGE a] :
    (R(lowerStar AddCommGrpCat.{u + 1} g).obj K).IsGE a := by
  let L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    ⟨K, ⟨a, inferInstance⟩⟩
  have : L.IsGE a := (L.isGE_ι_obj_iff a).1 (show K.IsGE a from inferInstance)
  refine (DerivedCategory.isGE_iff _ a).2 fun q hq ↦ ?_
  exact (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
    (lowerStar AddCommGrpCat.{u + 1} g) L a hq).of_iso
    ((DerivedCategory.homologyFunctor _ q).mapIso
      ((lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlusCompatibility.app L)).symm

private lemma allowable_derived_upperStar {U V : Scheme.{u}} (f : U ⟶ V) (P : Set ℕ)
    (K : DerivedCategory (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : allowableTorsionPlusProperty V P K) :
    allowableTorsionPlusProperty U P (D(upperStar AddCommGrpCat.{u + 1} f).obj K) := by
  constructor
  · intro n
    exact allowable_iso
      (((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryHomologyFunctorIso n).app K)
      (allowable_upperStar f P _ (hK.1 n))
  · obtain ⟨a, ha⟩ := hK.2
    have : K.IsGE a := ha
    exact ⟨a, (upperStar AddCommGrpCat.{u + 1} f).isGE_mapDerivedCategory_obj K a⟩

private lemma allowable_single_directImage {U V : Scheme.{u}} (g : U ⟶ V)
    [QuasiCompact g] [QuasiSeparated g] (P : Set ℕ)
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : allowableTorsionSheafProperty U P F) :
    allowableTorsionPlusProperty V P
      (R(lowerStar AddCommGrpCat.{u + 1} g).obj
        ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  have hge := (lowerStar AddCommGrpCat.{u + 1} g).isGE_rightDerivedFunctor_obj_singleFunctor F
  refine ⟨?_, ⟨0, hge⟩⟩
  intro q
  by_cases hq : q < 0
  · exact allowable_zero _ (DerivedCategory.isZero_of_isGE _ 0 q hq)
  · lift q to ℕ using (by omega : 0 ≤ q)
    apply allowable_iso
      ((DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
        ((lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlusCompatibility.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    intro Ω _ _ s y
    let Ω' := AlgebraicClosure Ω
    let ι : Ω →+* Ω' := algebraMap Ω Ω'
    let G := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} g).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
    have := Scheme.isIso_pointSmallEtalePrecomp_sheafFiber s
      (Spec.map (CommRingCat.ofHom ι)) G
    let j := asIso ((Scheme.pointSmallEtalePrecomp s
      (Spec.map (CommRingCat.ofHom ι))).sheafFiber.app G)
    obtain ⟨n, hn, hx, hp⟩ := qcqs_higherDirectImages_prime_torsion g P F
      (fun Ω _ _ s x ↦ by
        obtain ⟨n, hn, hp, hx⟩ := hF Ω s x
        exact ⟨n, hn, hx, hp⟩) q Ω'
          (Spec.map (CommRingCat.ofHom ι) ≫ s) (j.hom.hom y)
    refine ⟨n, hn, hp, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso j.hom).1
    change j.hom.hom (n • y) = j.hom.hom 0
    rw [map_zero]
    exact (map_nsmul j.hom.hom n y).trans hx

private lemma allowable_derived_directImage {U V : Scheme.{u}} (g : U ⟶ V)
    [QuasiCompact g] [QuasiSeparated g] (P : Set ℕ)
    (K : DerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : allowableTorsionPlusProperty U P K) :
    allowableTorsionPlusProperty V P (R(lowerStar AddCommGrpCat.{u + 1} g).obj K) := by
  let : (allowableTorsionSheafProperty U P).IsClosedUnderIsomorphisms :=
    ⟨fun i hi ↦ allowable_iso i hi⟩
  let : (allowableTorsionSheafProperty U P).ContainsZero :=
    ⟨0, Limits.isZero_zero _, allowable_zero _ (Limits.isZero_zero _)⟩
  obtain ⟨a, ha⟩ := hK.2
  have : K.IsGE a := ha
  refine ⟨?_, ⟨a, rightDerived_isGE g K a⟩⟩
  intro n
  let Kn := (DerivedCategory.TStructure.t.truncLE n).obj K
  have hKn : allowableTorsionPlusProperty V P
      (R(lowerStar AddCommGrpCat.{u + 1} g).obj Kn) := by
    exact DerivedCategory.prop_of_bounded
      ((allowableTorsionPlusProperty V P).inverseImage R(lowerStar AddCommGrpCat.{u + 1} g))
      (allowableTorsionSheafProperty U P) (allowable_single_directImage g P) Kn
      ⟨⟨a, inferInstanceAs (DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.TStructure.t.truncLE n).obj K) a)⟩, ⟨n, inferInstance⟩⟩
      (DerivedCategory.homologyProperty_truncLE hK.1 n)
  have hι : IsIso ((DerivedCategory.homologyFunctor _ n).map
      (R(lowerStar AddCommGrpCat.{u + 1} g).map
        ((DerivedCategory.TStructure.t.truncLEι n).app K))) := by
    let T := (DerivedCategory.TStructure.t.triangleLEGT n).obj K
    have : T.obj₃.IsGE (n + 1) := inferInstanceAs
      (DerivedCategory.TStructure.t.IsGE ((DerivedCategory.TStructure.t.truncGT n).obj K)
        (n + 1))
    have : (R(lowerStar AddCommGrpCat.{u + 1} g).obj T.obj₃).IsGE (n + 1) :=
      rightDerived_isGE g T.obj₃ (n + 1)
    exact DerivedCategory.isIso_homologyMap_mor₁ _
      ((R(lowerStar AddCommGrpCat.{u + 1} g)).map_distinguished _
        (DerivedCategory.TStructure.t.triangleLEGT_distinguished n K))
      (n - 1) n (by omega)
      (DerivedCategory.isZero_of_isGE
        (R(lowerStar AddCommGrpCat.{u + 1} g).obj T.obj₃) (n + 1) _ (by omega))
      (DerivedCategory.isZero_of_isGE
        (R(lowerStar AddCommGrpCat.{u + 1} g).obj T.obj₃) (n + 1) _ (by omega))
  exact allowable_iso (asIso ((DerivedCategory.homologyFunctor _ n).map
    (R(lowerStar AddCommGrpCat.{u + 1} g).map
      ((DerivedCategory.TStructure.t.truncLEι n).app K)))) (hKn.1 n)

/-- Smooth base change in the bounded-below allowable-torsion category on X.
Source: blueprint, sec-smooth-base-change, sk-rem-rest, order 1440
(blueprint: sbc-thm-bounded-below-derived-smooth-base-change).

Proof:
1. Truncate K above each n. The truncation is bounded and retains allowable-torsion
cohomology, by the standard truncation triangle and its cohomology isomorphisms.
2. Apply bounded allowable-torsion smooth base change to each truncation. The
bounded-below truncation criterion compares both images in degree n. Naturality
of the canonical exchange transformation makes the comparison square commute,
so its remaining edge is an isomorphism. Cohomology detects derived isomorphisms.
3. For a sheaf in degree zero, qcqs higher direct images preserve allowable prime
torsion. The plus/unbounded comparison identifies this with total derived direct
image. Left exactness supplies the lower cohomological bound.
4. For general K, bounded triangulated devissage applied to its upper truncations
extends step 3 to each truncation. Right derived direct image preserves lower
bounds, so the image of the upper truncation agrees with the image of K on H^n.
Transport the torsion property along this isomorphism for every n.
5. Exact inverse image preserves cohomology and lower bounds. Its geometric stalk
comparison transports allowable annihilators. Thus the source is allowable torsion
and bounded below. Transport this property to the target along the isomorphism
proved in step 2; the allowable-torsion subcategory is full. -/
theorem boundedBelow_derived_smooth_baseChange
    {X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T}
    {f : X ⟶ S} {g : T ⟶ S} [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (sq : ChosenCartesianSquare h e f g)
    (K : AbelianDerivedCategoryPlusTorsionOfPrimes T S.invertiblePrimes) :
    allowableTorsionPlusProperty X S.invertiblePrimes
        (D(upperStar AddCommGrpCat.{u + 1} f).obj
          (R(lowerStar AddCommGrpCat.{u + 1} g).obj K.obj)) ∧
      allowableTorsionPlusProperty X S.invertiblePrimes
        (R(lowerStar AddCommGrpCat.{u + 1} h).obj
          (D(upperStar AddCommGrpCat.{u + 1} e).obj K.obj)) ∧
      IsIso (abelianDerivedBaseChangeArrow sq K.obj) := by
  let sq' : ChosenCartesianSquare e h g f :=
    { toCommSq := sq.toCommSq.flip
      isoPullback := sq.isoPullback ≪≫ Limits.pullbackSymmetry f g
      hom_fst := by simp [sq.hom_snd]
      hom_snd := by simp [sq.hom_fst] }
  have hiso : IsIso (abelianDerivedBaseChangeArrow sq K.obj) := by
    apply (DerivedCategory.isIso_iff _ _).2
    intro n
    let Kn := (DerivedCategory.TStructure.t.truncLE n).obj K.obj
    have hKn : allowableTorsionBoundedProperty T S.invertiblePrimes Kn := by
      constructor
      · intro q
        by_cases hq : q ≤ n
        · have hι : IsIso ((DerivedCategory.homologyFunctor _ q).map
              ((DerivedCategory.TStructure.t.truncLEι n).app K.obj)) := by
            have : ((DerivedCategory.TStructure.t.triangleLEGT n).obj K.obj).obj₃.IsGE
                (n + 1) := inferInstanceAs
              (DerivedCategory.TStructure.t.IsGE
                ((DerivedCategory.TStructure.t.truncGT n).obj K.obj) (n + 1))
            exact DerivedCategory.isIso_homologyMap_mor₁ _
              (DerivedCategory.TStructure.t.triangleLEGT_distinguished n K.obj)
              (q - 1) q (by omega)
              (DerivedCategory.isZero_of_isGE _ (n + 1) _ (by omega))
              (DerivedCategory.isZero_of_isGE _ (n + 1) _ (by omega))
          exact allowable_iso (asIso ((DerivedCategory.homologyFunctor _ q).map
            ((DerivedCategory.TStructure.t.truncLEι n).app K.obj))).symm (K.property.1 q)
        · exact allowable_zero _ (DerivedCategory.isZero_of_isLE Kn n q (by omega))
      · obtain ⟨a, ha⟩ := K.property.2
        have : K.obj.IsGE a := ha
        exact ⟨⟨a, inferInstanceAs
          (DerivedCategory.TStructure.t.IsGE
            ((DerivedCategory.TStructure.t.truncLE n).obj K.obj) a)⟩,
          ⟨n, inferInstance⟩⟩
    have hi : IsIso (abelianDerivedBaseChangeArrow sq
        ((DerivedCategory.TStructure.t.truncLE n).obj K.obj)) :=
      (isIso_abelianDerivedBaseChangeArrow_of_bounded_allowable_torsion sq ⟨Kn, hKn⟩).1
    have hc := boundedBelow_truncation_criterion g f e h sq' S.invertiblePrimes K n
    have hs := hc.2.1
    have ht : IsIso ((DerivedCategory.homologyFunctor _ n).map
        (R(lowerStar AddCommGrpCat.{u + 1} h).map
          (D(upperStar AddCommGrpCat.{u + 1} e).map
            ((DerivedCategory.TStructure.t.truncLEι n).app K.obj)))) := hc.2.2.1
    have hn := (DerivedCategory.homologyFunctor _ n).congr_map
      (abelian_exchange_naturality sq
        ((DerivedCategory.TStructure.t.truncLEι n).app K.obj))
    simp only [Functor.map_comp, Functor.id_obj] at hn
    have hcomp : IsIso ((DerivedCategory.homologyFunctor _ n).map
        ((hypercohomologyBaseChangeFunctor g f).map
          ((DerivedCategory.TStructure.t.truncLEι n).app K.obj)) ≫
        (DerivedCategory.homologyFunctor _ n).map
          (abelianDerivedBaseChangeArrow sq K.obj)) := by
      change IsIso ((DerivedCategory.homologyFunctor _ n).map
        (D(upperStar AddCommGrpCat.{u + 1} f).map
          (R(lowerStar AddCommGrpCat.{u + 1} g).map
            ((DerivedCategory.TStructure.t.truncLEι n).app K.obj))) ≫ _)
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.homologyFunctor _ n).map
        ((hypercohomologyBaseChangeFunctor g f).map
          ((DerivedCategory.TStructure.t.truncLEι n).app K.obj))) _
  have hsource : allowableTorsionPlusProperty X S.invertiblePrimes
      (D(upperStar AddCommGrpCat.{u + 1} f).obj
        (R(lowerStar AddCommGrpCat.{u + 1} g).obj K.obj)) := by
    exact allowable_derived_upperStar f S.invertiblePrimes _
      (allowable_derived_directImage g S.invertiblePrimes K.obj K.property)
  exact ⟨hsource, (allowableTorsionPlusProperty X S.invertiblePrimes).prop_of_iso
    (asIso (abelianDerivedBaseChangeArrow sq K.obj)) hsource, hiso⟩

end AlgebraicGeometry.Etale
