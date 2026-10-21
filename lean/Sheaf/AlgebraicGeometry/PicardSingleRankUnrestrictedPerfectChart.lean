/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardUniversalSingleRankMatch
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.PicardRankMatchDirectImage
import Sheaf.AlgebraicGeometry.ProperFlatAffineCechPerfectModel
import WeilConjectures.AlgebraicGeometry.AffineFlatModuleTensorFlat
import all Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-! # Perfect charts for one direct-image rank condition

Source: Stacks Project, Tag 0BDP, first three proof paragraphs; Tag 0B91(2).
(blueprint: lem-sc-picard-single-rank-unrestricted-perfect-chart).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A zero module is the free module of rank zero. -/
private theorem freeZero_isZero (X : Scheme.{u}) :
    IsZero (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 0))) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (SheafOfModules.freeHomEquiv _).injective
  funext x
  exact Fin.elim0 x.down

/-- On an empty scheme every module has every rank, using the empty open cover. -/
private theorem rank_of_isEmpty (X : Scheme.{u}) [IsEmpty X]
    (M : X.Modules) (r : ℕ) : M.IsFiniteLocallyFreeOfRank r := by
  apply Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top M
    (fun x : X ↦ (⊤ : X.Opens))
  · apply eq_top_iff.mpr
    intro x _
    exact isEmptyElim x
  · intro x
    exact isEmptyElim x

/-- A zero module has rank one exactly on an empty scheme. -/
private theorem zero_rank_one_iff (X : Scheme.{u}) (M : X.Modules) (hz : IsZero M) :
    M.IsFiniteLocallyFreeOfRank 1 ↔ IsEmpty X := by
  constructor
  · intro hr
    constructor
    intro x
    have hr0 : M.IsFiniteLocallyFreeOfRank 0 :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (hz.iso (freeZero_isZero X)).symm
    have := hr
    have h1 := Modules.finiteLocallyFreeOfRank_stalk_finrank M 1 x
    have := hr0
    have h0 := Modules.finiteLocallyFreeOfRank_stalk_finrank M 0 x
    omega
  · intro h
    have := h
    exact rank_of_isEmpty X M 1

open scoped ZeroObject in
/-- Zero is perfect, using the actual zero complex on every open. -/
private theorem zero_isPerfect (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    IsPerfect X (0 : schemeDerivedCategory X) := by
  intro x
  let R := (moduleRings X.toRingedSpace).over (⊤ : X.Opens)
  let D : CochainComplex (SheafOfModules.{u} R) ℤ := HomologicalComplex.zero
  refine ⟨⊤, trivial, D, ⟨?_, ?_⟩, ?_⟩
  · exact ⟨0, 0, fun _ _ ↦ isZero_zero _⟩
  · intro n
    refine ⟨0, 0, 0, ?_⟩
    exact (isZero_zero (SheafOfModules.{u} R)).eq_of_src _ _
  · let A := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) ⊤
    exact ⟨(A.mapDerivedCategory.map_isZero (isZero_zero _)).iso
      (DerivedCategory.Q.map_isZero HomologicalComplex.isZero_zero)⟩

open scoped ZeroObject in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The zero derived object has zero derived tensor cohomology in every degree. -/
private theorem zero_tensor_vanishes (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M : X.Modules) (i : ℤ) :
    schemeDerivedTensorCohomologyVanishes X (0 : schemeDerivedCategory X) M i := by
  let D : CochainComplex X.Modules ℤ := HomologicalComplex.zero
  have hD : CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) D := by
    apply CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace X.toRingedSpace D
    · exact ⟨0, fun _ _ ↦ isZero_zero _⟩
    · intro n
      change SheafOfModules.IsFlat (0 : X.Modules)
      let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
      let : SymmetricCategory X.Modules := SheafOfModules.symmetricCategory X.sheaf
      let : MonoidalPreadditive X.Modules :=
        Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
      obtain ⟨⟨h⟩, _⟩ := SheafOfModules.tensorClosed X.sheaf
      let := h
      exact (ObjectProperty.flat_of_isZero (A := X.Modules) (isZero_zero X.Modules)).2
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let : SymmetricCategory X.Modules := SheafOfModules.symmetricCategory X.sheaf
  let : MonoidalPreadditive X.Modules :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  refine ⟨D, hD, ⟨(DerivedCategory.Q.map_isZero HomologicalComplex.isZero_zero).iso
    (isZero_zero _)⟩, ?_⟩
  let e := CochainComplex.mapBifunctorSingle₂Iso
    (MonoidalCategory.curriedTensor X.Modules) M D
  have hz : IsZero (((((MonoidalCategory.curriedTensor X.Modules).flip.obj M).mapHomologicalComplex
      (.up ℤ)).obj D).homology i) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _
      (((MonoidalCategory.curriedTensor X.Modules).flip.obj M).map_isZero (isZero_zero _))
  exact (HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso e |>.isZero_iff.mpr hz

open scoped ZeroObject in
/-- The chosen derived pullback preserves zero, by its triangulated structure. -/
private theorem derivedPullback_zero_isZero {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    IsZero ((derivedPullback g).obj (0 : schemeDerivedCategory S)) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hL, ⟨hshift, htri⟩, hε⟩ :=
      (derivedPullback_spec g)
  let := hshift
  let := htri
  exact Functor.map_isZero _ (isZero_zero _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Near every base point the single-rank predicate is universal rank-r lowest cohomology.
This supplies the input complex and comparison, but constructs no representing locus.
Source: Stacks Project, Tag 0BDP, first three proof paragraphs; Tag 0B91(2).
(blueprint: lem-sc-picard-single-rank-unrestricted-perfect-chart).

Proof:
1. The clopen rank loci X_r of E have open and closed images: flat local finite
   presentation makes f open, and properness makes f closed. The image V=f(X)
   is clopen. For a nonempty homogeneous fibre of rank r, the clopen neighbourhood
   V minus f(X minus X_r) contains only nonempty fibres of this rank.
2. On this neighbourhood finite local freeness makes F finitely presented and
   relatively flat. Tag 0B91 gives perfect Rf_*F and arbitrary derived base change.
   Its pullbacks have no negative cohomology. Shrink near s to a finite strictly
   perfect model of Tor amplitude [0,b]. Degree-zero derived base change identifies
   all its pulled-back H^0 sheaves with the ordinary direct images in the predicate.
   The reference E has rank r on all inverse images. In any local witness its rank
   equals r by invariant basis number on a stalk of a nonempty fibre. Locality of
   rank-r freeness proves the equivalence in both directions, including nonreduced
   tests and rank zero.
3. If s has empty fibre, take U=S minus V. All pullback fibres and direct images
   are empty and zero respectively. The reference clause is vacuous. Take the
   actual zero derived object K, b=0 and r=0: both sides hold on every test scheme.
4. If the fibre at s has two different ranks a and c, take the intersection of the
   images of X_a and X_c as U. Every fibre over U contains both ranks. They persist
   after residue-field extension, so a nonempty test scheme cannot satisfy the
   reference clause, tested at one of its residue-field points. Thus the predicate
   holds exactly for empty tests. Take the actual zero derived object K, b=0 and
   r=1: its pulled-back H^0 is zero, which is rank one exactly on an empty scheme,
   since the residue field at any point of a nonempty scheme is nonzero.
5. These three cases exhaust all fibres. The zero objects in the last two cases
   are perfect and have the stated vanishing. No complex is chosen from an
   undetermined existence claim. Empty tests have vacuous covers, so their module
   sheaves have every finite rank and both equivalences include them. -/
theorem exists_picardSingleRankUnrestrictedPerfectChart
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [∀ (T : Scheme.{u}) (U : T.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over U))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E F : X.Modules) [E.IsFiniteLocallyFree] [F.IsFiniteLocallyFree] (s : S) :
    ∃ U : S.Opens, s ∈ U ∧ ∃ (K : schemeDerivedCategory U.toScheme) (b : ℤ) (r : ℕ),
      IsPerfect U.toScheme K ∧
      (∀ M : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace),
        ∀ i : ℤ, i < 0 ∨ b < i →
          schemeDerivedTensorCohomologyVanishes U.toScheme K M i) ∧
      ∀ (T : Scheme.{u}) (g : T ⟶ U.toScheme),
        PicardUniversalSingleRankMatch f E F (g ≫ U.ι) ↔
          ∀ (T' : Scheme.{u}) (h : T' ⟶ T),
            SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
              ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) 0).obj
                  ((derivedPullback (h ≫ g)).obj K)) r := by
  obtain ⟨U, hsU, hnormal⟩ := exists_picardRankMatchDirectImageNormalForm f E F s
  rcases hnormal with ⟨r, hnormal⟩ | hnormal
  · have hchart :
    ∃ V : S.Opens, s ∈ V ∧ V ≤ U ∧
      ∃ (K : schemeDerivedCategory V.toScheme) (b : ℤ),
        IsPerfect V.toScheme K ∧
        (∀ M : SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace),
          ∀ i : ℤ, i < 0 ∨ b < i →
            schemeDerivedTensorCohomologyVanishes V.toScheme K M i) ∧
        ∀ (T : Scheme.{u}) (a : T ⟶ V.toScheme),
          Nonempty (((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).obj
              ((derivedPullback a).obj K)) ≅
            ((Modules.pushforward (pullback.snd f (a ≫ V.ι))).obj
              ((Modules.tensorPullback (pullback.fst f (a ≫ V.ι))).obj F))) := by
      classical
      obtain ⟨V, hV, hsV, hVU⟩ := exists_isAffineOpen_mem_and_subset hsU
      have := Modules.isGrothendieckAbelian X
      obtain ⟨D, d, hDge, hDle, hDflat, hDqc, hperfect, hcompare⟩ :=
        Modules.exists_proper_flat_affine_cech_perfect_model f F
          (Modules.isFlatOver_of_isFiniteLocallyFree f F) V hV
      have : D.IsStrictlyGE 0 := hDge
      have : D.IsStrictlyLE (d : ℤ) := hDle
      have hD : CochainComplex.IsAcyclicTensorKFlat (R := V.toScheme.sheaf) D :=
        CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace V.toScheme.toRingedSpace D
          ⟨d, fun i hi ↦ D.isZero_of_isStrictlyLE d i hi⟩
          (fun i ↦ isFlat_of_affineFlatOver_identity (D.X i) (hDflat i))
      refine ⟨V, hsV, hVU, DerivedCategory.Q.obj D, d, hperfect, ?_, ?_⟩
      · intro M i hi
        let : MonoidalCategory V.toScheme.Modules :=
          SheafOfModules.monoidalCategory V.toScheme.sheaf
        let : SymmetricCategory V.toScheme.Modules :=
          SheafOfModules.symmetricCategory V.toScheme.sheaf
        let : MonoidalPreadditive V.toScheme.Modules :=
          Classical.choice (SheafOfModules.tensorClosed V.toScheme.sheaf).1
        refine ⟨D, hD, ⟨Iso.refl _⟩, ?_⟩
        have hz : IsZero (D.X i) := by
          rcases hi with hi | hi
          · exact D.isZero_of_isStrictlyGE 0 i hi
          · exact D.isZero_of_isStrictlyLE d i hi
        let e := CochainComplex.mapBifunctorSingle₂Iso
          (MonoidalCategory.curriedTensor V.toScheme.Modules) M D
        have hzero : IsZero (((((MonoidalCategory.curriedTensor
            V.toScheme.Modules).flip.obj M).mapHomologicalComplex (.up ℤ)).obj D).homology i) :=
          ShortComplex.isZero_homology_of_isZero_X₂ _
            (((MonoidalCategory.curriedTensor V.toScheme.Modules).flip.obj M).map_isZero hz)
        exact (HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso e |>.isZero_iff.mpr hzero
      · intro T a
        have := Modules.isGrothendieckAbelian (pullback f (a ≫ V.ι))
        obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
          A, hA, hAmap, hAadd, ε, hε, htri, hK⟩ :=
          (derivedPullback_spec a)
        have hAeq : A = Modules.tensorPullback a :=
          CategoryTheory.Functor.ext hA (fun M N q ↦ hAmap q)
        subst A
        have := hAadd
        have := hK D hD
        let e : (derivedPullback a).obj (DerivedCategory.Q.obj D) ≅
            DerivedCategory.Q.obj
              (((Modules.tensorPullback a).mapHomologicalComplex (.up ℤ)).obj D) :=
          (derivedPullback a).mapIso ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))).symm.app D) ≪≫
            asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj D)) ≪≫
            DerivedCategory.Qh.mapIso
              (((Modules.tensorPullback a).mapHomotopyCategoryFactors (.up ℤ)).app D) ≪≫
            (DerivedCategory.quotientCompQhIso
              (SheafOfModules.{u} (moduleRings T.toRingedSpace))).app _
        let et : Modules.tensorPullback a ≅ Modules.pullback a :=
          (Modules.nonempty_tensorPullbackAdjunction a).some.leftAdjointUniq
            (Modules.pullbackPushforwardAdjunction a)
        obtain ⟨ec⟩ := hcompare a (pullback.fst f (a ≫ V.ι))
          (pullback.snd f (a ≫ V.ι)) (IsPullback.of_hasPullback f (a ≫ V.ι)) 0
        let ep : Modules.pullback (pullback.fst f (a ≫ V.ι)) ≅
            Modules.tensorPullback (pullback.fst f (a ≫ V.ι)) :=
          ((Modules.nonempty_tensorPullbackAdjunction
            (pullback.fst f (a ≫ V.ι))).some.leftAdjointUniq
              (Modules.pullbackPushforwardAdjunction _)).symm
        let q := Modules.pushforward (pullback.snd f (a ≫ V.ι))
        exact ⟨(DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
          (DerivedCategory.homologyFunctorFactors _ 0).app _ ≪≫
          (HomologicalComplex.homologyFunctor _ (.up ℤ) 0).mapIso
            ((NatIso.mapHomologicalComplex et (.up ℤ)).app D) ≪≫ ec ≪≫
          q.rightDerivedZeroIsoSelf.app _ ≪≫ q.mapIso (ep.app F)⟩
    obtain ⟨V, hsV, hVU, K, b, hK, hb, hcomp⟩ := hchart
    refine ⟨V, hsV, K, b, r, hK, hb, ?_⟩
    intro T g
    have hn := hnormal T (g ≫ S.homOfLE hVU)
    simp only [Category.assoc, homOfLE_ι] at hn
    rw [hn]
    constructor
    · intro h T' h'
      obtain ⟨e⟩ := hcomp T' (h' ≫ g)
      rw [Category.assoc] at e
      have hr := h T' h'
      rw [Category.assoc, homOfLE_ι] at hr
      have := hr
      exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e.symm
    · intro h T' h'
      obtain ⟨e⟩ := hcomp T' (h' ≫ g)
      rw [Category.assoc] at e
      have := h T' h'
      rw [Category.assoc, homOfLE_ι]
      exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e (r := r)
  · let : Zero (schemeDerivedCategory U.toScheme) := HasZeroObject.zero' _
    refine ⟨U, hsU, 0, 0, 1, zero_isPerfect U.toScheme,
      (fun M i _ ↦ zero_tensor_vanishes U.toScheme M i), ?_⟩
    intro T g
    rw [hnormal T g]
    constructor
    · intro h T' h'
      have : IsEmpty T' := ⟨fun t ↦ h.false (h' t)⟩
      exact rank_of_isEmpty T' _ 1
    · intro h
      have hz := (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).map_isZero
          (derivedPullback_zero_isZero ((𝟙 T) ≫ g))
      exact (zero_rank_one_iff T _ hz).mp (h T (𝟙 T))

end AlgebraicGeometry.Scheme
