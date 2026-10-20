/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.TorAmplitudeQCohTest
public import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel
import WeilConjectures.AlgebraicGeometry.PerfectAffineMapRepresentative
import all Sheaf.AlgebraicGeometry.ConnectiveRankOneModelStalk
import Sheaf.AlgebraicGeometry.RankOneResidueStalkComponent
import Sheaf.AlgebraicGeometry.DerivedResidueUnitBetti
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all Sheaf.AlgebraicGeometry.TorAmplitudeOpenLocal
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-! # The degree-zero residue-field criterion for a perfect complex

Source: Stacks Project, Tag 0E62, proof of Lemma 36.32.5
(blueprint: lem-sc-perfect-degree-zero-fibre-criterion).

Residue-field tensor is derived pullback along `S.fromSpecResidueField s`. Its cohomology
is a sheaf on `Spec κ(s)`, equivalently a `κ(s)`-module. Restriction to an open subscheme
is derived pullback along its inclusion. The structure sheaf is `SheafOfModules.unit`
placed in degree zero. The positive Tor-amplitude condition tests every module sheaf.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

section

-- Cache the standard module-sheaf structures: rebuilding their sheafification instances
-- repeatedly dominates elaboration of the localized derived-category comparisons.
private noncomputable local instance modules_abelian (S : Scheme.{u}) :
    Abelian (SheafOfModules.{u} (moduleRings S.toRingedSpace)) := inferInstance

private noncomputable local instance localized_modules_abelian (S : Scheme.{u}) (U : S.Opens) :
    Abelian (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) := inferInstance

private noncomputable local instance modules_colimits (S : Scheme.{u}) :
    HasColimits (SheafOfModules.{u} (moduleRings S.toRingedSpace)) := inferInstance

private noncomputable local instance localized_modules_colimits (S : Scheme.{u}) (U : S.Opens) :
    HasColimits (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) := inferInstance

private theorem bottom_homologyMap_isIso
    {C : Type*} [Category C] [Abelian C]
    {A B : CochainComplex C ℤ} (α : A ⟶ B)
    (hAn : IsZero (A.X (-1))) (hAp : IsZero (A.X 1))
    (hBn : IsZero (B.X (-1))) [IsIso (α.f 0)] :
    IsIso (HomologicalComplex.homologyMap α 0) := by
  have hdA : A.d 0 1 = 0 := hAp.eq_of_tgt _ _
  have hdB : B.d 0 1 = 0 := by
    apply (cancel_epi (α.f 0)).mp
    rw [α.comm 0 1, hdA, zero_comp, comp_zero]
  have hp : (ComplexShape.up ℤ).prev 0 = -1 :=
    (ComplexShape.up ℤ).prev_eq' (by decide)
  have hn : (ComplexShape.up ℤ).next 0 = 1 :=
    (ComplexShape.up ℤ).next_eq' (by decide)
  have hfA : (A.sc 0).f = 0 := by
    change A.d ((ComplexShape.up ℤ).prev 0) 0 = 0
    rw [hp]
    exact hAn.eq_of_src _ _
  have hfB : (B.sc 0).f = 0 := by
    change B.d ((ComplexShape.up ℤ).prev 0) 0 = 0
    rw [hp]
    exact hBn.eq_of_src _ _
  have hgA : (A.sc 0).g = 0 := by
    change A.d 0 ((ComplexShape.up ℤ).next 0) = 0
    rw [hn]
    exact hdA
  have hgB : (B.sc 0).g = 0 := by
    change B.d 0 ((ComplexShape.up ℤ).next 0) = 0
    rw [hn]
    exact hdB
  let φ := (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).map α
  change IsIso (ShortComplex.homologyMap φ)
  rw [(ShortComplex.LeftHomologyMapData.ofZeros φ hfA hgA hfB hgB).homologyMap_eq]
  change IsIso (_ ≫ α.f 0 ≫ _)
  infer_instance

set_option maxHeartbeats 800000 in
-- Composed derived homology and stalk comparisons require extra elaboration heartbeats.
private theorem bijective_stalk_homology_of_connective_rank_one_model (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ x : S, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory S)
    (a : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit S.ringCatSheaf) ⟶ E) (s : S)
    (U : S.Opens) (hs : s ∈ U) (hU : IsAffineOpen U)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
    (hP : Scheme.IsStrictlyPerfect S U P)
    (hnegative : ∀ i : ℤ, i < 0 → IsZero (P.X i))
    (hzero : Nonempty (P.X 0 ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin 1))))
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P)
    (ha : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
        ((derivedPullback (S.fromSpecResidueField s)).map a))) :
    Function.Bijective (Scheme.Modules.Hom.stalkLinearMap
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map a) s) := by
  let r := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U
  let M := SheafOfModules.unit S.ringCatSheaf
  let A := (CochainComplex.singleFunctor
    (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj (r.obj M)
  let c : r.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      DerivedCategory.Q.obj A :=
    (r.mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app (r.obj M)
  obtain ⟨α, hα⟩ := Scheme.perfect_affine_map_representative S U hU A P
    (strictlyPerfect_single_restricted_unit S U) hP
    (c.inv ≫ r.mapDerivedCategory.map a ≫ e.hom)
  let F := localizedModuleStalk S U ⟨s, hs⟩
  obtain ⟨hadd, hlim, hcolim, hst⟩ :=
    localized_homology_stalk_comparison S U ⟨s, hs⟩
  have := hadd
  have := hlim
  have := hcolim
  have hf : IsIso (F.map (α.f 0)) :=
    isIso_localized_stalk_component_of_residue_homology S E a s U hs P hP
      hnegative hzero e ha c α hα
  let T := F.mapHomologicalComplex (.up ℤ)
  have hAn : IsZero ((T.obj A).X (-1)) := F.map_isZero
    (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))
  have hAp : IsZero ((T.obj A).X 1) := F.map_isZero
    (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))
  have hBn : IsZero ((T.obj P).X (-1)) := F.map_isZero (hnegative (-1) (by omega))
  have : IsIso ((T.map α).f 0) := hf
  have hαH : IsIso (HomologicalComplex.homologyMap (T.map α) 0) :=
    bottom_homologyMap_isIso (T.map α) hAn hAp hBn
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0 ⋙ F
  let b := Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors _ 0) F ≪≫
    (F.mapHomologicalComplexHomologyIso (.up ℤ) 0).symm
  have hQ : IsIso (H.map (DerivedCategory.Q.map α)) :=
    (NatIso.isIso_map_iff b α).mpr hαH
  have hr : IsIso (H.map (r.mapDerivedCategory.map a)) := by
    rw [hα, Functor.map_comp, Functor.map_comp] at hQ
    have : IsIso (H.map c.inv ≫ H.map (r.mapDerivedCategory.map a)) :=
      IsIso.of_isIso_comp_right _ (H.map e.hom)
    exact IsIso.of_isIso_comp_left (H.map c.inv) _
  obtain ⟨t⟩ := hst 0
  let G := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0 ⋙
      Scheme.Modules.toPresheaf S ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} s
  have : IsIso ((r.mapDerivedCategory ⋙ H).map a) := hr
  have hg : IsIso (G.map a) := (NatIso.isIso_map_iff t a).mpr this
  exact ConcreteCategory.bijective_of_isIso (G.map a)

private theorem split_connective_zero_differential
    {C : Type*} [Category C] [Abelian C] (B : CochainComplex C ℤ)
    (hn : ∀ i : ℤ, i < 0 → IsZero (B.X i)) (hd : B.d 0 1 = 0) :
    ∃ N : CochainComplex C ℤ, Nonempty (Retract N B) ∧
      (∀ i : ℤ, i < 1 → IsZero (N.X i)) ∧
      Nonempty (B ≅ (CochainComplex.singleFunctor C 0).obj (B.X 0) ⊞ N) := by
  let A := (CochainComplex.singleFunctor C 0).obj (B.X 0)
  let p : B ⟶ A := HomologicalComplex.mkHomToSingle (𝟙 (B.X 0)) (by
    intro i hi
    exact (hn i (by change i + 1 = 0 at hi; omega)).eq_of_src _ _)
  let j : A ⟶ B := HomologicalComplex.mkHomFromSingle (𝟙 (B.X 0)) (by
    intro k hk
    have : k = 1 := by change 0 + 1 = k at hk; omega
    subst k
    simpa using hd)
  have hjp : j ≫ p = 𝟙 A := by
    ext i
    by_cases hi : i = 0
    · subst i
      simp [j, p]
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_src _ _
  let N := kernel p
  let q : B ⟶ N := kernel.lift p (𝟙 B - p ≫ j) (by simp [Category.assoc, hjp])
  have hiq : kernel.ι p ≫ q = 𝟙 N := by
    apply (cancel_mono (kernel.ι p)).mp
    simp only [q, Category.assoc, kernel.lift_ι, Preadditive.comp_sub, Category.comp_id,
      kernel.condition_assoc, zero_comp, sub_zero]
    exact (Category.id_comp _).symm
  let r : Retract N B := ⟨kernel.ι p, q, hiq⟩
  let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  let sp : S.Splitting :=
    { r := q
      s := j
      f_r := hiq
      s_g := hjp
      id := by change q ≫ kernel.ι p + p ≫ j = 𝟙 B; simp [q] }
  refine ⟨N, ⟨r⟩, ?_, ⟨sp.isoBinaryBiproduct ≪≫ biprod.braiding _ _⟩⟩
  intro i hi
  by_cases hz : i = 0
  · subst i
    have hp : IsIso (p.f 0) := by
      dsimp [p]
      rw [HomologicalComplex.mkHomToSingle_f]
      simp only [Category.id_comp]
      infer_instance
    have hcomp : (kernel.ι p).f 0 ≫ p.f 0 = 0 := by
      exact congrArg (fun f ↦ f.f 0) (kernel.condition p)
    have hzero : (kernel.ι p).f 0 = 0 := by
      apply (cancel_mono (p.f 0)).mp
      simpa using hcomp
    have : Mono ((kernel.ι p).f 0) := inferInstance
    rw [hzero] at this
    exact IsZero.of_mono_zero (N.X 0) (B.X 0)
  · let ri := r.map (HomologicalComplex.eval C (.up ℤ) i)
    apply (IsZero.iff_id_eq_zero _).2
    change 𝟙 ((HomologicalComplex.eval C (.up ℤ) i).obj N) = 0
    rw [← ri.retract, (hn i (by omega)).eq_of_src ri.r 0, comp_zero]

private theorem zero_of_retract {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y : C} (r : Retract X Y) (hY : IsZero Y) : IsZero X := by
  rw [IsZero.iff_id_eq_zero, ← r.retract, hY.eq_of_src r.r 0, comp_zero]

private theorem perfect_of_retract_finite_free_complex (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (N B : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (rN : Retract N B)
    (hb : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (B.X i))
    (hf : ∀ i : ℤ, ∃ m : ℕ, Nonempty (B.X i ≅ SheafOfModules.free
      (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin m)))) :
    X.IsPerfect (DerivedCategory.Q.obj N) := by
  classical
  intro x
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) ⊤
  let C := (R.mapHomologicalComplex (.up ℤ)).obj N
  refine ⟨⊤, trivial, C, ?_, ⟨R.mapDerivedCategoryFactors.app N⟩⟩
  constructor
  · obtain ⟨a, b, hb⟩ := hb
    exact ⟨a, b, fun i hi ↦ R.map_isZero
      (zero_of_retract (rN.map (HomologicalComplex.eval _ (.up ℤ) i)) (hb i hi))⟩
  · intro i
    obtain ⟨m, ⟨em⟩⟩ := hf i
    let r := (rN.map (HomologicalComplex.eval _ (.up ℤ) i)).map R
    let e := R.mapIso em ≪≫
      (SheafOfModules.mapFreeIso R (ULift.{u} (Fin m)) (Iso.refl _)).symm
    exact ⟨m, r.i ≫ e.hom, e.inv ≫ r.r, by
      simp only [Category.assoc, Iso.hom_inv_id_assoc, r.retract]
      rfl⟩

private theorem positive_tensor_vanishes_of_retract_free (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (N B : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (rN : Retract N B)
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (B.X i))
    (hf : ∀ i : ℤ, ∃ m : ℕ, Nonempty (B.X i ≅ SheafOfModules.free
      (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin m))))
    (hn : ∀ i : ℤ, i < 1 → IsZero (N.X i))
    (G : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ) (hi : i < 1) :
    schemeDerivedTensorCohomologyVanishes X (DerivedCategory.Q.obj N) G i := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  obtain ⟨⟨mp⟩, ⟨mc⟩, _⟩ := SheafOfModules.tensorClosed X.sheaf
  let := mp
  let := mc
  have := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have hflat (n : ℤ) : SheafOfModules.IsFlat (N.X n) := by
    obtain ⟨m, ⟨em⟩⟩ := hf n
    let r := rN.map (HomologicalComplex.eval _ (.up ℤ) n)
    let r' : Retract (N.X n) (SheafOfModules.free
        (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin m))) :=
      ⟨r.i ≫ em.hom, em.inv ≫ r.r, by simp [Category.assoc]⟩
    exact (ObjectProperty.flat_of_retract r'
      (ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _))).2
  have hnb : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (N.X n) := by
    obtain ⟨b, hb⟩ := hb
    exact ⟨b, fun n hn ↦ zero_of_retract
      (rN.map (HomologicalComplex.eval _ (.up ℤ) n)) (hb n hn)⟩
  have hK := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    X.toRingedSpace N hnb hflat
  refine ⟨N, hK, ⟨Iso.refl _⟩, ?_⟩
  let L := (HomologicalComplex.single
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ) 0).obj G
  have : N.IsStrictlyGE 1 := (N.isStrictlyGE_iff 1).2 hn
  have : CochainComplex.IsStrictlyGE (HomologicalComplex.tensorObj N L) (1 + 0) :=
    CochainComplex.isStrictlyGE_tensorObj N L 1 0
  have : CochainComplex.IsGE (HomologicalComplex.tensorObj N L) 1 := by
    simpa using (inferInstance : CochainComplex.IsGE (HomologicalComplex.tensorObj N L) (1 + 0))
  exact CochainComplex.isZero_of_isGE (HomologicalComplex.tensorObj N L) 1 i hi

end

set_option maxHeartbeats 1200000 in
-- Finite-free models and composed derived functors need extra elaboration heartbeats.
/-- A perfect object whose negative derived fibres vanish and whose degree-zero fibre map
from the structure sheaf is an isomorphism has an isomorphism on degree-zero cohomology,
and locally splits as the structure sheaf plus a perfect object of positive Tor-amplitude.
Source: Stacks Project, Tag 0E62, proof of Lemma 36.32.5
(blueprint: lem-sc-perfect-degree-zero-fibre-criterion).

Proof:
1. At each point use lem-sc-perfect-finite-free-residue-model to represent K on an affine
   neighbourhood by a bounded finite free complex with ranks equal to fibre cohomology
   dimensions. Its negative terms vanish. Termwise tensor computes derived tensor, giving
   Tor-amplitude [0, infinity) locally and hence globally, and no negative cohomology.
2. The map u factors through H^0(K)[0]. Its fibre isomorphism makes the comparison from
   H^0(K) tensor κ(s) to H^0(K tensor^L κ(s)) surjective. Apply
   lem-sc-perfect-cut-complex-degree-zero to split K locally as H^0(K)[0] plus a perfect
   complex of Tor-amplitude [1, infinity).
3. The degree-zero summand is perfect by lem-pc-perfect-summand and flat by its nonnegative
   Tor-amplitude. On an affine, lem-pc-perfect-affine-bounded-projective gives a bounded
   finite projective model. Split its exact positive tail from the top: the degree-zero
   cycles are finite projective, so their cokernel is finitely presented. Apply
   lem-weil-pbc-finitely-presented-flat-module-projective; H^0(K) is finite locally free.
4. The local splitting and flatness identify the degree-zero fibre with H^0(K) tensor κ(s).
   Thus H^0(u) is an isomorphism on every residue fibre. Apply
   lem-sc-finite-locally-free-residue-isomorphism to the finite locally free source and
   target. Substitute this isomorphism into the local splitting to obtain O plus P.
-/
theorem perfect_degreeZero_fibre_criterion (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ (U : S.Opens) (V : U.toScheme.Opens),
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    [∀ s : S, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace))]
    (K : schemeDerivedCategory S) (hK : schemeDerivedQCohProperty S K)
    (hperfect : S.IsPerfect K)
    (u : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit (moduleRings S.toRingedSpace)) ⟶ K)
    (hzero : ∀ s : S, IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
        ((derivedPullback (S.fromSpecResidueField s)).map u)))
    (hnegative : ∀ (s : S) (i : ℤ), i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) i).obj
        ((derivedPullback (S.fromSpecResidueField s)).obj K))) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map u) ∧
    ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ P : schemeDerivedCategory U.toScheme,
      U.toScheme.IsPerfect P ∧
      (∀ (G : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) (i : ℤ),
        i < 1 → schemeDerivedTensorCohomologyVanishes U.toScheme P G i) ∧
      Nonempty ((derivedPullback U.ι).obj K ≅
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj
            (SheafOfModules.unit (moduleRings U.toScheme.toRingedSpace)) ⊞ P) := by
  classical
  let (X : Scheme.{u}) : Abelian
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := modules_abelian X
  let (X : Scheme.{u}) (V : X.Opens) : Abelian
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) :=
    localized_modules_abelian X V
  let (X : Scheme.{u}) : HasColimits
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := modules_colimits X
  let (X : Scheme.{u}) (V : X.Opens) : HasColimits
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) :=
    localized_modules_colimits X V
  have _hK := hK
  have hmodel (s : S) : ∃ U : S.Opens, s ∈ U ∧ IsAffineOpen U ∧
      ∃ P : CochainComplex
        (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ,
        Scheme.IsStrictlyPerfect S U P ∧
        (∀ i : ℤ, i < 0 → IsZero (P.X i)) ∧
        Nonempty (P.X 0 ≅ SheafOfModules.free
          (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin 1))) ∧
        (∀ i : ℤ, ∃ m : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
          (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin m)))) ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj K ≅
            DerivedCategory.Q.obj P) := by
    have hn : ∀ i : ℤ, i < 0 → Scheme.derivedFiberBetti S K i s = 0 := by
      intro i hi
      let F := SheafOfModules.evaluation
        (moduleRings (Spec (S.residueField s)).toRingedSpace) (Opposite.op ⊤)
      have : F.Additive := { map_add := by intros; rfl }
      have hz : IsZero (F.obj ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) i).obj
            ((derivedPullback (S.fromSpecResidueField s)).obj K))) := by
        rw [IsZero.iff_id_eq_zero, ← F.map_id, (hnegative s i hi).eq_of_src (𝟙 _) 0]
        exact F.map_zero _ _
      have hs := ModuleCat.isZero_iff_subsingleton.mp hz
      let : Subsingleton (Scheme.derivedFiberCohomology S K i s) := hs
      exact Module.finrank_zero_of_subsingleton
    have hzeroRank := Scheme.derivedFiberBetti_zero_eq_one_of_unit_iso S K u s (hzero s)
    obtain ⟨_, _, U, hs, hU, P, hb, hrank, ⟨e⟩⟩ :=
      Scheme.exists_finiteFreeResidueModel S K hperfect s
    have hP : Scheme.IsStrictlyPerfect S U P := by
      refine ⟨hb, fun i ↦ ?_⟩
      obtain ⟨ei⟩ := hrank i
      exact ⟨Scheme.derivedFiberBetti S K i s, ei.hom, ei.inv, ei.hom_inv_id⟩
    have hPn : ∀ i : ℤ, i < 0 → IsZero (P.X i) := by
      intro i hi
      obtain ⟨ei⟩ := hrank i
      have hz : IsZero (SheafOfModules.free
          (R := (moduleRings S.toRingedSpace).over U)
          (ULift.{u} (Fin (Scheme.derivedFiberBetti S K i s)))) := by
        rw [hn i hi, IsZero.iff_id_eq_zero]
        apply (SheafOfModules.freeHomEquiv _).injective
        ext j
        exact Fin.elim0 j.down
      exact hz.of_iso ei
    have hPz : Nonempty (P.X 0 ≅ SheafOfModules.free
        (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin 1))) := by
      simpa only [hzeroRank] using hrank 0
    exact ⟨U, hs, hU, P, hP, hPn, hPz,
      (fun i ↦ ⟨Scheme.derivedFiberBetti S K i s, hrank i⟩), ⟨e⟩⟩
  have hiso : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map u) := by
    apply Scheme.Modules.isIso_of_bijective_stalkLinearMap
    intro s
    obtain ⟨U, hs, hU, P, hP, hPn, hPz, hPf, ⟨e⟩⟩ := hmodel s
    exact bijective_stalk_homology_of_connective_rank_one_model S K u s U hs hU P
      hP hPn hPz e (hzero s)
  refine ⟨hiso, ?_⟩
  intro s
  obtain ⟨U, hs, hU, P, hP, hPn, hPz, hPf, ⟨e⟩⟩ := hmodel s
  let r := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U
  let M := SheafOfModules.unit S.ringCatSheaf
  let A := (CochainComplex.singleFunctor
    (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj (r.obj M)
  let c : r.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      DerivedCategory.Q.obj A :=
    (r.mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app (r.obj M)
  obtain ⟨α, hα⟩ := Scheme.perfect_affine_map_representative S U hU A P
    (strictlyPerfect_single_restricted_unit S U) hP
    (c.inv ≫ r.mapDerivedCategory.map u ≫ e.hom)
  let F := (Scheme.Modules.overEquiv U).functor
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  have hcomponent : IsIso (F.map (α.f 0)) := by
    apply Scheme.Modules.isIso_of_bijective_stalkLinearMap
    intro x
    have hf := isIso_localized_stalk_component_of_residue_homology S K u x.val
      U x.property P hP hPn hPz e (hzero x.val) c α hα
    have : IsIso ((localizedModuleStalk S U x).map (α.f 0)) := hf
    exact ConcreteCategory.bijective_of_isIso
      ((localizedModuleStalk S U x).map (α.f 0))
  have : IsIso (α.f 0) := isIso_of_reflects_iso (α.f 0) F
  have hdP : P.d 0 1 = 0 := by
    apply (cancel_epi (α.f 0)).mp
    rw [α.comm 0 1]
    have hz : A.d 0 1 = 0 := by simp [A]
    rw [hz, zero_comp, comp_zero]
  let B := (F.mapHomologicalComplex (.up ℤ)).obj P
  have hBn (i : ℤ) (hi : i < 0) : IsZero (B.X i) := F.map_isZero (hPn i hi)
  have hdB : B.d 0 1 = 0 := by change F.map (P.d 0 1) = 0; rw [hdP, F.map_zero]
  obtain ⟨N, ⟨rN⟩, hNn, ⟨eN⟩⟩ := split_connective_zero_differential B hBn hdB
  have hBbound : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (B.X i) := by
    obtain ⟨a, b, hb⟩ := hP.1
    exact ⟨a, b, fun i hi ↦ F.map_isZero (hb i hi)⟩
  have hBfree : ∀ i : ℤ, ∃ m : ℕ, Nonempty (B.X i ≅ SheafOfModules.free
      (R := moduleRings U.toScheme.toRingedSpace) (ULift.{u} (Fin m))) := by
    intro i
    obtain ⟨m, ⟨em⟩⟩ := hPf i
    exact ⟨m, ⟨F.mapIso em ≪≫ (SheafOfModules.mapFreeIso F (ULift.{u} (Fin m))
      (Scheme.Modules.overEquivFunctorObjUnitIso U)).symm⟩⟩
  refine ⟨U, hs, DerivedCategory.Q.obj N,
    perfect_of_retract_finite_free_complex U.toScheme N B rN hBbound hBfree,
    ?_, ?_⟩
  · intro G i hi
    obtain ⟨a, b, hb⟩ := hBbound
    exact positive_tensor_vanishes_of_retract_free U.toScheme N B rN
      ⟨b, fun n hn ↦ hb n (Or.inr hn)⟩ hBfree hNn G i hi
  · let : HasDerivedCategory.{w} U.toScheme.Modules := inferInstanceAs
      (HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))
    have : PreservesBinaryBiproducts
        (DerivedCategory.Q : CochainComplex
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ ⥤
            schemeDerivedCategory U.toScheme) :=
      preservesBinaryBiproducts_of_preservesBiproducts _
    obtain ⟨eopen⟩ := open_pullback_restriction_iso S U K
    let eB : (derivedPullback U.ι).obj K ≅ DerivedCategory.Q.obj B :=
      eopen.symm ≪≫ (Functor.mapDerivedCategoryCompIso r F).app K ≪≫
        F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app P
    let e0 : B.X 0 ≅ SheafOfModules.unit (moduleRings U.toScheme.toRingedSpace) :=
      F.mapIso ((asIso (α.f 0)).symm ≪≫
        HomologicalComplex.singleObjXSelf (.up ℤ) 0 (r.obj M)) ≪≫
        (Scheme.Modules.overEquivFunctorObjUnitIso U).symm
    exact ⟨eB ≪≫ DerivedCategory.Q.mapIso eN ≪≫
      (DerivedCategory.Q.mapBiprod
        ((CochainComplex.singleFunctor _ 0).obj (B.X 0)) N) ≪≫
      biprod.mapIso (((DerivedCategory.singleFunctorIsoCompQ _ 0).app (B.X 0)).symm ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso e0) (Iso.refl _)⟩

end AlgebraicGeometry
