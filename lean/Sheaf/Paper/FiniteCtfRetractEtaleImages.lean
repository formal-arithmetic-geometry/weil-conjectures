/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q155
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Defs.Filter
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.FiniteDiscreteEncodingConstructibility
import Sheaf.Paper.FiniteDiscreteEncodingTensorTor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-! # Étale cohomology images of finite-coefficient derived retracts

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-ctf.proof.md, (3), finite-coefficient thickness
(blueprint: lem-sfb-finite-ctf-retract-etale-images).

The normalized encoding identifies the pulled-back condensed finite ring with the
constant ring. Its termwise derived equivalence writes the ordinary module-sheaf
comparison without imposing any descent or boundedness hypothesis on the retract.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Exact comparison identifies pulled-back étale cohomology with cohomology of the
specified pro-étale complex, using its given comparison isomorphism.
Source: blueprint finite-ring summands, step 1, and Stacks 09AL
(blueprint: lem-sfb-finite-ctf-retract-etale-images). -/
def finiteCtfComparisonHomologyIso (X : Scheme.{u}) (B : Type u) [CommRing B]
    (C₀ : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} B))))
    (K : DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B))))
    (α : (comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).mapDerivedCategory.obj C₀ ≅ K) (q : ℤ) :
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).obj
      ((DerivedCategory.homologyFunctor _ q).obj C₀) ≅
        (DerivedCategory.homologyFunctor _ q).obj K :=
  ((comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).mapDerivedCategoryHomologyFunctorIso q).app C₀ ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso α

private theorem ordinaryConstructible_iff (A : Type u) [CommRing A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    FiniteDiscreteOrdinary.ordinaryConstructible A T M ↔
      IsConstructible (ULift.{u + 1} A) M := by
  classical
  rw [FiniteDiscreteOrdinary.ordinaryConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  apply exists_congr
  intro S
  apply forall_congr'
  intro a
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨ULift.{u + 1} C.I₀, fun i ↦ C.X i.down, fun i ↦ C.f i.down,
      by
        convert C.mem₀ using 1
        exact le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩)
          (fun _ _ ⟨i⟩ ↦ ⟨(ULift.up i : ULift.{u + 1} C.I₀)⟩), fun i ↦ hC i.down⟩
  · rintro ⟨I, W, g, hg, h⟩
    let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage (S.domain a) :=
      ⟨⟨I, W, g⟩, hg⟩
    have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
    exact ⟨C.restrictIndexOfSmall.{u}, fun i ↦
      h (Precoverage.ZeroHypercover.Small.restrictFun.{u} C i)⟩

private theorem etaleBoundedConstructible (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u})
    (K : Etale.DerivedCategoryModule (ULift.{u + 1} A) T)
    (h : Etale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) T K) :
    Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T K := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := h
  refine ⟨fun n ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    (hc n), min a b, max a b, min_le_max, fun n hn ↦ ?_⟩
  rcases hn with hn | hn
  · exact (DerivedCategory.isGE_iff K a).mp ha n (lt_of_lt_of_le hn (min_le_left _ _))
  · exact (DerivedCategory.isLE_iff K b).mp hb n (lt_of_le_of_lt (le_max_right _ _) hn)

private theorem finiteEtaleModel (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (B : Type u) [CommRing B] [Finite B]
    [TopologicalSpace B] [DiscreteTopology B]
    (E : FiniteDiscreteOrdinary.Encoding B X)
    (C : DerivedCategory (FiniteDiscreteOrdinary.Internal B X))
    (hC : (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient B) X ⊓
      fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K) C) :
    ∃ C₀ : Etale.DerivedCategoryModule (ULift.{u + 1} B) X,
      Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} B) X C₀ ∧
      (∃ a b : ℤ, a ≤ b ∧
        Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} B) X a b C₀) ∧
      Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X
        ).mapDerivedCategory.obj C₀ ≅ E.fixedDerived.functor.obj C) := by
  have hb := (FiniteDiscreteOrdinary.encoding_constructibility B X E).2 C |>.mp hC.1
  have horigin : DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) X (E.fixedDerived.functor.obj C) := by
    apply DerivedCategory.boundedConstructible_of_homology (ULift.{u + 1} B) hb.1
    intro n
    exact exists_isConstructibleSheaf_iso_comparisonUpperStar_obj (ULift.{u + 1} B)
      ((ordinaryConstructible_iff B X _).mp (hb.2 n))
  obtain ⟨C₀, hc₀, ⟨α⟩⟩ := horigin
  obtain ⟨a, b, ht⟩ := hC.2
  have htor := (FiniteDiscreteOrdinary.encoding_tensor_tor B X E).2.2 C
    (min a b) b (min_le_right _ _) |>.mp (ht.mono (min_le_left _ _) le_rfl)
  have htor₀ := (_root_.DerivedCategory.torAmplitudeIn _ (min a b) b).prop_of_iso α.symm htor
  exact ⟨C₀, etaleBoundedConstructible B X C₀ hc₀,
    ⟨min a b, b, min_le_right _ _,
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
        ((DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff _ _ C₀).mp htor₀)⟩, ⟨α⟩⟩

private theorem imageSplitting {D : Type*} [Category* D] [Abelian D]
    {V : D} (e : End V) (he : e ≫ e = e) :
    image.ι e ≫ factorThruImage e = 𝟙 (image e) := by
  have hi : image.ι e ≫ e = image.ι e := by
    apply (cancel_epi (factorThruImage e)).mp
    simpa only [← Category.assoc, image.fac] using he
  apply (cancel_mono (image.ι e)).mp
  simpa only [Category.assoc, image.fac, Category.id_comp] using hi

private theorem liftedImage {D T : Type*} [Category* D] [Category* T] [Abelian D]
    (F : D ⥤ T) [F.Full] [F.Faithful]
    {V : D} {W Z : T} (α : F.obj V ≅ W) (i : Z ⟶ W) (r : W ⟶ Z)
    (hri : i ≫ r = 𝟙 Z) :
    ∃ e : End V, e ≫ e = e ∧
      F.map e ≫ α.hom = α.hom ≫ r ≫ i ∧
      (∀ e' : End V, e' ≫ e' = e' →
        F.map e' ≫ α.hom = α.hom ≫ r ≫ i → e' = e) ∧
      Nonempty (Z ≅ F.obj (image e)) := by
  let e := F.preimage (α.hom ≫ r ≫ i ≫ α.inv)
  have hmap : F.map e = α.hom ≫ r ≫ i ≫ α.inv := F.map_preimage _
  have he : e ≫ e = e := by
    apply F.map_injective
    simp only [F.map_comp, hmap]
    simp [Category.assoc, reassoc_of% hri]
  have hcomm : F.map e ≫ α.hom = α.hom ≫ r ≫ i := by
    simp [hmap, Category.assoc]
  refine ⟨e, he, hcomm, ?_, ?_⟩
  · intro e' _ h'
    apply F.map_injective
    apply (cancel_mono α.hom).mp
    exact h'.trans hcomm.symm
  · let k := image.ι e
    let s := factorThruImage e
    have hks : k ≫ s = 𝟙 _ := imageSplitting e he
    have hsk : s ≫ k = e := image.fac e
    refine ⟨⟨i ≫ α.inv ≫ F.map s, F.map k ≫ α.hom ≫ r, ?_, ?_⟩⟩
    · simp only [Category.assoc, ← F.map_comp_assoc, hsk, hmap]
      simp [hri]
    · have h' : α.hom ≫ r ≫ i ≫ α.inv = F.map (s ≫ k) := by
        rw [hsk, hmap]
      calc
        (F.map k ≫ α.hom ≫ r) ≫ i ≫ α.inv ≫ F.map s =
            F.map k ≫ (α.hom ≫ r ≫ i ≫ α.inv) ≫ F.map s := by simp [Category.assoc]
        _ = F.map k ≫ F.map (s ≫ k) ≫ F.map s := by rw [h']
        _ = F.map ((k ≫ s) ≫ (k ≫ s)) := by simp only [F.map_comp, Category.assoc]
        _ = 𝟙 _ := by simp only [hks, Category.id_comp, F.map_id]

/-- A derived retract of a finite-coefficient constructible finite-Tor complex has
constructible cohomology given by the pulled-back images of unique étale idempotents,
and retains every cohomological and Tor interval.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-ctf.proof.md, (3), finite-ring thickness; Stacks 09AK, 09AL and 03RZ
(blueprint: lem-sfb-finite-ctf-retract-etale-images).

Proof in words:
1. Use the normalized encoding and encoding_constructibility to identify the bounded
   constructible fixed-scalar complex. On a qcqs scheme its constructibility differs
   from the source convention only by the size of a covering index. Resize the index,
   descend the cohomology sheaves, and apply boundedConstructible_of_homology to choose
   C₀ and α. The finite-value/source étale constructibility comparison identifies the
   two étale conventions. encoding_tensor_tor and the source fixed-module comparison
   reflect a Tor interval of C to C₀.
2. Applying cohomology to the encoded retraction gives a retraction in sheaves.
   Conjugate its opposite composite by finiteCtfComparisonHomologyIso. Fullness of
   the sheaf comparison lifts it to e_q; faithfulness proves idempotence and uniqueness.
3. For the canonical image factorization s_q followed by k_q equals e_q, idempotence
   implies k_q followed by s_q equals identity, by cancelling the epimorphism s_q and
   monomorphism k_q. Thus image(e_q) is a retract of H^q(C₀). The proved constructible
   retract theorem, obtained by taking the kernel of the complementary idempotent,
   makes this image constructible. The finite-value comparison gives the stated notion.
4. The maps H^q(i) α_q.inv ν*(s_q) and ν*(k_q) α_q.hom H^q(r) are inverse, using the
   splitting and retraction equations. Constructibility of the pulled-back étale image
   follows from isConstructible_comparisonUpperStar_obj. Resize its covering index to
   recover the ordinary encoding convention. Boundedness passes to retracts, and
   encoding_constructibility gives bounded constructibility of J in internal coordinates.
5. Every homology of J is a retract of the corresponding homology of C, so vanishing
   passes to J. The generic Tor amplitude and finite Tor amplitude retract instances
   preserve every Tor interval and finite Tor amplitude in the ambient unbounded
   category. Combining this with bounded constructibility proves J belongs to Dctf. -/
theorem finiteCtfRetractEtaleImages (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (B : Type u) [CommRing B] [Finite B]
    [TopologicalSpace B] [DiscreteTopology B]
    (C J : DerivedCategory (FiniteDiscreteOrdinary.Internal B X))
    (hC : (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient B) X ⊓
      fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K) C)
    (i : J ⟶ C) (r : C ⟶ J) (hri : i ≫ r = 𝟙 J) :
    (∃ E : FiniteDiscreteOrdinary.Encoding B X,
      ∃ C₀ : DerivedCategory
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} B))),
        Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} B) X C₀ ∧
        (∃ a b : ℤ, a ≤ b ∧
          Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} B) X a b C₀) ∧
        ∃ α : (comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).mapDerivedCategory.obj C₀ ≅
              E.fixedDerived.functor.obj C,
          ∀ q : ℤ, ∃ e : End ((DerivedCategory.homologyFunctor _ q).obj C₀),
            e ≫ e = e ∧
            (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).map e ≫
                (finiteCtfComparisonHomologyIso X B C₀ _ α q).hom =
              (finiteCtfComparisonHomologyIso X B C₀ _ α q).hom ≫
                (DerivedCategory.homologyFunctor _ q).map (E.fixedDerived.functor.map r) ≫
                (DerivedCategory.homologyFunctor _ q).map (E.fixedDerived.functor.map i) ∧
            (∀ e' : End ((DerivedCategory.homologyFunctor _ q).obj C₀),
              e' ≫ e' = e' →
              (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).map e' ≫
                  (finiteCtfComparisonHomologyIso X B C₀ _ α q).hom =
                (finiteCtfComparisonHomologyIso X B C₀ _ α q).hom ≫
                  (DerivedCategory.homologyFunctor _ q).map (E.fixedDerived.functor.map r) ≫
                  (DerivedCategory.homologyFunctor _ q).map (E.fixedDerived.functor.map i) →
              e' = e) ∧
            Scheme.IsConstructibleEtaleModuleSheaf (image e) ∧
            Nonempty ((DerivedCategory.homologyFunctor _ q).obj
              (E.fixedDerived.functor.obj J) ≅
                (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).obj
                  (image e))) ∧
    (∀ q : ℤ, IsConstantModelConstructible (FiniteDiscreteOrdinary.coefficient B) X
      ((DerivedCategory.homologyFunctor _ q).obj J)) ∧
    (∀ a b : ℤ, (∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj C)) →
        ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((DerivedCategory.homologyFunctor _ q).obj J)) ∧
    (∀ a b : ℤ, a ≤ b → _root_.DerivedCategory.torAmplitudeIn _ a b C →
      _root_.DerivedCategory.torAmplitudeIn _ a b J) ∧
    (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient B) X ⊓
      fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K) J := by
  classical
  let E := (FiniteDiscreteOrdinary.encoding_exists B X).some
  obtain ⟨C₀, hc₀, ht₀, ⟨α⟩⟩ := finiteEtaleModel X B E C hC
  let R : Retract J C := ⟨i, r, hri⟩
  have himages (q : ℤ) := liftedImage
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X)
    (finiteCtfComparisonHomologyIso X B C₀ _ α q)
    ((DerivedCategory.homologyFunctor _ q).map (E.fixedDerived.functor.map i))
    ((DerivedCategory.homologyFunctor _ q).map (E.fixedDerived.functor.map r))
    ((R.map E.fixedDerived.functor).map (DerivedCategory.homologyFunctor _ q)).retract
  have himages' (q : ℤ) : ∃ e : End ((DerivedCategory.homologyFunctor _ q).obj C₀),
      e ≫ e = e ∧
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).map e ≫
          (finiteCtfComparisonHomologyIso X B C₀ _ α q).hom =
        (finiteCtfComparisonHomologyIso X B C₀ _ α q).hom ≫
          (DerivedCategory.homologyFunctor _ q).map (E.fixedDerived.functor.map r) ≫
          (DerivedCategory.homologyFunctor _ q).map (E.fixedDerived.functor.map i) ∧
      (∀ e', e' ≫ e' = e' →
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).map e' ≫
            (finiteCtfComparisonHomologyIso X B C₀ _ α q).hom =
          (finiteCtfComparisonHomologyIso X B C₀ _ α q).hom ≫
            (DerivedCategory.homologyFunctor _ q).map (E.fixedDerived.functor.map r) ≫
            (DerivedCategory.homologyFunctor _ q).map (E.fixedDerived.functor.map i) →
          e' = e) ∧
      Scheme.IsConstructibleEtaleModuleSheaf (image e) ∧
      Nonempty ((DerivedCategory.homologyFunctor _ q).obj (E.fixedDerived.functor.obj J) ≅
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).obj (image e)) := by
    obtain ⟨e, he, hcomm, huniq, hiso⟩ := himages q
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
      (hc₀.1 q)
    have : Scheme.IsConstructibleSheaf (image e) :=
      Scheme.IsConstructibleSheaf.of_retract ⟨image.ι e, factorThruImage e,
        imageSplitting e he⟩
    exact ⟨e, he, hcomm, huniq,
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
        inferInstance, hiso⟩
  have hbJ : DerivedCategory.TStructure.t.bounded J := by
    obtain ⟨a, b, h⟩ := (DerivedCategory.exists_homologyConcentratedIn_iff_bounded C).mpr hC.1.1
    exact (DerivedCategory.exists_homologyConcentratedIn_iff_bounded J).mp
      ⟨a, b, (DerivedCategory.homologyConcentratedIn a b).prop_of_retract R h⟩
  have hfixed : FiniteDiscreteOrdinary.ordinaryBoundedConstructible B X
      (E.fixedDerived.functor.obj J) := by
    refine ⟨(E.ordinary.functor ⋙ E.fixed.functor).bounded_mapDerivedCategory_obj hbJ, ?_⟩
    intro q
    obtain ⟨e, _, _, _, hc, ⟨β⟩⟩ := himages' q
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hc
    exact (ordinaryConstructible_iff B X _).mpr
      (isConstructible_of_iso β.symm (isConstructible_comparisonUpperStar_obj (image e)))
  have hcJ := (FiniteDiscreteOrdinary.encoding_constructibility B X E).2 J |>.mpr hfixed
  refine ⟨⟨E, C₀, hc₀, ht₀, α, himages'⟩, hcJ.2, ?_, ?_, hcJ, ?_⟩
  · intro a b h q hq
    let S := R.map (DerivedCategory.homologyFunctor _ q)
    exact IsZero.of_mono S.i (h q hq)
  · intro a b _ h
    exact (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_retract R h
  · exact (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_retract R hC.2

end AlgebraicGeometry.ProEtale
