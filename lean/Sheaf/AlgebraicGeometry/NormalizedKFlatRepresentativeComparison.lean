/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.NormalizedFlatTelescopeComparison
import Sheaf.CategoryTheory.NatTransFromResolvingClass
import Sheaf.Algebra.Homology.FlatTruncationTower
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.Algebra.Homology.FlatTruncationTelescopeComparison
import Sheaf.AlgebraicGeometry.TensorPullbackKFlatQuasiIso

/-! # Normalized comparison on the K-flat resolving class

Source: Stacks Project, Tag 06YJ, representative computation, and the
supplied-tensorator normalization in the parent node, step 2 (agent expansion).
(blueprint: lem-sc-normalized-kflat-representative-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- Homotopy objects which are K-flat representatives or their translates by one.
This predicate records actual representatives and contains no choice of data.
Source: Stacks Project, Tag 06YJ.
(blueprint: lem-sc-normalized-kflat-representative-comparison). -/
def kFlatShiftRepresentative (Y : Scheme.{u})
    (X : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
    CochainComplex.IsKFlat (R := Y.sheaf) P ∧
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P = X ∨
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)⟦(1 : ℤ)⟧ = X)

-- Build a resolving telescope, retaining its concrete shape rather than choosing
-- a flat replacement without remembering how it was constructed.
set_option maxHeartbeats 800000 in
-- Elaborating the cone augmentation uses the concrete sheaf coproduct instances.
private theorem exists_flat_telescope_resolution (Y : Scheme.{u})
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    ∃ (R : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (s : R ⟶ P), CochainComplex.IsKFlat (R := Y.sheaf) R ∧
        isFlatTelescope Y R ∧ QuasiIso s := by
  obtain ⟨E, t, q, hbounded, hflat, hq, _, hcompat⟩ :=
    CochainComplex.exists_flat_truncation_tower P
  let a : (∐ E) ⟶ P := Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ))
  let φ : (∐ E) ⟶ (∐ E) :=
    𝟙 (∐ E) - Sigma.desc (fun n : ℕ ↦ t n ≫ Sigma.ι E (n + 1))
  have hzero : φ ≫ a = 0 := by
    dsimp [φ, a]
    rw [Preadditive.sub_comp, Category.id_comp]
    apply sub_eq_zero.mpr
    apply Sigma.hom_ext
    intro n
    simp only [Category.assoc, Sigma.ι_desc_assoc, Sigma.ι_desc]
    exact (hcompat n).symm
  have hdesc : CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain (∐ E) P (-1)) =
        CochainComplex.HomComplex.Cochain.ofHom (φ ≫ a) := by
    rw [hzero]
    simp
  let s : CochainComplex.mappingCone φ ⟶ P := CochainComplex.mappingCone.desc φ 0 a hdesc
  have hinr : CochainComplex.mappingCone.inr φ ≫ s = a :=
    CochainComplex.mappingCone.inr_desc φ 0 a hdesc
  have hinl : (CochainComplex.mappingCone.inl φ).comp
      (CochainComplex.HomComplex.Cochain.ofHom s) (add_zero _) = 0 :=
    CochainComplex.mappingCone.inl_desc φ 0 a hdesc
  have hk : CochainComplex.IsKFlat (R := Y.sheaf) (CochainComplex.mappingCone φ) := by
    apply (CochainComplex.kFlat_closure Y.sheaf).2.2.2.1 E t
    intro n
    exact (CochainComplex.kFlat_closure Y.sheaf).1 (E n) (hbounded n) (hflat n)
  refine ⟨CochainComplex.mappingCone φ, s, hk, ⟨E, t, hbounded, hflat, rfl⟩, ?_⟩
  exact CochainComplex.quasiIso_flat_truncation_telescope P E t q hq hcompat s hinr hinl

-- Naturality of the explicit translated-unit comparison; no pullback shift is chosen.
private theorem unit_shift_naturality (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {K N : schemeDerivedCategory X} (b : K ⟶ N) :
    (schemeCanonicalShiftUnitIso X K).hom ≫ b⟦(1 : ℤ)⟧' =
      ((𝟙_ (schemeDerivedCategory X))⟦(1 : ℤ)⟧) ◁ b ≫
        (schemeCanonicalShiftUnitIso X N).hom := by
  let := schemeCanonicalTensorShift X
  let : ∀ M : schemeDerivedCategory X, (tensorRight M).CommShift ℤ :=
    fun M ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) M
  have : NatTrans.CommShift ((curriedTensor (schemeDerivedCategory X)).flip.map b) ℤ :=
    Functor.CommShift₂.commShift_flip_map (h := .int) b
  dsimp [schemeCanonicalShiftUnitIso]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← leftUnitor_naturality, Functor.map_comp]
  simpa only [Category.assoc, tensorRight, Functor.flip, curriedTensor] using
    congrArg (fun g ↦ g ≫ (shiftFunctor (schemeDerivedCategory X) (1 : ℤ)).map (λ_ N).hom)
      (NatTrans.shift_app_comm ((curriedTensor (schemeDerivedCategory X)).flip.map b)
        (1 : ℤ) (𝟙_ (schemeDerivedCategory X)))

private theorem unit_shift_inv_naturality (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {K N : schemeDerivedCategory X} (b : K ⟶ N) :
    b⟦(1 : ℤ)⟧' ≫ (schemeCanonicalShiftUnitIso X N).inv =
      (schemeCanonicalShiftUnitIso X K).inv ≫
        ((𝟙_ (schemeDerivedCategory X))⟦(1 : ℤ)⟧) ◁ b := by
  apply (cancel_epi (schemeCanonicalShiftUnitIso X K).hom).1
  rw [← Category.assoc, unit_shift_naturality]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

private theorem tensor_unit_shift_naturality {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
      (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    {K N : schemeDerivedCategory Y} (b : K ⟶ N) :
    (derivedPullback f).map (b⟦(1 : ℤ)⟧') ≫
        ((derivedPullback f).mapIso (schemeCanonicalShiftUnitIso Y N).symm ≪≫
          asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
            ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) N) ≪≫
          tensorIso e (Iso.refl _) ≪≫
          schemeCanonicalShiftUnitIso Z ((derivedPullback f).obj N)).hom =
      ((derivedPullback f).mapIso (schemeCanonicalShiftUnitIso Y K).symm ≪≫
          asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
            ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) K) ≪≫
          tensorIso e (Iso.refl _) ≪≫
          schemeCanonicalShiftUnitIso Z ((derivedPullback f).obj K)).hom ≫
        ((derivedPullback f).map b)⟦(1 : ℤ)⟧' := by
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom]
  simp only [tensorIso, Iso.refl_hom, tensorHom_def, whiskerLeft_id,
    Category.comp_id, Category.assoc]
  rw [← (derivedPullback f).map_comp_assoc, unit_shift_inv_naturality,
    Functor.map_comp_assoc, ← Functor.OplaxMonoidal.δ_natural_right_assoc]
  rw [whisker_exchange_assoc, ← unit_shift_naturality]

/-- A jointly normalized comparison on K-flat homotopy representatives and their
one-fold translates. Naturality is required only between objects of this class;
there is no natural transformation on the entire homotopy category here.

Source: Stacks Project, Tag 06YJ, K-flat computation; the tensorator coherence
part is the agent expansion of step 2 of the parent node, not an assertion of 06YJ.

Proof. For an arbitrary complex P, take a compatible tower of bounded-above
flat resolutions of its canonical truncations. Form the literal cone of one minus
the transition on their countable coproduct. Compatibility defines its augmentation
to P with zero first cone component. K-flat closure proves the cone K-flat, and
the flat truncation telescope comparison proves the augmentation a quasi-isomorphism.
In particular the explicit flat-telescope homotopy objects form a resolving class.

Use the joint normalized comparison on this smaller class and its one-fold
translates. Extend its components to a natural transformation on the homotopy
category by the right-fraction resolving-class lemma: the source functor inverts
all quasi-isomorphisms. At any unshifted K-flat P, the constructed augmentation
is a quasi-isomorphism between K-flat complexes, hence termwise tensor pullback
also inverts it after localization. Naturality then proves the extended component
at P is an isomorphism.

The shifted-unit composite b is natural by naturality of the canonical Koszul
comparison, the tensorator, and tensoring with e. The two sides of the desired
shift square are therefore natural transformations. Their components agree on
flat telescopes by the smaller comparison theorem. Precompose at an arbitrary P
with its telescope augmentation; its shifted image under the source is invertible,
so cancellation proves equality at P. At a shifted K-flat P, this equality also
proves the extended component invertible, since every other factor is invertible.
Restrict the resulting isomorphisms to the original K-flat representative class.
Their naturality and the required square are the two established natural
transformation identities. No data definition chooses an arbitrary flat resolution.
(blueprint: lem-sc-normalized-kflat-representative-comparison). -/
theorem exists_normalized_kFlat_representative_comparison
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        kFlatShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X),
        (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : kFlatShiftRepresentative Y X) (hX' : kFlatShiftRepresentative Y X')
          (s : X ⟶ X'),
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX').hom =
            (α X hX).hom ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s) ∧
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hP : CochainComplex.IsKFlat (R := Y.sheaf) P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (α (X⟦(1 : ℤ)⟧) ⟨P, hP, Or.inr rfl⟩).hom ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (α X ⟨P, hP, Or.inl rfl⟩).hom⟦(1 : ℤ)⟧' := by
  classical
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let H := HomotopyCategory A (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := A)
  let F := derivedPullback f
  let L := Q ⋙ F
  let QZ : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
      schemeDerivedCategory Z := DerivedCategory.Qh
  let G : H ⥤ schemeDerivedCategory Z :=
    (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Qh : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
        schemeDerivedCategory Z)
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  have hres (X : H) : ∃ (R : H) (s : R ⟶ X),
      flatTelescopeShiftRepresentative Y R ∧ W s := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨R, s, hR, htel, hs⟩ := exists_flat_telescope_resolution Y P
    exact ⟨q.obj R, q.map s, ⟨R, htel, Or.inl rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinv : W.IsInvertedBy L := by
    intro X X' s hs
    have : IsIso (Q.map s) := Localization.inverts Q W s hs
    exact inferInstanceAs (IsIso (F.map (Q.map s)))
  obtain ⟨e, α₀, hα₀, hsquare₀⟩ := exists_normalized_flat_telescope_comparison f
  obtain ⟨ε, hε⟩ := exists_natTrans_from_resolvingClass W
    (flatTelescopeShiftRepresentative Y) hres L G hinv (fun X hX ↦ (α₀ X hX).hom) hα₀
  -- Naturality identifies the counit at an unshifted K-flat model with its flat resolution.
  have hK (P : CochainComplex A ℤ) (hP : CochainComplex.IsKFlat (R := Y.sheaf) P) :
      IsIso (ε.app (q.obj P)) := by
    obtain ⟨R, s, hR, htel, hs⟩ := exists_flat_telescope_resolution Y P
    have hqs : W (q.map s) := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
    have hLs : IsIso (L.map (q.map s)) := hinv _ hqs
    have ht := tensorPullback_quasiIso_of_isKFlat f s hR hP hs
    have hGs : IsIso (G.map (q.map s)) := by
      change IsIso (QZ.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (((Scheme.Modules.tensorPullback f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map s)))
      exact Localization.inverts QZ (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ht)
    have hεR : IsIso (ε.app (q.obj R)) := by
      rw [hε _ ⟨R, htel, Or.inl rfl⟩]
      infer_instance
    have hcomp : IsIso (L.map (q.map s) ≫ ε.app (q.obj P)) := by
      rw [ε.naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left (L.map (q.map s)) _
  let b : shiftFunctor (schemeDerivedCategory Y) (1 : ℤ) ⋙ F ≅
      F ⋙ shiftFunctor (schemeDerivedCategory Z) (1 : ℤ) :=
    NatIso.ofComponents (fun K ↦
      F.mapIso (schemeCanonicalShiftUnitIso Y K).symm ≪≫
        asIso (Functor.OplaxMonoidal.δ F
          ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) K) ≪≫
        tensorIso e (Iso.refl _) ≪≫ schemeCanonicalShiftUnitIso Z (F.obj K))
      (fun t ↦ tensor_unit_shift_naturality f e t)
  let left : shiftFunctor H (1 : ℤ) ⋙ L ⟶ G ⋙
      shiftFunctor (schemeDerivedCategory Z) (1 : ℤ) :=
    Functor.whiskerLeft (shiftFunctor H (1 : ℤ)) ε ≫ (G.commShiftIso (1 : ℤ)).hom
  let right : shiftFunctor H (1 : ℤ) ⋙ L ⟶ G ⋙
      shiftFunctor (schemeDerivedCategory Z) (1 : ℤ) :=
    Functor.whiskerRight (Q.commShiftIso (1 : ℤ)).hom F ≫
      Functor.whiskerLeft Q b.hom ≫
      Functor.whiskerRight ε (shiftFunctor (schemeDerivedCategory Z) (1 : ℤ))
  have heq : left = right := by
    ext X
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨R, s, hR, htel, hs⟩ := exists_flat_telescope_resolution Y P
    have hqs : W (q.map s) := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
    have : IsIso (Q.map (q.map s)) := Localization.inverts Q W _ hqs
    have : IsIso (Q.map ((q.map s)⟦(1 : ℤ)⟧')) := by
      apply (NatIso.isIso_map_iff (Q.commShiftIso (1 : ℤ)) (q.map s)).2
      exact inferInstanceAs (IsIso ((shiftFunctor _ (1 : ℤ)).map (Q.map (q.map s))))
    have : IsIso ((shiftFunctor H (1 : ℤ) ⋙ L).map (q.map s)) :=
      inferInstanceAs (IsIso (F.map (Q.map ((q.map s)⟦(1 : ℤ)⟧'))))
    apply (cancel_epi ((shiftFunctor H (1 : ℤ) ⋙ L).map (q.map s))).1
    rw [left.naturality, right.naturality]
    have hr : left.app (q.obj R) = right.app (q.obj R) := by
      dsimp only [left, right, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, b, NatIso.ofComponents_hom_app]
      rw [hε _ ⟨R, htel, Or.inr rfl⟩,
        hε _ ⟨R, htel, Or.inl rfl⟩]
      exact hsquare₀ R htel
    rw [hr]
  have hiso (X : H) (hX : kFlatShiftRepresentative Y X) : IsIso (ε.app X) := by
    obtain ⟨P, hP, rfl | rfl⟩ := hX
    · exact hK P hP
    · have hεP := hK P hP
      have h := NatTrans.congr_app heq (q.obj P)
      have hright : IsIso (right.app (q.obj P)) := by
        dsimp only [right, NatTrans.comp_app, Functor.whiskerLeft_app,
          Functor.whiskerRight_app]
        infer_instance
      have hleft : IsIso (ε.app ((q.obj P)⟦(1 : ℤ)⟧) ≫
          (G.commShiftIso (1 : ℤ)).hom.app (q.obj P)) := by
        change IsIso (left.app (q.obj P))
        rw [h]
        exact hright
      exact IsIso.of_isIso_comp_right _ ((G.commShiftIso (1 : ℤ)).hom.app (q.obj P))
  let α := fun X hX ↦ @asIso _ _ _ _ (ε.app X) (hiso X hX)
  refine ⟨e, α, ?_, ?_⟩
  · intro X X' hX hX' s
    exact ε.naturality s
  · intro P hP
    exact NatTrans.congr_app heq (q.obj P)


end AlgebraicGeometry
