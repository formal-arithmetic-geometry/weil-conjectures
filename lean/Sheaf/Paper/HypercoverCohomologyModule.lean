module

public import WeilConjectures.AlgebraicGeometry.HypercoverCohomologyColimit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.Paper.HypercoverResolutionModel
import Sheaf.Paper.HypercoverInjectiveModuleRow
import Sheaf.Paper.HypercoverBottomRefinement
import Sheaf.Paper.FiniteSplitHypercoverRefinement
import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
import Mathlib.Algebra.Homology.Opposite

@[expose] public section

universe u₁ u v w z

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

private theorem module_colimit_of_representatives
    {R : Type u} [Ring R] {ι : Type v} {C : ι → ModuleCat.{w} R}
    {Ref : ι → ι → Type z}
    (common : ∀ i j, ∃ k, Nonempty (Ref k i) ∧ Nonempty (Ref k j))
    (t : ∀ {i j}, Ref i j → (C j ⟶ C i))
    {H : ModuleCat.{w} R} (c : ∀ i, C i ⟶ H)
    (hc : ∀ i j (f : Ref i j), t f ≫ c i = c j)
    (cover : ∀ y : H, ∃ (i : ι) (x : C i), c i x = y)
    (kill : ∀ i (x : C i), c i x = 0 → ∃ (j : ι) (f : Ref j i), t f x = 0)
    (B : ModuleCat.{w} R) (d : ∀ i, C i ⟶ B)
    (hd : ∀ i j (f : Ref i j), t f ≫ d i = d j) :
    ∃! e : H ⟶ B, ∀ i, c i ≫ e = d i := by
  classical
  have hc' (i j : ι) (f : Ref i j) (x : C j) : c i (t f x) = c j x :=
    congrArg (fun a ↦ a x) (hc i j f)
  have hd' (i j : ι) (f : Ref i j) (x : C j) : d i (t f x) = d j x :=
    congrArg (fun a ↦ a x) (hd i j f)
  have agree (i j : ι) (x : C i) (y : C j) (h : c i x = c j y) : d i x = d j y := by
    obtain ⟨k, ⟨a⟩, ⟨b⟩⟩ := common i j
    have hz : c k (t a x - t b y) = 0 := by
      rw [map_sub, hc', hc', h, sub_self]
    obtain ⟨l, f, hf⟩ := kill k (t a x - t b y) hz
    have heq : d k (t a x - t b y) = 0 := by
      rw [← hd' l k f, hf, map_zero]
    simpa only [map_sub, hd', sub_eq_zero] using heq
  have cover_copy := cover
  choose idx rep hrep using cover_copy
  let e : H → B := fun y ↦ d (idx y) (rep y)
  have he (i : ι) (x : C i) : e (c i x) = d i x := by
    exact agree _ _ _ _ (hrep (c i x))
  have headd (y z : H) : e (y + z) = e y + e z := by
    obtain ⟨i, x, rfl⟩ := cover y
    obtain ⟨j, v, rfl⟩ := cover z
    obtain ⟨k, ⟨a⟩, ⟨b⟩⟩ := common i j
    rw [← hc' k i a x, ← hc' k j b v, ← map_add, he, map_add, he, he]
  have hesmul (r : R) (y : H) : e (r • y) = r • e y := by
    obtain ⟨i, x, rfl⟩ := cover y
    rw [← map_smul, he, map_smul, he]
  let E : H ⟶ B := ModuleCat.ofHom
    { toFun := e
      map_add' := headd
      map_smul' := hesmul }
  refine ⟨E, ?_, ?_⟩
  · intro i
    ext x
    exact he i x
  · intro E' hE'
    ext y
    obtain ⟨i, x, rfl⟩ := cover y
    calc
      E' (c i x) = d i x := congrArg (fun a ↦ a x) (hE' i)
      _ = E (c i x) := (he i x).symm

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable {R : Type (u + 1)} [Ring R]

private theorem coface_d_eq (K : CosimplicialObject (ModuleCat.{u + 1} R)) (i j : ℕ) :
    (((alternatingFaceMapComplex (ModuleCat R)ᵒᵖ).obj K.op).d j i).unop =
      ((alternatingCofaceMapComplex (ModuleCat R)).obj K).d i j := by
  by_cases hij : i + 1 = j
  · subst j
    simp only [alternatingFaceMapComplex_obj_d, alternatingCofaceMapComplex,
      AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
      AlternatingCofaceMapComplex.objD, AlternatingFaceMapComplex.objD,
      unop_sum, unop_zsmul]
    rfl
  · simp [alternatingFaceMapComplex, AlternatingFaceMapComplex.obj,
      alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj,
      hij]

private noncomputable def cofaceUnopIso (K : CosimplicialObject (ModuleCat.{u + 1} R)) :
    (alternatingCofaceMapComplex (ModuleCat R)).obj K ≅
      ((alternatingFaceMapComplex (ModuleCat R)ᵒᵖ).obj K.op).unop :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro i j _
    simpa using (coface_d_eq K i j))

private noncomputable def refinementCochainHomotopy
    {U V : FiniteSplitEtaleHypercover X} (f g : U.Refinement V)
    (h : SimplicialObject.Homotopy f g)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    Homotopy
      ((alternatingCofaceMapComplex (ModuleCat R)).map
        (Functor.whiskerRight f.rightOp F.obj))
      ((alternatingCofaceMapComplex (ModuleCat R)).map
        (Functor.whiskerRight g.rightOp F.obj)) := by
  let h' := (h.whiskerRight F.obj.rightOp).toChainHomotopy.unop
  let eU := cofaceUnopIso (U.simplicial.rightOp ⋙ F.obj)
  let eV := cofaceUnopIso (V.simplicial.rightOp ⋙ F.obj)
  convert (h'.compLeft eV.hom).compRight eU.inv using 1 <;>
    ext n <;> simp [eU, eV, cofaceUnopIso] <;> rfl

private theorem homotopy_invariance (q : ℕ)
    {U V : FiniteSplitEtaleHypercover X} (f g : U.Refinement V)
    (h : isRefinementHomotopic f g) :
    cohomologyRefinement (ModuleCat.{u + 1} R) f q =
      cohomologyRefinement (ModuleCat.{u + 1} R) g q := by
  induction h with
  | rel f g h =>
      obtain ⟨h⟩ := h
      apply NatTrans.ext
      funext F
      exact (refinementCochainHomotopy f g h F).homologyMap_eq q
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end AlgebraicGeometry.FiniteSplitEtaleHypercover


open CategoryTheory

namespace AlgebraicGeometry

private theorem colimit_of_resolution_refinements
    {X : Scheme.{u₁}} [CompactSpace X] [QuasiSeparatedSpace X]
    (q : ℕ) (R : Type (u₁ + 1)) [Ring R]
    (hrow : ∀ (U : FiniteSplitEtaleHypercover X)
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{u₁ + 1} R)),
      Injective F → QuasiIso (FiniteSplitEtaleHypercover.sectionAugmentation R U F))
    (hcover : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u₁ + 1} R))
      (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X)
      (y : ((FiniteSplitEtaleHypercover.resolutionDoubleComplex R U I.cocomplex).total
        (.up ℕ)).homology q),
      ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U)
        (x : ((FiniteSplitEtaleHypercover.sectionComplexFunctor R V).obj F).homology q),
      HomologicalComplex.homologyMap
          (FiniteSplitEtaleHypercover.bottomInclusion R V I) q x =
        HomologicalComplex.homologyMap
          (FiniteSplitEtaleHypercover.totalRefinement R f I.cocomplex) q y)
    (hkill : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u₁ + 1} R))
      (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X)
      (x : ((FiniteSplitEtaleHypercover.sectionComplexFunctor R U).obj F).homology q),
      HomologicalComplex.homologyMap
        (FiniteSplitEtaleHypercover.bottomInclusion R U I) q x = 0 →
      ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U),
        (FiniteSplitEtaleHypercover.cohomologyRefinement (ModuleCat R) f q).app F x = 0) :
    FiniteSplitEtaleHypercover.IsCohomologyColimit (ModuleCat.{u₁ + 1} R) q
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u₁ + 1} R)) 0 ⋙
        Etale.cohomology (ModuleCat.{u₁ + 1} R) X (q : ℤ)) := by
  classical
  let e := FiniteSplitEtaleHypercover.derivedSingleIso (X := X) R q
  let c (U : FiniteSplitEtaleHypercover X) :=
    FiniteSplitEtaleHypercover.comparisonNat R hrow U q ≫ e.inv
  have hc (U V : FiniteSplitEtaleHypercover X) (f : U.Refinement V) :
      FiniteSplitEtaleHypercover.cohomologyRefinement (ModuleCat R) f q ≫ c U = c V := by
    dsimp only [c]
    rw [← Category.assoc, FiniteSplitEtaleHypercover.comparisonNat_refinement]
  refine ⟨fun _ _ f g h ↦ FiniteSplitEtaleHypercover.homotopy_invariance q f g h,
    c, hc, ?_⟩
  intro F B d hd
  let I := injectiveResolution F
  let hA (U : FiniteSplitEtaleHypercover X) :=
    FiniteSplitEtaleHypercover.resolutionAugmentation_quasiIso R hrow U I
  let a (U : FiniteSplitEtaleHypercover X) :=
    FiniteSplitEtaleHypercover.totalComparisonAt R U I q ≫ e.inv.app F
  have ha (U : FiniteSplitEtaleHypercover X) : IsIso (a U) := by
    dsimp only [a]
    infer_instance
  have hca (U : FiniteSplitEtaleHypercover X) :
      (c U).app F =
        HomologicalComplex.homologyMap
          (FiniteSplitEtaleHypercover.bottomInclusion R U I) q ≫ a U := by
    rfl
  have haf {U V : FiniteSplitEtaleHypercover X} (f : U.Refinement V) :
      HomologicalComplex.homologyMap
          (FiniteSplitEtaleHypercover.totalRefinement R f I.cocomplex) q ≫ a U = a V := by
    dsimp only [a]
    rw [← Category.assoc, FiniteSplitEtaleHypercover.totalComparisonAt_refinement]
  apply module_colimit_of_representatives
    (C := fun U ↦ (FiniteSplitEtaleHypercover.cohomologyFunctor (ModuleCat R) U q).obj F)
    (Ref := fun U V ↦ U.Refinement V)
    (common := (FiniteSplitEtaleHypercover.exists_and_cofiltered X).2.1)
    (t := fun f ↦ (FiniteSplitEtaleHypercover.cohomologyRefinement (ModuleCat R) f q).app F)
    (c := fun U ↦ (c U).app F)
    (hc := fun U V f ↦ congrArg (fun k ↦ k.app F) (hc U V f))
    (B := B) (d := d) (hd := hd)
  · intro y
    obtain ⟨U⟩ := (FiniteSplitEtaleHypercover.exists_and_cofiltered X).1
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (a U)).mp inferInstance y
    obtain ⟨V, f, x, hx⟩ := hcover F I U z
    refine ⟨V, x, ?_⟩
    rw [hca]
    change a V (HomologicalComplex.homologyMap
      (FiniteSplitEtaleHypercover.bottomInclusion R V I) q x) = y
    rw [hx]
    exact (congrArg (fun k ↦ k z) (haf f)).trans hz
  · intro U x hx
    apply hkill F I U x
    have hinj := (ModuleCat.mono_iff_injective (a U)).mp inferInstance
    apply hinj
    rw [map_zero]
    exact ((congrArg (fun k ↦ k x) (hca U)).symm.trans hx)


/-- The constant-ring module part of hypercover cohomology comparison.
Source: Stacks Project, Tag 01H0; blueprint order 949.
Proof: construct a natural comparison through the explicit section bicomplex of an
injective resolution. Injective rows make its global augmentation a quasi-isomorphism.
Finite refinement descent for its bottom inclusion gives representatives of every
class and kills every comparison kernel. Common refinements then make the induced
map to an arbitrary cocone well defined and R-linear. Dualized simplicial homotopies
show that the cohomology maps respect the refinement homotopy relation. The canonical
comparison with derived terminal sections identifies the cocone point with the stated
etale cohomology functor. All coefficient structures use only Ring R.
(blueprint: thm-weil-pbc-hypercover-cohomology-module-part) -/
theorem hypercover_cohomology_module_part (X : Scheme.{u₁}) [CompactSpace X]
    [QuasiSeparatedSpace X] (q : ℕ) (R : Type (u₁ + 1)) [Ring R] :
    FiniteSplitEtaleHypercover.IsCohomologyColimit (ModuleCat.{u₁ + 1} R) q
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u₁ + 1} R)) 0 ⋙
        Etale.cohomology (ModuleCat.{u₁ + 1} R) X (q : ℤ)) := by
  apply colimit_of_resolution_refinements q R
  · intro U F hF
    let := hF
    exact FiniteSplitEtaleHypercover.injective_module_row_quasiIso U R F
  · intro F I U y
    exact (FiniteSplitEtaleHypercover.bottom_refinement_descent R F I U q).1 y
  · intro F I U x hx
    exact (FiniteSplitEtaleHypercover.bottom_refinement_descent R F I U q).2 x hx

end AlgebraicGeometry
