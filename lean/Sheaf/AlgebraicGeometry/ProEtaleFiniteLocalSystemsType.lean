/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q79
-/
module

public import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
public import Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Sheaf.AlgebraicGeometry.ProEtaleConstantModuleRestriction
import Sheaf.AlgebraicGeometry.ProEtaleConstantModuleModelRigidity
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Clopen decomposition by the module model of a pro-etale local system

Source: Weil blueprint, main-20261015, sec-proetale-coefficients,
`sk-prop-pe-finite-local-systems/sk-prop-pe-finite-local-systems-type.md`
(blueprint: det-pe-finite-local-systems-type).

The models are modules over the universe lift of the discrete coefficient ring.
Restriction to a piece is expressed on covering objects over that open in the
original small pro-etale site, using the recorded localized module construction.
-/

@[expose] public section

set_option autoImplicit false

universe t u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem exists_locallyConstant_label (X : Scheme.{t})
    {I : Type (t + 1)} (V : I → X.ProEt)
    (f : ∀ i : I, V i ⟶ ProEt.mk (𝟙 X))
    (hf : Presieve.ofArrows V f ∈ (ProEt.precoverage X).coverings _)
    {R : Type v} (label : I → R)
    (hc : ∀ (i j : I) (a : (V i).left) (b : (V j).left),
      (V i).hom a = (V j).hom b → label i = label j) :
    ∃ l : LocallyConstant X R, ∀ (i : I) (x : (V i).left),
      l ((V i).hom x) = label i := by
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  let π : ∀ i : I, (V i).left ⟶ X := fun i ↦ (V i).hom
  have hπ (i : I) : (f i).left = π i := by
    exact (Category.comp_id (f i).left).symm.trans (f i).w
  have hf' : Presieve.ofArrows (fun i ↦ (V i).left) π ∈ fpqcPrecoverage X := by
    have h := hf
    change (Presieve.ofArrows V f).map (ProEt.forget X ⋙ Over.forget X) ∈
      proetalePrecoverage X at h
    rw [Presieve.map_ofArrows] at h
    change Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage X at h
    simp_rw [hπ] at h
    exact proetalePrecoverage_le_fpqcPrecoverage _ h
  let P := continuousMapPresheaf R
  let s (i : I) : P.obj (Opposite.op (V i).left) := ContinuousMap.const _ (label i)
  have hcompat : ∀ ⦃W : Scheme.{t}⦄ ⦃i j : I⦄
      (a : W ⟶ (V i).left) (b : W ⟶ (V j).left),
      a ≫ π i = b ≫ π j →
        (↾fun _ : PUnit ↦ s i) ≫ P.map a.op =
          (↾fun _ : PUnit ↦ s j) ≫ P.map b.op := by
    intro W i j a b hab
    apply ConcreteCategory.hom_ext
    intro z
    apply ContinuousMap.ext
    intro x
    exact hc i j (a x) (b x) (congrArg (fun g : W ⟶ X ↦ g x) hab)
  obtain ⟨g, hg, _⟩ :=
    (isSheaf_fpqcTopology_continuousMapPresheaf R).existsUnique_amalgamation_ofArrows
      π (Precoverage.generate_mem_toGrothendieck hf')
      (fun i ↦ (↾fun _ : PUnit ↦ s i)) hcompat
  let c : C(X, R) := g PUnit.unit
  refine ⟨⟨c, (IsLocallyConstant.iff_continuous _).mpr c.continuous⟩, ?_⟩
  intro i x
  have hi := ConcreteCategory.congr_hom (hg i) PUnit.unit
  exact congrArg (fun k : C((V i).left, R) ↦ k x) hi

set_option backward.isDefEq.respectTransparency false in
private noncomputable def constant_model_iso (X : Scheme.{t}) (Λ : Type u) [CommRing Λ]
    (U : X.ProEt) (M N : ModuleCat.{max u (t + 1)} (ULift.{t + 1, u} Λ)) (e : M ≅ N) :
    proEtaleConstantModuleSheafOverOfUniverses X Λ U M ≅
      proEtaleConstantModuleSheafOverOfUniverses X Λ U N := by
  let : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  let : HasSheafify ((ProEt.topology X).over U) AddCommGrpCat.{max u (t + 1)} :=
    hasSheafifyEssentiallySmallSite _ _
  let : ((ProEt.topology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have := (proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses X Λ U).1
  have := (proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses X Λ U).2
  let p : proEtaleConstantModulePresheafOfUniverses (Over U) Λ M ≅
      proEtaleConstantModulePresheafOfUniverses (Over U) Λ N :=
    { hom := { app _ := e.hom }
      inv := { app _ := e.inv } }
  exact (PresheafOfModules.sheafification _).mapIso p

set_option backward.isDefEq.respectTransparency false in
private theorem empty_slice_iso (X : Scheme.{t}) (Λ : Type u) [CommRing Λ]
    (U : X.ProEt) [IsEmpty U.left]
    (F G : SheafOfModules.{max u (t + 1)}
      (((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj
            (CommRingCat.of (ULift.{t + 1, u} Λ)))).over U)) : Nonempty (F ≅ G) := by
  have hz (H : SheafOfModules.{max u (t + 1)}
      (((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj
            (CommRingCat.of (ULift.{t + 1, u} Λ)))).over U)) : IsZero H := by
    apply (IsZero.iff_id_eq_zero _).2
    ext T x
    let : IsEmpty T.unop.left.left :=
      ⟨fun z ↦ isEmptyElim (T.unop.hom.left z)⟩
    let A := (SheafOfModules.toSheaf _).obj H
    have hb : ⊥ ∈ ((ProEt.topology X).over U) T.unop := by
      rw [GrothendieckTopology.mem_over_iff, map_bot]
      exact ProEt.bot_mem_topology _
    have ht := (A.isTerminalOfBotCover T.unop hb).isZero
    let : Subsingleton (A.obj.obj T) := AddCommGrpCat.subsingleton_of_isZero ht
    exact @Subsingleton.elim _ (AddCommGrpCat.subsingleton_of_isZero ht) _ _
  exact ⟨(hz F).iso (hz G)⟩

/-- The coproduct of the clopen fibres realizes the original scheme.
Source: Stacks Project, Schemes Lemmas 01JB and 01HI, via
`coproductCopiesMorphismsClopen` (blueprint: det-pe-finite-local-systems-type-coproduct).
The open pieces are pairwise disjoint and cover X, so the universal morphism from
its scheme coproduct is an isomorphism on the underlying locally ringed spaces. -/
theorem finiteLocalSystemsType_coproduct (X : Scheme.{t}) (R : Type v)
    (U : R → X.Opens) (hU : IsClopenDecomposition X R U) :
    Nonempty (IsColimit (Cofan.mk X (fun r : R ↦ (U r).ι))) := by
  classical
  let cover : X.OpenCover := Cover.mkOfCovers R (fun r ↦ (U r).toScheme)
    (fun r ↦ (U r).ι) (fun x ↦ by
      have hx : x ∈ ⨆ r, U r := by rw [hU.2]; trivial
      obtain ⟨r, hr⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨r, ⟨x, hr⟩, rfl⟩)
  have compatible (s : Cofan (fun r ↦ (U r).toScheme)) (i j : R) :
      pullback.fst (U i).ι (U j).ι ≫ s.inj i =
        pullback.snd (U i).ι (U j).ι ≫ s.inj j := by
    by_cases hij : i = j
    · subst j
      have he : pullback.fst (U i).ι (U i).ι = pullback.snd (U i).ι (U i).ι :=
        (cancel_mono (U i).ι).mp (pullback.condition)
      rw [he]
    · have : IsEmpty (pullback (U i).ι (U j).ι : Scheme.{t}) := by
        refine ⟨fun x ↦ ?_⟩
        have he := congrArg
          (fun f : pullback (U i).ι (U j).ι ⟶ X ↦ f x) (pullback.condition)
        have hi := (pullback.fst (U i).ι (U j).ι x).property
        have hj := (pullback.snd (U i).ι (U j).ι x).property
        change (pullback.fst (U i).ι (U j).ι x).1 =
          (pullback.snd (U i).ι (U j).ι x).1 at he
        exact (hU.1 i j hij).le_bot ⟨hi, he.symm ▸ hj⟩
      exact isInitialOfIsEmpty.hom_ext _ _
  refine ⟨Cofan.IsColimit.mk _ (fun s ↦ cover.glueMorphisms s.inj (compatible s))
    (fun s r ↦ cover.ι_glueMorphisms _ _ r) ?_⟩
  intro s m hm
  apply cover.hom_ext
  intro r
  exact (hm r).trans (cover.ι_glueMorphisms _ _ r).symm

set_option linter.unusedVariables false in
/-- A finite-presentation local system decomposes its base by its constant module model.
Source: Weil blueprint, main-20261015, sec-proetale-coefficients,
`sk-prop-pe-finite-local-systems-type.md`
(blueprint: det-pe-finite-local-systems-type).

Proof: choose local models on a trivializing cover, and choose their unique
representative labels. Overlap rigidity makes the labels agree above each base
point. Descend the constant label functions using the fpqc sheaf of continuous
maps to the discrete type R. The fibres of the descended locally constant map
are disjoint opens covering X. Glue scheme morphisms on those disjoint opens to
prove the coproduct universal property, without any smallness assumption on R.
Base change the original cover to each fibre and restrict its trivializations.
On nonempty members its representative label is the fibre label; on empty
members every module sheaf is zero. -/
theorem finiteLocalSystemsType (X : Scheme.{t}) (Λ : Type u) [CommRing Λ]
    (F : SheafOfModules.{max u (t + 1)}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj
            (CommRingCat.of (ULift.{t + 1, u} Λ)))))
    (hF : IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses X Λ
      (fun M ↦ Module.FinitePresentation (ULift.{t + 1, u} Λ) M) F)
    (R : Type v) (model : R → ModuleCat.{max u (t + 1)} (ULift.{t + 1, u} Λ))
    (hmodel : ∀ r : R, Module.FinitePresentation (ULift.{t + 1, u} Λ) (model r))
    (hrep : ∀ M : ModuleCat.{max u (t + 1)} (ULift.{t + 1, u} Λ),
      Module.FinitePresentation (ULift.{t + 1, u} Λ) M →
        ∃! r : R, Nonempty (M ≅ model r)) :
    ∃ U : R → X.Opens,
      IsClopenDecomposition X R U ∧
      Nonempty (IsColimit (Cofan.mk X (fun r : R ↦ (U r).ι))) ∧
      ∀ r : R, ∃ (I : Type (t + 1)) (V : I → X.ProEt)
        (f : ∀ i : I, V i ⟶ ProEt.mk (U r).ι),
        Presieve.ofArrows V f ∈ (ProEt.precoverage X).coverings _ ∧
          ∀ i : I,
            Nonempty (F.over (V i) ≅
              proEtaleConstantModuleSheafOverOfUniverses X Λ (V i) (model r)) := by
  classical
  obtain ⟨I, V, f, hf, hlocal⟩ := hF
  choose M hM e using hlocal
  choose label hlabel hunique using fun i ↦ hrep (M i) (hM i)
  have compatible (i j : I) (x : (V i).left) (y : (V j).left)
      (hxy : (V i).hom x = (V j).hom y) : label i = label j := by
    obtain ⟨a⟩ := proEtaleConstantModule_model_rigidity X Λ F (V i) (V j)
      (M i) (M j) (e i) (e j) x y hxy
    obtain ⟨b⟩ := hlabel j
    exact (hunique i (label j) ⟨a ≪≫ b⟩).symm
  obtain ⟨l, hl⟩ := exists_locallyConstant_label X V f hf label compatible
  let U : R → X.Opens := fun r ↦
    ⟨{x | l x = r}, l.isLocallyConstant.isOpen_fiber r⟩
  have hU : IsClopenDecomposition X R U := by
    refine ⟨?_, ?_⟩
    · intro r r' h
      rw [disjoint_iff]
      ext x
      change (l x = r ∧ l x = r') ↔ False
      exact ⟨fun hx ↦ h (hx.1.symm.trans hx.2), False.elim⟩
    · apply top_unique
      intro x _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨l x, rfl⟩
  refine ⟨U, hU, ?_, ?_⟩
  · exact finiteLocalSystemsType_coproduct X R U hU
  · intro r
    let j : ProEt.mk (U r).ι ⟶ ProEt.mk (𝟙 X) :=
      MorphismProperty.Over.homMk (U r).ι (Category.comp_id _)
    let W : I → X.ProEt := fun i ↦ pullback j (f i)
    let g : ∀ i : I, W i ⟶ ProEt.mk (U r).ι := fun i ↦ pullback.fst j (f i)
    have hg : Presieve.ofArrows W g ∈ (ProEt.precoverage X).coverings _ :=
      Precoverage.mem_coverings_of_isPullback f hf j g
        (fun i ↦ pullback.snd j (f i)) (fun i ↦ IsPullback.of_hasPullback _ _)
    refine ⟨I, W, g, hg, ?_⟩
    intro i
    obtain ⟨a⟩ := proEtaleConstantModule_restrict X Λ F (V i) (W i)
      (pullback.snd j (f i)) (M i) (e i)
    by_cases hi : label i = r
    · obtain ⟨b⟩ := hlabel i
      exact ⟨a ≪≫ constant_model_iso X Λ (W i) (M i) (model r) (hi ▸ b)⟩
    · have hempty : IsEmpty (W i).left := by
        refine ⟨fun x ↦ hi ?_⟩
        have hleft := hl i ((pullback.snd j (f i)).left x)
        have hw : (W i).hom x = (V i).hom ((pullback.snd j (f i)).left x) :=
          (congrArg (fun k : (W i).left ⟶ X ↦ k x)
            (pullback.snd j (f i)).w).symm
        have hr : l ((W i).hom x) = r := by
          have he := congrArg (fun k : (W i).left ⟶ X ↦ k x) (g i).w
          exact he ▸ ((g i).left x).property
        exact hleft.symm.trans (hw ▸ hr)
      let : IsEmpty (W i).left := hempty
      exact empty_slice_iso X Λ (W i) _ _

end AlgebraicGeometry.Scheme
