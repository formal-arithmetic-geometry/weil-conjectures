/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Sheaf.Paper.FiniteSplitHypercoverRefinement
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover

/-! # Simultaneous section lifts on finite hypercover refinements

Source: Stacks Project, Hypercoverings, Tag 01H0, first proof.
(blueprint: lem-sc-hypercover-refinement-section-lifts).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

private theorem glue_coproduct_sections {X : Scheme.{u}}
    (R : Type (u + 1)) [Ring R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    {l : ℕ} (T : Fin l → X.Etale) (V : X.Etale) (ι : ∀ i, T i ⟶ V)
    (hc : IsColimit (Cofan.mk V ι)) (s : ∀ i, F.obj.obj (op (T i))) :
    ∃! t : F.obj.obj (op V), ∀ i, F.obj.map (ι i).op t = s i := by
  classical
  let W₀ : Scheme.{u} := ∐ fun i ↦ (T i).left
  let f : W₀ ⟶ X := Sigma.desc (fun i ↦ (T i).hom)
  let : Etale f := IsZariskiLocalAtSource.sigmaDesc (fun i ↦ (T i).prop)
  let W : X.Etale := Scheme.Etale.mk f
  let κ : ∀ i, T i ⟶ W := fun i ↦
    MorphismProperty.Over.homMk (Sigma.ι (fun i ↦ (T i).left) i)
      (by dsimp [W]; simp [f])
  have hW : IsColimit (Cofan.mk W κ) := by
    refine Cofan.IsColimit.mk _ (fun t ↦
      MorphismProperty.Over.homMk (Sigma.desc (fun i ↦ (t.inj i).left)) ?_) ?_ ?_
    · change Sigma.desc (fun i ↦ (t.inj i).left) ≫ t.pt.hom = f
      apply Sigma.hom_ext
      intro i
      simp [f, ← Category.assoc]
    · intro t i
      apply MorphismProperty.Over.Hom.ext
      exact Sigma.ι_desc _ _
    · intro t m hm
      apply MorphismProperty.Over.Hom.ext
      apply Sigma.hom_ext
      intro i
      have h := congrArg (fun z ↦ z.left) (hm i)
      change Sigma.ι (fun i ↦ (T i).left) i ≫ m.left = (t.inj i).left at h
      simpa using h
  let e : W ≅ V := hW.coconePointUniqueUpToIso hc
  have he (i : Fin l) : κ i ≫ e.hom = ι i :=
    hW.comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
  have hκ : Sieve.ofArrows T κ ∈ X.smallEtaleTopology W := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff κ).mpr
    exact (sigmaOpenCover (fun i ↦ (T i).left)).iUnion_range
  let v (i : Fin l) : ModuleCat.of R R ⟶ F.obj.obj (op (T i)) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (s i))
  have hv {Z : X.Etale} {i j : Fin l} (a : Z ⟶ T i) (b : Z ⟶ T j)
      (h : a ≫ κ i = b ≫ κ j) : v i ≫ F.obj.map a.op = v j ≫ F.obj.map b.op := by
    by_cases hij : i = j
    · subst j
      have hab : a = b := by
        apply MorphismProperty.Over.Hom.ext
        exact (cancel_mono (Sigma.ι (fun i ↦ (T i).left) i)).mp
          (congrArg (fun z ↦ z.left) h)
      rw [hab]
    · have : IsEmpty Z.left :=
        isEmpty_of_commSq_sigmaι_of_ne
          (g := fun i ↦ (T i).left) ⟨congrArg (fun z ↦ z.left) h⟩ hij
      exact (Scheme.Etale.isTerminalSectionsOfIsEmpty F Z).hom_ext _ _
  let t := F.property.amalgamateOfArrows κ hκ v (@hv)
  have ht (i : Fin l) : F.obj.map (κ i).op (t 1) = s i := by
    have hi := ConcreteCategory.congr_hom
      (F.property.amalgamateOfArrows_map κ hκ v (@hv) i) 1
    change F.obj.map (κ i).op (t 1) = (v i) 1 at hi
    rw [show (v i) 1 = s i from LinearMap.toSpanSingleton_apply_one R _ _] at hi
    exact hi
  refine ⟨F.obj.map e.inv.op (t 1), ?_, ?_⟩
  · intro i
    rw [← ModuleCat.comp_apply, ← F.obj.map_comp, ← op_comp]
    have hei : ι i ≫ e.inv = κ i := by rw [← he i]; simp
    rw [hei]
    exact ht i
  · intro t' ht'
    have hh : F.obj.map e.hom.op t' = t 1 := by
      let a : ModuleCat.of R R ⟶ F.obj.obj (op W) :=
        ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (F.obj.map e.hom.op t'))
      let b : ModuleCat.of R R ⟶ F.obj.obj (op W) :=
        ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (t 1))
      have hab : a = b := by
        apply F.property.hom_ext_ofArrows κ hκ
        intro i
        have hi : F.obj.map (κ i).op (F.obj.map e.hom.op t') = s i := by
          rw [← ModuleCat.comp_apply, ← F.obj.map_comp, ← op_comp, he i]
          exact ht' i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        change F.obj.map (κ i).op (z • F.obj.map e.hom.op t') =
          F.obj.map (κ i).op (z • t 1)
        simp only [map_smul, hi, ht]
      have h := ConcreteCategory.congr_hom hab 1
      simpa [a, b] using h
    apply (ModuleCat.mono_iff_injective (F.obj.map e.hom.op)).mp inferInstance
    rw [hh, ← ModuleCat.comp_apply, ← F.obj.map_comp]
    simp


/-- Finitely many sections lift through a sheaf epimorphism on the constituent
pieces of one finite split refinement.
Source: Stacks Project, Tag 01H0, finite lifting conditions in its first proof.
(blueprint: lem-sc-hypercover-refinement-section-lifts).

Proof: for each section take its image sieve under the epimorphism. The local
surjectivity criterion for sheaf epimorphisms says this sieve covers. Apply simultaneous
finite refinement to these sieves. Membership of each constituent composite in the
image sieve is exactly the asserted section lift. No choices of compatible lifts are
needed, and the argument includes an empty list of requirements or empty constituents. -/
private theorem exists_refinement_lifting_sections_pieces {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (U : FiniteSplitEtaleHypercover X)
    (R : Type (u + 1)) [Ring R]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)} (p : F ⟶ G) [Epi p]
    (r k : ℕ) (degree : Fin k → Fin (r + 1))
    (s : ∀ j : Fin k,
      G.obj.obj (op (U.simplicial.obj (op (SimplexCategory.mk (degree j).val))))) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U),
      ∀ n : Fin (r + 1), ∃ (l : ℕ) (T : Fin l → X.Etale)
        (ι : ∀ i, T i ⟶ V.simplicial.obj (op (SimplexCategory.mk n.val))),
        Nonempty (IsColimit (Cofan.mk (V.simplicial.obj (op (SimplexCategory.mk n.val))) ι)) ∧
        ∀ (j : Fin k) (h : degree j = n) (i : Fin l),
          ∃ t : F.obj.obj (op (T i)),
            p.hom.app (op (T i)) t =
              G.obj.map (ι i ≫ f.app (op (SimplexCategory.mk n.val)) ≫
                eqToHom (congrArg (fun m : Fin (r + 1) ↦
                  U.simplicial.obj (op (SimplexCategory.mk m.val))) h.symm)).op (s j) := by
  have : Sheaf.IsLocallySurjective p :=
    (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{u + 1} R) p).mpr inferInstance
  exact exists_refinement_solving_local_requirements U r k degree
    (fun j ↦ Presheaf.imageSieve p.hom (s j))
    (fun j ↦ Presheaf.imageSieve_mem X.smallEtaleTopology p.hom (s j))

/-- Finitely many sections lift on the whole terms of a common finite split refinement.
Source: Stacks Project, Tag 01H0, finite lifting conditions in its first proof.
(blueprint: lem-sc-hypercover-refinement-section-lifts).

Proof: apply local surjectivity of a sheaf epimorphism to each image sieve, and use
finite refinement to solve these sieves on constituent pieces. A colimiting finite
cofan in the small etale site is the disjoint union of its terms. The sheaf axiom
glues arbitrary sections on these pieces uniquely, including the empty family.
Naturality of the epimorphism and uniqueness of gluing give its required image. -/
theorem exists_refinement_lifting_sections {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (U : FiniteSplitEtaleHypercover X)
    (R : Type (u + 1)) [Ring R]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)} (p : F ⟶ G) [Epi p]
    (r k : ℕ) (degree : Fin k → Fin (r + 1))
    (s : ∀ j : Fin k,
      G.obj.obj (op (U.simplicial.obj (op (SimplexCategory.mk (degree j).val))))) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U),
      ∀ j : Fin k, ∃ t : F.obj.obj
        (op (V.simplicial.obj (op (SimplexCategory.mk (degree j).val)))),
        p.hom.app _ t = G.obj.map (f.app (op (SimplexCategory.mk (degree j).val))).op
          (s j) := by
  classical
  obtain ⟨V, f, hf⟩ := exists_refinement_lifting_sections_pieces U R p r k degree s
  refine ⟨V, f, fun j ↦ ?_⟩
  obtain ⟨l, T, ι, ⟨hc⟩, hs⟩ := hf (degree j)
  have hs' (i : Fin l) : ∃ t : F.obj.obj (op (T i)),
      p.hom.app (op (T i)) t =
        G.obj.map (ι i ≫ f.app (op (SimplexCategory.mk (degree j).val))).op (s j) := by
    simpa using hs j rfl i
  choose t ht using hs'
  obtain ⟨a, ha, -⟩ := glue_coproduct_sections R F T _ ι hc t
  refine ⟨a, ?_⟩
  let b := G.obj.map (f.app (op (SimplexCategory.mk (degree j).val))).op (s j)
  have hab (i : Fin l) :
      G.obj.map (ι i).op (p.hom.app _ a) = G.obj.map (ι i).op b := by
    rw [← ModuleCat.comp_apply, ← p.hom.naturality, ModuleCat.comp_apply, ha i, ht i]
    rw [op_comp, G.obj.map_comp, ModuleCat.comp_apply]
  obtain ⟨c, hc₁, hc₂⟩ := glue_coproduct_sections R G T _ ι hc
    (fun i ↦ G.obj.map (ι i).op b)
  exact (hc₂ _ hab).trans (hc₂ _ (fun _ ↦ rfl)).symm

/-- A cycle in an exact sequence of sheaves becomes a boundary after refinement.
Source: Stacks Project, Tag 01H0, local vertical primitive step.
(blueprint: lem-sc-hypercover-refinement-section-lifts).

Proof: evaluation preserves kernels, so the cycle is a section of the kernel
sheaf. Exactness makes the map from the preceding sheaf to this kernel an
epimorphism. Lift this section on a common finite refinement by the preceding
theorem, and compose with the kernel inclusion. -/
theorem exists_refinement_primitive {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (U : FiniteSplitEtaleHypercover X)
    (R : Type (u + 1)) [Ring R]
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (hS : S.Exact) (n : ℕ)
    (s : S.X₂.obj.obj (op (U.simplicial.obj (op (SimplexCategory.mk n)))))
    (hs : S.g.hom.app _ s = 0) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U)
      (t : S.X₁.obj.obj (op (V.simplicial.obj (op (SimplexCategory.mk n))))),
      S.f.hom.app _ t = S.X₂.obj.map (f.app (op (SimplexCategory.mk n))).op s := by
  classical
  let W := U.simplicial.obj (op (SimplexCategory.mk n))
  let ev : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤ ModuleCat R :=
    sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op W)
  let a : ModuleCat.of R R ⟶ ev.obj S.X₂ :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ s)
  have ha : a ≫ ev.map S.g = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change S.g.hom.app _ (z • s) = 0
    simp only [map_smul, hs, smul_zero]
  let b := kernel.lift (ev.map S.g) a ha ≫ (PreservesKernel.iso ev S.g).inv
  let z : (kernel S.g).obj.obj (op W) := b 1
  have hz : (kernel.ι S.g).hom.app (op W) z = s := by
    have hb : b ≫ ev.map (kernel.ι S.g) = a := by
      simp only [b, Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι]
    have h := ConcreteCategory.congr_hom hb 1
    change (kernel.ι S.g).hom.app (op W) z = a 1 at h
    exact h.trans (LinearMap.toSpanSingleton_apply_one R _ _)
  let p := kernel.lift S.g S.f S.zero
  have : Epi p := hS.epi_kernelLift
  obtain ⟨V, f, hf⟩ := exists_refinement_lifting_sections U R p n 1
    (fun _ ↦ ⟨n, by omega⟩) (fun _ ↦ z)
  obtain ⟨t, ht⟩ := hf 0
  refine ⟨V, f, t, ?_⟩
  have hh := congrArg ((kernel.ι S.g).hom.app
    (op (V.simplicial.obj (op (SimplexCategory.mk n)))) : _ → _) ht
  have hp : p ≫ kernel.ι S.g = S.f := kernel.lift_ι _ _ _
  change ((p ≫ kernel.ι S.g).hom.app _) t = _ at hh
  rw [hp] at hh
  rw [← ModuleCat.comp_apply, (kernel.ι S.g).hom.naturality,
    ModuleCat.comp_apply, hz] at hh
  exact hh

end AlgebraicGeometry.FiniteSplitEtaleHypercover
