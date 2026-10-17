/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.AlgebraicGeometry.HypercoverStaircase

/-!
# Local exactness of resolutions of étale sheaves

For an exact sequence of sheaves `X₁ → X₂ → X₃` on `X_ét`, every section of `X₂` killed by
the second map is étale locally in the image of the first one; for a resolution `F ⟶ L^•`,
the cocycles of degree `0` are exactly the sections of `F`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

variable {X : Scheme.{u}}
  {A : Type (u + 2)} [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type*} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [∀ X, AddCommGroup (CA X)] [∀ X Y, AddMonoidHomClass (FA X Y) (CA X) (CA Y)]
  (hA : ElementwiseAbelian A)

include hA

/-- Sections of a kernel of sheaves are the kernel of the sections. -/
lemma exists_kernel_elem {K G H : Sheaf X.smallEtaleTopology A} {i : K ⟶ G} {g : G ⟶ H}
    {w : i ≫ g = 0} (hk : IsLimit (KernelFork.ofι i w)) (T : X.Etale)
    (s : ToType (G.obj.obj (op T))) (hs : g.hom.app (op T) s = 0) :
    ∃ k, i.hom.app (op T) k = s := by
  let E := sheafToPresheaf X.smallEtaleTopology A ⋙ (evaluation _ A).obj (op T)
  have hE : IsLimit ((KernelFork.ofι i w).map E) := KernelFork.mapIsLimit _ hk E
  have hS : (ShortComplex.mk (E.map i) (E.map g)
      (by rw [← E.map_comp, w, E.map_zero])).Exact :=
    ShortComplex.exact_of_f_is_kernel _ hE
  exact hA.elem_of_exact _ hS s hs

variable [HasSheafify X.smallEtaleTopology A]
  [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A]
  [X.smallEtaleTopology.WEqualsLocallyBijective A]

/-- In an exact sequence of sheaves, cocycles are locally coboundaries. -/
lemma imageSieve_mem_of_exact (S : ShortComplex (Sheaf X.smallEtaleTopology A)) (hS : S.Exact)
    (T : X.Etale) (s : ToType (S.X₂.obj.obj (op T))) (hs : S.g.hom.app (op T) s = 0) :
    Presheaf.imageSieve S.f.hom s ∈ X.smallEtaleTopology T := by
  have hepi : Epi (kernel.lift S.g S.f S.zero) := S.exact_iff_epi_kernel_lift.1 hS
  have hls : Sheaf.IsLocallySurjective (kernel.lift S.g S.f S.zero) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).2 hepi
  obtain ⟨k, hk⟩ := exists_kernel_elem hA (w := kernel.condition S.g) (kernelIsKernel S.g) T s hs
  refine X.smallEtaleTopology.superset_covering ?_ (hls.imageSieve_mem k)
  rintro T' g ⟨t, ht⟩
  refine ⟨t, ?_⟩
  have e : S.f.hom = (kernel.lift S.g S.f S.zero).hom ≫ (kernel.ι S.g).hom := by
    exact (congrArg (fun φ ↦ φ.hom) (kernel.lift_ι S.g S.f S.zero)).symm
  rw [e, NatTrans.comp_app, ConcreteCategory.comp_apply, ht, NatTrans.naturality_apply, hk]

/-- An injective resolution is locally exact in positive degrees. -/
lemma locallyExactPos_of_injectiveResolution {F : Sheaf X.smallEtaleTopology A}
    (I : InjectiveResolution F) : LocallyExactPos I.cocomplex :=
  fun b T s hs ↦ imageSieve_mem_of_exact hA _ (I.exact_succ b) T s hs

end AlgebraicGeometry.FiniteSplitEtaleHypercover
