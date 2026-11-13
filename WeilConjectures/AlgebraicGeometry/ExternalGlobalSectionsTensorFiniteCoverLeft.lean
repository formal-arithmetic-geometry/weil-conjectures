/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
import WeilConjectures.AlgebraicGeometry.ExternalGlobalSectionsRestrictionComparisonLeft
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Finite-cover descent in the first factor

Source: Stacks Project, Tag 0BED, lemma-kunneth, the degree-zero finite-cover argument.
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

private theorem isIso_app_of_pairwise_limits
    {k : Type w} [Field k]
    {Z : TopCat.{w}} {A B : Z.Presheaf (ModuleCat.{w} k)}
    {ι : Type w} (U : ι → TopologicalSpace.Opens Z) (c : A ⟶ B)
    (hA : IsLimit (A.mapCone (Pairwise.cocone U).op))
    (hB : IsLimit (B.mapCone (Pairwise.cocone U).op))
    (hc : ∀ j : Pairwise ι, IsIso (c.app (op ((Pairwise.diagram U).obj j)))) :
    IsIso (c.app (op (iSup U))) := by
  let d := Functor.whiskerLeft (Pairwise.diagram U).op c
  have : ∀ j, IsIso (d.app j) := fun j ↦ hc j.unop
  have : IsIso d := NatIso.isIso_of_isIso_app d
  let e := hA.conePointsIsoOfNatIso hB (asIso d)
  have he : c.app (op (iSup U)) = e.hom := by
    apply hB.hom_ext
    intro j
    rw [IsLimit.conePointsIsoOfNatIso_hom_comp]
    exact (c.naturality ((Pairwise.cocone U).op.π.app j)).symm
  rw [he]
  infer_instance

/-- Bijectivity descends from a finite cover of the first factor and its overlaps.
There are no quasi-coherence, compactness, or affine-diagonal assumptions in this lemma
(Stacks, Tag 0BED). -/
theorem externalGlobalSectionsTensor_bijective_of_finite_cover_left
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules)
    {ι : Type w} [Finite ι] (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (hU : ∀ i, Function.Bijective
      (externalGlobalSectionsTensor ((U i).ι ≫ f) g (F.restrict (U i).ι) G))
    (hUU : ∀ i j, Function.Bijective
      (externalGlobalSectionsTensor ((U i ⊓ U j).ι ≫ f) g
        (F.restrict (U i ⊓ U j).ι) G)) :
    Function.Bijective (externalGlobalSectionsTensor f g F G) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨c, htop, hlocal⟩ := exists_externalSectionsRestrictionComparisonLeft f g F G
  have hcomponent (V : X.Opens)
      (hV : Function.Bijective
        (externalGlobalSectionsTensor (V.ι ≫ f) g (F.restrict V.ι) G)) :
      IsIso (c.app (op V)) := by
    obtain ⟨eS, eT, he⟩ := hlocal V
    have : IsIso (ModuleCat.ofHom
        (externalGlobalSectionsTensor (V.ι ≫ f) g (F.restrict V.ι) G)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hV
    have : IsIso (c.app (op V) ≫ eT.hom) := by rw [he]; infer_instance
    exact IsIso.of_isIso_comp_right _ eT.hom
  have hA := (TopCat.Presheaf.IsSheaf.isSheafPairwiseIntersections
    U (scalarPresheaf_isSheaf f F)).some
  have hAt := isLimitOfPreserves
    (MonoidalCategory.tensorRight (scalarObj g G (op ⊤))) hA
  have hB : TopCat.Presheaf.IsSheaf (externalSectionsPushforwardLeft f g F G) :=
    TopCat.Sheaf.pushforward_sheaf_of_sheaf (pullback.fst f g).base
      (scalarPresheaf_isSheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
  have hBt := (TopCat.Presheaf.IsSheaf.isSheafPairwiseIntersections U hB).some
  have hsup := isIso_app_of_pairwise_limits U c hAt hBt (by
    rintro (i | ⟨i, j⟩)
    · exact hcomponent (U i) (hU i)
    · exact hcomponent (U i ⊓ U j) (hUU i j))
  rw [hcover] at hsup
  have : IsIso (c.app (op ⊤)) := hsup
  have : IsIso (ModuleCat.ofHom (externalGlobalSectionsTensor f g F G)) := by
    rw [← htop]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective
    (ModuleCat.ofHom (externalGlobalSectionsTensor f g F G))).1 inferInstance

end AlgebraicGeometry.Scheme.Modules
