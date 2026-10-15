/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
import Sheaf.AlgebraicTopology.ImageCoskeletonFactorization
import Mathlib.CategoryTheory.Sites.Adjunction
import Sheaf.Paper.TrivialKanHomotopyEquivalence
import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
import Mathlib.Algebra.Homology.Functor

/-!
# Homology comparison for coskeletal simplicial presheaves

Source: Stacks Project, Hypercoverings, Lemma 01GD
(blueprint: lem-weil-pbc-coskeleton-free-homology-comparison).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped Simplicial

-- Infer preservation of cover-indexed colimits from preservation at the coefficient universe.
attribute [local instance] preservesFilteredColimitsOfSize_shrink

namespace CategoryTheory.SimplicialObject

private theorem freeHomologyIso {R : Type w} [CommRing R]
    {X Y : SSet.{w}} (f : X ⟶ Y) (hf : SSet.modelCategoryQuillen.I.rlp f) (i : ℕ) :
    IsIso (((whiskeringRight _ _ _).obj (ModuleCat.free R) ⋙
      AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{w} R) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.down ℕ) i).map f) := by
  obtain ⟨g, hg, h, h₀, h₁⟩ := SSet.exists_section_homotopy_equivalence f hf
  let H : SSet.Homotopy (𝟙 X) (f ≫ g) :=
    { h := h
      h₀ := h₀
      h₁ := h₁
      rel := by ext j x; exact x.1.property.elim }
  let F := (whiskeringRight _ _ _).obj (ModuleCat.free R) ⋙
    AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{w} R)
  let G := F ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) i
  have hgf : G.map f ≫ G.map g = 𝟙 _ := by
    have hh := ((H.toSimplicialObjectHomotopy.whiskerRight
      (ModuleCat.free R)).toChainHomotopy).homologyMap_eq i
    change HomologicalComplex.homologyMap (F.map f) i ≫
      HomologicalComplex.homologyMap (F.map g) i = 𝟙 _
    simpa only [F, Functor.comp_map, Functor.comp_obj, SimplicialObject.whiskering,
      HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_comp,
      Functor.map_id, Functor.map_comp] using hh.symm
  have hfg : G.map g ≫ G.map f = 𝟙 _ := by rw [← G.map_comp, hg, G.map_id]
  exact ⟨⟨G.map g, hgf, hfg⟩⟩

private theorem isIso_freeHomologyMap_of_objectwise_rlp
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Type (max u v w)) [CommRing R]
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type (max u v w))} (f : L ⟶ K)
    (hobj : ∀ V : C, SSet.modelCategoryQuillen.I.rlp
      (((whiskeringRight _ _ _).obj
        ((evaluation (Cᵒᵖ) (Type (max u v w))).obj (Opposite.op V))).map f)) :
    ∀ i : ℕ, IsIso
      (((SimplicialObject.whiskering _ _).obj
          ((whiskeringRight _ _ _).obj (ModuleCat.free R) ⋙
            presheafToSheaf J (ModuleCat.{max u v w} R)) ⋙
        AlgebraicTopology.alternatingFaceMapComplex (Sheaf J (ModuleCat.{max u v w} R)) ⋙
        HomologicalComplex.homologyFunctor (Sheaf J (ModuleCat.{max u v w} R))
          (ComplexShape.down ℕ) i).map
          f) := by
  let F := (whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.free R)
  let φ := (AlgebraicTopology.alternatingFaceMapComplex (Cᵒᵖ ⥤ ModuleCat.{max u v w} R)).map
    (Functor.whiskerRight f F)
  have hφ : QuasiIso φ := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro V
    change QuasiIso
      ((AlgebraicTopology.alternatingFaceMapComplex (Cᵒᵖ ⥤ ModuleCat.{max u v w} R) ⋙
        ((evaluation Cᵒᵖ (ModuleCat.{max u v w} R)).obj V).mapHomologicalComplex _).map
          (Functor.whiskerRight f F))
    rw [AlgebraicTopology.map_alternatingFaceMapComplex]
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact freeHomologyIso
      (Functor.whiskerRight f ((evaluation Cᵒᵖ (Type (max u v w))).obj V))
      (hobj V.unop) i
  intro i
  change IsIso (HomologicalComplex.homologyMap
    (((SimplicialObject.whiskering _ _).obj (F ⋙ presheafToSheaf J _) ⋙
      AlgebraicTopology.alternatingFaceMapComplex _).map f) i)
  change IsIso (HomologicalComplex.homologyMap
    (((SimplicialObject.whiskering _ _).obj (presheafToSheaf J _) ⋙
      AlgebraicTopology.alternatingFaceMapComplex _).map (Functor.whiskerRight f F)) i)
  rw [← AlgebraicTopology.map_alternatingFaceMapComplex]
  change IsIso (HomologicalComplex.homologyMap
    (((presheafToSheaf J (ModuleCat.{max u v w} R)).mapHomologicalComplex _).map φ) i)
  exact (quasiIsoAt_iff_isIso_homologyMap _ i).mp
    (HomologicalComplex.quasiIsoAt_map_of_preservesHomology φ (presheafToSheaf J _) i)

/-- Stacks Project, Hypercoverings, Lemma 01GD, with free modules over a commutative ring.
(blueprint: lem-weil-pbc-coskeleton-free-homology-comparison)

Proof route:
1. Replace degree `n` of the truncation of `K` by the image of `f` and coskeletonize,
   obtaining `K'` and a factorization `L → K' → K`. The image is stable under the
   simplicial operators since the lower-degree components of `f` are isomorphisms.
   Use lem-weil-pbc-truncated-coskeleton-finite-limits for the counit and functoriality.
2. The image inclusion in degree `n` becomes both mono and epi after sheafification,
   hence an isomorphism (lem-weil-pbc-sheaf-sets-mono-epi-iso). Sheafification preserves
   finite limits (lem-weil-pbc-sheafification-sets-exact), so `K' → K` becomes an
   isomorphism in every degree, by lem-weil-pbc-truncated-coskeleton-finite-limits.
3. By lem-weil-pbc-free-module-sheaf-sheafify-first, the free-module sheaf complexes
   of `K'` and `K` are isomorphic, hence so are their homology sheaves.
4. Evaluate `L → K'` at each object of the site. Evaluation preserves the finite
   limits computing coskeleta, so lem-weil-pbc-coskeletal-map-trivial-kan applies:
   the map is a trivial Kan fibration, bijective below `n` and surjective at `n`.
5. By lem-weil-pbc-trivial-kan-homotopy-equivalence it has a simplicial homotopy
   inverse. By lem-weil-pbc-simplicial-homotopy-free-chain-homotopy, the induced
   free-module chain map is a chain homotopy equivalence, hence a homology isomorphism.
6. Homology of module presheaves is objectwise and exact sheafification commutes with
   homology (lem-weil-pbc-site-module-presheaf-sheafification-exact). Thus `L → K'`
   induces isomorphisms on homology sheaves; the objectwise inverses need not be natural.
7. Compose these isomorphisms with those of `K' → K` to obtain the conclusion.
-/
theorem isIso_homologyMap_of_local_surjective_coskeletal
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Type (max u v w)) [CommRing R]
    (n : ℕ) (hn : 1 ≤ n)
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type (max u v w))} (f : L ⟶ K)
    (hlow : ∀ i : ℕ, i < n → IsIso (f.app (Opposite.op ⦋i⦌)))
    (hsurj : Epi ((presheafToSheaf J (Type (max u v w))).map
      (f.app (Opposite.op ⦋n⦌))))
    (hL : IsIso ((coskAdj n).unit.app L))
    (hK : IsIso ((coskAdj n).unit.app K)) :
    ∀ i : ℕ, IsIso
      (((SimplicialObject.whiskering _ _).obj
          ((whiskeringRight _ _ _).obj (ModuleCat.free R) ⋙
            presheafToSheaf J (ModuleCat.{max u v w} R)) ⋙
        AlgebraicTopology.alternatingFaceMapComplex (Sheaf J (ModuleCat.{max u v w} R)) ⋙
        HomologicalComplex.homologyFunctor (Sheaf J (ModuleCat.{max u v w} R))
          (ComplexShape.down ℕ) i).map
          f) := by
  obtain ⟨M, p, q, hfac, hp, hq⟩ :=
    exists_imageCoskeleton_factorization J n hn f hlow hsurj hL hK
  let F := (whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.free R) ⋙
    presheafToSheaf J (ModuleCat.{max u v w} R)
  have hqF : IsIso (((SimplicialObject.whiskering _ _).obj F).map q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨⟨j⟩⟩
    change IsIso ((presheafToSheaf J (ModuleCat.{max u v w} R)).map
      (Functor.whiskerRight (q.app (Opposite.op ⦋j⦌)) (ModuleCat.free R)))
    rw [← J.W_iff]
    have := Sheaf.preservesSheafification_of_adjunction J (ModuleCat.adj R)
    apply J.W_of_preservesSheafification (ModuleCat.free R)
    exact (J.W_iff _).mpr (hq j)
  intro i
  let H := (SimplicialObject.whiskering _ _).obj F ⋙
    AlgebraicTopology.alternatingFaceMapComplex (Sheaf J (ModuleCat.{max u v w} R)) ⋙
    HomologicalComplex.homologyFunctor (Sheaf J (ModuleCat.{max u v w} R))
      (ComplexShape.down ℕ) i
  have hpH : IsIso (H.map p) := isIso_freeHomologyMap_of_objectwise_rlp J R p hp i
  have hqH : IsIso (H.map q) := by
    exact Functor.map_isIso
      (AlgebraicTopology.alternatingFaceMapComplex _ ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) i)
      (((SimplicialObject.whiskering _ _).obj F).map q)
  change IsIso (H.map f)
  rw [← hfac, H.map_comp]
  infer_instance

end CategoryTheory.SimplicialObject
