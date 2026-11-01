/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.AugmentedCechCommonSliceComparison
import WeilConjectures.ProperBaseChange.RingedGeneratingListsLocalEquality

/-! # Augmented comparisons on covering refinements

Source: Stacks Project, algebraization.tex, Tag 099E, and sites-cohomology.tex, Tag 08JB.
(blueprint: lem-weil-pbc-augmented-cech-cover-local-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory Opposite

namespace CategoryTheory

/-- On a covering sieve below any generating slice, a specified Cech model
and the given augmented complex have an augmented derived comparison.
No compatibility between these local comparisons is claimed.

Source: Stacks Project, algebraization.tex, Tag 099E, independence of generators,
and sites-cohomology.tex, Tag 08JB, exact restriction.
(blueprint: lem-weil-pbc-augmented-cech-cover-local-comparison).

Proof: on an arrow of the supplied cover choose its map to one of the covering
objects. Restrict that object's specified augmented model to the arrow's domain.
Apply augmented Cech restriction with the covering object's slice as base, and
also with the chosen generating slice as base. The canonical iterated-slice
equivalences identify both results with complexes on the domain slice. The
transported lists still generate the restricted ideal. Refine by the equality
of their section ideals and apply augmented generator independence. Compose its
comparison with the restricted supplied isomorphism and the derived restriction
composition isomorphism. The augmentation equations for all these comparisons
give the displayed square with the actual mapped augmentations. Refine once
more below any test object; transitivity of covering sieves gives the required
cover. Empty lists, zero generators and the zero ring satisfy the same equations.
-/
theorem augmented_cech_cover_local_comparison
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (A : Type u) (U : A → C)
    (hcover : ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧
      ∀ (W : C) (f : W ⟶ V), S f → ∃ a : A, Nonempty (W ⟶ U a))
    (r : A → ℕ) (b : ∀ a : A, Fin (r a) → O.obj.obj (op (U a)))
    (hgen : ∀ a : A, IsRingedIdealGeneratingList O I ι (U a) (r a) (b a))
    (e : ∀ a : A, DerivedCategory.Q.obj
        (ringedExtendedCech (O.over (U a)) (r a)
          (fun i ↦ ringedSliceSection O (U a) (b a i))).1 ≅
        (ringedDerivedRestriction O (U a)).obj (DerivedCategory.Q.obj K))
    (he : ∀ a : A,
      (e a).hom ≫ (ringedDerivedRestriction O (U a)).map (DerivedCategory.Q.map ε) ≫
          (ringedDerivedRingRestrictionIso O (U a)).hom =
        DerivedCategory.Q.map
          (ringedExtendedCech (O.over (U a)) (r a)
            (fun i ↦ ringedSliceSection O (U a) (b a i))).2)
    (V : C) (q : ℕ) (g : Fin q → O.obj.obj (op V))
    (hg : IsRingedIdealGeneratingList O I ι V q g) :
    ∀ (W : C) (a : W ⟶ V), ∃ S : Sieve W, S ∈ J W ∧
      ∀ (T : C) (b : T ⟶ W), S b →
        ∃ eT : (ringedKoszulDerivedOverMap O (b ≫ a)).obj
              (DerivedCategory.Q.obj
                (ringedExtendedCech (O.over V) q
                  (fun i ↦ ringedSliceSection O V (g i))).1) ≅
            (ringedKoszulDerivedOverMap O (b ≫ a)).obj
              ((ringedDerivedRestriction O V).obj (DerivedCategory.Q.obj K)),
          eT.hom ≫ (ringedKoszulDerivedOverMap O (b ≫ a)).map
              ((ringedDerivedRestriction O V).map (DerivedCategory.Q.map ε)) =
            (ringedKoszulDerivedOverMap O (b ≫ a)).map
              (DerivedCategory.Q.map
                  (ringedExtendedCech (O.over V) q
                    (fun i ↦ ringedSliceSection O V (g i))).2 ≫
                (ringedDerivedRingRestrictionIso O V).inv) := by
  intro W a
  obtain ⟨S, hS, hs⟩ := hcover W
  refine ⟨S, hS, ?_⟩
  intro T d hd
  obtain ⟨j, ⟨t⟩⟩ := hs T d hd
  obtain ⟨c, hc⟩ := augmented_cech_common_slice_comparison O I ι V (U j)
    q (r j) g (b j) hg (hgen j) T (d ≫ a) t
    (exists_cover_generatingLists_ideal_eq O I ι V q g hg (U j) (r j) (b j)
      (hgen j) T (d ≫ a) t)
  let F := ringedKoszulDerivedOverMap O (d ≫ a)
  let G := ringedKoszulDerivedOverMap O t
  let α := ringedKoszulDerivedOverComparison O (d ≫ a)
  let β := ringedKoszulDerivedOverComparison O t
  let k := DerivedCategory.Q.obj K
  let o := DerivedCategory.Q.obj (ringedSiteRingComplex O)
  let v := DerivedCategory.Q.map ε
  let u := DerivedCategory.Q.map
    (ringedExtendedCech (O.over V) q (fun i ↦ ringedSliceSection O V (g i))).2 ≫
      (ringedDerivedRingRestrictionIso O V).inv
  let z := DerivedCategory.Q.map
    (ringedExtendedCech (O.over (U j)) (r j)
      (fun i ↦ ringedSliceSection O (U j) (b j i))).2 ≫
        (ringedDerivedRingRestrictionIso O (U j)).inv
  have hj : (e j).hom ≫ (ringedDerivedRestriction O (U j)).map v = z := by
    apply (cancel_mono (ringedDerivedRingRestrictionIso O (U j)).hom).1
    simpa only [z, Category.assoc, Iso.inv_hom_id, Category.comp_id] using he j
  let l := c ≪≫ G.mapIso (e j) ≪≫ β.app k ≪≫ (α.app k).symm
  refine ⟨l, ?_⟩
  apply (cancel_mono (α.app o).hom).1
  simp only [Category.assoc]
  change l.hom ≫ F.map ((ringedDerivedRestriction O V).map v) ≫ α.hom.app o =
    F.map u ≫ α.hom.app o
  have hα := α.hom.naturality v
  have hβ := β.hom.naturality v
  change F.map ((ringedDerivedRestriction O V).map v) ≫ α.hom.app o =
    α.hom.app k ≫ (ringedDerivedRestriction O T).map v at hα
  change G.map ((ringedDerivedRestriction O (U j)).map v) ≫ β.hom.app o =
    β.hom.app k ≫ (ringedDerivedRestriction O T).map v at hβ
  change c.hom ≫ G.map z ≫ β.hom.app o = F.map u ≫ α.hom.app o at hc
  simp only [l, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [hα]
  simp only [← Iso.app_hom, Iso.inv_hom_id_assoc]
  simp only [Iso.app_hom]
  rw [← hβ]
  rw [← G.map_comp_assoc, hj]
  exact hc

end CategoryTheory
