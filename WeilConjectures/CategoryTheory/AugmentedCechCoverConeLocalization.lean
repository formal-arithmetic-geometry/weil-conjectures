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
public import WeilConjectures.CategoryTheory.AugmentedCechLocalOrthogonality
import WeilConjectures.CategoryTheory.AugmentedCechSliceConeLocalization
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Local localization-class membership of an augmentation cone

Source: Stacks Project, dualizing.tex, Tag 0A6R, and algebraization.tex, Tag 099E.
(blueprint: lem-weil-pbc-augmented-cech-cover-cone-localization).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Pretriangulated Opposite

namespace CategoryTheory

/-- The cone of an augmentation with Cech models on a covering family belongs
locally, on every slice, to the finite triangulated class of ideal localizations.

Source: Stacks Project, dualizing.tex, Tag 0A6R, augmentation-cone filtration;
algebraization.tex, Tag 099E, the bounded localization complex.
(blueprint: lem-weil-pbc-augmented-cech-cover-cone-localization).

Proof: restrict the supplied augmented isomorphism on each covering object. Exact
restriction identifies the restricted cone with the cone of that Cech augmentation.
The augmentation has identity degree-zero component and zero target in other degrees.
Its kernel is supported in degrees 1 through the length of the list. Each positive
term is a finite sum of localizations at nonempty products of generators. In each
summand, any chosen factor in that product acts invertibly and is the image of an
ideal section. Thus its degree-zero object belongs to the defining triangulated
localization class. Finite biproduct closure, bounded-complex devissage and the
short-exact-sequence triangle put the augmentation cone in that class. Restriction
preserves the inverse scalar actions, the sums and the triangles. Pull the supplied
cover down to every object below each slice to obtain the displayed covering sieve.
For a list of length zero the augmentation is the identity and the cone is zero.
-/
theorem augmented_cech_cover_cone_localization
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
            (fun i ↦ ringedSliceSection O (U a) (b a i))).2) :
    ∀ (V W : C) (a : W ⟶ V), ∃ S : Sieve W, S ∈ J W ∧
      ∀ (T : C) (b : T ⟶ W), S b →
        ringedIdealLocalizationTriangulated O I ι T
          ((ringedKoszulDerivedOverMap O (b ≫ a)).obj
            ((ringedDerivedRestriction O V).obj
              (DerivedCategory.Q.obj (CochainComplex.mappingCone ε)))) := by
  intro V W a
  obtain ⟨S, hS, hs⟩ := hcover W
  refine ⟨S, hS, ?_⟩
  intro T d hd
  obtain ⟨j, ⟨f⟩⟩ := hs T d hd
  let F := ringedDerivedRestriction O T
  let G := ringedKoszulDerivedOverMap O f
  let : F.CommShift ℤ := by dsimp [F, ringedDerivedRestriction]; infer_instance
  let : F.IsTriangulated := by dsimp [F, ringedDerivedRestriction]; infer_instance
  let : G.CommShift ℤ := by dsimp [G, ringedKoszulDerivedOverMap]; infer_instance
  let : G.IsTriangulated := by dsimp [G, ringedKoszulDerivedOverMap]; infer_instance
  let m := (ringedExtendedCech (O.over (U j)) (r j)
    (fun i ↦ ringedSliceSection O (U j) (b j i))).2
  let TM := G.mapTriangle.obj
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle m))
  let TK := F.mapTriangle.obj
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle ε))
  have hTM : TM ∈ distTriang _ := G.map_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished m)
  have hTK : TK ∈ distTriang _ := F.map_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished ε)
  let β := ringedKoszulDerivedOverComparison O f
  let α := ringedKoszulDerivedOverComparison O (d ≫ a)
  let k := DerivedCategory.Q.obj K
  let o := DerivedCategory.Q.obj (ringedSiteRingComplex O)
  let v := DerivedCategory.Q.map ε
  let x := G.mapIso (e j) ≪≫ β.app k
  let y := G.mapIso (ringedDerivedRingRestrictionIso O (U j)).symm ≪≫ β.app o
  have hj : (e j).hom ≫ (ringedDerivedRestriction O (U j)).map v =
      DerivedCategory.Q.map m ≫ (ringedDerivedRingRestrictionIso O (U j)).inv := by
    apply (cancel_mono (ringedDerivedRingRestrictionIso O (U j)).hom).1
    simpa only [m, Category.assoc, Iso.inv_hom_id, Category.comp_id] using he j
  have hβ := β.hom.naturality v
  change G.map ((ringedDerivedRestriction O (U j)).map v) ≫ β.hom.app o =
    β.hom.app k ≫ F.map v at hβ
  have hxy : TM.mor₁ ≫ y.hom = x.hom ≫ TK.mor₁ := by
    change G.map (DerivedCategory.Q.map m) ≫
        (G.map (ringedDerivedRingRestrictionIso O (U j)).inv ≫ β.hom.app o) =
      (G.map (e j).hom ≫ β.hom.app k) ≫ F.map v
    rw [Category.assoc, ← hβ]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun t ↦ G.map t ≫ β.hom.app o) hj.symm
  let γ := Pretriangulated.isoTriangleOfIso₁₂ TM TK hTM hTK x y hxy
  let z := Pretriangulated.Triangle.π₃.mapIso γ ≪≫
    (α.app (DerivedCategory.Q.obj (CochainComplex.mappingCone ε))).symm
  have hm := augmented_cech_slice_cone_localization O I ι (U j) (r j) (b j)
    (hgen j) T f
  intro P hPi hPt hP
  let := hPi
  let := hPt
  exact P.prop_of_iso z (hm P hPi hPt hP)

end CategoryTheory
