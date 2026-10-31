/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedInternalHomFilteredColimit
import WeilConjectures.AlgebraicGeometry.InternalHomFilteredContinuity
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-! # The strict finite-free internal Hom colimit formula

Source: Bhatt--Scholze 6.8.14--6.8.15, conditional continuity argument; Stacks
03DB, 03CO and 03EP
(blueprint: lem-sfb-strict-finite-free-hom-colimit-formula).

This is a proved generic part of the algebraic-closure coefficient argument.
The prescribed cocone, its actual maps, and the evaluation normalization are retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale.QlbarInternalHom

attribute [local irreducible] WeilConjectures.SfbHomFilteredColimit.tensor
  WeilConjectures.SfbHomFilteredColimit.homFixed
  WeilConjectures.SfbHomFilteredColimit.comparison
  WeilConjectures.coefficientTotalTensor homComplexFunctor
  WeilConjectures.coefficientHomResolution
  SheafOfModules.monoidalCategory

private theorem quasiIso_natTrans_of_iso
    {A B : Type*} [Category A] [Category B] [Abelian B]
    {F G : A ⥤ CochainComplex B ℤ} (η : F ⟶ G) {a b : A} (e : a ≅ b)
    (h : QuasiIso (η.app a)) : QuasiIso (η.app b) := by
  have := h
  exact quasiIso_of_arrow_mk_iso _ _
    (Arrow.isoMk (F.mapIso e) (G.mapIso e) (η.naturality e.hom))

@[no_expose] private def secondMapTransformation
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (F : A × B ⥤ D) (H : D ⥤ E) {L N : B} (f : L ⟶ N) :
    (Prod.sectL A L ⋙ F) ⋙ H ⟶ (Prod.sectL A N ⋙ F) ⋙ H where
  app a := H.map (F.map (𝟙 a, f))
  naturality {a a'} g := by
    dsimp only [Functor.comp_map, Prod.sectL_map]
    rw [← H.map_comp, ← H.map_comp, ← F.map_comp, ← F.map_comp]
    congr 2
    apply Prod.hom_ext
    · change g ≫ 𝟙 a' = 𝟙 a ≫ g
      simp
    · change 𝟙 L ≫ f = f ≫ 𝟙 N
      simp

private theorem arrangeFormula {p1 p2 p3 p4 p5 p6 p7 q1 q2 q3 q4 q8 q9 q11 : Prop}
    (h : p1 ∧ p2 ∧ p3 ∧ p4 ∧ p5 ∧ p6 ∧ p7)
    (h1 : q1) (f2 : p3 → q2) (h3 : q3) (h4 : q4)
    (f8 : p1 → q8) (f9 : p2 → q9) (h11 : q11) :
    q1 ∧ q2 ∧ q3 ∧ q4 ∧ p5 ∧ p3 ∧ p4 ∧ q8 ∧ q9 ∧ p6 ∧ q11 := by
  rcases h with ⟨hp1, hp2, hp3, hp4, hp5, hp6, _⟩
  exact ⟨h1, f2 hp3, h3, h4, hp5, hp3, hp4, f8 hp1, f9 hp2, hp6, h11⟩

section GenericColimit

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

@[no_expose] private def denominatorTransformation
    (R : Sheaf J CommRingCat.{u + 1})
    (P L : CochainComplex
      (WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u}
        J R) ℤ) :
    WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u}
        J R L ⋙
        WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u}
          J R P ⟶
      WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u}
        J R
        ((WeilConjectures.coefficientHomResolution.{u, u + 1, u}
          J R).obj L) ⋙
        WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u}
          J R P := by
  unfold WeilConjectures.SfbHomFilteredColimit.tensorFixed
  exact secondMapTransformation
    (WeilConjectures.SfbHomFilteredColimit.tensor.{u + 1, u, u} J R)
    (WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P)
    ((WeilConjectures.SfbHomFilteredColimit.resolutionUnit.{u + 1, u, u} J R).app L)

private theorem tensorFixed_preserves
    (R : Sheaf J CommRingCat.{u + 1})
    (B : CochainComplex (WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u}
      J R) ℤ) :
    ∀ (I : Type (u + 1)) [SmallCategory I], PreservesColimitsOfShape I
      (WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u}
        J R B) := by
  intro I _
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let M := WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u}
    J R
  have (Y : M) : PreservesColimitsOfSize.{u + 1, u + 1} (tensorLeft Y) :=
    SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R Y
  have (Y : M) : PreservesColimitsOfSize.{u + 1, u + 1} (tensorRight Y) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight Y)
  have (Y : M) : (tensorLeft Y).Additive :=
    SheafOfModules.tensorLeft_additive_independent R Y
  have (Y : M) : (tensorRight Y).Additive :=
    Functor.additive_of_iso (F := tensorLeft Y)
      (BraidedCategory.tensorLeftIsoTensorRight Y)
  let : MonoidalPreadditive M :=
    { whiskerLeft_zero := fun {Y Z W} ↦ (tensorLeft Y).map_zero Z W
      zero_whiskerRight := fun {Y Z W} ↦ (tensorRight Y).map_zero Z W
      whiskerLeft_add := fun {Y Z W} f g ↦ (tensorLeft Y).map_add (f := f) (g := g)
      add_whiskerRight := fun {Y Z W} f g ↦ (tensorRight Y).map_add (f := f) (g := g) }
  let Q := (curriedTensor M).map₂CochainComplex
  let U := HomologicalComplex.single M (.up ℤ) 0
  have hfixed : WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u}
      J R B = U ⋙ Q.flip.obj B := by
    unfold WeilConjectures.SfbHomFilteredColimit.tensorFixed
      WeilConjectures.SfbHomFilteredColimit.tensor WeilConjectures.coefficientTotalTensor
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro Y Z f
    change (Q.map (U.map f)).app B ≫ (Q.obj (U.obj Z)).map (𝟙 B) =
      (Q.map (U.map f)).app B
    rw [(Q.obj (U.obj Z)).map_id, Category.comp_id]
  rw [hfixed]
  dsimp only [U, Q]
  infer_instance

/-- The complete strict colimit formula at any specified finite-free filtered cocone.
Source: Bhatt--Scholze 6.8.14--6.8.15, conditional continuity argument; Stacks
03DB, 03CO and 03EP; the parent node's strict colimit step
(blueprint: lem-sfb-strict-finite-free-hom-colimit-formula).
Proof: transfer exact filtered colimits through the module forgetful functor.
Apply filteredColimit_comparison to the finite-free diagram. Exact filtered colimits
preserve the stage quasi-isomorphisms, and comparison_existsUnique gives normalization.
The continuity lemma supplies the combined tensor-Hom postcomparison. Tensor preserves
colimits, so post_post and two-out-of-three give the separate Hom postcomparison.
Finally the colimit universal property identifies the specified vertex with colimit T;
naturality transports both vertex quasi-isomorphisms and the denominator square.
The same proof covers rank zero, zero inputs and the empty underlying site. -/
theorem strictColimitFormula_of_finiteFree
    (R : Sheaf J CommRingCat.{u + 1})
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (T : I ⥤ WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u}
      J R) (c : Cocone T)
    (hc : Nonempty (IsColimit c))
    (hfree : ∀ i : I, ∃ d : ℕ, Nonempty
      (T.obj i ≅ limit (Discrete.functor (fun _ : Fin d ↦
        SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))))
    (P L : CochainComplex (WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u}
      J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := J) (R := R) P)
    (hcont : WeilConjectures.SfbHomFilteredColimit.Continuous.{u + 1, u, u}
      J R (I := I) P)
    (hL : ∃ b : ℤ, ∀ n : ℤ, n < b → IsZero (L.X n)) :
    Nonempty (IsColimit c) ∧
    QuasiIso (colimMap (Functor.whiskerLeft T
      (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L))) ∧
    WeilConjectures.SfbHomFilteredColimit.Normalized.{u + 1, u, u} J R P L
      (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L) ∧
    QuasiIso (colimit.post
      (T ⋙ WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
        ((WeilConjectures.coefficientHomResolution.{u, u + 1, u} J R).obj L))
      (WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P)) ∧
    IsIso (colimit.post T
      (WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
        ((WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P).obj L))) ∧
    (∀ i, QuasiIso
      ((WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L).app
        (T.obj i))) ∧
    (∀ i, QuasiIso
      (WeilConjectures.SfbHomFilteredColimit.roofDenominator.{u + 1, u, u} J R P L
        (T.obj i))) ∧
    QuasiIso
      ((WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L).app c.pt) ∧
    QuasiIso
      (WeilConjectures.SfbHomFilteredColimit.roofDenominator.{u + 1, u, u} J R P L c.pt) ∧
    (colimit.post T
        (WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
          ((WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P).obj L)) ≫
          (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L).app
            (colimit T) =
      colimMap (Functor.whiskerLeft T
        (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L)) ≫
          colimit.post T
            (WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
              ((WeilConjectures.coefficientHomResolution.{u, u + 1, u} J R).obj L) ⋙
                WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P)) ∧
    (∀ i,
      (WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P).map
          ((WeilConjectures.SfbHomFilteredColimit.tensor.{u + 1, u, u} J R).map
            (c.ι.app i, 𝟙 L)) ≫
        WeilConjectures.SfbHomFilteredColimit.roofDenominator.{u + 1, u, u} J R P L c.pt =
      WeilConjectures.SfbHomFilteredColimit.roofDenominator.{u + 1, u, u} J R P L
          (T.obj i) ≫
        (WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P).map
          ((WeilConjectures.SfbHomFilteredColimit.tensor.{u + 1, u, u} J R).map
            (c.ι.app i,
              𝟙 ((WeilConjectures.coefficientHomResolution.{u, u + 1, u} J R).obj L)))) := by
  classical
  have hc' := hc
  have : HasExactColimitsOfShape I
      (WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u} J R) :=
    HasExactColimitsOfShape.domain_of_functor I (SheafOfModules.toSheaf
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
  obtain ⟨b, hb⟩ := hL
  have ht :=
    WeilConjectures.SfbHomFilteredColimit.filteredColimit_comparison.{u + 1, u, u}
      J R T hfree P L hP hcont b hb
  have hpost :=
    (WeilConjectures.SfbHomFilteredColimit.internalHom_filtered_continuity.{u + 1, u, u}
      J R T hfree P L hP hcont b hb).2.1
  obtain ⟨hcolim⟩ := hc
  let e : colimit T ≅ c.pt := (colimit.isColimit T).coconePointUniqueUpToIso hcolim
  have ha (hi : ∀ i, QuasiIso
      ((WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L).app
        (T.obj i))) : QuasiIso (colimMap (Functor.whiskerLeft T
      (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L))) :=
    (HomologicalComplex.quasiIso (WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u} J R)
      (.up ℤ)).colimMap _ hi
  have hnorm : WeilConjectures.SfbHomFilteredColimit.Normalized.{u + 1, u, u}
      J R P L (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L) := by
    unfold WeilConjectures.SfbHomFilteredColimit.comparison
    exact (WeilConjectures.SfbHomFilteredColimit.comparison_existsUnique.{u + 1, u, u}
      J R P L).exists.choose_spec
  have hpost' : QuasiIso (colimit.post
      (T ⋙ WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
        ((WeilConjectures.coefficientHomResolution.{u, u + 1, u} J R).obj L))
      (WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P)) := by
    let := tensorFixed_preserves J R
      ((WeilConjectures.coefficientHomResolution.{u, u + 1, u} J R).obj L)
      I
    have hp := hpost
    rw [← colimit.post_post] at hp
    let := hp
    exact quasiIso_of_comp_right _
      ((WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P).map
        (colimit.post T
          (WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
            ((WeilConjectures.coefficientHomResolution.{u, u + 1, u} J R).obj L))))
  refine arrangeFormula ht hc' ha hnorm hpost' ?_ ?_ ?_
  · exact quasiIso_natTrans_of_iso
      (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L) e
  · exact quasiIso_natTrans_of_iso (denominatorTransformation J R P L) e
  · intro i
    exact (denominatorTransformation J R P L).naturality (c.ι.app i)

end GenericColimit

end AlgebraicGeometry.ProEtale.QlbarInternalHom
