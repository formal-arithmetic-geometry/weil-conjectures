/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S8
-/
module

public import Sheaf.Paper.IntrinsicCompletionCompleted
import Sheaf.Paper.KoszulReconstruction
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsProperties
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.CategoryTheory.Triangulated.DerivedLimitLevelwiseIsomorphism

/-! # Koszul reconstruction with normalized Roos evaluations

Source: proper base change, finite-reduction-reconstruction, order 1249, proof steps 2--3;
Koszul reconstruction, order 1248; Stacks Tags 091Z and 099M.
(blueprint: lem-weil-pbc-completed-koszul-model-roos-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

private theorem roosIso {B : ℕᵒᵖ ⥤ adicDatumDerived T d}
    (L L' : CompletedSequentialDerivedLimit T d B) :
    ∃ e : L.obj ≅ L'.obj, e.hom ≫ L'.p = L.p := by
  let v := fun n : ℕ ↦ B.map (homOfLE (Nat.le_succ n)).op
  obtain ⟨a, hp, hδ⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
    _ _ L.distinguished L'.distinguished (𝟙 _) (𝟙 _) (by simp)
  have hpa : a ≫ L'.p = L.p := by simpa using hp.symm
  have : IsIso a := isIso_derivedLimit_of_levelwise v v L.obj L'.obj L.p L'.p
    L.δ L'.δ L.distinguished L'.distinguished (fun _ ↦ 𝟙 _)
    (fun _ ↦ by simp) a (by simpa using hpa) (by simpa using hδ)
  exact ⟨asIso a, hpa⟩

private theorem localizedRoos
    (B : ℕᵒᵖ ⥤ CochainComplex (adicDatumModules T d) ℤ) :
    let v := fun n : ℕ ↦ B.map (homOfLE (Nat.le_succ n)).op
    let s := towerTransitionEndomorphism v
    let Q := completedConstantQ (adicDatumModules T d)
    ∃ δ, IsDerivedLimitTriangle (fun n ↦ Q.map (v n))
      (Q.obj (CochainComplex.mappingCocone (-s)))
      (Q.map (CochainComplex.mappingCocone.fst (-s)) ≫
        piComparison Q (fun n : ℕ ↦ B.obj (op n))) δ := by
  dsimp only
  let := HasDerivedCategory.standard (adicDatumModules T d)
  let := adicDatumCountableAB4Star T d
  let C := fun n : ℕ ↦ B.obj (op n)
  let Q := completedConstantQ (adicDatumModules T d)
  have hp := (derivedCategory_countableProducts_properties
    (adicDatumModules T d)).1 ℕ C
  have : PreservesLimit (Discrete.functor C) Q :=
    preservesLimit_of_preserves_limit_cone (limit.isLimit _) hp.some
  let e : Q.obj (∏ᶜ C) ≅ ∏ᶜ (fun n ↦ Q.obj (C n)) := asIso (piComparison Q C)
  let v : ∀ n : ℕ, C (n + 1) ⟶ C n :=
    fun n ↦ B.map (homOfLE (Nat.le_succ n)).op
  let s := towerTransitionEndomorphism v
  let s' := towerTransitionEndomorphism (K := fun n ↦ Q.obj (C n))
    (fun n ↦ Q.map (v n))
  have hs : Q.map s ≫ e.hom = e.hom ≫ s' := by
    apply Pi.hom_ext
    intro n
    dsimp only [e, asIso_hom, s, s', towerTransitionEndomorphism, towerProductShift]
    simp only [Functor.map_sub, Preadditive.sub_comp,
      Preadditive.comp_sub, Category.comp_id, Category.assoc,
      piComparison_comp_π, Pi.lift_π]
    rw [← Category.assoc, piComparison_comp_π]
    simp only [← Q.map_comp, Category.id_comp, Pi.lift_π]
  let D := Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle (-s))
  have hD : D ∈ distTriang _ :=
    DerivedCategory.mappingCocone_triangle_distinguished (-s)
  let δ := (-e.inv) ≫ D.mor₃
  refine ⟨δ, ?_⟩
  apply (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk D
      (Pretriangulated.Triangle.mk
        (Q.map (CochainComplex.mappingCocone.fst (-s)) ≫ e.hom) s' δ)
      (Iso.refl _) e (-e) ?_ ?_ ?_)).mp hD
  · dsimp only [D, Functor.mapTriangle, CochainComplex.mappingCocone.triangle,
      Pretriangulated.Triangle.mk, Iso.refl_hom]
    rw [Category.id_comp]
  · change Q.map (-s) ≫ (-e.hom) = e.hom ≫ s'
    simpa only [Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
      using hs
  · dsimp only [Pretriangulated.Triangle.mk, Iso.refl_hom, δ]
    rw [(shiftFunctor _ (1 : ℤ)).map_id]
    change D.mor₃ ≫ 𝟙 _ = (-e.hom) ≫ ((-e.inv) ≫ D.mor₃)
    simp only [← Category.assoc, Preadditive.neg_comp, Preadditive.comp_neg,
      neg_neg, Iso.hom_inv_id, Category.id_comp, Category.comp_id]

/-- The intrinsic Koszul completion is a Roos limit of the strict quotient tower,
with the quotient units as its evaluations. No completeness hypothesis is needed.

Source: blueprint proper base change, order 1248 and order 1249, proof steps 2--3;
Stacks Tags 091Z and 099M.
(blueprint: lem-weil-pbc-completed-koszul-model-roos-comparison).

Proof: compute the quotient tower on the given K-flat complex. The augmentations from
power Koszul complexes to positive quotients commute with transitions and degree-zero
units. Noetherian pro-zero Koszul homology identifies their derived inverse limits,
after tensoring with that K-flat complex. Exact countable products compute the Roos
fibres, so this identifies the explicit Koszul fibre with the quotient Roos fibre.
The first coordinate of the Koszul unit is the product of its degree-zero inclusions;
its augmentation at level n is the ordinary scalar-extension unit. The normalization
of the derived adjunction and its universal K-flat comparison therefore identifies
this evaluation with the displayed derived unit. For an arbitrary specified Roos
triple L, apply the triangulated-category morphism axiom to the rotated triangles,
using the identity on both product vertices. Two-out-of-three makes the resulting
map an isomorphism, and the triangle equation preserves the product map, hence every
evaluation. Transporting through the realization of the K-flat complex gives exactly
the asserted equations. Empty generator lists and zero coefficient rings satisfy the
same construction, without a nonzero-rank or nonempty-scheme assumption. -/
theorem completedKoszulModelRoosComparison {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (r : ℕ) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = d.ideal)
    (L : CompletedSequentialDerivedLimit T d (adicDatumModelTower T d M)) :
    ∃ e : completedIntrinsicCompletion T d r f M.complex ≅ L.obj,
      ∀ n : ℕ,
        completedIntrinsicCompletionMap T d r f M.complex M.realization ≫ e.hom ≫
          L.p ≫ Pi.π (fun a : ℕ ↦ (adicDatumModelTower T d M).obj (op a)) n ≫
          (adicDatumModelRestriction T d M n).hom ≫
          (adicDatumRestriction T (adicDatumProjection T d n)).map
            (adicDatumModelReductionIso T d M n).inv =
        (adicDatumAdjunction T (adicDatumProjection T d n)).unit.app K := by
  sorry

end AlgebraicGeometry.Scheme
