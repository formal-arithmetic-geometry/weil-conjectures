/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Exact descent of tensoring with a fixed K-flat complex

Source: Stacks Project, sites-cohomology.tex, Tags 06YM, 06YP and 06YU;
derived.tex, definition-cone and definition-distinguished-triangle;
more-algebra.tex, Tag 0FNH, item-shift-tensor.
(blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated)

The derived bifunctor and its resolving comparison are the ones already supplied
by site-derived-tensor descent. The helpers only expose that comparison and abbreviate
existing categories and functors. All site and coefficient universes remain independent.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory

namespace SheafOfModules.KFlatFixedTensor

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- The dependency's module-sheaf category on the given ringed site.
Source: Stacks, Modules on Sites, Section 03DA
(blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
abbrev Modules := CategoryTheory.ringedSiteModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The existing canonical tensor of module sheaves.
Source: Stacks, Tag 03EK (blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
abbrev ordinaryTensor := @curriedTensor (Modules R) _ (SheafOfModules.monoidalCategory R)

/-- The existing direct-sum total tensor, as a curried bifunctor on complexes.
Source: Stacks, Tag 06YM (blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
abbrev totalTensor := (ordinaryTensor R).map₂CochainComplex

variable [HasDerivedCategory.{w} (Modules R)]

/-- The published K-flat-derived tensor, with no new choice of tensor or resolutions.
Source: Stacks, Tag 06YU (blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
abbrev derivedTensor := Functor.curry.obj
  (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R)

/-- The actual resolving comparison selected by the published descent theorem.
It is oriented from the localized total tensor to the derived tensor. Its arguments
are exactly flat-term K-flat complexes; the homotopy comparison is composed with the
resolving comparison, using the dependency's membership equivalence.
Source: Stacks, Tag 06YU (blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
def representativeIso
    (A B : CochainComplex (Modules R) ℤ)
    (hA : CochainComplex.IsKFlatIndependentCoefficients A)
    (hB : CochainComplex.IsKFlatIndependentCoefficients B)
    (hAf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (A.X n))
    (hBf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (B.X n)) :
    DerivedCategory.Q.obj (((totalTensor R).obj A).obj B) ≅
      (((derivedTensor R).obj (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj B)) :=
  let h := SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
    J R
  let P := h.choose
  let c := h.choose_spec.2.2.1.choose_spec.1.some
  let d := h.choose_spec.2.2.1.choose_spec.2.choose_spec.some
  let a : P.FullSubcategory := ⟨(HomotopyCategory.quotient _ _).obj A,
    (h.choose_spec.1 _).2 ⟨hA, hAf⟩⟩
  let b : P.FullSubcategory := ⟨(HomotopyCategory.quotient _ _).obj B,
    (h.choose_spec.1 _).2 ⟨hB, hBf⟩⟩
  (DerivedCategory.Qh.mapIso (c.app (A, B))).symm ≪≫ d.app (a, b)

/-- Tensoring by a flat-term K-flat complex preserves all quasi-isomorphisms and
has exact descent to the published derived tensor. The natural representative
comparisons agree with the published comparisons on every resolving complex, and
commute with the canonical signed chain shifts. `CommShift₂Int` includes the zero
and addition laws, naturality in every derived fixed argument, and the mixed sign
`(-1)^(ab)`. `mapTriangle` includes the connecting arrow with its shift comparison.

Source: Stacks, Tags 06YM, 06YP and 06YU; derived.tex, definition-cone and
 definition-distinguished-triangle; more-algebra.tex, Tag 0FNH, item-shift-tensor
(blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated).

Proof plan (the node's nine steps):
1. Sheaf tensor is additive and distributes over the finite cone sums, using
   lem-weil-pbc-independent-sheaf-tensor-colimits. The total differential gives
   homotopies h tensor 1, and (-1)^p 1 tensor h, respectively, so tensor descends
   to additive functors on the homotopy category.
2. Use lem-pc-tensor-mapping-cone-iso. In A tensor C(f), multiply its shifted-source
   summand by (-1)^p; in C(f) tensor A use the identity on both summands.
   The chain equations have coefficients (-1)^(p+1), -1 and (-1)^p in the first
   case and -d_X tensor 1 + (-1)^q 1 tensor d_A in the second. The projection
   equations use precisely s²_1 and s¹_1 of lem-weil-pbc-total-tensor-integer-shifts.
   Negating them preserves the connecting arrow -p, as well as the inclusion.
3. By lem-pur-quasi-iso-cone-acyclic, tensor an acyclic cone with A. K-flatness
   makes it acyclic. The signed swap (-1)^(ij) gives the other tensor order;
   its two differential coefficients are (-1)^(ij+j) and (-1)^(ij).
   Apply the cone comparison and cone criterion again, with no assumption on
   either endpoint of the original quasi-isomorphism.
4. The integer-shift comparisons identify tensor with A[n] with a shift of
   tensor with A, proving K-flatness. Its degree i term is A^(i+n), hence flat.
5. Apply lem-weil-pbc-localization-universal-property to the exact localization
   of lem-pur-homotopy-category-triangulated. Descend each signed shift map;
   faithfulness descends the zero and addition identities.
6. Additivity follows from preservation of biproduct diagrams. Every distinguished
   triangle is a localized cone triangle up to isomorphism. Step 2 proves its
   image distinguished including the connecting arrow, hence exactness.
7. Compare with lem-weil-pbc-site-derived-tensor-descent on resolving objects.
   Extend the comparison uniquely by localization. For r:P→B, use the composite
   inverse Q(H(r)), representative comparison at P, then T(1,Q(r)) (or T(Q(r),1)).
   lem-pc-kflat-resolution supplies P; uniqueness proves independence and naturality.
8. Conjugate the signed chain comparisons by the resolving comparison and descend
   in both variables. Descend inverses and coherence by the arbitrary-transformation
   extension and faithfulness clauses. The mixed (-1)^(ab) identity descends too.
9. Chain maps in the fixed argument commute with the varying shifts by the shift
   leaf. Extend the squares, invert the quasi-isomorphism squares, and compose
   along words in the localization. Uniqueness removes dependence on the word.
   All totals use direct sums; no bounds or flat cohomology enter the argument.
-/
theorem kFlat_fixed_tensor_triangulated :
    ∃ s : (derivedTensor R).CommShift₂Int,
      ∀ (A : CochainComplex (Modules R) ℤ)
        (hA : CochainComplex.IsKFlatIndependentCoefficients A)
        (hAf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (A.X n)),
        (∀ (B B' : CochainComplex (Modules R) ℤ) (f : B ⟶ B'),
          QuasiIso f → QuasiIso (((totalTensor R).obj A).map f) ∧
            QuasiIso (((totalTensor R).flip.obj A).map f)) ∧
        (∀ n : ℤ, CochainComplex.IsKFlatIndependentCoefficients (A⟦n⟧) ∧
          ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) ((A⟦n⟧).X i)) ∧
        (((derivedTensor R).obj (DerivedCategory.Q.obj A)).IsTriangulated ∧
          ((derivedTensor R).flip.obj (DerivedCategory.Q.obj A)).IsTriangulated) ∧
        (∃ cL : (totalTensor R).obj A ⋙ DerivedCategory.Q ≅
            DerivedCategory.Q ⋙ (derivedTensor R).obj (DerivedCategory.Q.obj A),
          NatTrans.CommShift cL.hom ℤ ∧
          ∀ (B : CochainComplex (Modules R) ℤ)
            (hB : CochainComplex.IsKFlatIndependentCoefficients B)
            (hBf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (B.X n)),
            cL.app B = representativeIso R A B hA hB hAf hBf) ∧
        (∃ cR : (totalTensor R).flip.obj A ⋙ DerivedCategory.Q ≅
            DerivedCategory.Q ⋙ (derivedTensor R).flip.obj (DerivedCategory.Q.obj A),
          NatTrans.CommShift cR.hom ℤ ∧
          ∀ (B : CochainComplex (Modules R) ℤ)
            (hB : CochainComplex.IsKFlatIndependentCoefficients B)
            (hBf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (B.X n)),
            cR.app B = representativeIso R B A hB hA hBf hAf) ∧
        (∀ (B B' : CochainComplex (Modules R) ℤ) (f : B ⟶ B'),
          (((derivedTensor R).obj (DerivedCategory.Q.obj A)).mapTriangle.obj
            (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f))) ∈
              distTriang (DerivedCategory (Modules R)) ∧
          (((derivedTensor R).flip.obj (DerivedCategory.Q.obj A)).mapTriangle.obj
            (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f))) ∈
              distTriang (DerivedCategory (Modules R))) := by
  sorry

end SheafOfModules.KFlatFixedTensor
