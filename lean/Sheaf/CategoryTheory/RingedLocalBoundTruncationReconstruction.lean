/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Reconstruction from lower truncations under ringed-site local bounds

Source: Stacks Project, Cohomology on Sites, Tags 0D6R and 0D6S, and Derived Categories,
Tag 0H72 (blueprint: lem-sfb-ringed-local-bound-truncation-reconstruction).

The underlying Roos data of the resolution-derived limit are supplied by
`ringedStrictTowerHomotopyLimitIndependentCoefficients`. We state reconstruction for
those data without selecting a cone or a comparison from a nonunique existence theorem.
As in 0H72, every comparison with the specified projections is invertible.

The cofinal collection can be taken to be all coverings satisfying the displayed
vanishing bound. Refinement is expressed by factorization through an arrow of the
original covering. Cohomology is computed by applying sections to any K-injective
resolution of a module sheaf in degree zero, exactly its right derived functor.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC r w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Reconstruction from the good lower truncations, with all canonical projections.
Source: Stacks Project, Cohomology on Sites, Tags 0D6R and 0D6S; Derived Categories,
Tag 0H72 (blueprint: lem-sfb-ringed-local-bound-truncation-reconstruction).

The five object-property instances say precisely that `S` is a weak Serre subcategory.
The coefficient universe `r` is independent of the site's two universes; essential
smallness is relative to `r`. The standard sheafification instances provide the ordinary
abelian category of module sheaves. The integer bound may vary with `V`.

For each covering `P` of `V`, `hlocal` supplies a refining covering `T` on whose members
all the prescribed module cohomology groups vanish. This is equivalent to the cofinal
collection in 0D6R. Empty coverings and negative bounds are included.

The product and Roos triangle below are the underlying data of the resolution-derived
limit of the strict good-truncation tower, supplied by
lem-weil-pbc-ringed-strict-tower-homotopy-limit. Writing them as parameters makes no
choice of homotopy limit. The conclusion includes an isomorphism with every required
projection; its second clause asserts invertibility for the actual specified comparison,
independently of the nonunique lift in 0H72.

Proof plan (the node's five steps):
1. Represent `E` by a complex and form its strict good-truncation tower using
   def-kun-truncations. Each truncation is bounded below and its cohomology belongs to
   `S`. In degree `j`, its transitions are isomorphisms once `n >= max(0,-j)`.
2. The compatible truncation maps give a product map killed by `1-s`. Exactness of
   Hom into the Roos triangle (lem-weil-pbc-hom-into-triangle-exact) supplies a comparison
   with all projections. The resolution construction has this same underlying triangle.
3. Apply lem-sfb-ringed-local-bound-stationary-limit-cohomology with precisely `B` and
   the cofinal bounded coverings in `hlocal`. It identifies each stabilized projection
   on cohomology. There is no common lower bound on the tower and no exact-products
   assumption.
4. On degree-`j` cohomology the comparison followed by a stabilized projection is the
   canonical truncation map. Both the latter and the projection are invertible, so the
   comparison is invertible on every cohomology object. This works for every compatible
   comparison, including the specified resolution comparison.
5. Apply lem-weil-pbc-unbounded-derived-iso-cohomology in the ordinary unbounded derived
   category. The projection equalities from step 2 hold for every `n`, including `n=0`.
-/
theorem ringed_local_bound_truncation_reconstruction
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    [HasSheafify J.toGrothendieck AddCommGrpCat.{r}]
    [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (R : Sheaf J.toGrothendieck RingCat.{r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{r, r, vC, uC} R)]
    (S : ObjectProperty (ringedSiteModules.{r, r, vC, uC} R))
    [S.IsClosedUnderIsomorphisms] [S.ContainsZero]
    [S.IsClosedUnderKernels] [S.IsClosedUnderCokernels] [S.IsClosedUnderExtensions]
    (B : Set C)
    (_hcover : ∀ U : C, ∃ P : Presieve U, P ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), P f → V ∈ B)
    (_hlocal : ∀ V : C, V ∈ B → ∃ d : ℤ,
      ∀ P : Presieve V, P ∈ J V → ∃ T : Presieve V, T ∈ J V ∧
        (∀ (W : C) (f : W ⟶ V), T f →
          ∃ (U : C) (g : U ⟶ V) (a : W ⟶ U), P g ∧ a ≫ g = f) ∧
        ∀ (W : C) (f : W ⟶ V), T f →
          ∀ (p : ℤ), d < p → ∀ F : ringedSiteModules.{r, r, vC, uC} R, S F →
            ∀ (I : CochainComplex (ringedSiteModules.{r, r, vC, uC} R) ℤ)
              (ι : (CochainComplex.singleFunctor
                (ringedSiteModules.{r, r, vC, uC} R) 0).obj F ⟶ I),
              I.IsKInjective → QuasiIso ι →
                IsZero ((((SheafOfModules.toSheaf R ⋙
                  sheafToPresheaf J.toGrothendieck AddCommGrpCat.{r} ⋙
                  (evaluation Cᵒᵖ AddCommGrpCat.{r}).obj (op W)).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj I).homology p))
    (E : DerivedCategory (ringedSiteModules.{r, r, vC, uC} R))
    (_hE : DerivedCategory.homologyProperty S E)
    [HasProduct (fun n : ℕ ↦
      (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E)]
    (L : DerivedCategory (ringedSiteModules.{r, r, vC, uC} R))
    (π : L ⟶ ∏ᶜ (fun n : ℕ ↦
      (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E))
    (δ : (∏ᶜ (fun n : ℕ ↦
      (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E)) ⟶ L⟦(1 : ℤ)⟧)
    (_hL : IsDerivedLimitTriangle (fun n : ℕ ↦
      (DerivedCategory.TStructure.t.natTransTruncGEOfLE
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
          (Int.neg_le_neg (Int.ofNat_le.mpr (Nat.le_succ n)))).app E) L π δ) :
    (∃ e : E ≅ L, ∀ n : ℕ,
      e.hom ≫ π ≫ Pi.π (fun n : ℕ ↦
        (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E) n =
          (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) ∧
    ∀ c : E ⟶ L, (∀ n : ℕ,
      c ≫ π ≫ Pi.π (fun n : ℕ ↦
        (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E) n =
          (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) → IsIso c := by
  sorry

end CategoryTheory
