/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Sheaf.Algebra.Homology.SplitFlatFilteredSheafModels
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Homology.FlatCoverFunctor
import Sheaf.CategoryTheory.RightFractionDenseSubcategory
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.UniformFiniteFilteredLocalization
import Sheaf.CategoryTheory.DgAbcHomotopyCategoryTriangulated
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.Abelian.Filtration
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
/-!
# Flat resolutions for a fixed finite filtration

Source: Varshavsky §5.2.1(b), filtered tensor referred to Illusie V §2; the
agent-formulated finite-flag resolution tool using Stacks 077J, 06YQ and 0GSL
(blueprint: lem-trf-finite-filtered-flat-resolution).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v r

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.FilteredFlat

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- Fixed finite filtered flat resolutions, K-flatness of all split-flat models,
the inclusion-induced localization equivalences with interval compatibility, and
convolution acyclicity with either order of tensor factors.

Source: Varshavsky §5.2.1(b) motivates the filtered tensor; the resolution tool
is the finite-flag adaptation of Stacks 077J and 06YQ, with localization from 0GSL.
(blueprint: lem-trf-finite-filtered-flat-resolution).

Proof:
1. For a filtered module E, take flat epimorphisms B_j onto F^jE, for a ≤ j ≤ b
   (Stacks 03EW). Their direct sum, filtered by labels j ≥ p, maps strictly
   epimorphically onto E: its j=p summand already covers F^pE. Outside the
   interval use the a summand or the zero object. No projectivity is asserted.
2. Start above a cochain bound N of M. Descending in n, form the cycle-pair
   pullback T^n consisting of (x,y) with d_P y=0 and f y=d_M x, with the
   intersection filtration. The induction invariant is the epimorphism from
   cycles of each F^pP onto cycles of F^pM in degree n+1. Pulling it back
   along d_M makes F^pT^n onto F^pM^n epimorphic.
3. Apply the split-flat cover to T^n. Its two projections define f^n and d_P^n.
   The pair equations give d_P squared zero and the chain-map equation.
   Pull back along x ↦ (x,0) on cycles to obtain the next cycle epimorphism.
   Induction on N-n gives bounded-above P with degreewise split-flat terms.
4. For K=ker f with induced filtration, a cycle z in F^pK^{n+1} gives (0,z)
   in F^pT^n. Pulling back the cover gives epimorphic boundary lifts inside
   F^pK. Thus every step of K is acyclic. The termwise short exact sequences
   of steps and their long exact sequences make every F^pf a quasi-isomorphism.
   All lifts here are epimorphic base changes, never lifts on arbitrary sections.
5. Strictness identifies the kernel of gr^pf with gr^pK: subtract a lift from
   F^{p+1}P of the image in F^{p+1}M. The short exact sequence of successive
   steps of K makes every grade of K acyclic. The graded short exact sequence
   then makes every gr^pf a quasi-isomorphism.
6. Every term of P and every graded term is a finite sum of flat sheaves.
   Bounded-above flat complexes are K-flat by 06YQ. Apply this also to any
   other split-flat model, not merely the particular replacement constructed.
7. Filtered cochain complexes form a dg category, with differential on maps
   d_Y h - (-1)^degree(h) h d_X. Finite direct sums, signed shifts and cones
   preserve the interval and upper cochain bound. The cone has terms
   Y^i ⊕ X^{i+1} and differential (y,x) ↦ (d_Y y+fx,-d_X x).
   The dg zero, shift and cone criteria give its homotopy triangulation.
8. Grading commutes with shifts, filtered homotopies and these cones. Graded
   acyclic objects form a replete triangulated subcategory, by the long exact
   cone sequence. Its cone class is the graded quasi-isomorphisms, so those
   arrows have a right calculus of fractions.
9. The full split-flat homotopy subcategory supplies a denominator onto every
   object by steps 1--5. Resolve the middle object of each roof and of each
   common refinement. This gives essential surjectivity and bijections on
   localized hom sets (0GSL/right-fraction dense-subcategory criterion).
   To identify the target with chain-map localization, use the cylinder
   X^n ⊕ X^{n+1} ⊕ X^n, with d(x,y,z)=(dx+y,-dy,dz-y), projection
   π(x,y,z)=x+z and endpoint inclusions. The filtered homotopy
   h(x,y,z)=(0,-z,0) gives 1-i_0π=dh+hd. Hence π is a graded
   quasi-isomorphism. If f-g=dk+kd, the filtered chain map
   H(x,y,z)=fx+ky+gz identifies f and g after inverting π. Thus
   localization factors through filtered homotopy. The two localization
   universal properties give inverse functors with the displayed normalization.
10. Widening intervals keeps complexes and maps, adds zero splitting summands
    in new grades, and preserves graded quasi-isomorphisms. The inclusion square
    commutes before localization. The localization universal property gives
    the comparison isomorphism in the statement, coherent for nested intervals.
11. Direct sums of sheaves are exact: they are filtered colimits of finite sums
    and filtered colimits are exact in this Grothendieck abelian category.
    Thus quotients can pass through the countable sums in total complexes,
    even when the second factor is unbounded in both cochain directions.
12. Write P^i as the finite direct sum of flat B_j^i in grade j. The convolution
    step in bidegree (i,k) is the direct sum of B_j^i tensor F^{s-j}W^k:
    in any summand with p+q=s and j≥p, q≥s-j; the converse occurs at p=j.
    Flatness makes the tensor-step inclusions monic and identifies their
    quotients with B_j^i tensor gr^{s-j}W^k. The same formula passes through
    the countable total sums by step 11. This specifies an actual decreasing
    convolution filtration, whose existence is part of the conclusion.
13. The differential of P is triangular in grade labels. Its off-diagonal
    components disappear in grade s: their W-step index is strictly too large.
    Therefore gr^s Tot(P tensor W) is the finite sum over j of
    Tot(gr^jP tensor gr^{s-j}W), with the usual Koszul differential.
    Each summand is acyclic by K-flatness and graded acyclicity of W, and
    finite sums of acyclic complexes are acyclic.
14. The Koszul swap x tensor y ↦ (-1)^{deg x deg y} y tensor x is a chain
    isomorphism preserving the convolution images, by sheaf tensor symmetry.
    It transports the preceding acyclicity to the reversed tensor order. -/
theorem finite_filtered_flat_resolution :
    (∀ (a b : ℤ), a ≤ b → ∀ M : Complexes R a b,
      ∃ (P : FlatComplexes R a b) (f : P.obj ⟶ M),
        (∀ p n : ℤ, Epi ((FilteredObject.restrictionSteps f.hom p).f n)) ∧
        ∀ p : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom p)) ∧
    (∀ (a b : ℤ), a ≤ b → ∀ P : FlatComplexes R a b,
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P.obj.obj.obj ∧
        ∀ p : ℤ, CochainComplex.IsKFlatIndependentCoefficients (R := R)
          (P.obj.obj.filtration.gradedPiece p)) ∧
    (∃ E : ∀ (a b : ℤ) (_ : a ≤ b),
        (flatHomotopyQuasiIso R a b).Localization ≌
          UniformFilteredDerived (Modules R) (some (a, b))
            (CochainComplex.minus (Modules R)),
      (∀ (a b : ℤ) (hab : a ≤ b),
        Nonempty ((flatHomotopyQuotient R a b ⋙
          (flatHomotopyQuasiIso R a b).Q) ⋙ (E a b hab).functor ≅
            flatInclusion R a b ⋙
              (uniformFilteredQuasiIso (some (a, b))
                (CochainComplex.minus (Modules R))).Q)) ∧
      ∀ (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d) (ha : c ≤ a) (hb : b ≤ d),
        Nonempty (widenFlatLocalization R a b c d ha hb ⋙ (E c d hcd).functor ≅
          (E a b hab).functor ⋙ widenDerived R a b c d ha hb)) ∧
    (∀ (a b : ℤ), a ≤ b → ∀ (P : FlatComplexes R a b)
      (W : FilteredObject (CochainComplex (Modules R) ℤ)),
      W.filtration.IsFinite → (∀ p : ℤ, (W.filtration.gradedPiece p).Acyclic) →
      (∃ F : DecreasingFiltration (tensorTotal R P.obj.obj.obj W.obj),
        IsConvolution R P.obj.obj W F ∧ ∀ s : ℤ, (F.gradedPiece s).Acyclic) ∧
      (∃ F : DecreasingFiltration (tensorTotal R W.obj P.obj.obj.obj),
        IsConvolution R W P.obj.obj F ∧ ∀ s : ℤ, (F.gradedPiece s).Acyclic)) := by
  sorry

end SheafOfModules.FilteredFlat
