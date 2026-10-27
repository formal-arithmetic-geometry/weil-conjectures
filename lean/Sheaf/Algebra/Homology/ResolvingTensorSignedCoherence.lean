/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Paper.PullbackTensorCanonicalShiftUnit
public import Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints
public import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.KFlatTotalTensorModel

/-! # Transport and signed coherence of a normalized resolving tensor comparison

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 06YU and 0FPT;
more-algebra.tex, section-sign-rules, item-shift-tensor and item-flip-tensor-product.
(blueprint: lem-pur-resolving-tensor-signed-coherence).

All tensors and representative comparisons are the published K-flat constructions.
The sole construction below conjugates the specified natural isomorphism by eta.
In the shift equation the first shift is extracted before the second: the second
shift therefore uses the original first-factor degree, as in the source node.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC uD vD r wR wS

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.CochainPullback hiding Modules
open SheafOfModules.KFlatFixedTensor
open SheafOfModules.PullbackTensorCanonical

namespace SheafOfModules.ResolvingTensorSigned

attribute [local irreducible] SheafOfModules.monoidalCategory
  siteDerivedTensorIndependentCoefficients representativeIso
  CategoryTheory.Functor.mapDerivedCategory
  PullbackTensorCanonical.IsNormalized HasCanonicalTensorShifts
  DerivedTensorConstraints.IsNormalized

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wS} (Modules S)]
  (f : RingedPullback.{r, uC, vC, uD, vD} R S)
  [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L]
  (L : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S))

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- Conjugation of the given normalized canonical tensor comparison by eta.
The components are eta inverse, followed by muL, followed by eta tensor eta.
This is a composite of actual natural isomorphisms, with no new tensor choice.
Source: Stacks 07A4, transport of the representative comparison
(blueprint: lem-pur-resolving-tensor-signed-coherence). -/
def transportedComparison
    (muL : Phi L ≅ Psi L) (eta : L ≅ f.L.mapDerivedCategory) :
    Phi f.L.mapDerivedCategory ≅ Psi f.L.mapDerivedCategory :=
  isoWhiskerLeft (Functor.uncurry.obj (canonicalDerivedTensor R)) eta.symm ≪≫
    muL ≪≫ isoWhiskerRight (NatIso.prod eta eta)
      (Functor.uncurry.obj (canonicalDerivedTensor S))

attribute [local irreducible] transportedComparison

variable (k : Comparison.{r, uC, vC, uD, vD} f)
  (epsilon : DerivedCategory.Q ⋙ L ⟶ pull.{r, uC, vC, uD, vD} f ⋙ DerivedCategory.Q)
  [L.CommShift ℤ] [NatTrans.CommShift epsilon ℤ]
  [(derivedTensor R).CommShift₂Int] [(derivedTensor S).CommShift₂Int]

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- Transport of the representative-normalized pullback tensor comparison has
its prescribed resolving components, is unique among all natural transformations,
and respects simultaneous integer shifts, Koszul symmetry and reassociation.
The normalized associator and symmetry use the existing constraint predicate;
its existential shift component merely projects out those two normalizations.
No restriction is made on the boundedness of any complex or derived object.

Source: Stacks sites-cohomology.tex, Tags 07A4, 06YU and 0FPT;
more-algebra.tex, section-sign-rules, item-shift-tensor and item-flip-tensor-product
(blueprint: lem-pur-resolving-tensor-signed-coherence).

Proof plan, following the node's seven steps:
1. Total tensors and shifts of flat-term K-flat complexes are resolving by
   lem-pur-kflat-total-tensor-model and lem-weil-pbc-kflat-fixed-tensor-triangulated.
   The preservation hypotheses put their pullbacks in the target resolving class.
2. Conjugate muL by eta. Naturality of eta at the representative map r cancels
   eta at the total tensor. Substitute eta followed by kappa = epsilon on each
   resolving input and its total tensor. The muL normalization becomes precisely
   IsNormalized with epsilon replaced by the exact factorization kappa.
3. Cancel U(r) and the tensor of the invertible kappa components. Two normalized
   natural transformations agree on resolving pairs; the unique-extension clause
   of lem-weil-pbc-site-derived-tensor-descent gives equality everywhere.
4. Extract the first shift a before the second b. On homogeneous original
   first-factor degree p, both routes send s tensor (x tensor y) to
   (-1)^(bp) (s tensor x) tensor (1 tensor y). Exact localization has the
   degreewise-identity shift comparison, so additivity preserves this sign.
   Naturality and the direct-sum universal property give the chain equation.
5. On bidegree (p,q), both symmetry routes give
   (-1)^(pq) (s tensor y) tensor (1 tensor x), by scalar balancing and the
   cochain comparison of lem-pur-cochain-pullback-tensor-coherence.
6. The nested resolving totals are legitimate by step 1. Insert their r maps
   and cancel the computation isomorphisms. The two associativity routes send
   s tensor ((x tensor y) tensor z) to
   (s tensor x) tensor ((1 tensor y) tensor (1 tensor z)), with no extra sign.
   This is the cochain comparison's unsigned reassociation equation.
7. For fixed a,b the two shift paths are natural transformations of bifunctors;
   so are the symmetry paths. The reassociation paths are transformations of
   trifunctors. Finite-variable faithful restriction from
   lem-pur-derived-tensor-additive-constraints descends steps 4--6 to all derived
   objects and morphisms. All totalizations use full direct sums, without bounds.
-/
theorem resolving_tensor_signed_coherence
    (hL : L.IsLeftDerivedFunctor epsilon
      (HomologicalComplex.quasiIso (Modules R) (.up ℤ)))
    (hshiftR : HasCanonicalTensorShifts (R := R))
    (hshiftS : HasCanonicalTensorShifts (R := S))
    (hflat : ∀ M : Modules R, IsFlatOnSite (J := J) (R := R) M →
      IsFlatOnSite (J := K) (R := S) (f.L.obj M))
    (hresolving : ∀ P : CochainComplex (Modules R) ℤ,
      P.IsKFlatIndependentCoefficients →
      (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
      CochainComplex.IsKFlatIndependentCoefficients ((pull.{r, uC, vC, uD, vD} f).obj P) ∧
        ∀ n : ℤ, IsFlatOnSite (J := K) (R := S)
          (((pull.{r, uC, vC, uD, vD} f).obj P).X n))
    (hsums : ∀ I : Type r, PreservesColimitsOfShape (Discrete I) f.L)
    (eta : L ≅ f.L.mapDerivedCategory) [NatTrans.CommShift eta.hom ℤ]
    (heta : ∀ P : CochainComplex (Modules R) ℤ,
      P.IsKFlatIndependentCoefficients →
      (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
      eta.hom.app (DerivedCategory.Q.obj P) ≫ f.L.mapDerivedCategoryFactors.hom.app P =
        epsilon.app P)
    (muL : Phi L ≅ Psi L)
    (hmuL : PullbackTensorCanonical.IsNormalized f k L epsilon muL.hom)
    (alphaR : DerivedTensorConstraints.leftAssociated R ≅
      DerivedTensorConstraints.rightAssociated R)
    (sigmaR : DerivedTensorConstraints.tensor R ≅ DerivedTensorConstraints.swapped R)
    (hconstraintsR : ∃ t : ∀ a b : ℤ,
      DerivedTensorConstraints.shiftedSource R a b ≅
        DerivedTensorConstraints.shiftedTarget R a b,
      DerivedTensorConstraints.IsNormalized R t alphaR sigmaR)
    (alphaS : DerivedTensorConstraints.leftAssociated S ≅
      DerivedTensorConstraints.rightAssociated S)
    (sigmaS : DerivedTensorConstraints.tensor S ≅ DerivedTensorConstraints.swapped S)
    (hconstraintsS : ∃ t : ∀ a b : ℤ,
      DerivedTensorConstraints.shiftedSource S a b ≅
        DerivedTensorConstraints.shiftedTarget S a b,
      DerivedTensorConstraints.IsNormalized S t alphaS sigmaS) :
    PullbackTensorCanonical.IsNormalized f k f.L.mapDerivedCategory
      f.L.mapDerivedCategoryFactors.hom (transportedComparison f L muL eta).hom ∧
    (∀ tau : Phi f.L.mapDerivedCategory ⟶ Psi f.L.mapDerivedCategory,
      PullbackTensorCanonical.IsNormalized f k f.L.mapDerivedCategory
        f.L.mapDerivedCategoryFactors.hom tau →
      tau = (transportedComparison f L muL eta).hom) ∧
    (∀ (a b : ℤ) (A B : DerivedCategory (Modules R)),
      (transportedComparison f L muL eta).hom.app (A⟦a⟧, B⟦b⟧) ≫
          (Functor.uncurry.obj (derivedTensor S)).map
            (Prod.mkHom ((f.L.mapDerivedCategory.commShiftIso a).hom.app A)
              ((f.L.mapDerivedCategory.commShiftIso b).hom.app B)) ≫
          (((derivedTensor S).flip.obj ((f.L.mapDerivedCategory.obj B)⟦b⟧)).commShiftIso a).hom.app
            (f.L.mapDerivedCategory.obj A) ≫
          (shiftFunctor _ a).map
            ((((derivedTensor S).obj (f.L.mapDerivedCategory.obj A)).commShiftIso b).hom.app
              (f.L.mapDerivedCategory.obj B)) ≫
          (shiftFunctorAdd' _ b a (a + b) (add_comm b a)).inv.app
            (((derivedTensor S).obj (f.L.mapDerivedCategory.obj A)).obj
              (f.L.mapDerivedCategory.obj B)) =
        f.L.mapDerivedCategory.map
          ((((derivedTensor R).flip.obj (B⟦b⟧)).commShiftIso a).hom.app A ≫
            (shiftFunctor _ a).map (((derivedTensor R).obj A).commShiftIso b |>.hom.app B) ≫
            (shiftFunctorAdd' _ b a (a + b) (add_comm b a)).inv.app
              (((derivedTensor R).obj A).obj B)) ≫
          (f.L.mapDerivedCategory.commShiftIso (a + b)).hom.app
            (((derivedTensor R).obj A).obj B) ≫
          ((transportedComparison f L muL eta).hom.app (A, B))⟦a + b⟧') ∧
    (∀ A B : DerivedCategory (Modules R),
      f.L.mapDerivedCategory.map (sigmaR.hom.app (A, B)) ≫
          (transportedComparison f L muL eta).hom.app (B, A) =
        (transportedComparison f L muL eta).hom.app (A, B) ≫
          sigmaS.hom.app (f.L.mapDerivedCategory.obj A, f.L.mapDerivedCategory.obj B)) ∧
    (∀ A B N : DerivedCategory (Modules R),
      f.L.mapDerivedCategory.map (alphaR.hom.app ((A, B), N)) ≫
          (transportedComparison f L muL eta).hom.app
            (A, ((derivedTensor R).obj B).obj N) ≫
          (Functor.uncurry.obj (derivedTensor S)).map
            (Prod.mkHom (𝟙 _) ((transportedComparison f L muL eta).hom.app (B, N))) =
        (transportedComparison f L muL eta).hom.app
            (((derivedTensor R).obj A).obj B, N) ≫
          (Functor.uncurry.obj (derivedTensor S)).map
            (Prod.mkHom ((transportedComparison f L muL eta).hom.app (A, B)) (𝟙 _)) ≫
          alphaS.hom.app ((f.L.mapDerivedCategory.obj A, f.L.mapDerivedCategory.obj B),
            f.L.mapDerivedCategory.obj N)) := by
  sorry

end SheafOfModules.ResolvingTensorSigned
