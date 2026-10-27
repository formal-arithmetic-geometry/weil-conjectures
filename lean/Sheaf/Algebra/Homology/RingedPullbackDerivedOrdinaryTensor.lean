/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Algebra.Homology.RingedDerivedTensorAugmentationNaturality
public import Sheaf.Paper.PullbackTensorCanonicalShiftUnit
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.RingedTopoiTensorComparisonData
public import Sheaf.Paper.RingedTopoiTensorComparisonConstruction
public import Sheaf.Paper.ProjectionMateExact
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence

/-! # Pullback compatibility of the derived-to-ordinary tensor augmentation

Source: Stacks Project, sites-cohomology.tex, Tag 0FPH,
lemma-tensor-pull-compatibility, entire diagram.
(blueprint: lem-sfb-ringed-pullback-derived-ordinary-tensor).

All complexes are unbounded. The canonical tensor comparison is specified by its
existing representative normalization; the augmentation is the already selected
natural transformation on pairs of actual complexes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe uC vC uD vD r wR wS

open CategoryTheory
open CategoryTheory.CochainPullback hiding Modules
open SheafOfModules.KFlatFixedTensor

namespace SheafOfModules

/-- Derived pullback commutes with the canonical derived-to-ordinary tensor augmentation.
The normalized `mu` is the canonical comparison of Tag 07A4, not an arbitrary tensor map:
`IsNormalized` is its existing unique representative characterization. The parameters
`L`, `epsilon`, and `hL` present the universal left derived pullback. The data `f` and `k`
are the ringed geometric morphism and its insertion-of-one ordinary tensor comparison.

Source: Stacks Project, Tag 0FPH, lemma-tensor-pull-compatibility, entire diagram.
(blueprint: lem-sfb-ringed-pullback-derived-ordinary-tensor).

Proof plan:
1. Choose flat-term K-flat resolutions p : P → A and q : Q → B using
   lem-pc-kflat-resolution. By lem-pur-kflat-total-tensor-model their total tensor C
   is again flat-term K-flat. By lem-weil-pbc-ringed-pullback-preserves-kflat the
   pulled-back resolutions have the same properties. The left-derived comparison
   is invertible on P, Q and C by lem-weil-pbc-ringed-topoi-derived-pullback.
   The map c = T(p,q), and its ordinary pullback, need not be quasi-isomorphisms.
2. Set s = Q(p) tensor-derived Q(q) and e = rho(P,Q) after s inverse. The augmentation
   normalization in lem-sfb-ringed-derived-tensor-augmentation-naturality gives
   rho(A,B) = e followed by Q(c). Naturality of epsilon at the actual cochain map c
   therefore expresses the right edge through theta = L(e) followed by epsilon(C),
   without inverting epsilon(T(A,B)).
3. On P,Q, substitute the representative normalization of
   lem-weil-pbc-pullback-tensor-canonical-shift-unit and rho = representativeIso inverse.
   The cochain comparison of lem-pur-cochain-pullback-tensor-coherence is delta:
   both insert 1 on local pure tensors, as specified by
   def-weil-pbc-canonical-ringed-tensor-comparison. Cancelling the invertible resolving
   comparisons proves the required square for P,Q. This is the canonical mu used by
   lem-weil-pbc-ringed-projection-mate-exact and
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback.
4. Apply naturality of mu to Q(p), Q(q), of epsilon to p,q, and of rho to their
   ordinary pullbacks. Cancel the isomorphism L(s). The other edge becomes theta
   followed by Q(delta(P,Q)) and Q(T(f*p,f*q)).
5. Naturality of the ordinary tensor comparison gives
   f*(c) followed by delta(A,B) = delta(P,Q) followed by T(f*p,f*q).
   On each bidegree both maps send r tensor (x tensor y) to
   (r tensor p(x)) tensor (1 tensor q(y)). The comparison preserves bidegrees, so
   respects the signed total differential without an extra sign. Localize and
   precompose with theta. Steps 2 and 4 identify the two resulting composites with
   the two sides below. No flatness of the structural map or of A,B is used.
-/
theorem ringedPullback_derived_ordinary_tensor
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
    [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wS} (Modules S)]
    (f : RingedPullback.{r, uC, vC, uD, vD} R S)
    (k : Comparison.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f)
    (L : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S))
    (epsilon : DerivedCategory.Q ⋙ L ⟶
      pull (J := J) (K := K) (R := R) (S := S) f ⋙ DerivedCategory.Q)
    (hL : L.IsLeftDerivedFunctor epsilon
      (HomologicalComplex.quasiIso (Modules R) (.up ℤ)))
    (mu : PullbackTensorCanonical.Phi (R := R) L ≅
      PullbackTensorCanonical.Psi (S := S) L)
    (hmu : PullbackTensorCanonical.IsNormalized
      (J := J) (K := K) (R := R) (S := S) f k L epsilon mu.hom)
    (A B : CochainComplex (Modules R) ℤ) :
    L.map ((ringedTensorAugmentation R).app (A, B)) ≫
        epsilon.app (((totalTensor R).obj A).obj B) ≫
        DerivedCategory.Q.map (comparison (J := J) (K := K) (R := R) (S := S) f k A B).hom =
      mu.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫
        (Functor.uncurry.obj (derivedTensor S)).map
          (Prod.mkHom (epsilon.app A) (epsilon.app B)) ≫
        (ringedTensorAugmentation S).app
          ((pull (J := J) (K := K) (R := R) (S := S) f).obj A,
            (pull (J := J) (K := K) (R := R) (S := S) f).obj B) := by
  sorry

end SheafOfModules
