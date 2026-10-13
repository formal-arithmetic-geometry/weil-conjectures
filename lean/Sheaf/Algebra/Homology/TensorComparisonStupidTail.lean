/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
import Sheaf.Algebra.Homology.MixedTensorKFlatQuasiIso
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Gluing tensor comparisons along a stupid tail

Source: Stacks Project, Tag 06XY, derived tensor exactness and the finite
stupid-truncation argument in Lemma 15.60.9; Tag 08IB, Tor comparison.
(blueprint: lem-pc-tensor-comparison-stupid-tail).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

namespace CochainComplex

/-- The comparison for a complex follows from comparisons for its bottom term
and its next stupid tail. No Tor vanishing or upper bound is assumed here.

Source: Stacks Project, Tag 06XY, Lemma 15.60.9 (the degreewise split stupid-tail
sequence), Lemma 15.60.12 and Definition 15.60.13 (K-flat model independence and
exact derived tensor); Tag 08IB, derived-to-ordinary tensor comparison.
(blueprint: lem-pc-tensor-comparison-stupid-tail).

Proof:
1. Write T = sigma_{>=k+1} Q and S = Q.X k[-k]. Since Q vanishes below k,
   inclusion of T and projection onto S form a degreewise split short exact
   sequence 0 -> T -> Q -> S -> 0. The connecting chain map S -> T[1] is d^k,
   with the sign convention of the shift. Tensoring with B preserves this
   sequence because each term sequence is split; its triangle is distinguished.
2. Derived tensor is exact by Tag 06XY, Definition 15.60.13. Applying it to the
   same triangle gives a distinguished triangle with vertices T tensor^L B,
   Q tensor^L B, S tensor^L B. Its canonical comparisons to ordinary tensor
   give a morphism of triangles: the augmentations are natural, commute with
   shifts and with the connecting map d^k. These comparisons may be computed
   with any K-flat resolutions by Lemma 15.60.12, so the two hypotheses apply
   to the outer vertices independently of the resolutions used to form this
   triangle. K-flat resolutions exist by Lemma 15.60.10.
3. Apply the long exact cohomology sequences. For every degree the four outer
   maps of the five-term segment are isomorphisms by hsingle and htail. The
   five lemma makes the middle map an isomorphism. Compute that middle map
   on the specified K-flat resolution f using model independence; it is
   exactly the homology map of f tensor B. Therefore f tensor B is a
   quasi-isomorphism. This proof does not use boundedness of Q or T. -/
theorem quasiIso_tensor_of_stupid_tail
    {R : Type u} [CommRing R] {B : Type u} [CommRing B] [Algebra R B]
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) (k : ℤ)
    (hbelow : ∀ n : ℤ, n < k → IsZero (Q.X n))
    (hsingle : ∀ (P : CochainComplex.KFlat (ModuleCat.{u} R))
      (f : P.obj ⟶ (HomologicalComplex.single (ModuleCat.{u} R)
        (ComplexShape.up ℤ) k).obj (Q.X k)), QuasiIso f →
      QuasiIso ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f))
    (htail : ∀ (P : CochainComplex.KFlat (ModuleCat.{u} R))
      (f : P.obj ⟶ Q.stupidTrunc (ComplexShape.embeddingUpIntGE (k + 1))), QuasiIso f →
      QuasiIso ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f))
    (P : CochainComplex.KFlat (ModuleCat.{u} R)) (f : P.obj ⟶ Q)
    (hf : QuasiIso f) :
    QuasiIso ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) := by sorry

end CochainComplex
