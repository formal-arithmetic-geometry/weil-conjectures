/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import Sheaf.Algebra.Homology.FlatTruncationTower
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.Algebra.Homology.FlatTruncationTelescopeComparison

/-! # K-flat resolutions without identifying the site universes

Source: Stacks Project, Cohomology on Sites, Tag 06YS
(blueprint: lem-pc-kflat-resolution).
-/

@[expose] public section

universe r u v

open CategoryTheory

namespace CochainComplex

/-- Every complex has a K-flat resolution with flat terms and degreewise epimorphic
augmentation. The site object and morphism universes are independent.
Source: Stacks Tag 06YS (blueprint: lem-pc-kflat-resolution).
Proof:
1. Choose the strictly compatible bounded-above flat replacement tower of the good
truncations, with degreewise epimorphic quasi-isomorphisms q_n
(lem-pc-flat-truncation-tower).
2. On B, the countable sum of the replacements, let φ be one minus the tower shift and
let s be the sum of q_n followed by the truncation inclusions. Compatibility gives φ ≫ s = 0.
The cone desc construction, with shifted component zero and unshifted component s, gives
f : Cone(φ) ⟶ G. The telescope is K-flat by lem-pc-kflat-closure. Evaluation preserves
coproducts; their terms and the finite sums forming the cone terms are flat by the same
closure lemma. Reindex countable sums by ULift into r, without changing the site.
3. The cone desc restrictions satisfy lem-pc-flat-truncation-telescope-comparison, so f is
a quasi-isomorphism. In degree i choose n = i.toNat + 1. The truncation inclusion is an
isomorphism in that degree, so its composite with q_n is epi. This composite factors
through f in degree i, proving the required degreewise epimorphic augmentation. -/
theorem exists_isKFlatResolutionIndependentCoefficients
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {R : Sheaf J CommRingCat.{r}}
    (G : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    ∃ (K : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
      (f : K ⟶ G), CochainComplex.IsKFlatIndependentCoefficients K ∧
        (∀ i : ℤ, exactFunctor _ _
          (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (K.X i))) ∧
        QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i)) := by
  sorry

end CochainComplex
