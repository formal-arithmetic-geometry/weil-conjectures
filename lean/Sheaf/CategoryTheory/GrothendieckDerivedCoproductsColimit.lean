/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Statements of the new targets (batch 2) about `GrothendieckDerivedCoproducts`

Kept in their own module so that `Sheaf.CategoryTheory.GrothendieckDerivedCoproducts`, which the first task's targets use, is unchanged.
-/

@[expose] public section

universe t u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Termwise coproducts of arbitrary unbounded cochain complexes compute coproducts
in the derived category of a Grothendieck abelian category, with the specified
termwise coprojections. The actual termwise construction is
`HomologicalComplex.coconeOfHasColimitEval`; its degree objects are colimits of the
component families and its differential is induced by the component differentials.
No nonemptiness or boundedness assumption is made.

Source: Stacks Project, Injectives, Tag 07D9, Lemma `lemma-derived-products`,
assertions (1)-(2) (blueprint: lem-kun-grothendieck-derived-coproducts).

Proof plan:
1. By `def-sp-grothendieck-abelian`, form coproducts in each degree. Induce the
sum differential by the coproduct property. Its square is zero by testing on
coprojections. Assemble chain maps degreewise to obtain a coproduct of complexes.
2. The same assembly works for homotopies: restriction along the coprojections
is a bijection from homotopy classes out of the sum to families of homotopy
classes out of the summands. Surjectivity assembles representatives; injectivity
assembles component homotopies.
3. Represent an arbitrary derived target by a complex M using
`def-weil-abstract-derived-category`. Apply
`lem-weil-pbc-kinjective-functorial-existence` to choose a quasi-isomorphism M to
an unbounded K-injective complex J. Localization identifies the target with Q(J).
4. Apply `lem-sc-kinjective-quasi-iso-comparison` to J, with sources the sum and
each summand. Its Hom bijections commute with restriction because Q preserves
composition. Transport the bijection of step 2 to derived Hom sets into Q(J).
5. Postcomposition with the target isomorphism transports this restriction
bijection to every derived target. This is the coproduct universal property for
the images of the specified coprojections. For an empty family, the degreewise
coproducts are zero and the family of Hom sets is a singleton, so the same
argument proves the empty coproduct assertion. -/
theorem isColimit_mapCocone_grothendieckSum
    (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [HasDerivedCategory.{t} A] (I : Type w) (K : I → CochainComplex A ℤ) :
    Nonempty (IsColimit ((Q (C := A)).mapCocone
      (HomologicalComplex.coconeOfHasColimitEval (Discrete.functor K)))) := by
  sorry

end DerivedCategory

