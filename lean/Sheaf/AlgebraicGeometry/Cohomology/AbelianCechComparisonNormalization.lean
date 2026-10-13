/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction

/-! # Normalization from the degree-zero quotient equation

Source: Stacks Project, Tag 01EQ, proof of Lemma 20.11.2.
(blueprint: new-abelian-cech-comparison-normalization)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
/-- The degree-zero quotient equation forces the canonical normalization.

Source: Stacks Project, Tag 01EQ, the two restriction augmentations in the proof
of Lemma 20.11.2; the degree-zero gluing identification is implemented by the
source library's cechCohomologyZeroIso.
(blueprint: new-abelian-cech-comparison-normalization)

Proof: Fix an injective resolution I. For x in Čech H-zero, represent c x by a
map a from the constant integer sheaf to I-zero using I.extMk_surjective.
Evaluation at 1 gives a global section killed by d-zero, hence a section cycle z.
Apply hc to x, a and z. In degree zero the homology projections from cycles are
isomorphisms, since both complexes start in degree zero and have no boundaries.
Consequently the resulting equality in total homology is equality of the total
zero cocycles. Compose it with iCycles and project onto the (0,0) summand.
The explicit alpha and beta formulas identify the resulting equality with the
restrictions of the section represented by a being the image of x under the
resolution augmentation, on every U_i. The degree-zero Čech gluing isomorphism
and separatedness of I-zero identify that section with the augmentation of the
global section obtained by gluing x. Exactness of the augmented resolution in
degree zero factors a uniquely as b followed by I.ι.f 0, for a map b from the constant integer
sheaf to F. The
Ext-zero cocycle formula identifies I.extMk a with Ext.mk₀ b. Evaluation of b
at 1 is the section represented by functorHZeroIso applied to c x. The preceding
restriction equality and monicity of I.ι.f 0 identify this section with the
gluing of x. Cancel this isomorphism and use equality on every x to obtain the
stated equality of morphisms.

Only the degree-zero predicate is needed; no assumption on alpha in positive
degrees is used. An empty covering forces X to be empty by hcover, so gluing and
all degree-zero groups are zero. Infinite coverings use the ordinary sheaf
condition and introduce no finiteness assumption. -/
theorem abelianCechComparison_zero_normalization
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (c : (TopCat.Sheaf.cechCohomologyFunctor U 0).obj F ⟶
      (Sheaf.functorH (Opens.grothendieckTopology X) 0).obj F)
    (hc : IsAbelianCechComparison U F 0 c) :
    c = (TopCat.Sheaf.cechCohomologyZeroIso U hcover).inv.app F ≫
      (Sheaf.functorHZeroIso (Opens.grothendieckTopology X) isTerminalTop).inv.app F := by sorry
end AlgebraicGeometry.Scheme.Modules
