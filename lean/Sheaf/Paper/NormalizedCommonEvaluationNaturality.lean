/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.DerivedAutomorphismHomEvaluation

/-! # Naturality of normalized common-stage evaluation

Source: blueprint latest, lem-fix-weil-operations.proof.md, evaluation paragraph;
derived-automorphism Hom evaluation, common-stage descent, steps 15--16
(blueprint: lem-pod-normalized-common-evaluation-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory Opposite AlgebraicGeometry
namespace WeilConjectures

/-- The Hom-first common-stage evaluation is natural in both internal-Hom entries.
No separatedness or finite-type hypothesis is needed for this coefficient identity.
Source: blueprint latest, lem-fix-weil-operations.proof.md, evaluation paragraph;
lem-pod-derived-automorphism-hom-evaluation, steps 15--16.

Proof: choose one finite coefficient field representing both permitted pairs and
both components of the pair arrow. Enlarge it to contain the tensor and internal-Hom
object stages and all the finite comparisons. The prescribed common-stage tensor
and Hom functor formulas express their maps by conjugating the rational maps at
this field. The normalization of podCommonClosed, specialized to the identity
transpose, expresses each evaluation by the rational evaluation, conjugated by the
same tensor and Hom comparisons. Substitute these expressions into both sides.
The intervening Hom and tensor comparisons cancel; the remaining equality is
normalizedRationalEvaluation_naturality at that finite field. The scalar comparison
preserves evaluation and obeys the tower cocycle, so a further common enlargement
preserves this equality. Equal representatives define equal classes; therefore the
two common-stage composites are equal, for arbitrary morphisms of the actual
category. Identity and zero pair arrows give respectively the identity and zero
naturality equations, and no injectivity of a scalar transition is used.
(blueprint: lem-pod-normalized-common-evaluation-naturality). -/
theorem normalizedCommonEvaluation_naturality
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (P P' : (commonStageHomPairs l Ω W).FullSubcategory) (g : P ⟶ P') :
    (commonStageDerivedTensor l Ω W).map
        (Prod.mkHom ((commonStageDerivedInternalHom l Ω W).map g) (𝟙 P'.obj.1.unop)) ≫
      (podCommonClosed l Ω W).evaluation P' =
    (commonStageDerivedTensor l Ω W).map
        (Prod.mkHom (𝟙 ((commonStageDerivedInternalHom l Ω W).obj P)) g.hom.1.unop) ≫
      (podCommonClosed l Ω W).evaluation P ≫ g.hom.2 := by sorry

end WeilConjectures
