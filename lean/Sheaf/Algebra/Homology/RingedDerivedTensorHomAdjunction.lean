/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y5
-/
module

public import Sheaf.Algebra.Homology.RingedDerivedTensorNative

/-! # Evaluation-normalized closedness of the ringed-site derived tensor

Source: Stacks Project, Tag 08J9, with Tags 0A90 and 0A8Z.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u w
open CategoryTheory WeilConjectures
namespace CategoryTheory.RingedDerivedNative

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (Modules.{c, v, u} J R)]

/-- The native derived tensor is left adjoint to the recorded derived internal Hom,
with the evaluation normalization on the fixed simultaneous K-flat comparison.
The equality fixes only the existing monoidal structure; this theorem constructs
its adjunctions and checks evaluation, and asserts no symmetry or constraint formulas.

Source: Stacks Project, Tag 08J9, proved using 0A90 and 0A8Z
(blueprint: lem-sf-ringed-derived-tensor-hom-adjunction).

Proof: choose K-flat representatives P,L and a K-injective replacement I(M).
The sheaf Hom complex Hom(L,I(M)) is K-injective because L is K-flat.
The Hom-total-tensor isomorphism of 0A90, ordinary global sections and zeroth
cohomology identify maps from P into this Hom complex with maps from Tot(P tensor L)
into I(M), modulo homotopy (0A8Z). K-injectivity identifies these classes with
morphisms in the derived category. The inverse of the native lax comparison
identifies the other side with morphisms out of the derived tensor. Both
localizations extend this equivalence uniquely to all derived objects and maps.
Currying on homogeneous sections sends x tensor y to phi(x)(y), without an
extra sign: the Hom differential is exactly the total-tensor chain-map equation.
This also takes homotopies to homotopies. Naturality under precomposition in P,L
and postcomposition in I(M) holds componentwise and descends through localization,
including inverse denominators. Package the resulting natural Hom equivalences
as adjunctions. Naturality in L is the evaluation_naturality field. The componentwise
formula applied before localization is precisely CoefficientTensorUncurryModel;
the inverse localized replacement augmentation gives its stated target comparison.
The monoidal structure and its fixed tensor comparison are those already constructed
by native K-flat localization, so their equalities are identities. -/
theorem closedAdjunction :
    ∃ S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R),
      S.monoidal = monoidal.{c, v, u, w} J R ∧
        ∃ T : CoefficientTensorModels.{u, c, v, w} J R S,
          HEq T.comparison (comparison.{c, v, u, w} J R) := by
  sorry

end CategoryTheory.RingedDerivedNative
