/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J6
-/
module

public import Sheaf.Paper.FourierAdicArtinSchreier
public import Sheaf.Paper.DerivedPullbackTensorIso

/-! # The trivial Artin--Schreier character gives the common-stage coefficient unit

Source: the constant-character clause of blueprint sk-lem-as-properties and
WeilConjectures/FourierTransform/ArtinSchreier.lean, nonempty_iso_artinSchreierSheafOf_one.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The unshifted completed trivial-character line is the actual coefficient unit.
Source: blueprint sk-lem-as-properties, trivial-character clause; Bhatt--Scholze,
Lemma 6.8.2(1); Stacks 03EL and 0941
(blueprint: lem-wf-fourier-trivial-character-unit).

Proof: injectivity of fourierCoefficientEmbedding and the normalization of
fourierIntegralCharacter identify its value at the trivial character with 1.
Apply nonempty_iso_artinSchreierSheafOf_one over the lifted prime field; the
isomorphism identifies the invariant functions with constant sections. Comparison
inverse image takes the constant regular etale module to the constant regular
pro-etale module. The fixed-ring/constant-ring equivalence and sheafification
preserve this identification. Extension along integralConstantToCompletionOfUniverses
sends that regular module to the completed regular module, by multiplication,
with inverse m mapped to 1 tensor m. Place this isomorphism in degree zero.
Its quotient projections identify every positive reduction with the coherent
coefficient-ring system. The reduction/limit adjunction and completeness of the
completed regular module identify it with pullbackTensorIntegralUnit. Apply
rationalization. Finally enlarge from the least coefficient field to the Fourier
coefficient stage, using pullbackTensorCommonUnitStage and the stage-system
isomorphism to a larger stage. The result is the displayed common-stage
isomorphism. These maps also apply to the empty scheme and to characteristic two;
p is invertible in the integral coefficients because p differs from l. -/
theorem fourierTrivialCharacter_unit (F : FourierSetting.{u}) (X : Scheme.{u})
    [IsNoetherian X] [CharP Γ(X, ⊤) F.field.p]
    [∀ x : X, Invertible (F.coefficients.l : X.residueField x)] :
    Nonempty ((⟨fourierCoefficientStage F,
      (sfRationalConstructibleLocalization F.coefficients.l (fourierCoefficient F) X).obj
        ⟨fourierAdicArtinSchreier F X 1 0, fourierAdicArtinSchreier_mem F X 1 0⟩⟩ :
          generalAlgebraicallyClosedConstructibleCategory F.coefficients.l F.coefficients.Qbar X)
      ≅ pullbackTensorCommonUnit F.coefficients.l F.coefficients.Qbar X) := by sorry

end WeilConjectures
