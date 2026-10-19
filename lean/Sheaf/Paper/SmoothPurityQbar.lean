/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Sheaf.Paper.IntrinsicCoefficientTwists
public import Sheaf.Paper.CompactSupportCoefficientAction
public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.Paper.DirectImagesConstructible
public import WeilConjectures.ZetaSeries
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.CompactSupportFiniteFieldIndependence
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.QcqsCompactSupportRealization

/-! # Smooth purity with algebraically closed coefficients

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-sp-qbar, order 1831
(blueprint: sk-thm-sp-qbar).

The compact-support action is a presentation of the already normalized finite-level,
integral and rational construction. It is not an arbitrary functor or comparison.
The right adjoint uses the intrinsic common-stage category throughout.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- Transport the inverse of l in the fixed base field to every residue field.
No invertibility assumption on the schemes is added.
Source: blueprint main-20261015, sk-thm-sp-qbar, global coefficient hypotheses
(blueprint: sk-thm-sp-qbar). -/
@[instance_reducible] def smoothQbarResidueInvertible (T : Scheme.{u}) [T.Over (Spec (.of D.k))] :
    ∀ x : T, Invertible (l : T.residueField x) :=
  fun x ↦ (by
    simpa using (finiteFieldDatumPrimeUnit D l hl).map
      ((T ↘ Spec (.of D.k)).residueFieldAlgebraMap x) : IsUnit (l : T.residueField x)).invertible

/-- The specified adic pullback followed by the signed coefficient twist and [2d].
All residue-field inverse instances are constructed from l distinct from p.
Source: blueprint main-20261015, sk-thm-sp-qbar, displayed right adjoint
(blueprint: sk-thm-sp-qbar). -/
def smoothQbarPurityRightFunctor
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    (f : X ⟶ Y) (d : ℕ) :
    generalAlgebraicallyClosedConstructibleCategory l Ω Y ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω X := by
  letI := smoothQbarResidueInvertible D l hl X
  letI := smoothQbarResidueInvertible D l hl Y
  exact commonStageDerivedPullback l Ω f ⋙ intrinsicQbarComplexTwistFunctor D l hl X Ω
    (d : ℤ) ⋙ shiftFunctor (generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (2 * (d : ℤ))

/-- Smooth purity: the normalized common-stage compact-support direct image is
left adjoint to adic pullback followed by (d)[2d]. The existential S supplies the
published compact-support coefficient action, including its finite maps and the
normalized integral coefficient comparisons. Thus no functor-existence or
coefficient-compatibility hypothesis is imposed.
Source: blueprint main-20261015, sk-thm-sp-qbar, order 1831
(blueprint: sk-thm-sp-qbar).

Proof (the six steps of the DAG node):
1. det-sp-integral-adjunction-bijection gives the integral adjunction with its
purity isomorphism gamma. Conjugate the unit by gamma inverse and the counit
by gamma. Naturality of gamma and the original triangles prove both triangles.
Raw rationalization tensors these maps with one. Integral naturality extends
linearly to u/varpi^n, and both triangles survive localization.
2. sk-lem-sp-field-extension identifies compact support and twisted pullback
under finite coefficient extension and preserves these units and counits.
Therefore the rational Hom bijections and their inverses commute with every
transition map, including the specified coefficient comparisons and tower laws.
3. The compact-support and pullback functors act on a common-stage representative
by comparison, finite-stage functor, inverse comparison. Naturality and tower
coherence make this independent of enlargement and representative; cancellation
of the middle comparisons proves composition and identities. These are exactly
the supplied S.system.functor and the right functor displayed below.
4. Represent M and K at one common finite field E. Apply the rational Hom
bijection on each further field F and pass to classes. Step 2 makes both the
bijection and inverse well defined; their composites are identities on every
representative, hence on the Hom colimits.
5. Descend each finite diagram of models, comparison isomorphisms, inverse
identities and arrows to a common finite overfield. Rational naturality there
proves independence relative to the representing isomorphisms and naturality
in both variables for arbitrary common-stage morphisms.
6. Apply the Hom bijection to identity arrows to obtain the unit and counit.
At each finite stage these are the rational unit and counit of step 1. Their
two triangle identities pass to common-stage classes, yielding the adjunction. -/
theorem smoothPurityQbar
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (c : Compactification f) :
    ∃ S : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω c,
      Nonempty (S.system.functor ⊣ smoothQbarPurityRightFunctor D l hl Ω f d) := by
  sorry

end WeilConjectures
