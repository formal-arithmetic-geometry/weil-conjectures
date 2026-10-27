/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G6
-/
module

public import Sheaf.Paper.FiniteFreeCoefficientExtensionData
import Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.FiniteFreeDerivedScalarCalculus
import Sheaf.SixFunctors.FiniteFreeImageComparison
import Sheaf.Paper.FiniteFreeExceptionalMate
import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange
import Sheaf.Paper.FiniteCoefficientDirectImage
import Sheaf.Paper.FiniteClosedShriek
import Sheaf.SixFunctors.FiniteDualizing
import Sheaf.Paper.FiniteCoefficientHomChange
import Sheaf.SixFunctors.FiniteCoefficientVerdier
import Sheaf.Paper.FiniteEtaleDescent
import Sheaf.Paper.DualityPairing
import Sheaf.SixFunctors.FiniteFreeComparisonTransitivity
import Sheaf.Paper.RamifiedReductionComparisonSquare
import Sheaf.SixFunctors.FiniteDualitySiteComparison
import Sheaf.SixFunctors.FiniteFreeEtaleProEtaleTransport

/-! # Normalized coefficient calculus on the two small sites

Source: blueprint latest, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/-- The normalized two-site coefficient calculus, without geometric transport or
ramification assertions.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--3;
the finite quotient comparisons are lem-coef-finite-direct-image,
lem-coef-finite-closed-shriek, lem-coef-finite-dualizing, thm-coef-finite-hom and
cor-coef-finite-verdier (blueprint: lem-sf-normalized-stage-coefficient-calculus).

Proof: factor each stage arrow through the same upper field at the source exponent.
The first factor is finite free: reduce an integral basis modulo the power of the
base uniformizer. Apply finiteFreeDerivedScalarCalculus to obtain constructibility
and finite Tor preservation, and finiteFreeImageComparisons for direct and compact
images. Transpose the inverse image comparison and the extended counit to obtain
the closed and compact-support right-adjoint comparisons. The finite-free Hom theorem
identifies the extended-evaluation transpose with an isomorphism. Compose with the
unit-valued exceptional comparison to obtain the Verdier arrow. For the second
factor, identify the base-parameter ideal with a positive power of the upper
uniformizer. Present the finite-dimensional upper field by a small algebraically
isomorphic field and transport its integer quotients by the induced ring
isomorphisms. The finite quotient theorems then apply at those two exponents,
with their published ULift coefficient identifications. The
closed etale comparison is recovered from its pro-etale realization by the finite
etale descent theorem. Thus all five maps are invertible on the specified domain.
The tensorator and symmetry are the descended balanced map and Koszul symmetry.
Transpose the two paths to prove evaluation and double-dual compatibility,
object naturality, units and composition. For two arbitrary stage arrows, refine
their factorizations to a grid of finite free inclusions and quotients. Finite-free
transitivity handles the horizontal paths, quotient cocycles handle the vertical
paths, and the mixed ramified square handles interchange. These give the five
composition fields of Calculus with exactly its recorded balanced associators.
Finally use the finite-duality site comparison to transport the etale equations;
the site unit and counit identify the transported closed and dualizing arrows
with proClosedMap and proOmegaMap. Full faithfulness on bounded etale-origin
objects reflects the closed equations. No ambient pro-etale exceptional adjunction
is used, and no arbitrary representing object is chosen. -/
theorem normalized_stage_coefficient_calculus
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T X Z : Scheme.{u})
    [T.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))] [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    (f : T ⟶ X) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of D.k))]
    (c : Compactification (X ↘ Spec (.of D.k))) :
    ∃ (et : Sites.Calculus false l E f i c) (pro : Sites.Calculus true l E f i c),
      Sites.Normalized l E f i c et pro ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (M : Sites.D true s.ring X),
        Sites.Ctf true s.ring X M → pro.closedMap a M = Sites.proClosedMap a.ringMap i M) ∧
      (∀ {s t : Stage l E} (a : Arrow s t),
        pro.omegaMap a = Sites.proOmegaMap a.ringMap c) := by
  sorry

end WeilConjectures.FiniteFreeCoefficients
