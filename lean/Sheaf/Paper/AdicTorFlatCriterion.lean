/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.LevelwiseAdicTruncations
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite

/-! # The Padic Tor criterion for flat cohomology

This is the first independent half of the criterion in
`Sheaf.Paper.AdicTorFlatCohomology`. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Higher Tor vanishing at all cutoffs implies flatness of every ambient
cohomology sheaf. This is the Tor half of the blueprint criterion; its proof is the
uniformizer resolution, finite-stratum descent, and Smith-normal-form argument in
steps 1--8 of `lem-weil-pbc-adic-tor-flat-cohomology`.

Source: blueprint integral truncations, hypothesis paragraph
(blueprint: lem-weil-pbc-adic-tor-implies-flat-cohomology).

Proof: use the
integral stratified perfect characterization to choose bounded finite projective
valuation-ring models. Smith normal form, descending through their highest degrees,
decomposes each into free one-term summands and uniformizer-power two-term summands.
A positive power summand has a nonzero residue-field Tor_1 at any sufficiently high
quotient level, by the alternating uniformizer-power resolution of consecutive
quotients. The assumed vanishing excludes these summands. The remaining models have
finite free cohomology. Exact restriction identifies their tensor kernels with those
of ambient cohomology; noetherian stratum detection makes the latter kernels zero.
Right exactness of tensor then proves flatness. Empty charts contribute only zero
modules, so no nonemptiness assumption is introduced. -/
theorem pbc_adic_tor_implies_flat_cohomology
    (T : Scheme.{u}) [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (K : PbcBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E)) :
    (∀ m : ℤ, PbcLevelwiseTorVanishing T (pbcPadicCoefficientDatum l E)
        (pbcReductionAdicTower T (pbcPadicCoefficientDatum l E) K.obj) m) →
      ∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
        (R := pbcAdicCompletion T (pbcPadicCoefficientDatum l E))
        ((DerivedCategory.homologyFunctor _ q).obj K.obj) := by
  sorry

end AlgebraicGeometry.Scheme
