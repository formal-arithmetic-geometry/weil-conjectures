/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import Mathlib.Topology.NoetherianSpace
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.SpectralEtaleLocalLattices
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.SpectralFiniteEtaleTraceLattice

/-!
# Integral lattices on a finite stratification of a Noetherian space

Source: latest Weil conjectures blueprint, `sk-lem-stratified-lattice`, statement
and proof, and the scope clarification of Wei Yang, Zulip #1412, item 17.
(blueprint: sk-lem-stratified-lattice)

The hypothesis concerns only the underlying topological space. The coefficients are
pulled-back condensed continuous-function rings, with the spectral topology on the
finite extension and the induced topology on its recorded valuation ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A lisse rational module has integral lattices on finitely many locally closed strata
when the underlying space is Noetherian. Local finite ranks may vary and may be zero.
The scalar-extension isomorphism is the adjoint of the specified monic inclusion.
A uniformizer can be chosen arbitrarily: it does not enter the conclusion.

Source: latest blueprint, `sk-lem-stratified-lattice`, statement and proof;
Wei Yang, Zulip #1412, item 17 (blueprint: sk-lem-stratified-lattice).

Proof. Every subset of a Noetherian space is quasi-compact; in particular X is
quasi-compact and intersections of affine opens are quasi-compact, so X is
quasi-separated. The separated surjective etale lattice atlas carries a universal
lattice. Choose finitely many affine opens whose images cover X to obtain a qcqs
etale surjection U to X, a locally free integral module M on U, and its specified
scalar-extension isomorphism with the pullback of L. Apply the etale stratification
lemma (Stacks 03S0, with separated case 07RZ using 07RY). It gives finitely many
locally closed strata on which the base change W to S is finite etale; it remains
surjective by base change. Pull back M and its isomorphism to W. Local freeness is
preserved, and the coefficient pullback and composition comparisons identify its
scalar extension with the pullback of L restricted to S. Apply finite-etale trace
descent on each S: form the image of the pushed lattice under the sheet-sum trace.
On a split cover and a common local constant-lattice refinement this is the sum of
finitely many finite free lattices. It is therefore locally finite free. Exact
localization identifies the scalar extension of its monic image inclusion with L;
the actual scalar-extension adjoint is invertible. No covering degree is divided
out. Package these inclusions over the finite stratification. For empty X use the
empty stratification; rank zero gives the zero lattice. No characteristic or
invertibility-of-l hypothesis is used. -/
theorem exists_stratified_lisse_integral_lattice_of_noetherianSpace
    (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let A := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers l E)
    let B := Profinite.continuousMapRingObj.{u} E
    let a : A ⟶ B :=
      (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.continuousMapRingSheafMap
            (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)
    ∀ L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X),
      LocallyFree (condensedRingObj B X) L →
      ∃ S : Scheme.FiniteLocallyClosedStratification X, ∀ i : Fin S.n,
        let T := S.domain i
        let aT := (upperStarFromPoint T).map a
        let LT := (CondensedRing.upperStar B (S.immersion i)).obj L
        ∃ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj A T),
          LocallyFree (condensedRingObj A T) M ∧
          ∃ ι : M ⟶ (Mod.comap aT).obj LT,
            Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction aT).homEquiv M LT).symm ι) := by
  dsimp only
  intro L hL
  have hlocal := spectralLisse_etale_lattice l E X L hL
  apply coefficient_stratified_lattice _ _ _ X L hL hlocal
  intro Y V q _ _ _ P hP N hN he
  obtain ⟨e⟩ := he
  exact spectralFiniteEtaleTrace_lattice l E Y P hP q N hN e

end AlgebraicGeometry.ProEtale.CondensedRing
