/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.ContinuousLocallyFreePullback
import Sheaf.Paper.ContinuousCoefficientRealizations
import Sheaf.Paper.ContinuousEtaleLocalLattices
import Sheaf.AlgebraicGeometry.EtaleStratifiedFinite
import Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import Sheaf.Paper.ContinuousCoefficientModuleEncoding
import Sheaf.Paper.ContinuousModuleEncodingSliceFreeness
import Sheaf.Paper.ContinuousModuleEncodingRestriction
import Sheaf.Paper.ContinuousModuleEncodingLattices
import Sheaf.Paper.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Lisse integral lattices on finite strata

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.13,
first paragraph, and Definitions 6.8.1, 6.8.3
(blueprint: lem-sfb-topological-stratified-lisse-lattices).

A submodule is expressed by a monomorphism into the restriction of scalars of the
rational module. The isomorphism required below is the scalar extension of this
specific inclusion, namely `Mod.extendHom`, rather than an unspecified isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- A lisse rational module admits lisse integral submodules on finitely many
constructible locally closed strata. Ranks may vary and may be zero.

Source: Bhatt--Scholze, Lemma 6.8.13, first paragraph, pp. 60--61;
coefficient and lisse conventions in Definitions 6.8.1, 6.8.3 and Lemma 6.8.2
(blueprint: lem-sfb-topological-stratified-lisse-lattices).

Proof plan:
1. Topological Noetherianity makes X qcqs. The totally disconnected coefficient
rings E and O_E identify their pulled condensed sheaves with the continuous-function
sheaves by lem-weil-pbc-continuous-coefficient-realizations, compatibly with inclusion.
Use def-weil-pbc-internal-abelian-sheaf-module-equivalence to compare module encodings.
2. Apply lem-weil-pbc-continuous-etale-local-lattice to obtain a qcqs etale surjection
U -> X and a lisse integral model of the pulled rational module.
3. Apply lem-weil-pbc-etale-stratified-finite to obtain finitely many constructible
locally closed strata on which this cover is finite etale. Its base changes are
surjective: a prime of the nonzero tensor product of the residue fields gives a
point above each point of the stratum. Each stratum is topologically Noetherian.
4. Pull the integral model and its rationalization to each base-changed cover.
Use lem-weil-pbc-continuous-locally-free-pullback, sk-prop-sfb-cartesian-coefficients,
def-sfb-module-upper-star, def-sfb-finite-upper-star-monoidal and
def-sfb-module-upper-star-comp. On finite free charts, the pulled bases and matrices
show that scalar extension and the rationalization isomorphism pull back compatibly.
5. On each stratum apply lem-weil-pbc-lisse-lattice-finite-etale-descent, which needs
no descent datum on the chosen model. The continuous module encoding and its
restriction, slice-freeness and lattice-compatibility lemmas identify the internal
and sectionwise versions and transfer the resulting model back to internal modules.
6. The map n -> theta(1 tensor n) is injective: on a free chart it is coordinatewise
inclusion O_E^r -> E^r, followed by theta; sheaf uniqueness descends injectivity.
Its image is therefore isomorphic to the lisse integral model and its inclusion
induces theta on scalar extension. For the empty scheme take the empty partition;
the same coordinate argument includes rank zero. No global lisse lattice is claimed. -/
theorem exists_topological_stratified_lisse_lattices
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X))
    (hL : CondensedRing.LocallyFree
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X) L) :
    ∃ S : Scheme.FiniteLocallyClosedStratification X,
      (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
      ∀ a : Fin S.n,
        ∃ L₀ : Mod (Sheaf (Scheme.ProEt.topology (S.domain a)) Ab.{u + 1})
            (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (S.domain a)),
          CondensedRing.LocallyFree
            (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (S.domain a)) L₀ ∧
          ∃ ι : L₀ ⟶ (Mod.comap (padicIntegersToPadicSubfield (S.domain a) ℓ E)).obj
              ((CondensedRing.upperStar (Profinite.continuousMapRingObj E.1)
                (S.immersion a)).obj L),
            Mono ι ∧ IsIso (Mod.extendHom (padicIntegersToPadicSubfield (S.domain a) ℓ E) ι) := by
  sorry

end AlgebraicGeometry.ProEtale
