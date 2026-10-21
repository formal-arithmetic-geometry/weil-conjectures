/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Paper.ContinuousLocallyFreePullback
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.ContinuousCoefficientRealizations
import Sheaf.Paper.ContinuousEtaleLocalLattices
import Sheaf.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import Sheaf.Paper.LatticeSheafLocallyConstant
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.LinearAlgebra.FreeModule.PID
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.PadicIntegersInvertEll

/-!
# Integral lattices after finite stratification

Source: Weil conjectures blueprint, main-20261015, six-functors basics,
`sk-lem-stratified-lattice`, statement and proof; Bhatt--Scholze, Section 6.8,
Proposition 6.8.4(6) and Lemma 6.8.13 (blueprint: sk-lem-stratified-lattice).

The coefficients are the pulled condensed topological rings, and modules are internal
module objects. The lattice inclusion is monic, and its scalar-extension adjoint is an
isomorphism. Thus the rationalization isomorphism is induced by that very inclusion.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A lisse rational module on a standing scheme has a lisse integral lattice on each
stratum of some finite locally closed stratification. Finite ranks may vary, including
rank zero. The coefficient topology is the canonical spectral norm topology; the integral
ring has the subspace topology. Scalar extension along its inclusion is inversion of `l`.
No uniformizer enters this conclusion; any chosen uniformizer in the coefficient datum
is allowed. The nodal-curve example in the source explains why stratification is necessary.

Source: blueprint main-20261015, `sk-lem-stratified-lattice`, and its proof paragraphs
"Sheaf of lattices", stratification, and "Pushing down by the trace";
Bhatt--Scholze, Section 6.8 (blueprint: sk-lem-stratified-lattice).

Proof plan:
1. Finite type over a field makes X Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. A finite affine cover and
   lem-sc-affine-noetherian-underlying-space show its underlying space is Noetherian;
   every open is quasi-compact, so X is qcqs. The natural continuous coefficient
   comparisons of lem-weil-pbc-continuous-coefficient-realizations are ring isomorphisms
   and commute with integral inclusion, since E and its valuation ring are totally
   disconnected. det-prop-sfb-qlbar-colimit-x-invert-ell identifies this inclusion with
   localization at l. These identifications transport the internal module actions.
2. Apply lem-weil-pbc-continuous-etale-local-lattice to obtain a qcqs etale surjection
   V -> X and a lisse integral lattice on V. Its map to its rationalization is injective
   on local bases, hence gives an actual integral submodule of the pulled-back L.
3. Apply lem-weil-pbc-etale-stratified-finite to V -> X. Its base changes over the
   resulting finitely many locally closed strata are finite etale and surjective.
   Pull the integral module and its rationalization to these strata using
   lem-weil-pbc-continuous-locally-free-pullback. In local bases the rationalization
   and its inverse pull back to inverse matrices, and integral inclusion stays injective.
4. Split a finite etale cover etale locally by
   lem-weil-pbc-finite-etale-etale-local-split. Summing over its sheets defines a trace.
   Sheet permutations preserve the sum, so the local traces glue. Define L0 as the
   sheaf image of the integral module under this trace. Locally it is the sum of the
   finitely many sheet lattices, and is closed under integral scalar multiplication.
5. Trivialize L pro-etale locally. By lem-weil-pbc-lattice-sheaf-locally-constant each
   embedded sheet lattice is locally a fixed lattice in E^r. Refine the finitely many
   trivializing covers successively to make all these lattices constant together.
6. Their finite sum is finitely generated and torsion-free over the DVR O_E by
   lem-weil-l-adic-extension-integers-dvr, hence finite free by
   lem-sc-dvr-fg-torsionfree-free. The nonempty sheet set ensures it spans E^r.
   A basis matrix and its inverse identify the sum homeomorphically with O_E^r.
   The surjection from the direct sum of the sheet lattices has a continuous linear
   section, obtained by lifting this finite basis. Thus its image on continuous-function
   sheaves is exactly the continuous-function module of the sum lattice.
7. Consequently L0 is lisse and its inclusion rationalizes to an isomorphism locally.
   The rationalizations glue, as do their local inverses. Discard empty strata; for
   empty X take the empty stratification, and for rank zero take the zero lattice.
-/
theorem exists_stratified_lisse_integral_lattice
    (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (_hpl : p ≠ l)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
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
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
