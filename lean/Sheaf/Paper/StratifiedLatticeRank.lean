/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.CoefficientHeartCommonStratification
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Topology.Defs.Filter

import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import Sheaf.AlgebraicGeometry.LisseLatticeCoefficientsSized
import Mathlib.LinearAlgebra.Dimension.Finrank
import Sheaf.AlgebraicGeometry.EtaleOpenFpqcDescent
import Mathlib.CategoryTheory.Sites.Precoverage
import Sheaf.AlgebraicGeometry.WeaklyEtaleStability
import Sheaf.Paper.CartesianCoefficients

/-!
# The clopen rank decomposition of a lisse coefficient module

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-stratified-lattice/
sk-lem-stratified-lattice-rank.md (blueprint: det-lem-stratified-lattice-rank).

The coefficients are the pulled-back condensed continuous-function ring of a finite
extension of the p-adic field. Every occurrence of the continuous coefficient ring explicitly
uses the canonical spectral norm topology; no topology on E is supplied as a hypothesis.
Lissity is the existing pro-etale local finite-freeness predicate. The open subschemes in
this statement have their actual restricted structure sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The rank of a lisse `E_X`-module is independent of every trivialization and every
preimage, and its rank loci are clopen. The canonical map from their scheme coproduct is an
isomorphism. On the rank-`r` open subscheme the module is pro-etale locally free of rank `r`;
only finitely many loci are nonempty when `X` is quasi-compact.

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-stratified-lattice/
sk-lem-stratified-lattice-rank.md (blueprint: det-lem-stratified-lattice-rank).

Proof plan, following the seven steps of the reviewed DAG:
1. Unpack `IsLisseCoefficientModule` into a pro-etale cover with finite free local models.
   The cover is fpqc, with no finiteness assumption on its index set (`sk-def-pe-site`).
2. Pull two trivializations to their overlap using `sk-prop-sfb-cartesian-coefficients`.
   By `lem-weil-pbc-condensed-field-continuous-realization` and
   `def-weil-pbc-lisse-lattice-coefficients`, their inverse transition matrices have entries
   in continuous E-valued functions. Evaluation at any point gives inverse E-linear maps.
   Basis comparison (`def-weil-vector-space-dimension`) makes the two ranks equal.
   Thus overlaps with unequal ranks are empty, including rank zero.
3. For each r the whole/empty local rank-r subsets and their complements are compatible
   on overlaps. Descend both via `lem-weil-pbc-etale-open-fpqc-descent`, with the identity
   etale map. Joint surjectivity identifies the descended opens as complements.
4. A point lifts to the cover, so it lies in exactly one rank locus. This also covers the
   empty scheme, on which all the rank loci are empty.
5. Adjoin any other trivializing object to the cover. Descent uniqueness identifies its
   rank loci with the original ones. This proves both the existential characterization
   and the universal assertion for all trivializations and all preimages.
6. Restrict the cover to each rank open using `lem-galois-fpqc-covering-base-change` and
   `sk-lem-pe-weakly-etale-stability`. Coefficient pullback identifies the local modules with
   rank-r free modules. The clopen partition gives an isomorphism from the scheme coproduct
   (`lem-weil-pbc-scheme-coproduct-family`), checked on its open components.
7. Quasi-compactness (`def-weil-pbc-quasi-compact-scheme`) gives a finite subcover of the
   disjoint rank opens. Every remaining rank open is empty.
-/
theorem exists_clopen_rank_decomposition_of_isLisse
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (@Profinite.continuousCoefficientRingObj E
        (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
        (@NonUnitalSeminormedRing.toIsTopologicalRing E
          (@SeminormedRing.toNonUnitalSeminormedRing E
            (spectralNorm.seminormedRing ℚ_[l] E)))) X))
    (hL : IsLisseCoefficientModule (@Profinite.continuousCoefficientRingObj E
      (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
      (@NonUnitalSeminormedRing.toIsTopologicalRing E
        (@SeminormedRing.toNonUnitalSeminormedRing E
          (spectralNorm.seminormedRing ℚ_[l] E)))) L) :
    ∃ R : ℕ → X.Opens,
      (∀ r : ℕ, IsClosed (R r : Set X)) ∧
      (∀ (x : X) (r : ℕ), x ∈ R r ↔
        ∃ (U : X.ProEt) (v : U.left), U.hom v = x ∧
          Nonempty
            ((CondensedRing.upperStar (@Profinite.continuousCoefficientRingObj E
              (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
              (@NonUnitalSeminormedRing.toIsTopologicalRing E
                (@SeminormedRing.toNonUnitalSeminormedRing E
                  (spectralNorm.seminormedRing ℚ_[l] E)))) U.hom).obj L ≅
              Mod.finiteFree
                (condensedRingObj (@Profinite.continuousCoefficientRingObj E
                  (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
                  (@NonUnitalSeminormedRing.toIsTopologicalRing E
                    (@SeminormedRing.toNonUnitalSeminormedRing E
                      (spectralNorm.seminormedRing ℚ_[l] E)))) U.left) r)) ∧
      (∀ (U : X.ProEt) (n : ℕ),
        Nonempty
          ((CondensedRing.upperStar (@Profinite.continuousCoefficientRingObj E
            (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
            (@NonUnitalSeminormedRing.toIsTopologicalRing E
              (@SeminormedRing.toNonUnitalSeminormedRing E
                (spectralNorm.seminormedRing ℚ_[l] E)))) U.hom).obj L ≅
            Mod.finiteFree
              (condensedRingObj (@Profinite.continuousCoefficientRingObj E
                (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
                (@NonUnitalSeminormedRing.toIsTopologicalRing E
                  (@SeminormedRing.toNonUnitalSeminormedRing E
                    (spectralNorm.seminormedRing ℚ_[l] E)))) U.left) n) →
        ∀ (v : U.left) (r : ℕ), U.hom v ∈ R r ↔ n = r) ∧
      (CompactSpace X → {r : ℕ | (R r : Set X).Nonempty}.Finite) ∧
      IsIso (Sigma.desc (fun r : ℕ ↦ (R r).ι)) ∧
      ∀ r : ℕ, ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (R r).toScheme,
        ∀ i : C.I₀,
          Nonempty
            ((CondensedRing.upperStar (@Profinite.continuousCoefficientRingObj E
              (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
              (@NonUnitalSeminormedRing.toIsTopologicalRing E
                (@SeminormedRing.toNonUnitalSeminormedRing E
                  (spectralNorm.seminormedRing ℚ_[l] E))))
                (C.f i ≫ (R r).ι)).obj L ≅
              Mod.finiteFree
                (condensedRingObj (@Profinite.continuousCoefficientRingObj E
                  (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
                  (@NonUnitalSeminormedRing.toIsTopologicalRing E
                    (@SeminormedRing.toNonUnitalSeminormedRing E
                      (spectralNorm.seminormedRing ℚ_[l] E)))) (C.X i)) r) := by
  sorry

end AlgebraicGeometry.ProEtale
