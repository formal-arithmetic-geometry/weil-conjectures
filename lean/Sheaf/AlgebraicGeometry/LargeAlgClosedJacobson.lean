/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
public import WeilConjectures.ZetaSeries
import Mathlib.SetTheory.Cardinal.HasCardinalLT
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Sheaf.FieldTheory.AlgClosedExtensionCardinalLowerBound
import WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso
import Sheaf.RingTheory.CardinalGeneratorNullstellensatz

/-!
# Making an arbitrary scheme Jacobson over an algebraically closed extension

Source: Stacks Project, Varieties, Tag 0479 (`lemma-make-Jacobson`), and
More on Groupoids in Spaces, Tag 0B8E (`lemma-group-space-scheme-over-kbar`)
(blueprint: lem-sfb-scheme-large-algclosed-jacobson).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every scheme over a field becomes Jacobson with rational closed points after a
sufficiently large algebraically closed field extension. The extension is not required
to be algebraic over the original field. No finiteness, reducedness or separation
condition is imposed on the scheme.

Source: Stacks Project, Varieties, Tag 0479 (`lemma-make-Jacobson`), with the rationality
consequence used in More on Groupoids in Spaces, Tag 0B8E
(`lemma-group-space-scheme-over-kbar`)
(blueprint: lem-sfb-scheme-large-algclosed-jacobson).

Proof plan:
1. Choose an affine open cover with coordinate rings `Aᵢ` (`def-pc-scheme`). Bound the
   cardinality of their disjoint union by one infinite cardinal `λ`, strictly larger
   than each `#Aᵢ`, using `lem-coef-small-family-regular-bound`. Choose an algebraically
   closed extension `K/k` with `λ ≤ #K` using
   `lem-sfb-algclosed-extension-cardinal-lower-bound`. This also covers an empty scheme.
2. The inverse image of each affine chart is the spectrum of `K ⊗[k] Aᵢ`, compatibly
   with its structure map to `Spec K`, by `lem-weil-pbc-affine-chart-base-change-iso`.
   The elements `1 ⊗ a`, indexed by `a : Aᵢ`, generate this algebra: pure tensors
   are scalar multiples of these elements and every tensor is a finite sum.
   By `lem-sfb-cardinal-generator-nullstellensatz`, each chart ring is Jacobson
   and every maximal quotient is algebraic over `K`.
3. These charts cover the base change. The spectrum criterion and the open-cover
   criterion of `lem-sfb-jacobson-spectrum-open-cover` give the Jacobson property,
   namely density of the ambient closed points in every closed subset.
4. A closed point remains closed in a chart containing it and hence corresponds to
   a maximal ideal (`def-weil-affine-spectrum`). Open restriction preserves its stalk.
   Its residue field (`def-weil-residue-field`) is the maximal quotient of the chart
   ring: localization of that quotient does nothing since it is a field. These
   identifications respect the structural map from `K`, so this field is algebraic
   over `K` by step 2.
5. Every algebraic element over the algebraically closed field `K` lies in `K`:
   split a nonzero annihilating polynomial into linear factors, and use that a
   product vanishing in a field has a vanishing factor (`def-weil-algebraic-closure`).
   The structural map is therefore surjective and, being a field homomorphism,
   injective (`def-pc-field-extension`). Its bijectivity is precisely clause (ii).
-/
theorem exists_algClosed_extension_jacobson_rational
    (k : Type u) [Field k] (U : Scheme.{u}) (f : U ⟶ Spec (.of k)) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      IsAlgClosed K ∧
        JacobsonSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        ∀ x : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
          x ∈ closedPoints ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) →
          Function.Bijective
            ((pullback.snd f
              (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueFieldAlgebraMap x) := by
  sorry

end AlgebraicGeometry.Scheme
