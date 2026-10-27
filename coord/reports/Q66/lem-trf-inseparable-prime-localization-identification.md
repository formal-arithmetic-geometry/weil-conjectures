## Worker report

The module `Sheaf.RingTheory.InseparablePrimeLocalizationIdentification` states
`Algebra.TensorProduct.inseparable_primeLocalization_identification`. Its only
postponed proof is `sorry`. The accompanying
`Algebra.TensorProduct.primeLocalizationBaseChangeMap` is the actual canonical
map obtained by applying Mathlib's `Algebra.TensorProduct.map` to the localization
map and the identity of E; it contains no postponed data or proof. It is a named
specialization of that existing construction, belonging to the item's canonical
map, rather than a new independent notion.

The node's statement is unchanged. The source was read in
`literature/stacks-project/varieties.tex`, lemma-geometrically-reduced-at-point
(Tag 035W), first proof paragraph, and `algebra.tex`, lemma-p-ring-map (Tag 0BRA).
035W explicitly identifies the unique local ring with the tensor product and
assumes no Noetherian, finite-type or closed-point condition. Algebra Tags 00DK
and 00CP supply the localization interpretation and compatibility clauses.

Hypothesis and clause correspondence (write A = R_p, S = R tensor E, C = A tensor E
in this report only; the Lean signature contains the full expressions):

- Field k and extension E/k: `(k : Type u) (E : Type v) [Field k] [Field E]
  [Algebra k E]`. Finiteness is `[Module.Finite k E]`, and pure inseparability is
  `[IsPurelyInseparable k E]`, exactly the dependency's recorded encoding.
- Commutative k-algebra R and prime p: `(R : Type w) [CommRing R] [Algebra k R]
  (p : Ideal R) [p.IsPrime]`. No other property of R or p is assumed.
- A is `Localization.AtPrime p`; m is `IsLocalRing.maximalIdeal A`, which equals
  `Ideal.map (algebraMap R A) p` by `Localization.AtPrime.map_eq_maximalIdeal`.
  S and C are Mathlib's `TensorProduct k R E` and `TensorProduct k A E` with their
  usual tensor-product commutative-ring multiplications, imported from
  `Mathlib.RingTheory.TensorProduct.Maps` and its public dependencies.
- The contraction bijection respecting inclusion in both directions is
  `∃ e : PrimeSpectrum C ≃o PrimeSpectrum A, ∀ q, e q =
  PrimeSpectrum.comap (algebraMap A C) q`. An order isomorphism has a bijective
  underlying map and preserves and reflects the prime-ideal inclusion order.
- Locality is `IsLocalRing C`. The existential ideal n is maximal, every maximal
  ideal n' equals n, its contraction to A is m, and every prime q contracting
  to m equals n. Thus all the node's descriptions of n are present explicitly.
- Every prime P of S over p is quantified as `(P : Ideal S) [P.IsPrime]` with
  `P.comap (algebraMap R S) = p` as its premise. The canonical map j is the
  constructed `primeLocalizationBaseChangeMap k E R p` and sends pure tensors
  to the specified `(r/1) tensor e` by the definition of tensor-product map.
- The inverse-image assertion is `n.comap j = P`. The identification is an
  existential `theta : Localization.AtPrime P ≃+* C`; this is a ring equivalence,
  not merely a module equivalence or a map with unspecified inverse.
- Compatibility with S is `theta.toRingHom.comp (algebraMap S S_P) = j`.
  The displayed fraction formula is asserted for every numerator a and every
  `b : P.primeCompl`, using `IsLocalization.mk' S_P a b` and
  `j a * Ring.inverse (j b)`. For these denominators j b is a unit: theta maps
  the unit b/1 to j b. Mathlib's `Ring.inverse` therefore is its unique inverse.
- Compatibility with A is an existential ring homomorphism `aMap : A →+* S_P`
  satisfying `aMap.comp (algebraMap R A) = (algebraMap S S_P).comp
  (algebraMap R S)`, together with `theta.toRingHom.comp aMap = algebraMap A C`.
  The first equation determines aMap uniquely by the universal property of R_p,
  and on r/v it sends r/v to `(r tensor 1)/(v tensor 1)`. This introduces the
  canonical map by its defining universal property, without supplying an
  arbitrary map as a hypothesis or requiring a separate algebra instance.
- The final clause quantifies over `(D : Type t) [Ring D]` and every `f : S →+* D`
  with `∀ b : P.primeCompl, IsUnit (f b)`. There is a unique pair of extensions
  `(fC, fP)` agreeing with f on S and satisfying `fC.comp theta.toRingHom = fP`.
  These are the maps induced by the same f. Extension uniqueness follows from
  the localization universal property (for C transported across theta), so
  the use of unique extensions is exactly the node's induced-map compatibility.
  D need not be a k-algebra or commutative; all four universes are explicitly
  declared and independent, and the statement uses no `let` or hidden `show`.

Dependency declarations read and used:

- `def-pc-field-extension`: `Algebra`,
  `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, exposed by the public tensor-ring
  import; its existing tensor multiplication and maps are used, not copied.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, including its local-ring
  instance and maximal-ideal identification. Residue fields and fibre rings
  are not needed for this item's statement.
- `def-weil-pbc-finite-purely-inseparable-extension`: `IsPurelyInseparable`,
  `Mathlib.FieldTheory.PurelyInseparable.Basic`, and `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`.

All recorded proof dependencies with declarations are covered by private imports:
`AlgebraicGeometry.isHomeomorph_baseChange_of_isPurelyInseparable` from
`WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange`;
`AlgebraicGeometry.pullbackSpecIso` from `Mathlib.AlgebraicGeometry.Pullbacks`
(which also exposes Spec for `def-weil-affine-spectrum`);
`Ideal.exists_le_maximal` from `Mathlib.RingTheory.Ideal.Maximal`;
`IsLocalizedModule.rTensor` and `IsLocalizedModule.map_lTensor` from
`Mathlib.RingTheory.Localization.BaseChange`;
`IsLocalRing.notMem_maximalIdeal` from
`Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`.
`IsLocalization.lift`, `IsLocalization.ringHom_ext` and
`Localization.AtPrime.under_maximalIdeal` are already covered by the public
localization import. The docstring gives the node's six-step proof plan and
names every proof-dependency node.

Searches (2026-10-24):

- `msearch.py ... leanfinder "A finite purely inseparable scalar extension of a
  local algebra is local and is the prime localization of the scalar extended
  algebra, compatibly with all ring maps"`: eight hits, including Frobenius
  localization and local-ring maps; no full identification with these clauses.
- `msearch.py ... loogle "IsPurelyInseparable, IsLocalRing"`: zero hits.
- `msearch.py ... grep "PurelyInseparable|tensorRight" RingTheory/Localization`:
  five hits for `IsLocalization.tensorRight`, `tensorRightAlgEquiv`, and its
  pure-tensor formula; no purely inseparable localization-identification theorem.
- `msearch.py ... leansearch "prime localization of a tensor product with a
  finite purely inseparable field extension is the scalar extension of the
  original local ring"`: eight hits. `IsLocalization.tensor` and
  `PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable` provide ingredients,
  not the complete statement. Both declarations and docstrings were read.
- `rg` searches for pure inseparability and tensor/localization in project
  `lean/WeilConjectures` and `lean/Sheaf`, and for the item id upstream, found no
  full statement. The upstream
  `Algebra.TensorProduct.purelyInseparable_baseChange_localRing` in
  `WeilConjectures.RingTheory.PurelyInseparableBaseChangeLocalRing` was read: it
  assumes Noetherianity and does not identify S_P with C, so it cannot attach
  this node. `Sheaf.RingTheory.GeometricReducednessLocalBaseChange` uses the
  mathematical identification in its proof plan but does not state it.
- `rg` on both project trees and `dag/lean_names_upstream.json` for the proposed
  declaration names found no existing declaration. The tensor map itself is
  reused directly as the body of the named canonical map.

Edge cases checked before writing: E = k, including all characteristic-zero
purely inseparable extensions; R a field and p = 0; a nonmaximal prime of a
polynomial ring; arbitrary non-Noetherian R; and R = E with E/k nontrivially
purely inseparable, so E tensor E may be nonreduced. Neither reducedness nor
closedness of p is used. The zero ring has no prime p and is correctly excluded
by `[p.IsPrime]`, not by an extra nontriviality hypothesis. The target D may be
the zero ring, and its denominators are then units; the induced maps remain
unique. Independent field, ring and target universes are all retained.

No statement correction, missing dependency module, new definition node or
unresolved statement dispute was needed. Compilation through the prescribed
`scompile.py` passed in both sandbox and final module-name modes. The first
attempt exposed a missing public import for `PrimeSpectrum.comap`; changing
`Prime.Basic` to `Prime.RingHom` repaired it. No other errors or warnings remain.

## Second reading by Q66

This is a separate self-reading of the node and final file, not an independent
worker review: the dispatcher expressly prohibits starting other agents, and
the maintainer supplies independent review of the delivery. I re-read the full
node statement and the theorem signature after the successful compile.

The field, finite-extension, purely-inseparable, algebra and prime hypotheses
are all present and there are no Noetherian, finite-type, reduced or closed-point
assumptions. `≃o` together with the pointwise contraction equation gives the
specified bijection in both inclusion directions. The named n has both its
unique-maximal and unique-prime-over-m characterizations. P is an arbitrary
prime over p, not just a chosen prime. The inverse-image identity, ring
equivalence, fraction formula, S-compatibility, A-compatibility and arbitrary-D
compatibility each appear in the same scope under the same theta. In particular,
A-compatibility specifies aMap's restriction to R, and the map to D clause
asserts existence and uniqueness of the induced extensions rather than assuming
maps with unspecified behavior. The canonical j is constructed from the actual
localization algebra homomorphism, not chosen from an existence theorem. The
only change found necessary during verification was the public spectrum-map
import noted above; no mismatch requiring a node correction was found.
