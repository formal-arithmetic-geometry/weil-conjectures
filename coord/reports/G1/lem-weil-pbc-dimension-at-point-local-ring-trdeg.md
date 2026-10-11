## Worker report

The module `Sheaf.RingTheory.DimensionAtPointLocalRingTrdeg` states
`AlgebraicGeometry.topologicalKrullDimAt_eq_ringKrullDim_add_trdeg`, with a single `sorry`
and no definitions or proved theorems. The source was read in
`/home/ubuntu/c1-stacks-review/algebra.tex`, label
`lemma-dimension-at-a-point-finite-type-field`, lines 28222–28267 (Stacks Tag 00P1).
The repository's literature checkout is absent; this local Stacks copy contains the exact
label and proof recorded by the node. The four proof steps in the node are reproduced in
natural language in the declaration docstring, naming their dependency nodes.

Hypotheses and clauses:

- A field k: `{k : Type u} [Field k]`.
- A commutative finite type k-algebra S: `{S : Type v} [CommRing S] [Algebra k S]
  [Algebra.FiniteType k S]`. No domain, reducedness, equidimensionality, or algebraic
  closedness hypothesis is imposed.
- A prime ideal p: `(p : Ideal S) [p.IsPrime]`.
- The localization and residue field are `Localization.AtPrime p` and `p.ResidueField`.
  The latter inherits its canonical k-algebra structure through S and its localization;
  no independently chosen field embedding is introduced.
- Dimension at the corresponding point of Spec S is
  `topologicalKrullDimAt (⟨p, inferInstance⟩ : Spec (CommRingCat.of S))`.
- Local-ring Krull dimension is `ringKrullDim (Localization.AtPrime p)`.
- Residue-field transcendence degree is `Algebra.trdeg k p.ResidueField`.
- Finiteness and the formula are expressed together by `∃ d r : ℕ`, with local-ring
  dimension equal to `(d : WithBot ℕ∞)`, transcendence degree equal to
  `(r : Cardinal.{v})`, and local topological dimension equal to
  `((d + r : ℕ) : WithBot ℕ∞)`. Thus all three are finite and the first is exactly the
  sum of the last two. Conversely, the node's finiteness and formula supply these
  witnesses. This avoids a lossy cardinal-to-natural conversion at infinite cardinals.

Dependency declarations used (full signatures and docstrings read):

- `def-weil-pbc-finite-type-algebra`: `Algebra.FiniteType`,
  `Mathlib.RingTheory.FiniteType`, lines 36–40: finite generation of the top subalgebra.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, lines 45–58; `Ideal.ResidueField`,
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, lines 25–35. The fibre-ring clause
  of that dependency is not needed by this item.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, lines 88–103,
  applied to the inherited field structure on the residue field.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`,
  `Mathlib.AlgebraicGeometry.Scheme`, lines 469–480.
- `def-kun-topological-dimension-at-point`: `topologicalKrullDimAt`,
  `WeilConjectures.Mathlib.Topology.KrullDimension`, lines 327–334: infimum over open
  neighbourhoods, exactly the node's local dimension.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim`,
  `Mathlib.RingTheory.KrullDimension.Basic`, lines 26–31.
- `def-kun-transcendence-degree`: `Algebra.trdeg`,
  `Mathlib.RingTheory.AlgebraicIndependent.Basic`, lines 38–46: cardinal supremum
  over algebraically independent subsets.

Edge cases checked mathematically before writing:

- S = k: d = r = 0, all dimensions vanish.
- S = k[t], p = (0): d = 0, r = 1, local topological dimension = 1.
- S = k[t], p maximal: d = 1, r = 0, including maximal ideals with nontrivial finite
  residue extensions over a non-algebraically closed field.
- Reducible S, e.g. k[x,y]/(xy): the statement allows arbitrary components and uses
  the maximum over components through p as in the source, rather than imposing a domain.
- The zero ring admits no prime ideal, so the given prime hypothesis already handles the
  empty spectrum; no extraneous `Nontrivial S` assumption is introduced.
- Dimension zero, nilpotents, arbitrary characteristic, and independent universes u and v
  are allowed. No finite dimension is assumed in the hypotheses.

Searches actually run through `/home/ubuntu/weil-launcher/msearch.py`:

- LeanFinder: "finite type algebra over field dimension at point equals local ring dimension
  plus residue field transcendence degree". Eight hits, on cotangent-space finrank,
  standard-smooth relative dimension, localization presentations, and inertia degree;
  none states the formula.
- Loogle: `ringKrullDim, Algebra.trdeg`. Zero hits.
- LeanSearch: "dimension at a point finite type algebra field transcendence degree residue
  field". Service unavailable (Internal Server Error); this is not a no-match result.
- Mathlib grep: `topologicalKrullDimAt|ringKrullDim.*trdeg|trdeg.*ringKrullDim`.
  Zero hits.

Additional local `rg` searches covered `trdeg`, `topologicalKrullDimAt`, the item id, and
`ringKrullDim.*trdeg|trdeg.*ringKrullDim` in the source project's `WeilConjectures/`,
Mathlib, `lean/Sheaf`, and `dag/lean_names_upstream.json`. The source has
`Algebra.trdeg_eq_of_ringKrullDim_eq` in
`WeilConjectures.Mathlib.RingTheory.NoetherNormalization`, which concerns the total
Krull dimension of a finite type domain, not dimension at a prime and its residue field.
The project's `Sheaf.RingTheory.ClosedPointDimensionLocalRing` only treats maximal ideals.
Neither is an exact match. The chosen full declaration name has no existing declaration
in either source tree.

Server validation: `scompile.py G1 lem-weil-pbc-dimension-at-point-local-ring-trdeg
<module>` compiled in 1.5 s, exit 0, without warnings. No statement correction or disputed
statement was needed; every original dependency record was usable.

## Second reading by G1

I read the sandbox node and module independently against Stacks Algebra Tag 00P1,
`lemma-dimension-at-a-point-finite-type-field`, in
`/home/ubuntu/c1-stacks-review/algebra.tex:28222–28267`. The source introduces a field,
a finite type algebra, its spectrum and a prime point; there is no standing domain,
perfectness, algebraic-closedness or characteristic assumption. Its proof also gives
finiteness of the three quantities, as the node expressly requests.

The node's objects, hypotheses and conclusion, matched in order:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary field k | `{k : Type u} [Field k]` | Exact. |
| Commutative k-algebra S | `{S : Type v} [CommRing S] [Algebra k S]` | Exact; no domain assumption. |
| Finite type over k | `[Algebra.FiniteType k S]` | Exact finite generation; no separate Noetherian hypothesis. |
| Prime ideal p of S | `(p : Ideal S) [p.IsPrime]` | Exact, including nonmaximal primes. |
| Localization S_p | `Localization.AtPrime p` | Canonical localization at the prime complement. |
| Residue field κ(p), as a k-extension | `p.ResidueField` with inherited algebra instances | Canonical quotient of S_p, with the composite k-algebra map, not a freely chosen extension. |
| X = Spec S and its corresponding point | `(⟨p, inferInstance⟩ : Spec (CommRingCat.of S))` | Exact prime-spectrum point with its Zariski topology. |
| Dimension of X at that point | `topologicalKrullDimAt` applied to that point | Infimum over open neighbourhoods, equal to the minimum in the dependency node. |
| Local-ring dimension | `ringKrullDim (Localization.AtPrime p)` | Exact Krull dimension, not dimension of all of S. |
| Transcendence degree of κ(p)/k | `Algebra.trdeg k p.ResidueField` | Exact cardinal-valued transcendence degree. |
| All three quantities finite | `∃ d r : ℕ` and the three displayed equalities | Local-ring dimension is d, transcendence degree is r, and point dimension is d+r, hence all finite. Conversely finite dimensions and the node's formula yield these witnesses. |
| Point dimension equals local-ring dimension plus transcendence degree | Third conjunct equals `((d + r : ℕ) : WithBot ℕ∞)` with the preceding two equalities | Exact formula. Natural witnesses avoid collapsing infinite cardinal values to zero. |

All witnesses occur after k, S and p; there is no uniform dimension bound or extra
hypothesis. Both universes u and v are independently bound. The cardinal universe v
is that of S and its residue field, not a restriction on the base-field universe.

I opened every statement-dependency node and the declarations it records:
`Algebra.FiniteType` (FiniteType.lean:39), `Localization.AtPrime`
(Localization/AtPrime/Basic.lean:57), `Ideal.ResidueField`
(LocalRing/ResidueField/Ideal.lean:33), `Algebra` (Algebra/Algebra/Defs.lean:95),
`AlgebraicGeometry.Spec` (Scheme.lean:470), `topologicalKrullDimAt`
(WeilConjectures/Mathlib/Topology/KrullDimension.lean:333), `ringKrullDim`
(KrullDimension/Basic.lean:30), and `Algebra.trdeg`
(AlgebraicIndependent/Basic.lean:45). The recorded signatures and definitions
provide exactly the required notions. The fibre clause in the localization node
is not used here. No missing notion, new definition node or dependency module is needed.

Edge cases: for S=k all witnesses are zero; for k[t] at (0), d=0 and r=1;
at a maximal ideal, d=1 and r=0, also for a nontrivial finite residue extension.
Nilpotents and reducible algebras are allowed. For S=k[x] × k[x,y], a generic point
on the first component has d=0, r=1 and local dimension 1 although the whole
spectrum has dimension 2: the chosen local-topological definition passes this test.
The zero ring has no prime, so the empty spectrum is covered vacuously; every
neighbourhood of the specified point is nonempty, excluding negative infinity
without an added hypothesis. Zero-dimensional algebras and every characteristic
are covered. There is no index-set parameter; the source's set of minimal primes
below p is necessarily nonempty, not an assumed nonempty set in the signature.

Independent searches on 2026-10-11, using different wording from the first reader:

- LeanFinder through msearch.py: "height of a prime and transcendence degree of its
  residue field sum to dimension of open neighbourhoods". Eight hits, including
  `IsLocalization.AtPrime.ringKrullDim_eq_height` and height inequalities; none
  includes the residue-field transcendence-degree/local-topological formula.
- Loogle through msearch.py: `"trdeg", "ResidueField"`. Zero hits.
- LeanSearch through msearch.py: "For a finitely generated commutative algebra over
  a field, the dimension near a prime is its height plus the transcendence degree
  of the residue field". Internal Server Error; recorded as unavailable, not
  evidence of absence.
- Independent rg over Mathlib, WeilConjectures and lean/Sheaf for
  `residuefield.*(trdeg|dimension)|trdeg.*residuefield|dimension.*at.*point|height.*trdeg|trdeg.*height`
  (case insensitive), plus `topologicalKrullDimAt|ringKrullDim.*trdeg|trdeg.*ringKrullDim`.
  No exact existing statement. I opened `Algebra.trdeg_eq_of_ringKrullDim_eq`:
  it assumes a domain and compares total dimension with the transcendence degree
  of that algebra, rather than the quantities at an arbitrary prime. I also
  opened `topologicalKrullDimAt_eq_ringKrullDim_localizationAtMaximal`:
  it requires a maximal ideal. Smooth relative-dimension results require smoothness.
  None can replace this statement. The theorem's full name is absent from the
  searched source trees.

H5–H9: no definitions or auxiliary theorems are introduced; the only proof is
`by sorry`. Both docstrings give Tag 00P1 and the correct blueprint id. The
statement docstring reproduces all four proof steps and their dependency nodes:
V(p) and its fraction field; minimal primes and localization; chains below p;
component dimensions and concatenation of chains. All imports serve notions in
the statement, the namespace has no Sheaf prefix, and every line is at most 100
characters. No variables or universes are unbound. There is no statement correction,
so no corrected-source or citer-verdict review is applicable.

Mismatches found: none. Changes: appended this independent second-reading report;
the correct Lean module and node record were preserved. I checked by exact string
comparison that `lean.statement` is verbatim the file's signature before `:=`.
Server scompile.py compiled the complete one-module delivery in 1.6 seconds,
exit 0, with no warnings.
