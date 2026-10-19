## Worker report

The module `Sheaf.AlgebraicGeometry.NagataBoundaryDivisor` states
`AlgebraicGeometry.exists_admissibleBlowup_boundaryDivisor`. It binds a scheme
`T : Scheme.{u}` with `[CompactSpace T]` and `[QuasiSeparatedSpace T]`, an open
`U : T.Opens`, and its quasi-compactness hypothesis
`hU : IsCompact (U : Set T)`. The existential `B : IsAdmissible T U` is the
`U`-admissible blow-up and its scheme is `B.I.blowup`, with structure map
`B.I.blowupMap : B.I.blowup ⟶ T`. The existential
`J : B.I.blowup.IdealSheafData` is the effective Cartier boundary ideal.

The first conclusion clause,
`IsSchemeTheoreticallyDominant (B.I.blowupMap ⁻¹ᵁ U).ι`, says that the open
immersion of the inverse-image open is scheme-theoretically dominant, i.e. the
inverse image of `U` is schematically dense. The second clause `J.IsInvertible`
is the recorded effective Cartier ideal predicate. The final clause identifies
its support with the complement of the inverse-image open:
`(J.support : Set B.I.blowup) =
((B.I.blowupMap ⁻¹ᵁ U : B.I.blowup.Opens) : Set B.I.blowup)ᶜ`.
No density, reducedness, or Noetherian hypothesis is added.

The statement dependencies are used as follows. `sk-def-nagata-admissible`
uses `AlgebraicGeometry.IsAdmissible` from
`WeilConjectures.Blowup.AdmissibleBlowup` (the recorded structure contains the
finite-type ideal and disjointness from `U`).
`def-nagata-effective-cartier-ideal` uses
`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible` from
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`.
`def-nagata-scheme-theoretically-dense-open` uses Mathlib's
`AlgebraicGeometry.IsSchemeTheoreticallyDominant` from
`Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`, applied to
the open immersion `(B.I.blowupMap ⁻¹ᵁ U).ι`.

The edge cases checked were `U = ⊤` (the complement can be empty and the
boundary ideal can be the unit ideal), `U = ⊥` (the inverse image is empty and
the boundary is all of the blow-up), disconnected and nonreduced schemes, and
zero or nilpotent ideals. The formulation only requires quasi-compactness of
`U` and qcqs hypotheses on `T`, and does not impose a density or reducedness
condition on the original open.

The searches for an existing exact declaration were:

- `msearch.py Q79 sk-lem-nagata-boundary-divisor leanfinder "For a quasi-compact open in a qcqs scheme there exists an admissible blow-up with schematically dense inverse image and effective Cartier boundary"`: no exact match.
- `msearch.py Q79 sk-lem-nagata-boundary-divisor loogle "AlgebraicGeometry.Scheme, blowup"`: no match for this existence statement.
- `msearch.py Q79 sk-lem-nagata-boundary-divisor grep "blowup|blow.up|cartierBoundary"`: no matching declaration in the searched Mathlib subtree.
- `rg -n "boundary|schematically|IsAdmissible|cartierBoundary"` over `WeilConjectures/` and `lean/Sheaf`: found the stronger preparation theorem
  `AlgebraicGeometry.exists_admissibleBlowup_cartierBoundary` in the upstream
  source, but it does not state the required schematic-density clause, so it is
  not an exact existing match; no project declaration duplicates this statement.
- The dependency declarations were read in full: `IsAdmissible` in
  `WeilConjectures/Blowup/AdmissibleBlowup.lean`, `IsInvertible` in
  `WeilConjectures/Mathlib/AlgebraicGeometry/IdealSheaf/Invertible.lean`, and
  `IsSchemeTheoreticallyDominant` in Mathlib's
  `SchemeTheoreticallyDominant.lean`.

The file compiles cleanly with the required `scompile.py` wrapper; the only
expected diagnostic is the declaration's `sorry` warning. There are no new
nodes, dependency-module repairs, or statement corrections.

## Second reading by Q79

This section was written by the maintainer's independent reviewer (cc review
service, run 2), replacing the delivered placeholder ("No second reading by a
worker"). The node, its source place, the three statement dependencies and
their Lean declarations, and the delivered module were all opened.

Node statement (main-20261015 `_section.md`, order 9, verbatim in the node):
"Let $T$ be quasi-compact and quasi-separated and $U\subseteq T$ a quasi-compact
open. There is a $U$-admissible blow-up $T'\to T$ such that its inverse image of
$U$ is schematically dense in $T'$ and its complement is the support of an
effective Cartier divisor."

Clause by clause:

- $T$ a scheme: `{T : Scheme.{u}}`, universe-polymorphic. Correct.
- $T$ quasi-compact, quasi-separated: `[CompactSpace T] [QuasiSeparatedSpace T]`. Correct, no stronger.
- $U\subseteq T$ quasi-compact open: `(U : T.Opens) (hU : IsCompact (U : Set T))`. Correct.
- "There is a $U$-admissible blow-up $T'\to T$" (sk-def-nagata-admissible):
  `∃ B : IsAdmissible T U`, with $T'$ = `B.I.blowup` and the map
  `B.I.blowupMap`. `AlgebraicGeometry.IsAdmissible`
  (WeilConjectures/Blowup/AdmissibleBlowup.lean, the dependency's recorded
  declaration) stores a quasi-coherent ideal `I`, `I.ofFiniteType` and
  `Disjoint U I.support` (equivalent to $\mathcal I|_U=\mathcal O_U$). Correct.
- "its inverse image of $U$ is schematically dense in $T'$"
  (def-nagata-scheme-theoretically-dense-open, Mathlib match):
  `IsSchemeTheoreticallyDominant (B.I.blowupMap ⁻¹ᵁ U).ι`. The open immersion
  is quasi-compact (U qc, blow-up of a finite-type ideal is proper), so the
  Mathlib predicate (kernel of $\mathcal O\to j_*\mathcal O$ zero) is the node's
  injectivity. Correct.
- "its complement is the support of an effective Cartier divisor"
  (def-nagata-effective-cartier-ideal): `∃ J : B.I.blowup.IdealSheafData`,
  `J.IsInvertible` (every point has an affine neighbourhood on which the ideal is
  `Ideal.span {s}` with `s ∈ nonZeroDivisors`, exactly the node's definition)
  and `(J.support : Set _) = (B.I.blowupMap ⁻¹ᵁ U)ᶜ`. Correct. "Its" refers to
  the inverse image of $U$; the same `B` carries both conclusions, as in the
  source.
- Quantifier order: ∃ blow-up, then ∃ divisor, conclusions on the same blow-up. Correct.

Edge cases: U = ⊤ (I = unit ideal, T' = T, J = unit ideal with empty support);
U = ⊥ (I = 0, blow-up empty, all clauses vacuous/true); T empty; nonreduced or
disconnected T. The Lean covers each; no density, reducedness or Noetherian
hypothesis is added; no universe restriction.

Searches: `rg` in WeilConjectures/ and lean/Sheaf for IsSchemeTheoreticallyDominant
together with IsInvertible and blowup. Found
`exists_admissibleBlowup_cartierBoundary` (AdmissibleBlowup.lean:664, Cartier
clause only) and `exists_isAdmissible_isSchemeTheoreticallyDominant_preimage`
(Density.lean:238, density clause only); neither states both conclusions for
one blow-up, so no existing exact declaration. det-nagata-boundary-divisor-cartier
is a different, stronger node.

Gates: no hollow definition (the module states one theorem, proof `sorry`);
module and declaration docstrings carry the source place and
`(blueprint: sk-lem-nagata-boundary-divisor)`; the declaration docstring
follows steps 1-5 of the node's proof (step 6, persistence, is proof-only and
not part of the statement). `lean.statement` equals the file's signature
verbatim. Only the node's `lean` field changed against the base.

Compile: `nt_compile.py --json` on the delivered file with `#print axioms`
appended: clean in 3.5 s, axioms propext, sorryAx, Classical.choice, Quot.sound.

Mismatches found: none in the Lean or node. Changed: this section only.
