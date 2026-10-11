## Worker report

The module states `IsInvertible.compl_support_dense` for an effective Cartier
ideal `C` on an arbitrary scheme `Y`. It has a `sorry` proof, as stage 2 requires.

- The node's scheme `X` is `Y : Scheme.{u}`. Its effective Cartier ideal is
  `C : Y.IdealSheafData` with `hC : C.IsInvertible`. Its closed subscheme is
  `C.subscheme`, whose underlying image is `C.support`; the complementary
  open is `C.support.compl`, included by `Scheme.Opens.ι C.support.compl`.
- The quasi-compactness required by the node's cited definition of a
  scheme-theoretically dense open is the `QuasiCompact` first conjunct.
- Scheme-theoretic density, equivalently injectivity of the structure sheaf
  morphism on all opens for this quasi-compact inclusion, is the
  `IsSchemeTheoreticallyDominant` second conjunct.
- Topological density of the complement is the `Dense` third conjunct.
- The final conjunct says that every open contained in `C.support` is bottom;
  hence the divisor contains no nonempty open subset.

Dependency declarations: `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`
in `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`, and
`AlgebraicGeometry.IsSchemeTheoreticallyDominant` in
`Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`.
I read both declarations and their docstrings. The latter's `ker_eq_bot`
encodes sheaf injectivity; `Scheme.Hom.app_injective` gives injectivity on
each open under quasi-compactness.

The source is Stacks Project, Divisors, Tag 07ZU, at
`/home/ubuntu/c1-stacks-review/divisors.tex:2449`. The repository's
`literature/stacks-project/` checkout is absent on this machine. The proof
there reduces to affine charts with a regular generator and injectivity of
`A → A_f`. The module docstring follows all three DAG proof steps and names
their proof dependencies.

Edge cases: the empty scheme and the empty divisor are allowed. If the
complement is empty on a nonempty scheme, the ideal would locally have zero
as a nonzerodivisor, so the hypothesis excludes that case. No reducedness,
Noetherian, irreducibility, or field hypothesis is added. Nonreduced schemes
with regular effective Cartier ideals remain included.

Searches: `msearch.py ... leanfinder "effective Cartier divisor complement
is scheme theoretically dense and topologically dense with nowhere dense
support"` found only related declarations, not the full statement.
`msearch.py ... loogle "IsInvertible.isSchemeTheoreticallyDominant_compl_support,
IsSchemeTheoreticallyDominant, IsDense"` returned no hits (the upstream name
is not in Mathlib). `msearch.py ... grep
"IsInvertible.*(dense|Dense|Dominant)|isSchemeTheoreticallyDominant.*
(cartier|Cartier|invertible|Invertible)" AlgebraicGeometry` returned no
Mathlib hits. `rg` in `WeilConjectures` found
`IsInvertible.isSchemeTheoreticallyDominant_compl_support` in
`WeilConjectures.Blowup.Density`; it states only scheme-theoretic dominance,
so it is not the full node statement. The exact item-id grep in
`WeilConjectures` and the `rg` search in repository `lean/Sheaf` returned
no match.

## Second reading by H1

I read the node, both dependency nodes and their recorded declarations, the
Lean module, and Stacks Divisors, Tag 07ZU (the lemma and proof at
`/home/ubuntu/c1-stacks-review/divisors.tex:2449`). The node's objects,
hypothesis, and conclusions match the Lean as follows:

- An arbitrary scheme `X`: `{Y : Scheme.{u}}`. The universe is declared and
  unrestricted; the changed letter has no mathematical effect.
- The closed subscheme `D` cut out by an effective Cartier ideal:
  `{C : Y.IdealSheafData}` and `(hC : C.IsInvertible)`. The dependency
  `def-nagata-effective-cartier-ideal` records exactly this declaration;
  `IsInvertible` asks for a regular-principal ideal on an affine neighborhood
  of every point, with no Noetherian, reducedness, or field assumption.
  Mathlib's `IdealSheafData.range_subschemeι` identifies the underlying
  image of `C.subscheme` with `C.support`.
- The open complement `U` and its inclusion `j`:
  `C.support.compl` and `Scheme.Opens.ι C.support.compl`. These are the
  complement of the same closed subscheme and its canonical open immersion.
- Quasi-compactness of `j`, as required by the cited density definition:
  `QuasiCompact (Scheme.Opens.ι C.support.compl)`, the first conjunct.
- Injectivity of `O_Y → j_* O_U`: the second conjunct,
  `IsSchemeTheoreticallyDominant (Scheme.Opens.ι C.support.compl)`.
  The dependency `def-nagata-scheme-theoretically-dense-open` matches the
  Mathlib class with zero kernel; for a quasi-compact morphism, Mathlib's
  `Scheme.Hom.app_injective` gives injectivity on every open.
- Topological density of `U`: `Dense (C.support.compl : Set Y)`, the third
  conjunct. This uses the whole underlying space, including nonreduced ones.
- No nonempty open subset contained in `D`:
  `∀ V : Y.Opens, (V : Set Y) ⊆ C.support → V = ⊥`, the last conjunct.
  The quantifier ranges over all opens, including bottom.

The empty scheme and empty divisor are included. A nonempty scheme with empty
complement is ruled out by the effective Cartier hypothesis, not by a hidden
Lean assumption. No natural-number or characteristic parameter occurs. The
single universe `u` allows arbitrary scheme universes; there is no index set.

Independent searches: LeanFinder for "complement of effective Cartier divisor
is affine and schematically dense with dense underlying open" returned
related basic-open results, not this statement. Loogle for
`IsInvertible, IsSchemeTheoreticallyDominant, Dense` returned no matching
theorem. The `msearch.py` grep for
`Cartier.*dense|cartier.*dense|IsInvertible.*Dense|support.*nowhere` returned
no Mathlib hit. An `rg` search of Mathlib's algebraic geometry files,
`WeilConjectures`, and the repository's `lean/Sheaf` found the upstream
`IsInvertible.isSchemeTheoreticallyDominant_compl_support` in
`WeilConjectures.Blowup.Density`; I opened it and confirmed that it states
only the scheme-theoretic dominance conjunct, not all four conclusions.

Verdict: no mismatch. The module, node statement record, and worker report
needed no mathematical change. The `sorry` is the sole proof, and its docstring
tracks the node's three proof steps and their dependencies. The clean
`scompile.py` run emitted no errors or warnings.
