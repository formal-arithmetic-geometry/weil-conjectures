## Worker report

The delivery adds `Ideal.IsLocallyKoszulRegular`, the affine notion from Stacks Tag 07CV(2):
for every prime ideal containing `L`, a principal localization away from an element outside the
prime has a finite Koszul-regular generating tuple. The tuple is `Fin r → Localization.Away u`,
its generation clause is the equality between the mapped ideal and `Ideal.span (Set.range a)`,
and Koszul regularity is the existing `RingTheory.Sequence.IsKoszulRegular`. The empty tuple and
vacuous unit-ideal case are permitted.

The main theorem renders the item clause by clause. `{R} {S}` with `[CommRing R] [CommRing S]
and `[Algebra R S]` gives the commutative rings and ring homomorphism. `hfinite` is the finite
polynomial presentation: a natural `N`, an `R`-algebra map from `MvPolynomial (Fin N) R` to `S`,
and its `Function.Surjective` proof. `t : ℕ` and `g : Fin t → S` encode the finite principal cover;
`hg : Ideal.span (Set.range g) = ⊤` says it generates the unit ideal, including `t = 0`.
For every `j : Fin t`, `hlocal` supplies `n`, a surjective `R`-algebra map to
`Localization.Away (g j)`, and a locally Koszul-regular kernel. The conclusion supplies a natural
`n`, a surjective `R`-algebra map from `MvPolynomial (Fin n) R` to `S`, and a locally
Koszul-regular kernel. No flatness or Noetherian assumptions occur in the signature.

Dependency declarations used are `Localization.Away` from `Mathlib.GroupTheory.MonoidLocalization.Away`
and `RingTheory.Sequence.IsKoszulRegular` from `WeilConjectures.RingTheory.KoszulRegularSequence`.
The polynomial ring is Mathlib `MvPolynomial` from `Mathlib.Algebra.MvPolynomial.Basic`.
The recorded universal-property declarations `MvPolynomial.aeval` (Eval) and
`MvPolynomial.algHom_ext` (Basic) were also read; the signature only needs `MvPolynomial`.
The theorem's proof
imports the inverse-variable localization result from `Mathlib.RingTheory.MvPolynomial.Localization`
and is left as `sorry` as required for stage 2. The two other proof dependencies,
presentation independence and inverse-equation elimination, have no recorded Lean declarations
at the time of writing, so there are no modules for them to import yet; their exact uses are
retained in the docstring and the unchanged proof-dependency list.

Edge cases checked against Tag 07D1: `t = 0` makes `Ideal.span (Set.range g) = ⊤` force the zero
algebra; then the kernel is the unit ideal and the prime condition in the local predicate is
vacuous. `N = 0`, each `n = 0`, and `r = 0` are allowed by `Fin 0`; the empty Koszul sequence is
covered by `IsKoszulRegular`. The statement has no Noetherian or flatness hypothesis.

Searches: `msearch.py ... leanfinder` for a polynomial-presentation gluing theorem returned only
finite-presentation and smoothness results, no match; `... loogle 'IsKoszulRegular, Localization.Away'`
returned no hits (unknown identifier); `... grep '[Ll]ocally[Kk]oszul|[Kk]oszul[Rr]egular'`
returned no hits. Repository `rg` found no existing local ideal predicate. `tools/blueprint_refs.py
search 'locally Koszul'` found no matching blueprint node. Mathlib and source searches for
`IsLocallyKoszulRegular`, `IsKoszulRegularIdeal`, and `locally.?koszul` found no declaration.
The Stacks source was read at `literature/stacks-project/more-algebra.tex`, Definition 07CV and
Lemma 07D1.

No `STATEMENT-DISPUTED` issue or node fault was found.

## New nodes

`def-sfb-locally-koszul-regular-ideal` is a new definition node because the item and its dependency
statements require the Tag 07CV ideal predicate, and no DAG, Mathlib, source-Lean, or Sheaf
declaration supplied it. Its module is `Sheaf.RingTheory.LocallyKoszulRegularIdeal`; its source,
searches, and exact localizing-prime clauses are recorded in the node file.

No independent second reader was started: this worker delivers directly for the maintainer's independent review, as prescribed by the current brief.

Validation: `scompile.py` compiled each delivered module separately in dependency order on the
server with no errors or warnings. The first dry run rejected only record formatting and the
missing required new-node `import_flags`; those records were repaired before the repeated dry run.

## Second reading by Q109

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
