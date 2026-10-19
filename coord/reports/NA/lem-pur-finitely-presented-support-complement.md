## Worker report

The module `Sheaf.RingTheory.FinitelyPresentedSupportComplement` states
`Module.isClosed_support_and_isCompact_compl`, with `sorry` as its entire proof.
The item statement is unchanged. No new nodes or dependency modules are needed.

Hypotheses and clauses, in the order of the node:

- A commutative ring B is `(B : Type u) [CommRing B]`.
- A B-module M is `(M : Type v) [AddCommGroup M] [Module B M]`. The ring and module
  universes are independent and explicitly bound.
- Admitting a presentation by two finite free modules is
  `[Module.FinitePresentation B M]`. The definition in
  `Mathlib.Algebra.Module.FinitePresentation` requires a finite generating set and
  a finitely generated kernel of its canonical presentation. Over a ring this is
  precisely the node's existence of a right exact sequence `B^u → B^v → M → 0`:
  `Module.FinitePresentation.exists_fin'` supplies those maps, surjectivity, and
  `Function.Exact`; conversely finite free relations give the finitely generated
  kernel. No particular presentation is part of the conclusion.
- The space Spec B is `PrimeSpectrum B`, the underlying topological space of the
  recorded `AlgebraicGeometry.Spec (CommRingCat.of B)` from
  `Mathlib.AlgebraicGeometry.Scheme`, imported publicly as the dependency requires.
  The Spec definition and its docstring were read in that source file.
- The support is exactly Mathlib's `Module.support B M`, defined in
  `Mathlib.RingTheory.Support` as
  `{p | Nontrivial (LocalizedModule p.asIdeal.primeCompl M)}`.
  This is the node's condition that the localization is nonzero. The localization
  is the existing fraction construction, not new data: `LocalizedModule.mk_eq`
  in `Mathlib.Algebra.Module.LocalizedModule.Basic` identifies `m/s` and `m'/s'`
  exactly when some multiplier outside p makes `s' • m` and `s • m'` equal.
- Closedness is the first conjunct `IsClosed (Module.support B M)`.
- Quasi-compactness of the complement is the second conjunct
  `IsCompact (Module.support B M)ᶜ`. This does not impose Hausdorffness:
  `isCompact_iff_finite_subcover` in `Mathlib.Topology.Compactness.Compact`
  states exactly that every open cover has a finite subcover.

Dependency declarations read and used:

- Statement dependency `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and
  `AlgebraicGeometry.Spec.map`, `Mathlib.AlgebraicGeometry.Scheme`. Only its
  underlying topological space is needed by this node; no specialized replacement
  of the affine-spectrum definition is needed.
- Proof dependency `lem-weil-pbc-cauchy-binet`: `Matrix.cauchy_binet`,
  `Sheaf.LinearAlgebra.Matrix.CauchyBinet`, imported non-publicly. Its full statement
  and docstring were read, including its zero-size and empty-sum clauses.
- Proof dependency `lem-weil-pbc-matrix-adjugate-identity`: `Matrix.adjugate_mul`
  and `Matrix.mul_adjugate`, `Mathlib.LinearAlgebra.Matrix.Adjugate`, imported
  non-publicly.
- Proof dependency `lem-weil-pbc-spec-localization-away-basic-open`:
  `PrimeSpectrum.isTopologicalBasis_basic_opens`,
  `PrimeSpectrum.localization_away_isOpenEmbedding`, and
  `PrimeSpectrum.localization_away_comap_range`, all in
  `Mathlib.RingTheory.Spectrum.Prime.Topology`, already imported transitively by
  the public prime-spectrum module import. Their signatures were read.
- Proof dependency `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`:
  `PrimeSpectrum.iSup_basicOpen_eq_top_iff` and `PrimeSpectrum.compactSpace`,
  in the same topology module. The proof needs the compactness clause, also
  available directly as `PrimeSpectrum.isCompact_basicOpen`.

The declaration docstring carries all six node proof steps: presentation and
maximal minors, annihilators from localization fractions, Cauchy--Binet, the
adjugate converse and closedness, compact basic opens via localization, and the
finite union argument. The source was read locally in Stacks `algebra.tex`,
`lemma-support-finite-presentation-constructible` (Tag 051B), whose statement is
exactly the two conclusions of this theorem.

Edge cases checked before writing: for M = 0 the support is empty and its
complement is the compact spectrum; for the zero ring the spectrum and both
subsets are empty. A presentation with v = 0 gives M = 0 and the empty minor 1.
When u < v there are no maximal minors and the complement is empty. Empty covers
of the empty complement admit the empty subcover. No nontriviality, nonempty
index, positive-rank, Noetherian, or characteristic hypothesis is imposed.

Searches for existing declarations:

- `msearch.py leanfinder`, query “The support of a finitely presented module is
  closed and its complement is quasi compact”: eight hits, including
  `Module.isClosed_support`, `Module.support_eq_zeroLocus`,
  `PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg`, and
  `Module.isOpen_freeLocus`; none states both conclusions for finite presentation.
- `msearch.py loogle`, query `Module.support, IsCompact`: zero hits.
- `msearch.py grep`, query `FinitePresentation.*support|support.*FinitePresentation|051B`
  in `RingTheory`: one hit, the explicit TODO for this result in
  `Mathlib/RingTheory/Spectrum/Prime/Module.lean:21`. That file was read in full:
  `Module.isClosed_support` only states closedness for finitely generated modules.
- `msearch.py leansearch`, query “The complement of the support of a finitely
  presented module is quasi compact”: UNAVAILABLE, Internal Server Error.
- `rg` of the item ID and `support.*[Cc]ompact|[Cc]ompact.*support` in upstream
  `WeilConjectures` and project `lean/Sheaf`: no declaration for this item.
  Results concern compactly supported cohomology, thick support of compact
  objects, or support of ideal sheaves, which are different notions.
- `rg` of `isClosed_support_and_isCompact_compl|FinitelyPresentedSupportComplement`
  in the upstream name index, upstream sources, and project sources: no collision.

No statement dispute or node fault found. The standalone server compile passed
cleanly (1.2 seconds, nice 19, two threads, 60-second limit). No local compiler or
library build was run.

## Second reading by NA

I read the node statement, Tag 051B at `literature/stacks-project/algebra.tex` (lemma
`algebra-lemma-support-finite-presentation-constructible`), and the Lean module
side by side. The introduced objects and hypotheses match: `B : Type u` with
`[CommRing B]`, `M : Type v` with `[AddCommGroup M] [Module B M]`, and
`[Module.FinitePresentation B M]`, which expresses finite presentation without
choosing a presentation. `Module.support B M` is the set of primes where the
localized module is nontrivial, matching the source's nonzero localization
condition. The conclusion has exactly both source clauses, `IsClosed
(Module.support B M)` and `IsCompact (Module.support B M)ᶜ`; `IsCompact` is the
open-cover finite-subcover formulation required by the node. Quantifier order,
universes, and the independent ring/module universes are preserved.

The proof docstring records the source proof's six steps: maximal minors and the
vanishing/minor equivalence, Cauchy--Binet, the adjugate converse and closedness,
basic-open compactness through localization, and the finite-union argument. The
listed dependency declarations are imported and correspond to the proof steps;
no private duplicate notion or extra hypothesis occurs. No mismatch was found,
so no Lean or node correction was needed.

Edge cases checked are the zero module, zero ring and empty spectrum, rank
`v = 0` (empty minor equal to one), `u < v` (no minors and empty complement),
and empty covers. These are all covered by the statement and proof docstring;
there is no characteristic, Noetherian, nontriviality, or nonempty-index
assumption. Searches recorded in the worker report (LeanFinder, Loogle,
LeanSearch, and grep over Mathlib, upstream, and project sources) found no
existing declaration with both conclusions; the Mathlib TODO and separate
closed-support/basic-open results are weaker. The server compilation with
`scompile.py` passed with only the permitted `sorry`.
