## Worker report

The module `Sheaf.RingTheory.FinitelyPresentedOverSubring` states
`Module.FinitePresentation.of_finiteType_subring`, with `sorry` as its entire proof.
No definitions, new nodes, dependency repairs, or statement corrections are required.

Source read: `literature/stacks-project/algebra.tex`, lines 583–627,
Lemma Tag 0561 (`lemma-finitely-presented-over-subring`), including its full proof.
The module docstring names that source; the theorem docstring records all five
DAG proof steps and their named dependencies.

Hypothesis and conclusion correspondence:

- The ring map `R → S` is `(f : R →+* S)`, with `[CommRing R] [CommRing S]`.
  These are the commutative rings used throughout the source's Algebra chapter
  and by the finite-type dependency. The map need not be injective.
- An `S`-module `M` is `[AddCommGroup M] [Module S M]`.
- Finite type over `R` is `(hS : RingHom.FiniteType f)`, exactly the dependency's
  recorded declaration, rather than a new predicate or an extra algebra structure.
- Finite presentation as an `R`-module is
  `(hM : @Module.FinitePresentation R M _ _ (Module.compHom M f))`.
  The explicit module argument restricts the given `S`-action along precisely `f`:
  `r` acts by `f r`. It does not quantify over an unrelated action on `M`.
- The full conclusion is `Module.FinitePresentation S M` for the original module.
- Universes `u`, `v`, and `w` are separately declared for the rings and module.
  All variables and universes are explicit; `autoImplicit` is disabled.

Dependency declarations read and used:

- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType` in
  `Mathlib.RingTheory.FiniteType`, lines 213–218. Its definition is
  `Algebra.FiniteType` for `f.toAlgebra`; the latter class, lines 37–40,
  says the top subalgebra is finitely generated.
- `def-sc-finitely-presented-module`: `Module.FinitePresentation` in
  `Mathlib.Algebra.Module.FinitePresentation`, lines 63–69, including its docstring:
  finite generators with finitely generated kernel. The exact-sequence form is
  `Module.FinitePresentation.exists_fin'`, lines 93–100, matching the node's
  definition by finite free modules.
- `lem-trf-polynomial-action-reduction` is only a proof dependency. Its node has
  neither a `lean` record nor a Mathlib match, so it has no module to import yet.
  The theorem docstring names it at the degree-reduction step. The two definition
  modules also supply the stated proof dependencies that are already formalized.

Searches actually run with `msearch.py`:

- LeanFinder, `finite type algebra module finitely presented over subring`:
  eight results; the nearest were
  `Module.FinitePresentation.of_finite_of_finitePresentation` and
  `Algebra.FinitePresentation.of_restrict_scalars_finitePresentation`.
  Their full source signatures/docstrings were read. The first concerns a ring
  finite as a module and finitely presented as an algebra; the second concerns
  algebra presentations, not an arbitrary module. Neither is the item.
- Loogle, `Module.FinitePresentation, RingHom.FiniteType`: zero hits.
- Grep, `FinitePresentation.*of_restrict|finitely.presented.*subring|of_finite_of_finitePresentation`
  in `RingTheory`: five hits, only the nearby algebra results above.
- LeanSearch, `An S-module finitely presented over R is finitely presented over S if S is a finite type R algebra`:
  eight results including module/algebra presentation comparisons, the class,
  and `Module.FinitePresentation.trans` (the reverse direction with extra
  finite-presentation assumptions); no exact match.
- Direct `rg` over Mathlib's Algebra/RingTheory finite-presentation declarations,
  over `WeilConjectures` for finite-presentation/finite-type terminology and the
  item id, over `lean/Sheaf`, and over `dag/lean_names_upstream.json` found no
  declaration of this transfer statement. The sole item-id occurrence in the
  side library was a proof-docstring reference in
  `Sheaf.TraceFormula.ValuationFlatFiniteModulePresentation`.
- The final declaration name was also searched in Mathlib, the upstream source,
  the side library, and the upstream name table; no name conflict was found.

Edge cases checked against the source construction: the zero module allows zero
module generators; zero rings and noninjective maps are allowed; no domain,
Noetherian, locality, freeness, or nontriviality instance occurs. With no algebra
generators (a surjective ring map), the same finite relations suffice. With the
identity map, the conclusion is the same finite-presentation property. A
polynomial extension has action relations but no module-finiteness hypothesis
on the algebra, as required by Tag 0561. There is no disputed statement or node
fault.

An initial compile rejected a typeclass binder for `RingHom.FiniteType`, which
is a predicate. This was repaired to the ordinary hypothesis `hS`. A subsequent
reading checked the source and node clause by clause and confirmed that the
canonical restriction via `Module.compHom M f` avoids any compatibility
hypothesis or silently chosen action. The final module uses the required
module header, public imports and section, topic directory, source docstrings,
and a single sorry theorem.

## Second reading by Q40

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
