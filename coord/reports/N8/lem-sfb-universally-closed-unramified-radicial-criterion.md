## Worker report

The module `Sheaf.AlgebraicGeometry.UniversallyClosedUnramifiedRadicialCriterion`
states `AlgebraicGeometry.IsClosedImmersion.iff_isUnramified_and_universallyInjective`.
Its sole proof is `sorry`, as required in stage 2. No definition, dependency repair,
new node, or statement correction is needed. Only the item's `lean` field changes.

I read the node, all five statement-dependency nodes and their recorded declarations,
and the proof-dependency records and source declarations. I read the source in
`literature/stacks-project/etale.tex`, labels `lemma-characterize-closed-immersion`
(Tag 04XV) and `lemma-universally-injective-unramified` (Tag 05VH). The statement
is precisely equivalence (1) and (5) of 04XV with universal closedness fixed as a
hypothesis. The four proof steps from the DAG are carried in the theorem docstring.

The correspondence of every hypothesis and clause is:

| Node text | Lean |
| --- | --- |
| Schemes X and Y | `{X Y : Scheme.{u}}`, with explicit `universe u` |
| A morphism g : X → Y | `(g : X ⟶ Y)` |
| g is universally closed | `[UniversallyClosed g]` |
| g is a closed immersion | `IsClosedImmersion g` |
| if and only if | `↔` |
| g is unramified | `IsUnramified g` |
| and universally injective | `∧ UniversallyInjective g` |

There is no finite-type, separatedness, noetherian, characteristic, nonemptiness,
or properness assumption. Local finite type is part of the recorded definition
of unramifiedness, not an additional hypothesis. `autoImplicit false` prevents
implicit unbound variables. The universe is arbitrary, and the statement uses
the existing scheme category and morphism definitions without new test objects.

Statement dependencies used (public imports):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  recorded `AlgebraicGeometry.UniversallyClosed` (defined in
  `Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed`); this quantifies
  closedness over base changes. `IsProper` and `IsSeparated` from this same
  dependency belong to the proof, not the theorem's hypotheses.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`: closed embedding and surjective stalk maps.
- `def-weil-unramified-morphism`:
  `Sheaf.AlgebraicGeometry.UnramifiedMorphism`, `AlgebraicGeometry.IsUnramified`,
  exactly `LocallyOfFiniteType g ∧ IsOpenImmersion (pullback.diagonal g)`.
- `def-weil-radicial-morphism`: its `mathlib_match` is
  `Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective`,
  `AlgebraicGeometry.UniversallyInjective`. I also read
  `UniversallyInjective.iff_diagonal` and `tfae_universallyInjective`.

Proof-only modules are imported with plain `import`, including those that are
also exposed transitively by statement imports:

- `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`:
  `AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono`
  (`lem-pc-proper-monomorphism-closed`).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (`def-weil-finite-type-morphism`).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.lift`
  (`def-pc-fibre-product`).
- `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion` (`def-weil-open-immersion`).
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`:
  `AlgebraicGeometry.IsSeparated.isSeparated_of_mono`
  (`lem-trf-scheme-monomorphism-separated`).
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed`:
  `AlgebraicGeometry.instQuasiCompactOfUniversallyClosed`
  (`lem-weil-pbc-universally-closed-quasi-compact`).

The other proof dependencies are already statement dependencies. No import cycle
is introduced, and no definition is duplicated.

Edge cases checked before writing:

- The empty source gives a closed immersion into any target, and is unramified
  and universally injective. The empty target admits only empty-source maps.
- Identities and isomorphisms satisfy the hypothesis and both sides.
- Closed immersions defined by nonzero or nilpotent ideals are allowed: no
  reducedness or flatness requirement appears in `IsUnramified`.
- A nontrivial finite purely inseparable field extension gives a universally
  closed and universally injective map of spectra, but fails unramifiedness
  and is not a closed immersion. This checks the unramified conjunct.
- The fold from two copies of Spec k to Spec k is universally closed and
  unramified, but fails universal injectivity and is not a closed immersion.
- A non-closed open immersion is unramified and universally injective but
  fails universal closedness. This verifies that the sole hypothesis is substantive.

Searches for an existing full statement:

- `msearch.py ... leanfinder`, query: "A universally closed morphism of schemes
  is a closed immersion if and only if it is unramified and universally injective".
  Eight hits: universal closedness of closed immersions and the definition of
  universal injectivity, but no full equivalence.
- `msearch.py ... leansearch`, query: "A universally closed scheme morphism is
  a closed immersion if and only if it is unramified and universally injective".
  Eight hits: definitions, closed-immersion affine criterion, and universal
  closedness of closed immersions; none is the statement.
- `msearch.py ... loogle`, query: `"IsClosedImmersion", "UniversallyInjective"`.
  Successful search with zero hits.
- `msearch.py ... grep`, query:
  `IsUnramified|[Uu]nramified.*[Ii]njective|[Ii]njective.*[Uu]nramified|iff_isProper_and_mono`,
  restricted to Mathlib `AlgebraicGeometry`. Three hits: the proper-monomorphism
  criterion and a ring-theoretic formally unramified calculation; no full equivalence.
- `rg -n` over `lean/WeilConjectures` and `lean/Sheaf` for `IsUnramified`,
  unramified/injective combinations, and this node id found the canonical
  unramified definition and related locus theorems. `UniversalClosedImmersionOpen`
  carries the argument in its proof docstring but states a different locus result.
- `rg -n` over Mathlib, both project roots and `dag/lean_names_upstream.json`
  for `iff_unramified_and_universallyInjective` and
  `iff_isUnramified_and_universallyInjective` found no collision.

No statement dispute or node fault was found. Compilation and preflight are run
through the prescribed wrappers; the theorem's expected sorry warning is permitted.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
