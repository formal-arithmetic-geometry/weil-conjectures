## Worker report

The module `Sheaf.TraceFormula.LocalMapCompletionApproximation` defines
`AlgebraicGeometry.localMapCompletionMap`, the canonical map between maximal-ideal
adic completions supplied by `RingHom.exists_adicCompletion_map_of_local`, and states
`AlgebraicGeometry.exists_etale_approximation_of_local_map` with proof `sorry`.

The hypotheses are rendered as follows. `S X Y : Scheme.{u}` and `f : X ⟶ S`,
`g : Y ⟶ S` are the three schemes and their structure maps; the instances
`[IsLocallyNoetherian S]`, `[LocallyOfFiniteType f]`, and
`[LocallyOfFiniteType g]` render the local Noetherian and finite-type assumptions.
The points and incidence are `(x : X)`, `(y : Y)`, and `hxy : g y = f x`.
`hG : IsGRing (S.presheaf.stalk (f x))` is exactly the G-ring hypothesis at
s = f x. The local map is `θ : Y.presheaf.stalk y →+* AdicCompletion
(IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)` with
`[IsLocalHom θ]`; `hθ` states its compatibility with the two maps from the common
base stalk, which is the Lean rendering of “local O_{S,s}-algebra homomorphism”.
For each `N`, `1 ≤ N` is rendered explicitly. The witnesses are `U`, `p`, `u`,
and `q`; `p u = x`, `q u = y`, `IsIso (p.residueFieldMap u)`, and `Etale p`
render the etale neighbourhood and residue-field isomorphism, while
`p ≫ f = q ≫ g` renders that `q` is an S-morphism. The existential proof binders
`hpu : p u = x` and `hqy : q u = y` express the point equalities and
provide the casts needed by the stalk maps, without repeating these equalities as conjuncts. For every stalk element `a`,
the displayed difference lies in the image of the N-th power of the maximal ideal
under the completion algebra map; this is exactly the stated congruence.

The statement-dependency declarations used are:

* `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` from
  `Mathlib.AlgebraicGeometry.Scheme` (`def-pc-scheme`).
* `AlgebraicGeometry.LocallyOfFiniteType` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (`def-weil-finite-type-morphism`).
* `AlgebraicGeometry.IsLocallyNoetherian` from
  `Mathlib.AlgebraicGeometry.Noetherian` (`pqf-def-locnoeth`).
* `AlgebraicGeometry.Etale` from `Mathlib.AlgebraicGeometry.Morphisms.Etale`
  (`def-weil-etale-morphism`).
* `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap` from
  `Mathlib.AlgebraicGeometry.ResidueField` (`def-weil-residue-field`).
* `AdicCompletion` and `AdicCompletion.of` from
  `Mathlib.RingTheory.AdicCompletion.Algebra` (`def-weil-pbc-adic-completion`).
* `IsGRing` is supplied by `Sheaf.RingTheory.GRing` (`def-weil-pbc-g-ring`);
  the explicit `hG` hypothesis uses exactly this recorded definition.
* `RingHom.exists_adicCompletion_map_of_local` from
  `Sheaf.RingTheory.CompletionMapForLocalHom` supplies the canonical completion map.
  Its landed node `lem-weil-pbc-fs-adic-completion-map-local` is added to `stmt_deps`.
  The coordinate characterization uniquely determines the chosen map, so its use is
  not a choice of arbitrary ring-map data.
* The proof-only import `Sheaf.RingTheory.FiniteTypeGRing` supplies
  `isGRing_of_finiteType`. The Artin-approximation proof child is not yet stated, so
  no import is available for it; the full six-step proof plan is in the docstring.

Edge cases checked: `N = 1` is allowed by the explicit bound; larger N are arbitrary.
The ideal power is defined also for N = 0 by the imported completion API, while the
statement intentionally follows the source's N ≥ 1. No nonemptiness of the schemes,
points, or stalk elements is added, and the construction is uniform in the universe
`u`.

Searches made: `msearch.py ... leanfinder "local map completion etale approximation
scheme stalk"` returned only general étale declarations and no match; `msearch.py ...
loogle "Scheme stalk completion local map Etale"` returned no hits (the query parser
also reported the bare query form); `msearch.py ... grep
"exists_etale_approximation|localMapCompletionMap" Mathlib` returned zero hits.
The repaired Loogle query `AdicCompletion` returned the general completion type and
its operations, with no approximation theorem. A LeanSearch query
"Approximate local ring homomorphism into completed scheme stalk by an elementary
etale neighbourhood" returned only basic local-stalk and etale APIs, with no match.
Additional `rg` searches over `lean/Sheaf` and the pinned Mathlib tree found no
existing theorem with this statement; the only completion-map result was the used
`RingHom.exists_adicCompletion_map_of_local`.

No `STATEMENT-DISPUTED` flag or node fault was found.

## Second reading by Q55

This is a self-check in the dispatcher-started worker, with no additional agents,
as the dispatch explicitly forbids starting them. The maintainer performs the
independent review. I reopened the node and checked each clause against the file.
The initial draft missed the G-ring assumption, so I added `hG` explicitly; the
report and recorded signature now include it. I also removed duplicate point
equalities, keeping exactly the existential equalities `hpu` and `hqy` that
transport the stalk types. The base point is `f x`, and `hxy` identifies `g y`
with it; no extra point or incidence assumption remains. The local map `θ`, its
locality instance and the transported ring-map identity `hθ` are the exact local
base-algebra map in the source. The positive natural numbers encode the integers
N ≥ 1 without dropping a case. The etale witness, residue-field isomorphism,
S-morphism equality and congruence for every target-stalk element all match.
The image ideal is exactly m_u^N extended to the completed ring. Empty schemes
are vacuous because x and y are already given; no characteristic or closed-point
condition is added. The module docstring includes the source, and the theorem
docstring now carries all six DAG proof steps.
