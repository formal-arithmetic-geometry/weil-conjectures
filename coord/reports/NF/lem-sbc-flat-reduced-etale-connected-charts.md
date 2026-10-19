## Worker report

The exact existing declaration is `AlgebraicGeometry.exists_etaleCover_factorization`
in `WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat`, source lines 599–609.
Its full docstring (lines 580–598) and signature were read against Stacks Tag 0EY5,
`more-morphisms.tex`, `lemma-cover-by-geometrically-connected` (lines 13257 onward).
No module, helper, definition node, dependency repair, or statement correction is needed.
The sandbox node changes only `lean`, with `existing: true`, branch `slopmaster2`.
Its recorded signature is verbatim from `theorem` through `:=`.

The correspondence of every hypothesis and clause is:

- Schemes and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Flatness: `[Flat f]`.
- Local finite presentation: `[LocallyOfFinitePresentation f]`.
- Every fibre geometrically reduced over its residue field: `[GeometricallyReduced f]`.
  This is equivalent to the fibrewise condition by
  `GeometricallyReduced.eq_geometrically` and
  `geometrically_iff_forall_fiberToSpecResidueField`.
- The chart family and intermediate bases: existential `ι : Type u`,
  `U V : ι → Scheme.{u}`, and maps `p`, `q`, `r` with exactly the node's domains
  and codomains (`p` represents `a_i`).
- Étale covering: `(∀ i, Etale (p i))` and
  `(∀ x : X, ∃ (i : ι) (y : U i), (p i).base y = x)`.
  This is the jointly surjective family condition of the recorded small étale site.
- Étale base maps: `(∀ i, Etale (r i))`.
- Flat chart maps: `(∀ i, Flat (q i))`.
- Finite presentation of the chart maps: the three conjuncts
  `(∀ i, LocallyOfFinitePresentation (q i))`, `(∀ i, QuasiCompact (q i))`,
  `(∀ i, QuasiSeparated (q i))`. `QuasiSeparated` means precisely quasi-compact diagonal.
- Every chart fibre geometrically connected: `(∀ i, GeometricallyConnected (q i))`,
  equivalent to the residue-field fibre condition by
  `GeometricallyConnected.iff_geometricallyConnected_fiber`.
- Every chart fibre geometrically reduced: `(∀ i, GeometricallyReduced (q i))`,
  using the same fibrewise equivalence as for the hypothesis.
- Factorization: `(∀ i, q i ≫ r i = p i ≫ f)`, exactly `r_i ∘ q_i = f ∘ a_i`.

Dependency records and their source declarations were read. All names below lie in
namespace `AlgebraicGeometry`; module paths below start with `Mathlib.AlgebraicGeometry`:

- `def-pc-scheme`: `Scheme`, `Scheme.Hom`, module `Scheme`.
- `def-weil-flat-morphism`: `Flat`, module `Morphisms.Flat`; its docstring identifies
  the equivalent stalkwise criterion `Flat.iff_flat_stalkMap`.
- `def-sbc-locally-finite-presentation`: `LocallyOfFinitePresentation`, module
  `Morphisms.FinitePresentation` (the node's `mathlib_match`).
- `def-pc-scheme-fibre`: `Scheme.Hom.fiber`, `fiberι`, `fiberToSpecResidueField`,
  module `Fiber`; these are the residue-field pullback and its projections.
- `def-pc-geometrically-irreducible`: its recorded family of specializations includes
  `GeometricallyReduced` and `GeometricallyConnected`, modules `Geometrically.Reduced`
  and `Geometrically.Connected`; these are the specializations actually used here.
- `def-weil-etale-morphism`: `Etale`, module `Morphisms.Etale`.
- `def-weil-pbc-etale-site`: `Scheme.smallEtaleTopology`, module `Sites.Etale`, and
  `Scheme.Etale`, module `Morphisms.Etale`.
  `Scheme.ofArrows_mem_smallEtaleTopology_iff` renders jointly surjective covers.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType`, module `Morphisms.FiniteType`,
  and `QuasiCompact`, module `Morphisms.QuasiCompact`. Only the latter notion occurs
  in this statement's finite-presentation clause.

Edge cases: empty X permits the empty covering; empty S forces empty X. The theorem
adds no nonemptiness assumption on X, S, or the index. Connected fibres are nonempty,
as intended in the source, but this does not require f to be surjective: the intermediate
étale bases cover only the appropriate local images. The index universe is the scheme
universe, and no Noetherian, separated, affine, characteristic, or field restriction is
added. All variables and the universe in the existing declaration are bound.
No statement dispute or node fault was found.

Searches run on this retry:

- `msearch.py ... leanfinder` with query “A flat locally finitely presented scheme
  morphism with geometrically reduced fibres admits etale charts with geometrically
  connected fibres”: eight related étale results, no exact Mathlib theorem.
- `msearch.py ... loogle` with query `AlgebraicGeometry.GeometricallyConnected`:
  twelve results, including the definition and the fibrewise equivalence.
- `msearch.py ... grep` with query
  `exists_etaleCover|cover_by_geometrically|etale.*factorization` in AlgebraicGeometry:
  zero hits.
- Direct `rg` for the declaration and node id in the upstream `WeilConjectures` source:
  the exact SlicingFlat declaration and its DegreeZero uses.
- Direct `rg` for `exists_etaleCover_factorization|cover_by_geometrically` in project
  `lean/Sheaf`: zero hits.
- Earlier logged `leansearch` query “Flat finitely presented morphism geometrically
  reduced fibres etale local geometrically connected factorization”: service unavailable,
  Internal Server Error; this is not treated as a no-match search.

Validation: `deliver2.py NF lem-sbc-flat-reduced-etale-connected-charts --no-push`
now prints `OK (dry run)` after the server existing-declaration probe and preflight,
except for the independent second reading which is deliberately left to the next worker.
The previous published-library duplicate-declaration failure no longer reproduces.
No local compilation, live-library edit, repository git command, or push was performed.

## Second reading by NF

The node states a morphism of schemes `f : X → S`, flat and locally of finite
presentation, with every scheme-theoretic fibre geometrically reduced over its
residue field.  The existing Lean declaration renders this as
`{X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
[GeometricallyReduced f]`; Mathlib's `geometrically_iff_forall_fiberToSpecResidueField`
identifies the last class with the node's fibrewise condition.

Its conclusion introduces an index `ι : Type u`, schemes `U V : ι → Scheme.{u}`,
and maps `p : ∀ i, U i ⟶ X`, `q : ∀ i, U i ⟶ V i`, and `r : ∀ i, V i ⟶ S`.
The clauses match the node in order: each `p i` is étale; the family covers `X`
via `∀ x : X, ∃ i y, (p i).base y = x`; each `r i` is étale; each `q i` is
flat, locally of finite presentation, quasi-compact, and quasi-separated; each
`q i` is geometrically connected and geometrically reduced; and
`q i ≫ r i = p i ≫ f`.  The three finiteness clauses are exactly the
source's finite-presentation condition, with quasi-separatedness the
quasi-compact diagonal condition.

The Stacks source (Tag 0EY5, `lemma-cover-by-geometrically-connected`) assumes
only flatness, local finite presentation, and geometrically reduced fibres, and
concludes precisely this étale covering and factorization.  The source's diagram
orientation agrees with Lean composition (`q ≫ r = p ≫ f`).  No hypothesis or
conclusion is added, dropped, weakened, or strengthened.

Edge cases were checked: `ι` may be empty when `X` is empty; no nonemptiness of
`X`, `S`, or the index is assumed; an empty base forces an empty source; no
Noetherian, separated, affine, field, characteristic, or surjectivity hypothesis
is present.  The universe `Type u` is the source theorem's universe and allows
all schemes appearing in the family.  The geometric connectedness condition
itself supplies the intended nonempty fibres where applicable.

I searched the DAG, project `lean/Sheaf`, the slopmaster2 source, and pinned
Mathlib by declaration name and by concepts (étale covering/factorization,
geometrically connected/reduced fibres, and flat finite-presentation slicing).
The exact declaration occurs only in
`WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat`; no Mathlib or project
duplicate exists.  I also checked the dependency declarations: `Scheme`,
`Flat`, `LocallyOfFinitePresentation`, fibre maps, `GeometricallyReduced` and
`GeometricallyConnected`, `Etale`, the small étale topology, `QuasiCompact`, and
`QuasiSeparated` are the recorded notions used by the theorem.  No mismatch was
found, so no Lean or node statement was changed in this second reading.

Independent search details: LeanFinder query “A reduced geometric fibre family
flat locally of finite presentation admits a jointly surjective etale family
factoring over etale bases with connected geometric fibres” returned eight
related results, none this theorem. Loogle query
`AlgebraicGeometry.GeometricallyReduced` returned twelve results, confirming the
class and fibre specialization, not the slicing theorem. The msearch grep query
`slicing|cover_by_geometrically_connected|exists_etaleCover_factorization`
returned only two irrelevant uses of “slicing” in Mathlib testing code. Direct
`rg` on the upstream morphisms and project modules found the exact general
SlicingFlat theorem and the distinct smooth special case in Slicing. These
searches are recorded in searches.jsonl.

Dependency signatures were opened in Mathlib Scheme, Morphisms/Flat,
Morphisms/FinitePresentation, Fiber, Geometrically/Connected,
Geometrically/Reduced, Geometrically/Basic, Morphisms/Etale,
Sites/Etale, Morphisms/QuasiCompact and Morphisms/QuasiSeparated. In particular,
`GeometricallyConnected.iff_geometricallyConnected_fiber` and the reduced
class's `eq_geometrically` with
`geometrically_iff_forall_fiberToSpecResidueField` justify both directions of
the fibre interpretation. `Scheme.ofArrows_mem_smallEtaleTopology_iff` equates
the covering condition with union of ranges being the whole space. Verdict:
all objects, hypotheses, and conclusion clauses agree with their dependency
notions. No helper, new definition, dependency repair, or statement correction
is required; hence no correction-citer audit is applicable.

The upstream module explicitly binds `universe u`; its theorem has no section
hypothesis beyond the displayed binders. Its Stacks annotation and docstring
identify 0EY5. This existing declaration delivery introduces no definition,
proof, sorry, or module to which new-module docstring conventions would apply.
The node has an empty proof list. I checked the recorded signature verbatim
against the existing source. The server dry run passed its existing-declaration
probe and preflight (`OK (dry run)`); there are no delivered Lean files to compile.
The second reading changed only this report, with no mathematical mismatch found.
