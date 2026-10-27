## Worker report

The module `Sheaf.AlgebraicGeometry.SeparatedSpaceDimensionOneScheme` states
`AlgebraicGeometry.AlgebraicSpace.exists_scheme_of_separated_dim_le_one`, with
`sorry` as its whole proof. It introduces no definition, auxiliary theorem, axiom,
or alternative algebraic-space encoding.

Source read: `literature/stacks-project/spaces-over-fields.tex`, lines 1438–1484,
Tag 0ADD, `lemma-codim-1-point-in-schematic-locus`. The source supplies a schematic
open neighbourhood at each point of a separated locally Noetherian space whose
local dimension is at most one. The node applies this everywhere, using local
finite type over a field to obtain local Noetherianity. The five-step docstring
records the node's finite-cover, finite-groupoid, saturated affine open, affine
descent, and Zariski gluing argument, including its empty case.

Hypotheses and conclusion, clause by clause:

- A field K: `{K : Type u} [Field K]`, using Mathlib's field class. There is no
  characteristic, algebraic-closure, or perfection restriction.
- An algebraic space X over Spec K:
  `(X : AlgebraicSpace (Spec (.of K)))`. This is the dependency's full subcategory
  of fppf sheaves on schemes over Spec K with representable diagonal and an étale
  surjective scheme atlas. In particular X is not assumed to be a scheme.
- Separatedness: `hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
  (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj))`. This uses the recorded scheme-test
  representability definition. Products in presheaves on `Over (Spec (.of K))`
  are relative products over Spec K: the represented base is terminal. Hence
  `prod.lift` here is exactly the relative diagonal, and the scheme projection
  in each test is required to be a closed immersion. It adds no properness or
  finite-type condition to this diagonal. The scheme notion `IsSeparated` from
  the proper-morphism dependency is precisely the closed-immersion condition on
  the relative diagonal; it cannot be applied directly to a nonschematic source,
  so the condition is expressed on its scheme tests instead.
- Local finite type: `hlft : ∀ (U : Over (Spec (.of K)))
  (a : yoneda.obj U ⟶ X.obj.obj), IsEtale a → LocallyOfFiniteType U.hom`.
  This is the node's explicit condition on all étale scheme charts. The arrow
  `U.hom` is the composite of the chart with the structural morphism. No
  surjectivity or quasi-compactness is imposed on an individual chart, and no
  global finite atlas is chosen. Every existing atlas is among these tests, so
  the condition is not vacuous.
- Topological Krull dimension at most one:
  `hdim : topologicalKrullDim (Point X.obj.obj) ≤ 1`. This uses Mathlib's
  `WithBot ℕ∞`-valued dimension and the project's actual field-valued point
  classes and final topology for all étale scheme-source maps. The atlas
  criterion is `points_atlas_isOpen_iff` in the already recorded proof
  dependency `AlgebraicSpaceEtaleOpenImage`.
- Representability by a K-scheme:
  `∃ U : Over (Spec (.of K)), Nonempty (yoneda.obj U ≅ X.obj.obj)`.
  The witness includes its morphism to Spec K. The presheaf isomorphism is on
  all schemes over Spec K, so it identifies precisely the original space over
  the field, including all nonreduced scheme tests.
- No quasi-compactness, properness, reducedness, connectedness, or nonemptiness
  hypothesis is present. These are the node's explicit exclusions, not extra
  conclusions about the representing scheme.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs` (Mathlib match of def-weil-field).
- `AlgebraicGeometry.Spec` and `Spec.map`, `Mathlib.AlgebraicGeometry.Scheme`.
- `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicSpace.IsRepresentableWith`,
  `AlgebraicSpace.IsEtale`, `AlgebraicSpace.IsAlgebraicSpace`,
  `Sheaf.AlgebraicGeometry.AlgebraicSpace`. Their full definitions and docstrings
  were read, including the atlas existence and scheme pullback squares.
- `AlgebraicGeometry.IsSeparated`, `Mathlib.AlgebraicGeometry.Morphisms.Separated`,
  supplied by the recorded `Mathlib.AlgebraicGeometry.Morphisms.Proper` import;
  `IsClosedImmersion` is its scheme diagonal condition.
- `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `topologicalKrullDim`, `Mathlib.Topology.KrullDimension`.
- `AlgebraicGeometry.AlgebraicSpace.Point`, `PointRepresentative`, `schemePointMap`,
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`, reused through
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology` and its instance
  `AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace`.

The item's `stmt_deps` gains the existing, landed definition node
`def-a1-space-point-topology`, under brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED
NODES). Its node statement and recorded module were read. This is an explicit
statement dependency for the topology already called for in the node's prose;
it does not correct or change that prose. No new node or dependency repair is
needed. All other node fields are preserved except `lean`.

Proof dependencies that already have declarations are imported with plain
`import`, as required by stages/2-statements §3.7:
`Mathlib.AlgebraicGeometry.Noetherian` (local Noetherianity and local-finite-type
stability), `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage`,
`WeilConjectures.AlgebraicGeometry.Dimension`,
`Sheaf.AlgebraicGeometry.GroupoidScheme`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability`.
The five finite-cover/groupoid/descent proof nodes with no recorded declarations
cannot yet contribute imports; their uses remain explicitly named in the
proof docstring. These are proof-only inputs and are not needed to type the
statement. The other proof inputs shared with statement dependencies already
have public imports.

Edge cases checked mathematically before writing:

- The empty space has empty point type and dimension bottom, hence satisfies
  the dimension bound. Its representing witness is the empty scheme over K;
  the conclusion imposes no nonemptiness on that scheme.
- Dimension zero is included by `≤ 1`, rather than an equality or pure-dimension
  condition. Disconnected mixtures of zero- and one-dimensional components
  are also included.
- An arbitrary disjoint union of curves can be non-quasi-compact. All hypotheses
  and the conclusion still make sense without a finite atlas or compactness
  instance; the proof works locally and glues.
- Nilpotent thickenings are not excluded: no reducedness or integral condition
  occurs. Scheme tests in the conclusion are unrestricted schemes.
- K, schemes, and chart fields share the existing `Scheme.{u}` size convention.
  `Point X.obj.obj` lives in `Type (u+1)` and Mathlib's topological dimension is
  universe-polymorphic, so no equality of unrelated universes is imposed.
- Separatedness is relative to Spec K rather than an accidentally chosen
  absolute presheaf category; the `Over` base in every test ensures this.

Searches made on 2026-10-22:

- `msearch.py ... leanfinder` query: "A separated algebraic space locally of
  finite type over a field of topological Krull dimension at most one is
  representable by a scheme". Eight hits, all scheme-level separatedness,
  affineness, or integrality facts; none states the algebraic-space result.
- `msearch.py ... leansearch` query: "A separated algebraic space locally of
  finite type over a field with dimension at most one is a scheme". Eight
  hits, scheme definitions and separatedness/properness properties; no match.
- `msearch.py ... loogle` query:
  `AlgebraicGeometry.AlgebraicSpace, topologicalKrullDim`. Zero hits; Mathlib's
  index has no `AlgebraicGeometry.AlgebraicSpace` identifier.
- `msearch.py ... grep` query `AlgebraicSpace|schematicLocus`, subdirectory
  `AlgebraicGeometry`. Zero Mathlib hits.
- `rg -n` of `AlgebraicSpace|isRepresentable.*[Dd]im|[Dd]im.*isRepresentable`
  in `lean/WeilConjectures` found only a Hilbert-presheaf representability
  theorem, which has different hypotheses and objects. The literal node id
  search in that tree found no hit.
- Searches in `lean/Sheaf/AlgebraicGeometry` found
  `exists_scheme_of_separated_etale` and
  `exists_scheme_of_separated_locally_quasi_finite`. Both require relative
  dimension-zero morphisms, so neither is this theorem. The proper-curve
  automorphism module cites this node in its proof but does not state it.
- Searches of Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `separated_space`, `separatedSpace`,
  `scheme_of_dim`, `representable_of_dim`, and the proposed exact declaration
  name found no existing declaration of the item.
- Existing project searches located and reused `Point`, `pointTopologicalSpace`,
  `IsRepresentableWith`, and `IsEtale`; these were not copied or redefined.

No statement dispute or source fault was found. The source's local-Noetherian
hypothesis follows from the node's local finite type over the field. The node
is not a blueprint unit's own statement, and no statement correction was made.

Validation: the prescribed `scompile.py Q139
lem-sfb-separated-space-dimension-one-scheme <file>` compiled the sandbox form
and final module form cleanly, with no compiler diagnostics (7.6 s and 17.1 s).
Only the single named theorem has a postponed proof. Every universe and variable
is explicitly bound; `set_option autoImplicit false` is present. Maximum Lean
line length is below 100 characters.

## Second reading by Q139

This is the author's second reading; independent mathematical review belongs to
the maintainer, as required by the dispatcher brief. I reread the item JSON,
the displayed theorem, and Tag 0ADD. `Field K` renders the unrestricted field;
`AlgebraicSpace (Spec (.of K))` retains the original nonschematic objects;
`IsRepresentableWith` applied to the product diagonal renders exactly
separatedness; all étale charts are tested by `hlft`; `Point` carries the landed
atlas topology in `hdim`; and the `Over` witness with its Yoneda isomorphism
renders scheme representability over K. In particular no atlas source is
mistaken for X in the dimension bound. The bottom dimension and empty witness
retain the empty case, and no hidden finite-type, properness, reducedness, or
connectedness binder occurs. I checked that the five-step proof docstring
records every step of the node's proof and that public versus proof imports
follow the prescribed distinction. The only record adjustment beyond `lean`
is the allowed addition of the already landed topology node to `stmt_deps`;
no mathematical mismatch required a correction.
