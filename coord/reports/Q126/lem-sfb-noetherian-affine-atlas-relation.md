## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianAffineAtlasRelation` states
`AlgebraicGeometry.AlgebraicSpace.noetherian_affine_atlas_relation`, with its whole
proof postponed by `sorry`. No definition or auxiliary theorem is introduced.

The inherited BLOCKED ending concerned a stage-1 split already reviewed under Q20.
The live node has that stage-1 review but no Lean record; queue.tsv lists stage 2.
The 2026-10-22 stage-handoff rule in brief-stage2.md explicitly authorizes this work.
No repair note for this item is present.

Clause-by-clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`; `(X : AlgebraicSpace S)` is the
  given algebraic space. There is no assumption on the base or separatedness of X.
- Locally Noetherian is `hln : ∀ T : X.EtaleSite,
  IsLocallyNoetherian (X.etaleForget.obj T)`. These are all representable étale
  scheme charts, including non-surjective charts, exactly as the node specifies.
- Quasi-compact is `hqc : CompactSpace (Point X.obj.obj)`, using the existing point
  quotient and topology, not a replacement topology.
- Absolute quasi-separatedness is `hqs`: the point space of `Limits.pullback a b`
  is compact for every pair of affine scheme tests V,W mapping to X. This is the
  affine-test formulation of the quasi-compact absolute diagonal, also used by the
  existing `coherentSubobjects_filtered_colimit` and explicitly in the sibling
  `lem-sfb-qcqs-space-fibre-product`. It is not separation of X over S. The fibre
  products of S-compatible maps are the same scheme fibre products over X; the
  ordinary affine-test diagonal criterion applies in this base-relative encoding.
- The atlas is `(U : Over S)` and `(p : yoneda.obj U ⟶ X.obj.obj)`; `hp : IsEtale p`
  includes representability, `hsurj : IsSurjective p` is the recorded representable
  surjectivity definition, and `haff : IsAffine U.left` means isomorphic to a ring
  spectrum (the canonical `U.left.isoSpec`).
- `IsNoetherian U.left` is the first conclusion. The existential R and maps t,s are
  schemes over S. `IsPullback (yoneda.map t) (yoneda.map s) p p` identifies them as
  precisely the representing scheme U x_X U and its projections; no unrelated
  scheme or arbitrary equivalence is substituted. This is a universal-property
  presentation of the fibre product, with its usual unique-isomorphism invariance.
- `IsNoetherian R.left` gives the second Noetherian conclusion. Mathlib's scheme
  definition is locally Noetherian and compact, as required for schemes.
- The eight explicit conjuncts `Etale`, `Flat`, `QuasiCompact`, `QuasiSeparated` on
  s.left and t.left render every property for both projections. Mathlib
  QuasiCompact means compact inverse images of compact opens (equivalently affine
  opens); QuasiSeparated means QuasiCompact of the relative diagonal.
- The final existential supplies e,i,c, with c's domain exactly
  `Limits.pullback s.left t.left`. `Scheme.IsGroupoid s.left t.left e i c` asserts
  every source, target, unit, inverse and associativity law in the recorded node.
  Here t is the first projection and s the second. This does specify the usual
  maps: the pullback square makes the two projections jointly monic; the groupoid
  equations force e to have components (id,id), i to swap the components, and c to
  have first component from the first arrow and second component from the second.
  Thus no arbitrary groupoid operations survive this formulation.

Recorded dependencies used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `IsSurjective`, `EtaleSite`, `etaleForget`; these are exposed by the point module.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`;
  `IsPullback` from the accompanying pullback-square interface. Pullbacks of
  schemes are provided by `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidLaws`: `Scheme.IsGroupoid`, including its
  full test-scheme laws; no duplicate groupoid predicate is introduced.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `Point` and
  `pointTopologicalSpace`. Its already-landed node is added to stmt_deps because
  its topology now appears in the signature. It already belonged to proof_deps.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated` and the
  imported `QuasiCompact` class.

The available proof dependencies are imported: ChartwiseEtalePermanence's
`chartwise_etale_permanence`, the point topology, groupoid laws, affine scheme
compactness/quasi-separatedness, and scheme pullbacks including `pullbackSpecIso`.
`lem-sfb-qcqs-space-fibre-product` and `lem-sfb-space-qcqs-permanence` have no Lean
record or match yet, so no unavailable proof-only module is imported. Neither is
needed to state this theorem. The full accepted four-step proof plan is in the
theorem docstring, including the scheme/space point-topology identifications.

Edge cases checked: empty X and empty affine U/R are allowed; no nonemptiness is
assumed. For X = Spec k and U two disjoint copies, all four arrows and the pair
composition have the stated orientation. The doubled affine line is allowed:
R need not be affine or separated over the base. The locally Noetherian
non-quasi-separated quotient A^1/Z is excluded by hqs, as Stacks 03EA requires.
The single explicit universe u is the existing scheme/algebraic-space convention;
no independent smaller test universe or coefficient restriction is introduced.

Searches made using the prescribed msearch.py wrapper:

- leanfinder: "The relation scheme of an affine etale atlas of a Noetherian
  algebraic space is Noetherian and has etale flat quasi compact quasi separated
  projections"; eight scheme-only hits, including IsNoetherian,
  IsLocallyNoetherian and noetherianSpace_of_isAffine; no atlas statement.
- loogle: "AlgebraicGeometry.IsNoetherian, AlgebraicGeometry.Etale"; zero hits.
- grep: "IsGroupoid|AlgebraicSpace", subdirectory AlgebraicGeometry; zero hits.
- leansearch: "Noetherian algebraic space affine etale atlas relation scheme
  groupoid"; eight scheme results (Noetherianity, affine covers, Etale), no match.
- rg over project WeilConjectures and Sheaf for locally-Noetherian/atlas/groupoid
  expressions: found the reusable Scheme.IsGroupoid and the coherent-union
  Noetherian hypotheses, but no theorem asserting this node. Searching both roots
  for this node id and the chosen declaration name gave no match; the upstream
  name index also has no match for the chosen name.

Sources opened locally: spaces-properties.tex definition-noetherian (03EA),
lemma-quasi-compact-affine-cover (03H6), and absolute definition-separated;
spaces-cohomology.tex lemma-directed-colimit-coherent (07UV). The latest blueprint
is not itself stating this auxiliary atlas theorem; its source is this Stacks
prerequisite. No statement correction, new node, dependency module or disputed
statement is required.

Validation: scompile.py compiled this module in sandbox and library mode cleanly
(17.0 and 5.5 seconds respectively). The final import list is compiled again in the
required dry run. Every variable and universe is explicitly bound.

## Second reading by Q126

Author's delivery self-check only; independent review belongs to the maintainer.
I reread the live node, dependency definitions, source and complete Lean signature.
All three Noetherian hypotheses and all three atlas hypotheses are present. Both
Noetherian conclusions, all eight projection properties, and the full existing
groupoid predicate are present. The pullback-square conjunct ties R,s,t to p;
its joint monicity makes the groupoid operations canonical. The s/t orientation
matches SchemeGroupoidLaws. No separatedness or base compactness was added, no
empty case dropped, and no data are postponed. Only lean and the authorized added
statement dependency change. The initially omitted explicit proof-only Mathlib
imports were added; no mathematical mismatch was found in the final statement.
