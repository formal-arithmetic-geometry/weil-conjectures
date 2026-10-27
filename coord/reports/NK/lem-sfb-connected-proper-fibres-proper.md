## Worker report

Module: `Sheaf.AlgebraicGeometry.ConnectedProperFibresProper`.
Main declaration: `AlgebraicGeometry.AlgebraicSpace.proper_of_flat_of_connected_proper_geometricFibres`.
This is stage 2: its proof is `sorry`. The only other declaration,
`geometricPointSpaceMap`, constructs the canonical Yoneda map of the given field-valued
point, using the actual `Scheme.fppfTopology.over S` representable-sheaf functor. It has
real data and no postponed data or proof. No new definition node is necessary for this
map belonging to the theorem's geometric-fibre construction.

Clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| S is a scheme | `{S : Scheme.{u}}` |
| S is locally Noetherian | `[IsLocallyNoetherian S]` |
| Y is an algebraic space | `(Y : AlgebraicSpace S)` |
| h : Y → S | `h : Y ⟶ schemeSpace (Over.mk (𝟙 S))`; the target is the actual representable sheaf of the base scheme |
| h is separated, with closed-immersion diagonal | `hsep : MapIsSeparated h`, the recorded closed-diagonal representability test |
| h is flat on étale charts | `hflat : MapIsFlat h` |
| h is quasi-compact | `hqc : MapIsQuasiCompact h.hom.hom` |
| h is quasi-separated | `hqs : MapIsQuasiCompact (pullback.diagonal h.hom.hom)` |
| h is locally of finite presentation on étale charts | `hlfp : MapIsLocallyOfFinitePresentation h`; together with the preceding two rows this is finite presentation |
| Every geometric point Spec Ω → S | `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (barS : Spec (.of Ω) ⟶ S)` |
| Its geometric fibre | `enlargedFibreProduct (geometricPointSpaceMap barS) h`, the actual sheaf pullback Spec Ω ×_S Y, with the existing algebraic-space property |
| Fibre is nonempty and connected | `ConnectedSpace (Point (...).obj.obj)`; Mathlib's class extends `PreconnectedSpace` and has `toNonempty : Nonempty ...` |
| Fibre is proper over Ω | `MapIsProper (enlargedFibreProductFst (geometricPointSpaceMap barS) h)`, the projection to Spec Ω |
| Therefore h is proper | `MapIsProper h` |
| Proper means separated, finite type and universally closed after every base change | The existing `MapIsProper` is precisely `MapIsSeparated ∧ MapIsFiniteType ∧ MapIsUniversallyClosed`; universal closedness quantifies over every algebraic-space base change |

The reversal of pullback factors makes the existing first-projection construction project
onto Spec Ω. This is canonically the same fibre as Y ×_S Spec Ω. All spaces remain over S;
a morphism of such spaces to Spec Ω supplies its Ω-structure, so this represents the
properness of the fibre over Ω, including arbitrary further base changes.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and its
  actual fppf-sheaf, representable-diagonal and atlas definition; `IsEtale` and
  `IsRepresentableWith` underlying the morphism tests were read in full.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points use the
  recorded inline field/morphism form. Also read `Scheme.SpecToEquivOfField` in
  `Mathlib.AlgebraicGeometry.ResidueField` to check its point/residue-field interpretation.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, the every-affine-open
  class equivalent to the recorded affine-Noetherian-cover formulation.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsSeparated`,
  `MapIsFlat`, `MapIsLocallyOfFinitePresentation`, `MapIsProper`, and their definitions
  through `MapIsLocally`, `MapIsFiniteType`, `MapIsUniversallyClosed`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact`, using affine test
  schemes, actual pullback presheaves and compact point spaces. No curve-family predicate
  or dimension restriction is used.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `Point`, with field-valued
  representatives modulo common-extension equality.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`, the
  existing final topology of étale scheme charts.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `enlargedFibreProduct`, `enlargedFibreProductFst`. Their full definitions were read:
  these are representable sheaf data and the chosen sheaf pullback, with only their
  uniquely specified Prop-valued algebraic-space properties postponed upstream.

The statement dependencies cite the following construction owners
`def-trf-scheme-algebraic-space`, `def-sfb-space-sheaf-fibre-product`,
`def-sfb-proper-curve-moduli`, `def-a1-algebraic-space-point-classes`, and
`def-a1-space-point-topology`. The fibre-product definition node is new and records the two unchanged existing declarations; all other owners are reused. No dependency module is added.
Their dependency closures were checked to exclude a path back to this item.
The item's statement, proof and proof-dependency lists are unchanged.

The existing proof dependencies are imported (plain imports):
`Sheaf.Paper.StrictHenselizationFunctoriality`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`,
`WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover`,
`WeilConjectures.Mathlib.RingTheory.Henselian`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen`, and
`Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`.
Four proof dependencies have no recorded Lean declaration yet, so there is no module to
import for `lem-sfb-space-proper-strict-local-test`,
`lem-sfb-space-flat-proper-fp-locality`, `lem-sfb-space-proper-fpqc-descent`, and
`lem-sfb-space-henselian-proper-clopen-lift`. They introduce no object needed by this
statement; they remain in the natural-language proof for stage 3.

Edge cases checked before writing: an empty base is allowed, with vacuous geometric-point
quantification and necessarily empty Y. Over a nonempty base an empty fibre fails
`ConnectedSpace`, as required by the explicit nonemptiness hypothesis. Disconnected
proper fibres also fail the hypothesis. A point fibre satisfies the topological hypothesis;
there is no dimension, reducedness, smoothness, positive-characteristic, algebraic-extension
or irreducibility restriction. Non-Noetherian sources are not assumed away. The universe
`u` is shared by the base schemes, test fields and big-site tests; an independent smaller
universe of test fields has not been introduced. There are no auto-bound variables,
file-local notations, auxiliary instances, or hidden `let` expressions in the signature.
The quasi-separatedness clause remains explicit even though separatedness implies it.

Searches on 2026-10-23 (raw msearch results are in the sandbox searches.jsonl):

- LeanFinder: "A separated flat finitely presented morphism of algebraic spaces with
  nonempty connected proper geometric fibres is proper". Eight hits, all scheme-only
  properness definitions/permanence or the underlying proper topological map; no match.
- LeanSearch: "A separated flat finitely presented morphism of algebraic spaces with
  connected proper geometric fibres is proper". Eight scheme properness declarations;
  no criterion for algebraic spaces.
- Loogle: `AlgebraicGeometry.IsProper, AlgebraicGeometry.Flat`. Zero hits.
- msearch grep: `proper.*connected.*(fibre|fiber)|(fibre|fiber).*proper.*connected`.
  Zero Mathlib hits.
- `rg` of the same pattern, `proper_of.*flat` and `MapIsOfFinitePresentation` in the
  project's `lean/WeilConjectures` and `lean/Sheaf`: only references and results assuming
  properness or concerning unrelated scheme cohomology/Stein factorizations; no match.
- `rg` of the item id in `lean/WeilConjectures`: no result; the upstream-name index
  also has no matching connected/proper theorem.
- Source searches found `schemeSpace`, `enlargedFibreProduct`, their projection, the
  morphism-property predicates and point topology; these are all reused.

The local Stacks sources for Tag 0CWI (henselian proper-clopen lifting) and Tag 042S
(flat locally finitely presented implies universally open) were read. Their hypotheses
agree with steps 3 and 4 of the supplied proof. The declaration docstring carries all
five proof steps and the empty-base case. No statement fault or dispute was found.

Validation: the prescribed `scompile.py NK lem-sfb-connected-proper-fibres-proper`
compiled the file in sandbox mode (5.7 s) and with its library module name (9.1 s),
with no errors or non-sorry warnings. Final preflight and delivery also compile the file.

## Second reading by NK

The dispatcher explicitly forbids starting other agents and delegates the independent
reading to the maintainer; this section records a second self-check, not a claim of
an independent worker review. I reopened the node and the final signature. The base is
locally Noetherian but not assumed affine or quasi-compact. The source is an algebraic
space, not restricted to a scheme. The morphism has exactly the separatedness, flatness
and three finite-presentation clauses. Geometric points range over arbitrary algebraically
closed fields in the site universe. The fibre uses the actual canonical map and actual
sheaf pullback; its first projection goes to the field spectrum. `ConnectedSpace` checks
both nonemptiness and connectedness in the existing atlas topology, while `MapIsProper`
retains all three properness clauses and all base changes. The conclusion is the same
properness predicate for h. No mismatch or source statement correction was needed.

## New nodes

`def-sfb-space-sheaf-fibre-product` owns the existing definitions
`AlgebraicGeometry.AlgebraicSpace.enlargedFibreProduct` and
`AlgebraicGeometry.AlgebraicSpace.enlargedFibreProductFst` in
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`. It defines the actual fppf-sheaf
pullback bundled as an algebraic space, together with the first projection. This is
Stacks 04T9 and the following fibre-product lemma in spaces.tex, also used in 03G2.
For every test scheme the sections are matching pairs; the first projection forgets
the second component. No extra hypothesis on f or g is imposed. Empty spaces and
identity maps are allowed, and no atlas is chosen. Its `lean.statement` is the verbatim
`def enlargedFibreProduct` signature; its `lean.declarations` lists both definitions.
The data are `Limits.pullback f.hom g.hom` and `Limits.pullback.fst f.hom g.hom`;
the cited theorem supplies only a Prop-valued algebraic-space property.

LeanSearch and LeanFinder for "Fibre product of algebraic spaces is the sheaf pullback
with the canonical first projection" each returned eight scheme/topological pullback
hits. Mathlib grep for `enlargedFibreProduct|AlgebraicSpace.*pullback|pullback.*AlgebraicSpace`
returned zero hits. Project source search found the two existing definitions only in
EnlargedEtaleRingedSite. Upstream WeilConjectures has no match. DAG searches found
only theorem records containing their declaration names; definition nodes mentioning
fibre products do not own this construction. The blueprint ownership/ancestor searches
were repeated: ancestor is null, and the inherited via chain is retained with this
item prepended. The new node stores the raw search records. Existing declarations
are reused with `existing: true`; no duplicate module is delivered.

## Repair of returned head 4c5d7549a45c

H2 is repaired by the new definition owner above. The item's `stmt_deps` now cites
`def-sfb-space-sheaf-fibre-product` instead of
`lem-trf-space-enlarged-etale-ringed-site-model`. `schemeSpace` remains owned by
`def-trf-scheme-algebraic-space`. The current repository item still has no Lean record;
its fields agree with the retained packet except the authorized `lean` and `stmt_deps`
changes. The Lean module remains byte-identical to the saved returned packet (SHA256: 16b057fea3cbc26b957e9c6631eb026a7fdcdcf41cfd2bb9a1afba22bbe079e6).
The initial saved-packet dry run passed, but does not discharge the independent H2 return;
the repaired packet is compiled and dry-run again before delivery.

Second self-check of the repair: I reopened both definitions, their docstrings and the
new node. Matching-pair sections and componentwise restriction give the sheaf pullback,
and `Limits.pullback.fst` gives exactly its first projection. The new owner has only
definition dependencies, no theorem proof dependencies, and no path back to this item.
No hypothesis, conclusion, source statement, proof or proof dependency was changed.
The independent mathematical review remains the maintainer's, as required by the
dispatcher; no other agents were started.

Repair validation: `scompile.py` recompiled the unchanged item cleanly (sandbox 4.9 s,
library name 8.3 s). The first repaired-packet preflight required the current schema
field `import_flags` on the new node; added the empty list, then reran the dry run.
