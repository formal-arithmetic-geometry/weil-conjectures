## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedSpaceUnionPushout` states
`AlgebraicGeometry.AlgebraicSpace.closed_union_isPushout`, with a single postponed
proof and no new definitions. The item's `lean` record is supplied and its
`stmt_deps` gains the landed `def-sfb-space-module-structure-map` as requested
in the H2 return. The accepted stage-1 split is preserved.

The inherited BLOCKED ending confused a stage-1 merge with completion of stage 2.
The current node has its stage-1 reviewed split but no Lean record. I read the
handoff in coord/brief-stage2.md §0, the ledger entry at 12:19 and NU's stage-1
report: stage 2 remains to be done. There is no released repair note for this item.

Hypothesis and clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`; the ambient algebraic space over
  that same base is `X : AlgebraicSpace S`. All morphisms below are morphisms in
  this category, so all are over S. The existing size convention is retained.
- `A B : ClosedSubspace X` are the closed subobjects with their complete scheme
  structures. Their inclusions are `A.val.arrow` and `B.val.arrow`; their source
  algebraic spaces are `(A.val : AlgebraicSpace S)` and similarly B.
- The node identifies I and J by the closed-ideal correspondence, which identifies
  each with the kernel of the canonical structure map. Accordingly `hIJ` says,
  for every `V : X.EtaleSite` and every section `s` of O_X on V, if both structure
  maps send s to zero then s is zero. Kernels of module-sheaf maps are sectionwise
  kernels. Thus this is exactly I intersect J = 0 as subsheaves. It does not assert
  only set-theoretic coverage or discard nilpotents. The quasi-coherence of these
  kernel ideals is supplied by the recorded correspondence theorem for these
  closed subspaces; it is not an extra hypothesis. A first attempt using the
  abstract subobject infimum caused typeclass search to request an unavailable
  complete lattice; the equivalent sectionwise condition avoids that instance.
- `E`, `a`, `b` and `hE : IsPullback a b A.val.arrow B.val.arrow` specify E as the
  fibre product A times_X B, with both projections. This quantifies over any
  presentation of the uniquely determined product; hE is the meaning of the
  node's definition of E, rather than an additional geometric restriction. The
  fibre-product node supplies existence. No arbitrary uncharacterized map is used.
- The conclusion `IsPushout a b A.val.arrow B.val.arrow` is the colimit universal
  property for precisely this cocone: for each H and maps f and g with
  `a ≫ f = b ≫ g` it gives a unique h with `A.val.arrow ≫ h = f` and
  `B.val.arrow ≫ h = g`. Mathlib's IsPushout contains a nonempty IsColimit witness
  for the PushoutCocone, so both existence and uniqueness are included.
- No Noetherian, separated, quasi-compact, reducedness or nonemptiness predicate
  appears. There is no chosen atlas or finite-cover assumption in the statement.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `EtaleSite`, `structureSheaf`, and `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace`: `ClosedSubspace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedIdealCorrespondence`:
  `closed_ideal_correspondence`; its kernel clause identifies exactly the two
  ideals in the hypothesis.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap`:
  `AlgebraicGeometry.AlgebraicSpace.moduleStructureMap`, recorded by the directly
  cited landed node `def-sfb-space-module-structure-map`, supplies the canonical
  structure-module map. Its module is explicitly publicly imported. No new copy
  of the map or ideals is made.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, including the full-subcategory universal property.
- `Mathlib.CategoryTheory.Limits.HasLimits`: the colimit interface and IsColimit;
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic` and its Defs
  module give `CategoryTheory.IsPullback` and `CategoryTheory.IsPushout`.

The full proof in the theorem docstring follows all five DAG steps, including the
empty-fibre affine-neighbourhood case in the Ferrand comparison, compatibility on
scheme overlaps, and equality detection after descent. Plain proof imports include
the recorded scheme-theoretic-union and atlas-descent modules, as well as Mathlib
closed-immersion/integral/separated/universally-closed, affine-basis and etale
composition inputs. The scheme closed-union pushout and Ferrand agreement nodes
currently have no recorded Lean module, so no nonexistent import was invented.

Sources read locally: Stacks spaces-pushouts.tex, lemma-pushout-fpqc-local
(Tag 0GFQ), and lemma-pushout-along-closed-immersion-and-integral (Tag 0EDP);
morphisms.tex, lemma-scheme-theoretic-union (Tag 0C4J). The first source identifies
local and overlap colimits as the descent criterion; the latter two provide the
scheme-chart pushout and its algebraic-space target universal property.

Edge cases checked before writing: X empty; A or B empty (forcing the other
kernel ideal to be zero); A=X or B=X; both equal X; disjoint branches; and
nonreduced schemes. In R=k[e,x,y]/(e^2,xy), I=(x), J=(y), their intersection is
zero and the common nilpotent e survives on both branches. In R=k[e]/(e^3),
I=(e), J=(e^2), the section e^2 witnesses failure of hIJ, correctly excluding
that thickening. A universal statement on empty charts is harmless: their
structure-section rings are zero, and the empty pushout universal property holds.

Searches actually run via msearch.py, with outputs kept in searches.jsonl:

- leanfinder: `A closed scheme theoretic union of two algebraic subspaces is a
  pushout along their intersection`: eight hits, concerning open scheme gluing,
  coproducts and open intersections; none states the algebraic-space result.
- loogle: `"IsPushout", "IsClosedImmersion"`: zero hits.
- grep, AlgebraicGeometry: `closed.*union|union.*closed|AlgebraicSpace`: three
  Mathlib files (IrreducibleComponent, Smooth, Properties), no exact match.
- leansearch: `Closed algebraic subspaces with zero intersection of defining
  ideals form a categorical pushout along their fibre product`: eight hits,
  algebra pushouts, binary coproducts and a scheme pullback characterization,
  no exact match.
- rg of both lean/WeilConjectures and lean/Sheaf for the exact node id and for
  closed-union/pushout terminology: no existing declaration of this result;
  SchemeTheoreticUnion only constructs the scheme union. Other hits involve
  open gluing, topological closed unions, or citations in proof docstrings.

No new node, dependency repair, statement correction or statement dispute.
Compilation uses scompile.py exclusively; dry-run and final delivery use deliver2.py.

## Second reading by NQ

I reread the node and module after elaboration. This is a self-check, not a claim
of an independent agent review: the dispatcher brief forbids starting other
agents and delegates the independent review to the maintainer.

Checked the exact binders against the statement: S and X are arbitrary; A and B
are the existing closed subobjects, not underlying closed sets; the two section
maps have common domain O_X and kernels equal to the prescribed defining ideals;
quantifying over every chart is necessary and present. The fibre product is
characterized, with arrows in the right order, and IsPushout uses exactly these
arrows and both original inclusions. Its colimit witness tests all algebraic-space
targets over S, not merely schemes, affine targets or separated targets. There
are no extra geometric conditions. The only implementation repair replaced the
abstract lattice expression with its sectionwise equivalent and wrapped an
oversized docstring line. No mathematical clause changed.


## Returned delivery repair (H2)

Return read: L's independent stage-2 review of immutable head a6efd7be4308,
2026-10-24 17:20 UTC. The reviewer accepted the mathematics and identified one
missing direct statement dependency: hIJ uses moduleStructureMap.

Added `def-sfb-space-module-structure-map` to the item's `stmt_deps` and added
`public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap` to
the Lean module. Read that node's landed record and the full canonical-map
declaration and docstring. The report now lists that dependency directly.
Compared the retained sandbox with current main: before repair only `lean`
differed. Verified the node's `statement`, `proof` and `proof_deps` remain
identical to both the returned work and current main. The theorem signature
and proof are byte-for-byte unchanged. No H7 correction is introduced.

Second reading of this repair: both occurrences of moduleStructureMap in hIJ
now have their owning definition node directly cited, and its recorded module
is explicitly publicly imported. All mathematical clause checks above remain
applicable. The delivery wrapper supplies the current-main rebase; compilation,
dry-run and delivery are repeated for this changed packet.
