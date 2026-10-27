## Worker report

The module `Sheaf.AlgebraicGeometry.SteinSubmersiveReducedDescent` states
`CategoryTheory.stein_submersive_reduced_descent`, with its proof `sorry`.
No definitions or other theorem obligations are added. The docstring contains
all seven proof steps from the node, grouping the graph and schematic-image steps.
The two proof dependencies have no recorded Lean declarations, so there are no
corresponding proof imports available.

Hypothesis and conclusion correspondence:

- The field is `(k : Type u) [Field k]`. The base everywhere is `Spec (.of k)`.
- The algebraic stack is `F : BasedCategory.{v, w} (Over (Spec (.of k)))`, with
  `hF : IsAlgebraicModuliStack F`. No DM or finite-type condition is used.
- `V : AlgebraicSpace (Spec (.of k))` is the given space over k.
  `p : BasedFunctor F (discreteModuli V.obj.obj)` is its given k-morphism.
- Quasi-compactness is `hqc : IsQuasiCompactAlgebraicModuliMap ... p`, using the
  same universe parameters as `IsAdequateModuliSpace`: the test universes include
  both endpoint universes and the scheme universe. Quasi-separatedness is
  `hqs : IsQuasiSeparatedAlgebraicModuliMap p`, the existing representable
  relative-diagonal qcqs predicate. This imposes no atlas choice.
- Universal submersiveness is `hsub`: for every algebraic space T and morphism
  `g : T ⟶ V`, the actual second projection of the 2-fibre product induces a
  surjective point map, and a target subset is open iff its inverse image is
  open. These are the existing atlas topologies. The iff includes continuity
  as well as the quotient topology condition. This is literally the conclusion
  interface of `adequate_moduli_universally_submersive`, without assuming adequacy.
- `hstein : IsIso (moduliStructureMap hF.1.1 V p)` is the canonical structure map
  on V's small etale site, not an arbitrary isomorphism of sheaves.
- Z is any algebraic space over k. `hZ` says its actual diagonal is representable
  by scheme immersions, using `AlgebraicSpace.IsRepresentableWith` and
  `IsImmersion q.left`. This is precisely a locally separated target.
- The first conjunct says that if the two composites of a,b with p are
  2-isomorphic then a = b. This is injectivity on morphism classes; natural
  transformations between the algebraic-space sheaves themselves are the
  morphisms V → Z and need no additional quotient.
- The second conjunct, for every `h`, equates existence of a factorization
  `Nonempty (ModuliTwoIso (p.comp (discreteModuliMap a)) h)` with compatibility
  on the reduced self fibre product. The latter is expressed without choosing
  a reduction object: every reduced scheme T and every map `t : h_T → F ×_V F`
  gives 2-isomorphic composites of the actual first/second projections with h.
  Every such map factors through R = (F ×_V F)_red: pullback kills its nilradical.
  Conversely take a smooth scheme atlas of R, whose scheme is reduced. Its map
  into F ×_V F is one of the tests; equality there detects equality of maps
  R → Z by sheaf descent. Thus the condition is equality on the full reduced
  substack, not merely agreement at field-valued points. This equivalent test
  formulation introduces no missing notion or construction needing a new node.
- There is no hypothesis on the geometric fibres of p.

Dependencies used:

- `Mathlib.Algebra.Field.Defs`: `Field` (the def-weil-field Mathlib match).
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`:
  `CategoryTheory.moduliStructureMap`, using the actual small-etale direct image.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`:
  `CategoryTheory.IsQuasiCompactAlgebraicModuliMap`,
  `CategoryTheory.IsQuasiSeparatedAlgebraicModuliMap`.
- `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`:
  `CategoryTheory.moduliPointTopologicalSpace`, owned by
  `def-sfb-stack-point-topological-space` (existing:true, same module).
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `CategoryTheory.ModuliPoints`, `CategoryTheory.moduliPointMap`, owned by
  `def-sfb-dm-stack-morphism-properties`; available through the public import above.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`:
  `CategoryTheory.moduliTwoFiberSnd`; its existing groupoid framework supplies
  `BasedCategory`, `BasedFunctor`, `discreteModuli`, `discreteModuliMap`,
  `ModuliTwoIso`, `moduliTwoFiberProduct`, `moduliTwoFiberFst`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`, the
  recorded declaration of def-pc-reduced-scheme.
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `AlgebraicGeometry.IsImmersion`.

The five additional statement dependencies are already landed definition nodes for
the qcqs predicates, stack point topology, point sets/maps, second projection, and
reduced schemes.
Their statements, records and declaration signatures/docstrings were read.
No dependency record is repaired. The informal mathematical statement is unchanged;
the H2 repair below adds the two point-definition owner citations.

Edge cases checked: empty V forces empty U by surjectivity; both injectivity and
factorization then have their usual empty-source interpretation. Empty Z is not
excluded. The empty reduced test scheme is included, as are arbitrary nonempty
reduced schemes. Nonreduced U and V are allowed: compatibility tests only the
reduced relation, while the full structure-sheaf isomorphism retains the nilpotent
information needed for descent. No reducedness of U or V, separatedness of Z,
Noetherian hypothesis, finite-type hypothesis, or characteristic restriction is
added. Stack morphism/object universes v,w remain independent of scheme universe u.

Searches performed (2026-10-24):

- msearch.py leanfinder: "Universally submersive Stein morphism of algebraic stacks
  descends maps agreeing on the reduced fibre product to locally separated algebraic
  spaces". Eight hits, concerning dominant scheme maps and separated targets;
  none states this stack/algebraic-space result.
- msearch.py leansearch: "Maps to a locally separated algebraic space descend along
  a universally submersive morphism inducing an isomorphism of structure sheaves".
  Eight hits, concerning locally ringed spaces, separated morphisms and flat descent;
  no match.
- msearch.py loogle: "IsQuotientMap, IsImmersion, QuasiCompact, QuasiSeparated".
  Zero hits (unknown identifier IsQuotientMap).
- msearch.py grep: `Stein|[Uu]niversally[Ss]ubmersive|[Rr]educed[Ss]tack` in
  Mathlib/AlgebraicGeometry: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for the item id and
  `stein_submersive`: only the downstream AdequateLocallySeparatedUniversality
  docstring mentions the item. No existing declaration states it.
- rg in lean/Sheaf for submersiveness, stack qcqs, point topology and reduction
  located the reused declarations above. DAG searches confirmed their owning nodes.
  No existing reduction object was found; none is needed for the equivalent inline
  reduced-scheme compatibility test. Upstream name-index search found no clash.

Sources checked online: https://arxiv.org/pdf/1005.2398v3 printed pp.35--36,
Proposition 7.1.1 and especially its exact Hom diagram; and
https://davidrydh.se/papers/submersion20100305.pdf Proposition 7.2 and Theorem 7.4,
printed pp.28--29. Alper explicitly uses the reduced self fibre product in this
exactness assertion. There is no mathematical statement correction or unresolved dispute. The H2 repair
below changes only citations and records that textual change for the delivery gate.

Repair validation (2026-10-24): scompile.py compiled the unchanged module under
both its sandbox name and its library name against current sources, exit 0,
without compiler diagnostics. The saved Lean signature equals `lean.statement`
verbatim. The statement-text diff consists solely of the two requested citations.
The repaired packet's required dry run and final push follow this check.

## Second reading by Q145

Self-review with the node and Lean file open; no separate agent was started,
as required by the dispatcher brief. Independent maintainer review follows delivery.
Checked the field/base, source stack, target spaces, qcqs, all base changes,
canonical small-etale structure map, immersive diagonal, injectivity and both
implications of the image criterion. The reduced-scheme test was checked in both
directions using factorization through reduction and reduced smooth charts, rather
than replacing equality by geometric-point agreement. No mismatch was found and
no hypothesis or clause was changed.


## Returned H2 repair

Return: independent immutable head `8994a27a53f2`, H2, 2026-10-24.
Replaced `lem-sfb-stack-point-topology-flat-lfp-open` in `stmt_deps` by
`def-sfb-stack-point-topological-space`; added
`def-sfb-dm-stack-morphism-properties`. Added both definition-owner citations
immediately after the displayed point-space map in the informal statement.
Read both current node records and the full signatures/docstrings of
`moduliPointTopologicalSpace`, `ModuliPoints`, and `moduliPointMap`.
The module and `lean.statement` remain byte-for-byte unchanged from the returned
packet. The wrapper rebases the repaired packet on current `sheaf-dag`.

Second reading of the repair: `hsub` uses the atlas topology instance for both
point spaces and the actual induced point map of the second projection. The two
new citations own exactly those declarations; the openness theorem itself is not
a statement prerequisite. All hypotheses, conclusions, edge cases, imports and
the single `sorry` remain as checked in the maintainer's mathematical review.

## Statement corrected

Citation-only correction requested by H2; no mathematical content changes.
The old statement is the same mathematical text without the two definition-owner
citations after `$|\mathcal U\times_VV'|\to|V'|$`; `statement_change.old_statement`
records its full verbatim text. The source remains Alper, Proposition 7.1.1 proof,
printed p.36, exact Hom diagram (and its Rydh descent input).
The delivery gate requires a `statement_change` record for any statement-text
change, so this record also preserves the main branch's old statement dependencies.

Citer audit: `lem-sfb-adequate-locally-separated-universality` — holds: true.
Its proof steps 1 and 4 use exactly the same descent lemma; neither the hypotheses
nor its image criterion changes. A scan of all current DAG nodes found no other
statement- or proof-dependency citer. No citer is edited.
