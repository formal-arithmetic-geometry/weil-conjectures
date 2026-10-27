## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceSeparatedFpComposition` states
`AlgebraicGeometry.AlgebraicSpace.separated_finitePresentation_composition_and_separated_baseChange`
with one `sorry`. It defines no new notion. The node's mathematical statement and proof are unchanged.
Its `stmt_deps` additionally names three already landed owning definition nodes:
`def-sfb-space-morphism-properties`, `def-sfb-space-quasi-compact-presheaf-map`, and
`def-sfb-presheaf-map-separated-diagonal`. The first owns chartwise local finite
presentation; the second owns `IsQuasiCompactPresheafMap`; the third owns
`diagonalPresheafMap` and `IsSeparatedPresheafMap`. These last two definition nodes
record existing declarations in `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`.
The theorem `quasiCompact_separated_etaleLocal` in that module is not used by this
statement and its theorem node is not a statement dependency.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; the three spaces are
  `{X Y Z : AlgebraicSpace S}`. The explicit universe `u` is precisely the existing
  algebraic-space convention; no additional universe equality is imposed.
- The arbitrary space morphisms are `(f : X ⟶ Y)` and `(g : Y ⟶ Z)`.
  `f ≫ g` is the categorical composite corresponding to g composed with f.
- Separatedness is `IsSeparatedPresheafMap f.hom.hom`: by its definition it asks
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)` for the canonical
  presheaf diagonal. Thus every scheme test is a closed immersion.
- Local finite presentation is `MapIsLocallyOfFinitePresentation f`. Its full definition
  quantifies over all compatible representable étale source and target scheme charts,
  applying the recorded scheme `LocallyOfFinitePresentation` to their horizontal map.
- Quasi-compactness is `IsQuasiCompactPresheafMap f.hom.hom`. Its affine tests demand
  a quasi-compact scheme atlas that is representable, étale and surjective onto the
  tested fibre product. The FIRST conjunct of the dependency theorem
  `quasiCompact_baseChange_and_fppfLocal` identifies this exact predicate with the
  node's definition by ALL quasi-compact algebraic-space tests. In particular this is
  not a replacement by a weaker representable-map or scheme-only assertion.
- Quasi-separatedness is expanded as
  `IsQuasiCompactPresheafMap (diagonalPresheafMap f.hom.hom)`.
  The diagonal's source and target are algebraic spaces by the recorded fibre-product
  theorem, so the same all-space-test comparison applies to it. No new definition
  of quasi-separatedness or finite presentation is introduced.
- The FIRST conjunction component assumes separatedness of f and of g independently
  and concludes separatedness of `f ≫ g`.
- The SECOND component assumes for each of f and g the triple consisting of local
  finite presentation, quasi-compactness, and quasi-compactness of its diagonal,
  and concludes exactly this triple for `f ≫ g`. This is finite presentation,
  including the quasi-separatedness clause explicitly required by Tag 03XP.
- The THIRD component assumes only local finite presentation of f and g and concludes
  local finite presentation of the composite, with no global finiteness assumptions.
- The FOURTH component quantifies over every `(Y' : AlgebraicSpace S)` and
  `(h : Y' ⟶ Y)`. Separatedness of f implies separatedness of
  `Limits.pullback.snd f.hom.hom h.hom.hom`, the underlying canonical presheaf map
  X ×_Y Y' → Y'. It is the underlying sheaf fibre product, which is an algebraic
  space by `fibreProduct_isAlgebraicSpace`; no noncanonical map is chosen.
- All four components are implications inside the conjunction, so the separatedness
  assumptions do not leak into either finite-presentation assertion. There is no
  `IsRepresentable` hypothesis on f, g, or h.

Dependencies read and used (all signatures and docstrings inspected):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`, through the public statement imports.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`,
  and the proof dependency `IsClosedImmersion.comp`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation` and the proof dependency `locallyOfFinitePresentation_comp`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (no Hausdorffness).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCompactFppfLocal`:
  `quasiCompact_baseChange_and_fppfLocal`, including its all-space-test comparison.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`: `IsQuasiCompactPresheafMap`,
  `diagonalPresheafMap`, `IsSeparatedPresheafMap`. Their DAG owners are respectively
  `def-sfb-space-quasi-compact-presheaf-map` and
  `def-sfb-presheaf-map-separated-diagonal`, both existing-declaration records.
  No use of the module's étale-locality theorem is claimed.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocally`, `MapIsLocallyOfFinitePresentation`.
- Proof-only `Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties`:
  `scheme_etale_source_target_properties`.
- Proof-only `Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion`:
  `etalePresentation_property_criterion` and `etalePresentation_property_iff_scheme`.
- Proof-only `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`:
  `Scheme.instIsStableUnderCompositionPrecoverageOfIsStableUnderComposition`, with
  `Precoverage.comp_mem_coverings`, as the recorded étale covering-composition leaf specifies.
- `def-weil-size-convention` is a convention record with no module; explicit universe
  polymorphism implements it.

Source check: read `literature/stacks-project/spaces-morphisms.tex`,
`definition-separated`, `lemma-base-change-separated`, `lemma-composition-separated`,
`definition-locally-finite-presentation` and `lemma-composition-finite-presentation`.
They give exactly these four conclusions and the expanded finiteness definition.
The declaration docstring carries all six proof steps, with the DAG dependencies.

Edge cases checked before writing: empty schemes and spaces remain permitted; all chart
conditions then have their usual vacuous meaning and a quasi-compact empty atlas is allowed.
Identity maps and identity base change are included. The lfp assertion permits
non-quasi-compact maps. The fp assertion retains diagonal quasi-compactness, rather than
incorrectly assuming it follows from lfp and qc. Nonrepresentable space morphisms remain
allowed throughout. No Noetherian, characteristic, nonemptiness, separation of the base,
or representability assumption has been introduced.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Composition and base change of separated morphisms and finite presentation of algebraic spaces"`:
  eight hits, all scheme results (including `IsSeparated.stableUnderComposition`,
  `IsSeparated.isStableUnderBaseChange`, and scheme lfp composition); no space theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsSeparated, AlgebraicGeometry.LocallyOfFinitePresentation"`:
  zero hits.
- `msearch.py ... grep "separated.*comp|finitePresentation.*comp|locallyOfFinitePresentation_comp" AlgebraicGeometry`:
  nineteen Mathlib hits, on schemes; includes the recorded scheme composition instance.
- `msearch.py ... leansearch "Separated morphisms of algebraic spaces compose and base change; finite presentation of algebraic spaces is stable under composition"`:
  eight scheme-only hits, including separated composition and base change and quasi-separated composition.
- `rg` of `lean/WeilConjectures/AlgebraicGeometry` for `AlgebraicSpace`,
  `IsSeparatedPresheafMap`, `MapIsLocallyOfFinitePresentation`: no matching space interface.
  Search of `lem-sfb-space-separated-fp-composition` in `lean/WeilConjectures`: no hits.
- `rg` of `lean/Sheaf` found the reused predicate-owning modules above and references
  to this node in downstream proof docstrings, but no theorem stating these four implications.
  Search for the new declaration name found no collision.
- The existing `MapIsQuasiSeparated` in `StackQcqsMorphism` uses the point-topology
  quasi-compactness predicate from `ProperCurveModuli`; the present signature directly
  expands the node's atlas predicate instead, following its stated dependency's exact
  all-space-test equivalence. It neither defines nor copies a second named notion.

No node fault or statement dispute was found. Only the theorem's proof is postponed.

## Second reading by NP

This is the author's separate clause-by-clause rereading, not a claim of independent
agent review; the dispatcher instructed this worker not to start agents, and the
maintainer supplies the independent delivery review. Reopened the node and module:
S/X/Y/Z and f/g binders match; the three independent composition implications have
exactly their respective hypotheses; finite presentation retains all three clauses
for both inputs and output; every Y' and every h is quantified in the final clause.
The canonical pullback second projection points to Y', as required. Scheme-test
separatedness and atlas quasi-compactness use the dependency declarations verbatim,
and the all-space-test equivalence in the existing dependency justifies the latter.
No representability or extra separation assumption was found. The source matches
without a statement correction. The only DAG additions relative to current main
are the three landed owning definition nodes named above; there are no new nodes
or dependency repairs. For the returned H2 point, reread both definition-node
statements, their existing Lean records, and the three declarations in the source
module: the affine-test atlas condition matches `IsQuasiCompactPresheafMap`, and
the canonical diagonal and its closed-immersion scheme tests match
`diagonalPresheafMap` and `IsSeparatedPresheafMap`. The statement needs these
notions, not the étale-locality theorem sharing their module. The replacement
changes the DAG ownership references and leaves the checked Lean signature intact.


## Returned delivery repair

H2 on immutable head `4113567cc377`: replaced
`lem-trf-space-qc-separated-etale-local` in `stmt_deps` with the already landed
`def-sfb-space-quasi-compact-presheaf-map` (Q97) and
`def-sfb-presheaf-map-separated-diagonal` (Q32). Their existing declaration
records name exactly the three definitions used by the signature. Updated the
worker report and second reading to identify those owners. Compared the retained
packet with current main: only `lean` and the permitted additions to `stmt_deps`
differ. The Lean file, `lean.statement`, mathematical statement and proof are
unchanged from the returned delivery. The delivery wrapper rebases the repaired
packet on current main and performs the prescribed preflight and compilation.
