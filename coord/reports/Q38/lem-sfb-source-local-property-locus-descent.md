## Worker report

Item: lem-sfb-source-local-property-locus-descent. The module
`Sheaf.AlgebraicGeometry.SourceLocalPropertyLocusDescent` states
`CategoryTheory.source_local_property_locus_descent` with one `sorry` proof.
No statement or proof text is changed. Five fully defined Prop-valued helpers
spell out vocabulary already introduced by this node; no data is postponed.

Source read: `literature/stacks-project/stacks-properties.tex`, lemma-local-source,
Tag 06M3, including the proof of (A),(B), lines 2081–2150. This item is its
scheme-target variant, with Q = locally of finite type and R = all morphisms.
The six proof steps in the node, including the scheme refinements of the space
overlap and the explicit scheme-chart identity, are reproduced in the theorem
docstring. Source locality is an additional hypothesis of this node and is retained.

Clause-by-clause rendering:

- Base scheme and size convention: `{S : Scheme.{u}}`; presheaf values and field
  extensions have universe u, with arbitrary explicit total-category levels
  `v₁,w₁,v₂,w₂`. The source-local family index is `Type (max u z)`, so no bound
  smaller than the scheme universe makes detection vacuous. All universes and
  variables are explicitly declared; `autoImplicit` and `relaxedAutoImplicit`
  are false.
- Algebraic spaces and morphisms: `AlgebraicSpace S`, with its existing full
  subcategory morphisms and underlying natural transformations `.hom.hom`.
  Stack maps are existing `BasedFunctor`s; stacks use `IsAlgebraicModuliStack`.
  The 2-fibre product is the existing `moduliTwoFiberProduct`.
- Predicate P: `P : MorphismProperty (AlgebraicSpace S)`. `hiso` states invariance
  under simultaneous source and target isomorphisms, with the commuting square.
- Arbitrary base-change stability (i): `hbase` quantifies every space target
  map and every actual pullback square, identified by the underlying presheaf
  `IsPullback`, and asserts `P f → P q`. Because spaces form a full subcategory
  and their pullbacks are the sheaf pullbacks, this includes every base change,
  without fixing a noncanonical model or requiring chosen limits.
- Fppf target locality (ii): `htarget` has exactly the flat, locally finitely
  presented, surjective target-map hypotheses and the equivalence `P f ↔ P q`.
  Flatness and local finite presentation are the recorded all-etale-chart
  predicates `MapIsFlat` and `MapIsLocallyOfFinitePresentation`. Surjectivity is
  the singleton instance of `IsJointlySurjective`, hence field-extension lifting
  on field-valued point classes. No representability-by-schemes condition is
  added to this map between spaces.
- Etale source locality (iii): `hsource_preserve` states preservation under
  precomposition by an etale space map. `hsource_detect` quantifies jointly
  surjective etale families and detects P. `MapIsLocally (@Etale)` is the
  existing scheme-chart definition; it does not restrict maps to scheme sources.
- Scheme-target canonical loci: `hscheme` quantifies every space E, S-scheme T,
  and map `g : E.obj.obj ⟶ yoneda.obj T`. Its sole geometric hypothesis is
  `MapToSchemeIsLocally (@LocallyOfFiniteType) E T g`.
  `IsGreatest {J | SpaceMapProperty P (J.val.ι ≫ g)} W` says both that the
  restriction to W has P and that EVERY other such open lies in W.
- Scheme-base-change compatibility in the hypothesis: for every `b : T' ⟶ T`
  and every space presentation `E'` of the actual presheaf pullback,
  `W'.val = W.val.preimage p` and the second `IsGreatest` give exactly
  `W_{g_{T'}} = W_g ×_T T'`. There is no flatness restriction on b. Stating the
  formula for all pullback presentations avoids a choice of canonical model.
- Extension to representable stack maps: `ModuliSpaceMapProperty P` tests
  every scheme map t into the target and requires a presentation
  `HasSpaceBaseChange f T t X a` satisfying `SpaceMapProperty P a`.
  `SpaceMapProperty` transports P across actual source/target presheaf
  isomorphisms, with equality of the represented arrow. On algebraic spaces
  it is exactly P by `hiso`; on open subfunctors and Yoneda schemes it permits
  their actual presheaves without inventing algebraicity data or a private
  duplicate definition. Its witnesses are only presentations of fixed objects.
- The map in the conclusion: `A`, `Y`, `hY`, `f` render the space source,
  algebraic stack target and actual map. `hf : ModuliSpaceTest
  (@LocallyOfFiniteType) f` is the recorded scheme-base-change, etale-chart
  meaning of local finite type. Its presentations also express representability,
  which follows from the algebraic-space diagonal in this setting.
- Largest open W_f: the existential `W : OpenSubspace A` and
  `IsLargestSpaceSourceOpen P A f W` assert extended P on the restricted map
  and inclusion of every open with extended P. The order is the existing
  inclusion order on open subfunctors.
- Every representable stack base change: the first concluding universal
  quantifies every algebraic stack Z and every representable map `b : Z → Y`.
  `HasCompatibleLargestSourceOpen` produces the algebraic space B = A_b and
  its two actual projections p and q, pinned by an equivalence with
  `moduliTwoFiberProduct b f` and TWO `ModuliTwoIso`s. Thus neither projection
  is an arbitrary map and no 2-isomorphism is discarded. It produces Wb, proves
  its largestness for q, and asserts the literal equality
  `Wb.val = W.val.preimage p`. This is precisely equality as open subspaces of
  A_b, not just an abstract equivalence of opens.
- The particular scheme case is stated separately in the final universal over
  every T and `t : h_T → Y`, with the SAME conclusion and no representability
  or flatness assumption on t. The diagonal criterion supplies representability.
- No quasi-compactness, Noetherianity, nonemptiness, separatedness or finite-type
  strengthening is present.

Dependency declarations used (all read at their full definitions/docstrings):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `.FinitePresentation`, `.Etale`,
  `.FiniteType`: `Flat`, `LocallyOfFinitePresentation`, `Etale`, `LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, its morphisms,
  `IsRepresentableWith` and `IsEtale` as used in the owning definitions.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `discreteModuli`,
  `discreteModuliMap`, `moduliTwoFiberProduct`, `moduliTwoFiberFst`,
  `ModuliTwoIso`, `HasSpaceBaseChange`, `IsRepresentableByAlgebraicSpaces`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace` and its order.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsFlat`, `MapIsLocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`: `IsJointlySurjective`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapToSchemeIsLocally`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliSpaceTest`.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `moduliTwoFiberSnd`.

The last five owning definition nodes are added to stmt_deps, using the explicit
permission to add already-landed statement dependencies. This is not a change
of mathematical statement. No new node or dependency repair is needed.
The recorded scheme-only open-immersion definition is used unchanged: this item
uses open subspaces of A, rather than separately introducing open substacks.

Proof import: `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus` is plain
`import`, not public. The other proof inputs
`lem-sfb-invariant-open-substack-descent`, `lem-sfb-representable-pullback-over-space`,
and `lem-sfb-stack-diagonal-space-source-representability` have no Lean records in
this checkout; they are listed in the proof docstring, with no imports invented.
They are proof dependencies only, not missing notions needed to type the statement.

Edge cases checked before writing and rechecked against the signature:
empty A and empty test schemes are allowed; the empty etale family is not excluded
(and can cover only a point-empty space); P identically true gives the full open;
P identically false cannot satisfy existence even on empty E, as it should not;
identity target maps give the original locus; arbitrary nonflat scheme maps are
included in hscheme and in the conclusion; source and target stack universes are
independent; arbitrary characteristic and non-quasi-compact atlases are permitted.

Searches for an existing statement, all via the prescribed wrappers or read-only rg:

- `msearch.py ... leanfinder "Canonical largest open source loci for algebraic stack
  maps descend from scheme targets and commute with representable base change"`:
  eight hits, scheme locality/UniversallyOpen results; no stack-locus descent.
- `msearch.py ... leansearch "A largest open locus for morphisms of algebraic stacks
  descends from scheme target tests"`: eight scheme descent/flat descent hits;
  no match for the node.
- `msearch.py ... loogle "MorphismProperty.IsLocalAtTarget"`: unknown identifier;
  retried with `"IsLocalAtTarget"`: twelve generic locality declarations, none
  constructing canonical source loci on algebraic stacks.
- `msearch.py ... grep "largestOpen|propertyLocus|localSource" AlgebraicGeometry`:
  no matches.
- Read-only rg over both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  source-local/locus/descent concepts, and exact new declaration names: no existing
  statement or name match. Related specific loci (`SpaceNodalLocusBaseChange`,
  `AlgebraicStackOpenDmLocus`) were opened and checked; neither states this result.
- Read the existing open-subspace, morphism-property, scheme-test, jointly-surjective,
  and 2-fibre-product APIs above. Reused them instead of defining private copies.

Validation: prescribed `scompile.py` compiled this file as both the sandbox and
library module with no diagnostics (3.6 s and 3.5 s on the first compile).
Every helper has real data (a Prop formula); the only postponed proof is the
named theorem matching this DAG item. No STATEMENT-DISPUTED issue found.

## Second reading by Q38

A separate clause-by-clause pass over the node and the completed module checked
all three locality assumptions, scheme-only nature of the locus hypothesis,
largestness rather than just maximality, and representable STACK base changes
rather than only scheme changes. The second projection was checked explicitly:
`HasSpaceSourceBaseChange` compares `moduliTwoFiberSnd b f` with the actual
`discreteModuliMap p`, while the first projection compares `moduliTwoFiberFst b f`
with q. The equality of opens is literal preimage, and the new open's largestness
is a separate conjunct, so the formula does not merely assert P after base change.
The scheme case is included explicitly, covering stack universes that differ
from those of represented schemes. The P-presheaf transport is constrained by
isomorphisms and a commuting arrow, not arbitrary data. The extra existing owning
nodes were added to stmt_deps to account for every API used. Explicit imports of
the original recorded Mathlib dependencies were added after this reading.
No mathematical mismatch or statement correction was found. This is the
worker's second pass; the maintainer performs the independent review, as the
assignment specifies. No sub-agent was started.
