## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceNoetherianCoherentAcc` states four
parts of `lem-sfb-space-noetherian-coherent-acc`. Every theorem has exactly `by sorry`;
there are no definitions or proofs in this delivery. The informal statement is unchanged.

The source texts were read at spaces-cohomology.tex, lemma-coherent-Noetherian
(07UB, lines 1877–1906) and lemma-acc-coherent (07UJ, lines 2096–2118), and
spaces-morphisms.tex, lemma-locally-finite-type-locally-noetherian
(04ZK, lines 4464–4486). The current blueprint unit is
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`;
this node is an auxiliary result on its inherited direct-image prerequisite chain,
not the unit's own statement.

Hypotheses and clauses:

- The base scheme is `{S : Scheme.{u}}`, and all spaces are the existing
  `AlgebraicSpace S`. The explicit `universe u` follows the recorded size convention;
  the existing space module fixes the site objects in u+1 and section carriers in u.
  No extra site/coefficient universe equality or test-universe restriction is imposed.
- The existing `X.Modules` is the module category of the small étale structure sheaf.
  `AlgebraicSpaceModuleOperations` is publicly imported for the recorded tensor
  pullback/direct-image convention; the theorem does not assert an additional
  property of those operations.
- Local Noetherianity is exactly `∀ T : X.EtaleSite,
  IsLocallyNoetherian (X.etaleForget.obj T)`. Every étale scheme chart occurs,
  without an affine, finite-type, quasi-compact or surjectivity restriction on T.
- Quasi-compactness is `CompactSpace (Point X.obj.obj)` with the existing final atlas
  topology. The node's proof explicitly compares this with the quasi-compact atlas
  convention. Absolute quasi-separatedness is `MapIsQuasiCompact
  (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj))`: the diagonal of the presheaf over S.
  This is the product over S, not an absolute product of schemes over Spec Z.
- `noetherian_of_quasiSeparated_finiteType` takes all three Noetherian conditions
  on B (`hBln`, `hBqc`, `hBqs`), quasi-separatedness of f as quasi-compactness of
  `pullback.diagonal f.hom.hom` (`hfqs`), and the recorded `MapIsFiniteType f`
  (`hfft`, including quasi-compactness). Its three conjuncts give exactly the same
  Noetherian conditions on X. No Noetherian assumption on S is present.
- Coherence is rendered everywhere as `F.IsQuasicoherent` together with
  `∀ T, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
  ((X.schemeRestriction T).obj F)`. The chart restriction is the canonical existing
  restriction to Zariski opens; the ringed-space predicate is the actual finite-type
  and finite-type-kernel predicate, not a surrogate finite-presentation definition.
- `coherent_iff_finiteType_iff_finitePresentation` assumes only the chartwise local
  Noetherian condition and an arbitrary `F : X.Modules`. Its first equivalence has
  right side `F.IsQuasicoherent ∧ F.IsFiniteType`. Its second has right side
  `F.IsFinitePresentation`, with no separately added quasi-coherence assumption.
  This Mathlib predicate is locally a cokernel of a map of finite free modules.
  The conjunction of these two equivalences is exactly the three-way equivalence.
- `noetherian_coherent_submodules_acc` assumes the three Noetherian conditions on X
  and both parts of the given chart coherence convention for F. A submodule is
  `Subobject F`, whose quotient identifies isomorphic presentations over F.
  `G : ℕ → Subobject F`, `Monotone G`, and quasi-coherence of every `(G n : X.Modules)`
  render an arbitrary increasing sequence of quasi-coherent submodules. The conclusion
  `∃ n, ∀ m, n ≤ m → G m = G n` states equality as submodules of F, not just
  isomorphism of their underlying abstract modules. The starting index zero is allowed.
- `noetherian_quasiCoherent_ideals_maximal` assumes just the same three Noetherian
  conditions on X. `Z : Set (QuasiCoherentIdeal X)` and `Z.Nonempty` describe every
  nonempty set of quasi-coherent ideal sheaves, using the recorded subtype of
  subobjects of `SheafOfModules.unit X.structureSheaf`. Its conclusion
  `∃ I ∈ Z, ∀ J ∈ Z, I ≤ J → J = I` is maximality for inclusion, not a greatest
  member or a finite-generation assumption.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`, `EtaleSite`,
  `etaleForget`, `structureSheaf`, `Modules`.
- `def-weil-size-convention` is the recorded metatheoretic convention, not a Lean object.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` exposes the existing
  `SheafOfModules.IsQuasicoherent` predicate and its slice sheafification instances.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleDirectImageModel`,
  `moduleDirectImage`, `moduleTensorPullback`, `moduleTensorAdjunction` fix the ringed-site
  module convention.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, the chart predicate.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the dependency's `IsQuasiCoherentFiniteType`
  records the conjunction, and its public import exposes the exact predicate
  `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`; Mathlib supplies `IsQuasicoherent`,
  `IsFiniteType`, and `IsFinitePresentation` without replacement definitions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsFiniteType`; the latter uses `MapIsQuasiCompact`, the existing affine-test
  predicate from `Sheaf.AlgebraicGeometry.ProperCurveModuli`.
- Added already-landed statement dependencies: `def-a1-space-point-topology`
  (`Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`, `pointTopologicalSpace`),
  `def-trf-space-module-scheme-restriction`
  (`Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`, `schemeRestriction`),
  and `def-sfb-space-quasi-coherent-ideal`
  (`Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal`, `QuasiCoherentIdeal`).
  Their full source definitions and node statements were read. They supply exactly
  the topology, chart interpretation and ideals already mentioned in this node.
  This adds no new definition node or dependency module.

All recorded, available non-Mathlib proof dependency modules are imported privately:
fibre products/étale covers, étale-local Noetherian descent, quasi-compact affine tests,
Zariski/étale quasi-coherent equivalence, scheme coherence/finite-type equivalence,
affine finiteness, and scheme ACC. Mathlib's Noetherian and quasi-coherent imports also
supply the scheme locally-finite-type inheritance and finite-presentation facts.
The proof dependencies `lem-sfb-qc-space-affine-etale-atlas`,
`lem-sfb-space-quasiseparated-test-calculus`, and
`lem-sfb-scheme-etale-module-exact-finiteness-comparison` have no recorded Lean module
in the read snapshot and are therefore not imported; their intended uses remain in
the theorem docstrings. None is needed to type the present statements.

Edge cases checked before writing: the empty space and zero module satisfy the same
statements, and no nonempty atlas or nonzero ring/module assumption was inserted.
On the empty space there is only the zero ideal, so the nonempty-set conclusion is
correct. The ideal set itself must be nonempty; this is explicit. Chains may be
constant from zero and include zero and whole submodules. An infinite disjoint union
of fields is locally Noetherian but not quasi-compact, so the coherence equivalence
still applies while global ACC is not asserted there. No separation, Noetherianity
or quasi-compactness of the base S was silently added. The finite-type clause retains
its quasi-compactness, and f retains relative quasi-separatedness.

Searches performed using the prescribed msearch.py for Q30 and this item:

- LeanFinder: “On a Noetherian algebraic space coherent modules satisfy the ascending
  chain condition and coherence is equivalent to finite presentation”. Returned
  scheme Noetherian predicates, finite-presentation/finite equivalence for modules,
  and general quasi-coherent presentation APIs. No algebraic-space theorem match.
- LeanSearch: “On a locally Noetherian algebraic space coherent modules are finitely
  presented and submodules of coherent modules satisfy ascending chain condition”.
  Returned algebraic-module ACC and finite-presentation constructors; no matching
  algebraic-space result.
- Loogle: `SheafOfModules.IsFinitePresentation, SheafOfModules.IsFiniteType`.
  Returned `SheafOfModules.instIsFiniteTypeOfIsFinitePresentation`; it supplies one
  general implication only, not the node's locally Noetherian equivalence or ACC.
- Mathlib grep: `noetherian.*submodule|IsCoherent|IsLocallyNoetherian` in
  AlgebraicGeometry. Returned scheme-only Noetherian results; their signatures
  were read, and none applies directly to algebraic spaces.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for the node id and for
  `noetherian.*coherent|coherent.*noetherian|Noetherian.*AlgebraicSpace|AlgebraicSpace.*Noetherian`.
  Existing scheme ACC is used as a proof dependency; algebraic-space coherent-support,
  coherent-filtered-union and coherent-abelian results are different statements.
  Searches for `schemeRestriction`, `IsLocallyNoetherian`, `IsCoherent`, `Subobject`,
  `FiniteType`, and `FinitePresentation` found the reused interfaces above.
  The four new full declaration names do not duplicate the source or Mathlib.

No statement correction, disputed statement, new definition, or dependency-interface
repair was necessary. The initial prescribed scompile.py run compiled both its
sandbox probe (33.1 s) and the delivered library module (1.9 s) cleanly.

## Second reading by Q30

This independent reading was written by the maintainer's second reader (cc review service). It replaces the
delivery's self-audit note. It was checked against the immutable delivery 7d94e624.

| Node clause | Lean | Verdict |
|---|---|---|
| S a scheme; algebraic spaces over S, small étale structure sheaf, size convention | `{S : Scheme.{u}}`, `AlgebraicSpace S`, `X.Modules` = modules over `X.structureSheaf` on `X.EtaleSite` (objects u+1, sections u) | exact, no extra universe equality |
| locally Noetherian on étale charts (pqf-def-locnoeth) | `∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T)` | exact: every étale chart, which is equivalent to the Stacks atlas definition |
| quasi-compact | `CompactSpace (Point X.obj.obj)` with the landed final point topology (def-a1-space-point-topology) | exact (|X| quasi-compact ⇔ quasi-compact scheme atlas, compared in node proof step 2) |
| quasi-separated (quasi-compact diagonal) | `MapIsQuasiCompact (prod.lift (𝟙 _) (𝟙 _))`: diagonal into the presheaf product over the final object S | matches the landed node, whose stage-1 proof step 2 explicitly takes the diagonal over S (advisory below) |
| f quasi-separated, finite type (def-sfb-space-morphism-properties) | `MapIsQuasiCompact (pullback.diagonal f.hom.hom)` (= unfolding of the landed `MapIsQuasiSeparated`), `MapIsFiniteType f` (quasi-compactness ∧ chartwise LocallyOfFiniteType) | exact |
| conclusion: X Noetherian | the three conjuncts with the same predicates on X | exact |
| coherent (pqf-def-coherent) | `F.IsQuasicoherent ∧ ∀ T, RingedSpace.IsCoherent _ ((X.schemeRestriction T).obj F)` (finite type plus finite-type kernels of all maps from finite free modules on opens, Stacks 01BV) | exact; this is the same rendering as the sibling SpaceCoherentAdicSystem |
| coherent ⇔ qcoh of finite type ⇔ finitely presented | two `↔` with `F.IsQuasicoherent ∧ F.IsFiniteType` and Mathlib `F.IsFinitePresentation` (QuasicoherentData covering the top, finite generators/relations) | exact; the index universes are pinned to the site universe, and no universe parameter is left free |
| ACC on a Noetherian X for quasi-coherent submodules of coherent F | `G : ℕ → Subobject F`, `Monotone G`, each `(G n).IsQuasicoherent` ⇒ `∃ n, ∀ m ≥ n, G m = G n` | exact: equality as subobjects, n ≥ 0 |
| maximal member of every nonempty set of quasi-coherent ideals | `Z : Set (QuasiCoherentIdeal X)`, `Z.Nonempty` ⇒ `∃ I ∈ Z, ∀ J ∈ Z, I ≤ J → J = I` with the landed subtype of subobjects of `unit` | exact: this is maximality, not a greatest element |

Edge cases: the empty space, where the only ideal is 0, and the set must be nonempty; the zero module; constant chains; an infinite disjoint union of fields, which is locally Noetherian but not quasi-compact, so only the coherence equivalence applies. No Noetherian or separatedness hypothesis is placed on S.

Records: the node differs from the live node only by `lean` and three added stmt_deps (def-a1-space-point-topology, def-trf-space-module-scheme-restriction, def-sfb-space-quasi-coherent-ideal). All three are landed definition nodes and are used in the signatures. `lean.statement` is verbatim in the file. All imported modules exist in the live tree. There are no definitions (none hollow), all proofs are `sorry`, and the docstrings carry the source places, `(blueprint: …)` and the proof steps.

Advisory: Stacks (spaces-properties Definition 03HJ, definition-noetherian) defines quasi-separatedness absolutely, over Spec Z. The landed def node def-sfb-space-absolute-quasi-separated renders that notion, and the siblings ArtinRees and CoherentFilteredUnion use it. This node's landed stage-1 text uses the diagonal over S instead. The two agree when S is quasi-separated, which includes every current citer over Spec Z or an affine base. The ACC and maximal-ideal clauses have a hypothesis that is weaker but still sufficient, and the inheritance clause is true in this convention. A citer that needs the absolute form of clause 1 for a non-quasi-separated S would need a §1(C) correction of this node.
