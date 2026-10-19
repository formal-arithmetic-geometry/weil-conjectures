## Worker report

The delivery states `SSet.Enhanced.SimplePresheaf.simple_inner_anodyne_base_change` in
`Sheaf.CategoryTheory.SimpleInnerAnodyneBaseChange`. Its sole theorem proof is `sorry`.
The added definition module `Sheaf.CategoryTheory.SimplePresheafInnerAnodyne` has no
postponed proofs or chosen objects from existence assertions. The original item's
statement and proof are unchanged; its statement dependencies gain the new definition node.

Clause-by-clause correspondence:

- Small monoidal infinity category and structural cartesian fibration:
  `St : CocartesianStraightening.Statement.{u}` and
  `A : SegalPresheaf.CartesianPresentation St` use the recorded definition's
  straightened opposite presentation. `A.ambientTotal` is C_tensor and
  `A.ambientProjection` is p, with its coefficient universe u retained inside
  the independent ambient universe `max (u + 1) v`. The fibre over `[n]` is the
  dependency's space of n labels; no ordinary category replaces this infinity category.
- Space-valued presheaves: `transportDiagrams.{u,v} ... false` is the full coherent
  internal functor category into `transportSpaces.{u,v}`. `H` is the dependency's
  normalized `YonedaLimits.HomPresentation`, used by `representedSimplex` and
  `IsRepresentable`, rather than a new Yoneda construction.
- Restriction p*: `SegalPresheaf.restriction A.ambientProjection`. Left Kan
  extension p!: `D : ProjectionExtension A.ambientProjection`, whose extension has
  the existing `CoherentAdjunction` to that actual restriction. It retains the
  universal unit/counit data; it is not an unconstrained comparison map.
- Ordinary discrete horns: `ordinaryInnerHorns` consists of `discreteArrow
  (horn n b).ι` with `2 ≤ n`, `0 < b.val`, `b.val < n`. `discreteComparison`
  composes actual ordinary evaluation with `DiscreteWeight.discreteKan` and its
  coherent Kan-nerve map. Thus the horns are in P(Delta), not merely in SSet.
- The smallest ordinary class closed under pushouts, transfinite compositions,
  retracts: `IsOrdinaryInnerAnodyne` uses `weakSaturation.{u,v}`, the intersection
  of all `IsWeaklySaturated` predicates containing those horns. This uses the
  existing coherent `IsHomotopyPushout`, `arrowCategory`, `IsRetractVertex` and
  small well-ordered diagrams. Continuity is imposed at every nonzero limit stage
  by the actual predecessor cocone; no two-out-of-three or arbitrary arrow-colimit
  closure is imposed. Equivalences are included in the usual replete convention,
  also forced by length-zero composites and arrow retracts of identities.
- Labelled generators: `labelledInnerHorns H D` quantifies over every n, inner b,
  and label `c : fiber q (SegalPresheaf.baseVertex n) _⦋0⦌`. Its represented apex
  is exactly `SegalPresheaf.representedSimplex q H n c`. The square has right map
  r to p*Delta^n, bottom map p* of the ordinary horn inclusion, and is required to
  satisfy `IsPullbackOf`. Its generator is `topEdge s`, the projection to the
  labelled simplex. `IsLabelledInnerAnodyne` is their weak saturation.
- The structural map r is normalized by `AdjointIsEquivalence D (discreteObject
  Δ[n]) r`. For this represented label, adjunction and Yoneda give p_!y(c)=Delta^n;
  any invertible adjunct is an order automorphism of [n], hence is the identity.
  This characterizes the structural unit up to its contractible choices. It does
  not permit a noncanonical map with only the right underlying source and target.
- L and f:X->p*L: `L` is a vertex and `f` an edge of the respective presheaf
  categories. X is the source `(transportDiagrams ...).δ 1 f`. The first conjunct
  of `hf : IsSimple H D L f` fixes f's target to the restriction of L.
- Every simplex sigma, in ALL dimensions: `IsSimple` quantifies over `(n : ℕ)`
  and all edges sigma with source `discreteObject Δ[n]` and target L. It includes
  existence of a homotopy pullback and tests every such square. Its apex must
  satisfy `IsRepresentable H`. Its actual left projection, `leftEdge s`, must
  satisfy `AdjointIsEquivalence D (discreteObject Δ[n])`. That predicate explicitly
  represents the adjunct by a compositional triangle with first edge p_!(r) and
  second edge the counit at Delta^n, and tests invertibility of its long edge.
- u:K->L in A_Delta: theorem argument `k` is the edge, K is its source, `hk`
  fixes its target L, and `hu : IsOrdinaryInnerAnodyne k` is the membership premise.
- The conclusion: `s` and `hs : IsPullbackOf f (restriction.map k) s` specify the
  homotopy pullback along p*k. (`restriction.map` here means its simplicial `.app`
  on the edge k.) The right and bottom boundaries are fixed exactly. The existing
  `IsSpacePullbackSquare` predicate fixes the entire cone and requires it limiting;
  despite its historical name it is defined for any ambient simplicial set.
  `IsLabelledInnerAnodyne H D (topEdge s)` says the projection to X is in A_C.
  Quantification over every universal square is independent of representative choice.

Dependency declarations used: `Sheaf.CategoryTheory.SegalPresheafLocalization`
(`CartesianPresentation`, `ambientTotal`, `ambientProjection`, `restriction`,
`representedSimplex`, `baseVertex` in `SSet.Enhanced.SegalPresheaf`);
`Sheaf.CategoryTheory.InfinityYonedaPresheafLimits` (`YonedaLimits.HomPresentation`);
`Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction` (`CoherentAdjunction`);
`Sheaf.CategoryTheory.EnhancedStrongSaturation` (`arrowCategory`, `arrowEdge`,
`IsRetractVertex`, `IsHomotopyPushout`, `squareRow`);
`Sheaf.CategoryTheory.DiscreteWeightCoherentCocones` (`discreteKan`,
`ordinarySimplex`, `ordinarySimplex_naturality`);
`Sheaf.CategoryTheory.SpaceBaseChange` (`spaceSquare`, `spaceSquareEdge`,
`IsSpacePullbackSquare`); `Sheaf.CategoryTheory.FiniteReedyLocalization`
(`largeNerve`, `comparison`, `diagram`, `object`, `transformation`, `IsColimitEdge`).
The five recorded proof-dependency modules are imported without `public`, and the
six-step natural-language proof, including each of their uses, is in the theorem docstring.

Edge cases checked: simplicity includes n=0 and n=1, while the generator sets
exclude those dimensions and both outer horns. An empty L has no simplex maps,
so the corresponding simplicity tests are correctly vacuous (a map to p*L still
has its specified target). Empty discrete presheaves are constructed by the actual
constant empty Kan complex. The one-point ordinal gives zero-length composition;
nonzero limit stages use all strict predecessors. Coefficient and containing
universes remain independent. No chosen pullback or underlying representability
can replace the projection test. All normalized Yoneda and adjunction presentations
are universal data, not additional mathematical restrictions on C.

Searches: launcher `msearch.py` leanfinder query “Simple maps of space valued
presheaves pull back inner anodyne maps to labelled inner anodyne maps” returned
8 ordinary subcomplex/model-category hits and no match. Loogle query
`"innerAnodyneExtensions", "pullback"` returned 0 hits. Mathlib grep query
`simpleMap|simple_map|innerAnodyne.*pullback|pullback.*innerAnodyne` returned 0 hits.
LeanSearch query “Simple maps of presheaf infinity categories and labelled inner
anodyne weakly saturated horn inclusions” returned 8 ordinary horn/filler/model
hits, none applicable. The new node includes their complete returned output.
Repository `rg` searches for simple maps, Segal presheaves and weak saturation found
and reused the components listed above; upstream search and the exact item-id
search found no base-change statement. `tools/blueprint_refs.py search 'simple map'`
returned 0 blueprint nodes. The relevant DAG search found the item but no definition
node for its inline simple-map/labelled-horn predicates.

Source checked online: https://arxiv.org/html/2311.13362v1, Definitions 6.1, 6.2,
6.7 and Proposition 6.9. The source uses the projection's adjoint, as does the node.
No statement fault, correction, or STATEMENT-DISPUTED flag.

Validation: both modules passed separate file-only compilation, in dependency order,
through `scompile.py Q56 lem-coef-simple-inner-anodyne-base-change`; no diagnostics
other than the permitted theorem sorry. No global build or direct Git operation.

## New nodes

`def-coef-simple-presheaf-inner-anodyne` supplies the inline notions needed to state
the item: weak saturation in coherent categories, actual discrete presheaf horns,
left Kan extension with adjunction, the simple-map predicate, and labelled horn
saturation. Source: Haugseng Definitions 6.1, 6.2, 6.7 and Chu–Haugseng Definition
2.7.11. Its statement cites exactly the five component interfaces it uses, and
its module has only real definitions. Existing ordinary SSet weak saturation and
strong saturation of infinity-category arrows do not define the required weak
saturation; two-out-of-three would change this class. The searches above establish
that no existing node or declaration provides these combined predicates.

## Second reading by Q56

The dispatcher explicitly forbids spawning other agents and instructs this worker
to deliver directly for the maintainer's independent review. No independent worker
review is claimed here. A final self-audit reread the node, both full source files
and the recorded signatures. It matched every hypothesis and conclusion as listed
above, checked the orientation of all four square edges and the adjoint triangle,
and verified the labelled generator source is the recorded represented simplex.
The audit fixed underdetermined universe arguments on the finite-Reedy predecessor
cocones and on weak saturation; it did not change the mathematical statement.

Dry-run repair: the first preflight reported the cycle
`def-cbc-enhanced-strong-saturation -> lem-coef-sheaf-flat-model -> ... ->
lem-coef-simple-inner-anodyne-base-change`. The new node does not use strong
saturation: it uses only the elementary arrow, retraction and pushout helpers
that happen to be declared in that source module. Its mathematical statement now
defines these basic conventions explicitly from coherent functor categories,
triangles and colimits, citing `def-cbc-enhanced-diagrams-cones`. The Lean still
imports and reuses the exact existing helpers (`IsStronglySaturated` and
`strongSaturation` are never used), avoiding duplicate definitions. Thus no
strong-saturation theorem or downstream sheaf model is an input to this definition.
No existing node was edited.

The repaired dry run passed: `OK (dry run): commit 8560489c0c passes the preflight
and compiles; nothing pushed`. Both modules were compiled separately, including
the dependency overlay; there were no compiler errors or non-sorry warnings.
