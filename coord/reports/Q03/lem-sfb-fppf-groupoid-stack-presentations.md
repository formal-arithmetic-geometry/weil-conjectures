## Worker report

The module `Sheaf.AlgebraicGeometry.FppfGroupoidStackPresentations` states the three
clauses of `lem-sfb-fppf-groupoid-stack-presentations`, as three named theorems. Each
proof is exactly `by sorry`. No new definition, chosen stackification, axiom, or data
construction is introduced. The natural-language statement and accepted proof split
are unchanged. The item changes only in `lean` and additions of already landed statement dependencies.
The returned delivery repair reuses the existing surjectivity definition through its
landed definition-node owner. There are no new or changed dependency modules.

Source checked directly: `literature/stacks-project/algebraic.tex`,
`remark-flat-fp-presentation` (04WY); `spaces-groupoids.tex`,
`lemma-quotient-stack-2-cartesian` (04M9), `lemma-quotient-stack-restrict` (046S), and
`lemma-quotient-stack-restrict-equivalence` (046T). The statement's interpretation of
algebraic stack is the existing etale-stack/smooth-atlas convention, not a stronger
smoothness assumption on either groupoid.

The existing `SpaceGroupoidQuotientPresentation` is used to quantify over a specified
realization of `[U/R]`. Its `groupoid`, `stack`, `arrows`, `fully_faithful`,
`locally_surjective`, and `composition` fields express exactly the pointwise groupoid,
fppf stackification, original arrows, locally represented objects, and composition.
This avoids selecting data from a mere existence theorem. Universes `u v w v' w'`
are explicitly bound: schemes and algebraic spaces use `u`, and the categories of the
two quotient stacks can have independent object and morphism universes. All tests are
on the existing `Over S` big site, with the scheme and field universes aligned.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Base scheme S, stated universe convention | `{S : Scheme.{u}}`; explicit `universe u v w v' w'`; test schemes are `Over S` |
| Groupoid in algebraic spaces U,R, with s,t,e,inverse,composition | `U R : AlgebraicSpace S`, `s t : R ⟶ U`, natural transformations `e i c`, and `SpaceGroupoidQuotientPresentation`'s `IsPresheafGroupoid` field |
| `[U/R]` is the fppf stackification, with its canonical object map | `F`, `a`, and `P : SpaceGroupoidQuotientPresentation ... F a`; every realization is allowed, rather than a privately chosen stackification |
| (1) s and t flat | `hs : MapIsFlat s`, `ht : MapIsFlat t` |
| (1) s and t locally of finite presentation | `hsfp`, `htfp : MapIsLocallyOfFinitePresentation ...` |
| (1) diagonal representable by algebraic spaces | `HasAlgebraicSpaceDiagonal F` |
| (1) object map representable and surjective | `IsRepresentableByAlgebraicSpaces a` and `IsSurjectiveModuliMap a` |
| (1) object map flat and locally of finite presentation | `ModuliSpaceTest @Flat a` and `ModuliSpaceTest @LocallyOfFinitePresentation a` |
| (1) R is canonically the self two-fibre product, with s,t projections | `moduliTwoFiberLift (discreteModuliMap s.hom.hom) (discreteModuliMap t.hom.hom) (BasedNatIso.mkNatIso P.arrows.val P.arrows.property)` is an equivalence; this actual comparison has those two projections by construction and uses precisely the presentation's arrow isomorphism |
| (2) algebraic stack Z | `hZ : IsAlgebraicModuliStack Z`, with exactly the recorded etale-stack, algebraic-space diagonal and smooth scheme-atlas meaning |
| (2) scheme U and map a to Z | `U : Over S`, `a : BasedFunctor (discreteModuli (yoneda.obj U)) Z` |
| (2) a representable, surjective, flat, locally finitely presented | `ha`, `hasurj`, `haflat`, `hafp`, using the same predicates as clause (1) |
| (2) self-relation R with groupoid operations induced by isomorphisms in Z | Existential `R s t e i c P`; `P` is a quotient presentation directly into Z and identifies R-arrows with the actual vertical arrows in Z, respecting composition |
| (2) R really is U x_Z U, with its actual projections and arrow comparison | The existential comparison built by `moduliTwoFiberLift` from `s`, `t`, and `P.arrows` is an equivalence |
| (2) both projections flat and locally finitely presented | Four conjuncts `MapIsFlat s`, `MapIsFlat t`, `MapIsLocallyOfFinitePresentation s`, `MapIsLocallyOfFinitePresentation t` |
| (2) canonical map from the quotient to Z is an equivalence commuting with a | For every other presentation `F b Q`, there exist `H : BasedFunctor F Z` and `κ : ModuliTwoIso (b.comp H) a`, with `H.toFunctor.IsEquivalence` |
| (2) canonical action on arrows | The final equality conjugates `H.map Q.arrows` by `κ` and identifies it with `P.arrows`; it is a characterization of the induced canonical map, not an arbitrary equivalence |
| (3) surjective flat locally finitely presented scheme map q:U->V | `U V : Over S`, `q : U ⟶ V`, `hqsurj : Surjective q.left`, `hqflat : Flat q.left`, `hqfp : LocallyOfFinitePresentation q.left` |
| (3) groupoids (U,R) and (V,Q) | Operations `s t e i c` and `s' t' e' i' c'`, with presentation witnesses `P P'` for quotient stacks `F G` and canonical maps `a b` |
| (3) restriction relation R=(U x_S U) x_(V x_S V) Q | `hrestrict : IsPullback (prod.lift s t) f (prod.map (yoneda.map q) (yoneda.map q)) (prod.lift s' t')`; these are products of presheaves on Sch/S, hence products over S |
| (3) all operations induced | `hs ht` give endpoints over q; `he hi hc` assert compatibility with identity, inverse, and composition; `hc` uses the actual canonical pullback map on composable pairs |
| (3) induced quotient map is an equivalence | Existential `H : BasedFunctor F G`, `H.toFunctor.IsEquivalence` |
| (3) compatibility with the canonical maps from U and V | `κ : ModuliTwoIso (a.comp H) ((discreteModuliMap (yoneda.map q)).comp b)` |
| (3) the map is the one induced by the restriction | The equality for every test scheme, endpoints, and original arrow identifies its image with the arrow induced by f; `spaceGroupoidPresentationArrow` supplies the necessary endpoint transports |
| Representable properties use scheme base changes and etale scheme charts | Existing `ModuliSpaceTest`, `MapIsFlat`, and `MapIsLocallyOfFinitePresentation` |
| Surjectivity uses field-extension local lifting | Existing `IsSurjectiveModuliMap`; on the scheme map q use `Surjective q.left` |

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `discreteModuli`,
  `discreteModuliMap`, `ModuliTwoIso`, `moduliTwoFiberProduct`,
  `HasAlgebraicSpaceDiagonal`, `IsRepresentableByAlgebraicSpaces` and the underlying
  fibred-groupoid/stack definitions. Its curve-specific definitions are not copied.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `IsAlgebraicSpace` and the full-subcategory morphisms.
- `Sheaf.AlgebraicGeometry.GroupoidScheme`: `IsGroupoidScheme` read in full; the
  item's general-space form uses the already landed generalization below.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceGroupoid`: `IsPresheafGroupoid`.
- `Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation`:
  `SpaceGroupoidQuotientPresentation`, `spaceGroupoidPresentationArrow`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFlat`,
  `MapIsLocallyOfFinitePresentation` (`MapIsLocally` with the recorded scheme properties).
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliSpaceTest`, whose
  definition is general for based categories and does not impose a DM hypothesis.
- `Sheaf.AlgebraicGeometry.ModuliChartNormalization`: `moduliTwoFiberLift`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`, the actual
  representable fppf sheaf of a scheme, owned by `def-trf-scheme-algebraic-space`.
- `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`:
  `IsSurjectiveModuliMap`, the exact unchanged field-extension lifting convention,
  recorded by the existing definition node `def-sfb-surjective-moduli-map`.
- `Sheaf.AlgebraicGeometry.EtaleSmoothAtlasFppfDescent`:
  `isFppfModuliStack_of_etale_smooth_atlas`, kept for the fppf-stack comparison in (2).
- `Sheaf.CategoryTheory.GroupoidStackificationLocalDescription`:
  `Pseudofunctor.exists_groupoid_stackification_local_description`, read with its
  sheafification-unit normalization, local objects, and extension clause.
- Mathlib `Scheme`, `Flat` (including `Flat.iff_flat_stalkMap`),
  `LocallyOfFinitePresentation`, `Scheme.fppfTopology`, and `Limits.pullback` with
  its projections and `pullback.map`. The size convention has no declaration.

The eight added statement dependencies own exactly the landed interfaces used above:
`def-sfb-algebraic-space-groupoid`, `def-sfb-space-groupoid-quotient-presentation`,
`def-sfb-space-morphism-properties`, `def-sfb-algebraic-moduli-stack`,
`def-sfb-dm-stack-morphism-properties`, `def-sfb-moduli-chart-normalization`,
`def-trf-scheme-algebraic-space`, and `def-sfb-surjective-moduli-map`.
No dependency record or module is changed in this repair. The proof imports include the recorded
chart test, algebraic-space fibre products, sheafification, and the Mathlib
`Precoverage.mem_coverings_of_isPullback` match for fppf base change. The three proof
nodes `lem-sfb-flat-groupoid-algebraic-quotient`,
`lem-sfb-self-relation-quotient-embedding`, and
`lem-sfb-stack-fully-faithful-local-equivalence` currently have no Lean record, so
there is no module to import for those future proofs; none is required as extra
hypothesis to state this item.

Edge cases checked before drafting and again on the final signatures:

- The empty scheme and empty groupoid are allowed. No nonemptiness assumption occurs,
  and the presentation uses covering sieves, including the empty cover when covering.
- The identity groupoid gives the scheme/space itself and its ordinary diagonal.
- A flat group scheme over a field gives BG: arrow bijectivity preserves all
  automorphisms, so the statement is not a sheaf-of-isomorphism-classes substitute.
- Clause (3) does not require flat or locally finitely presented arrow projections.
  Its only fppf hypothesis is on q; removing surjectivity would fail for a missed
  connected component. The restriction square retains the full relation, rather
  than merely the orbit relation.
- Nontrivial isomorphisms and changed endpoint representatives are retained by the
  transported arrow equalities. This was an elaboration issue in the first draft,
  repaired using the existing helper with explicit owning spaces.
- Independent category universes are retained. No equality of site object and
  morphism universes, quasi-compactness, smoothness of the fppf map, finite index,
  characteristic restriction, or DM condition is added.

Searches performed with `msearch.py Q03 lem-sfb-fppf-groupoid-stack-presentations`:

- LeanFinder: `quotient stack flat finitely presented groupoid algebraic spaces fppf
  presentation restriction equivalence` returned eight unrelated scheme finiteness,
  flat descent, and quasi-coherent module results; no matching quotient-stack theorem.
- Loogle: `CategoryTheory.Pseudofunctor, CategoryTheory.BasedCategory,
  AlgebraicGeometry.IsGroupoidScheme` returned zero hits (the latter identifier is
  project-specific).
- LeanSearch: `flat locally finitely presented groupoid quotient stack restriction
  equivalence` returned eight unrelated quotient-module and scheme restriction/flat
  descent declarations; no matching theorem.
- Mathlib grep: `quotient.*[Ss]tack|[Gg]roupoid.*[Qq]uotient` in CategoryTheory found
  ordinary quotient/free groupoids, not a quotient stack of algebraic spaces.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for the same pattern and for
  the item id found existing groupoid and presentation definitions, scheme quotient
  sheaves, and proof-docstring references to this item; no theorem with all three
  clauses. Narrow upstream search for `def-fppf|flat-groupoid|04WY|046T` found none.
  Thus the existing groupoid/presentation interfaces are reused and only the three
  theorem statements are new.

Validation: prescribed `scompile.py` compiled this file both as a sandbox module and
under its delivered module name, with no error or non-sorry warning. The normal 60 s
per-file limit was retained. No local Lean/global build, shared-source write or direct
Git command was run. No statement dispute or statement correction is necessary.

## Second reading by Q03

I reread the final node and all three signatures against the source passages and the
existing presentation definition. This is the dispatcher's single-worker self-check;
I have not represented it as an independent agent review. The maintainer's independent
review remains the delivery review requested in the brief.

Clause (1) has precisely the four projection-property hypotheses and all five
object-map/diagonal properties. Its comparison functor is built from the original
arrow isomorphism, so projections and canonicity are preserved. Clause (2) explicitly
starts from the recorded algebraic-stack convention; the existential relation presents
Z itself and its self-product comparison is an equivalence. The further universal
presentation clause supplies exactly the canonical quotient equivalence, with the
specified triangle and arrow equation. Clause (3) includes the full Cartesian relation
square and all operation compatibilities. It imposes no groupoid flatness. The endpoint
transports use the recorded helper, with explicit spaces to avoid elaborator metavariables.
All three theorem proofs remain sorry-only; the existing predicate has its landed
definition-node owner and there are no postponed unowned statements. I found no mathematical statement mismatch after these checks.


## Returned delivery repairs

The latest return on immutable head `4a1d99ac74ac` identifies the extracted
`CategoryTheory.IsSurjectiveModuliMap` as a duplicate of the existing declaration in
`Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus` and explicitly requires
importing and reusing the existing declaration. This repair removes the proposed
`SurjectiveModuliMap.lean` module entirely, removes the proposed calculus-module
modification, and removes both proposed dependency-node edits from the packet.
The item's module publicly imports the existing calculus module and uses its exact
plain predicate. No declaration is renamed or restated.

The earlier H4/H13 return on `74c0f01ddc7f` is still addressed: the item cites the
already landed definition node `def-sfb-surjective-moduli-map`, whose unchanged
`existing: true` Lean record names `CategoryTheory.IsSurjectiveModuliMap` in the
calculus module. It does not cite the calculus theorem node in `stmt_deps` and uses
none of that theorem's conclusions. This keeps definition-node ownership without
moving or duplicating the existing definition. The owner node's statement, record,
and actual declaration/docstring were opened and compared with the use in clauses
(1) and (2): they quantify over field extensions and retain the actual restriction
and vertical comparison isomorphism, with independent category universes.

The repaired packet contains only the item module, item node and this report.
The node was rebased by reading current main and applying only the item's Lean record
and the already-landed statement-dependency additions. All three theorem signatures
and sorry-only bodies are unchanged from the returned head. The import now resolves
the original declaration from its existing module. No dependency metadata, existing
library module, mathematical statement, or proof plan is changed.

Repair self-check: reread the current definition-node record and original predicate,
confirmed the item cites `def-sfb-surjective-moduli-map` rather than the calculus
theorem, checked the final packet has no module declaring the predicate, and checked
that all three item theorem signatures remain unchanged. Server compilation,
the prescribed dry run and delivery are repeated on this repaired packet.
