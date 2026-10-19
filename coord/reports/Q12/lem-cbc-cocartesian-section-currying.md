## Worker report

The module `Sheaf.CategoryTheory.CocartesianSectionCurrying` states
`SSet.Enhanced.CocartesianSectionCurrying.cocartesian_section_currying :
Nonempty Statement.{u}`. Its only postponed proof is that theorem, with the node's
six proof steps in its docstring. `Statement` lists the conclusions as a single
simultaneous family, so its naturality assertions refer to the same currying maps.
No statement has been corrected, no dependency has been replaced, and no new node
is required. The helper declarations implement or describe this node's own marked
mapping objects and canonical comparison. Their data contain no `sorry` or choice.

Hypothesis and clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Choose a common containing universe; small S and Q and parameter A therein | Explicit `universe u` and `S Q A : SSet.{u}`. CatInfinity and coCart retain their recorded universe `u+1`; only their mapping-space source is explicitly lifted. |
| S is a quasicategory | `[Quasicategory S]` in each applicable field; explicit `hS` in product classification. |
| q:Q -> S is a cocartesian fibration of quasicategories | `(q : Q ⟶ S)`, `[Quasicategory Q]`, and `hq : cocartesianFibration q`; these are assumptions of each assertion, not assertions that every map is a fibration. |
| L_q is precisely the recorded cocartesian section object, including all transformations | `(cocartesianSections q).toSSet` from EnhancedCartesianFibration; no second section object is defined. |
| L_q is a quasicategory | `Statement.sections_quasicategory`. |
| Every quasicategory A in the common universe | `(A : SSet.{u}) [Quasicategory A]`, with no nonemptiness, Kan or other condition. |
| S x A -> S is cocartesian | `Statement.product_fibration`, using the actual degreewise product and first projection `fst S A`; the arbitrary-base predicate is exactly the existing horn/lift definition. |
| The product is classified by the constant diagram Delta_S A | `product_classification` uses the actual straightening of a coCart vertex whose marked object is `over (fst S A)`, an actual CatInfinity vertex `a` with `catInfinityObject a = A`, and `AreNaturallyEquivalent` to the whole constant diagram `SSet.const a`. The equality fixes the marked fibration, not merely an equivalent fibre object. |
| The right side is the full relative functor subcategory on cocartesian maps, retaining arbitrary transformations | `families (fst S A) q` is an abbreviation for the existing `Marked.Over.cartesianFunctors`, specialized to the natural cocartesian markings. That existing declaration is the full subcomplex of `funOver` on marking-preserving vertices, not the sharp complex or its core. The `marking` helper adjoins degeneracies explicitly; `space_comparison` includes its exact natural-fibrancy assertion, so these markings are precisely the cocartesian edges in the theorem's cases. |
| Currying is an equivalence of the two quasicategories | `curry` gives its actual simplicial map and `curry_quasicategories` gives both quasicategory assertions and `IsFunctorEquivalence`. No simplicial isomorphism, stronger than the requested conclusion, is asserted. |
| Degree n merely rearranges S x A x Delta[n] | `curry_formula`: for every degree n, test degree k, monotone map a:[k]->[n], base simplex s and parameter simplex b, the underlying relative map at `((s,b),Delta(a))` is `sectionValue q k s (h.app k a.op b)`. All coordinates of every map are fixed. |
| The induced core comparison is an equivalence of spaces with Map_coCart(S)(S x A,Q) | `space_comparison` gives the normalized map `c` from the actual core of Fun(A,L_q) to the naturally marked `mapSharp` and its weak homotopy equivalence; it states both Kan conditions. It further supplies the comparison `d` from the lift of that sharp complex to the actual recorded right-pinched `mappingSpace` of `CocartesianStraightening.coCart`, and asserts weak equivalence of `d` and the composite `uliftFunctor.map c ≫ d`. `IsCoCartComparison` fixes the source/target coCart objects, every vertex, the constant initial block, final identity and every remaining enriched mapping simplex by the greatest-vertex-of-subset formula of the recorded coherent-nerve comparison. Thus the target is literally the recorded coCart mapping space, not an arbitrary space with a claimed interpretation. |
| Evaluation is cocartesian | `evaluation_cocartesian` applies `preservesCocartesianEdges` to the actual `MonoidalClosed.uncurry` of the recorded section inclusion. It includes the equation saying evaluation is over S. The already published `cocartesianSectionEvaluation` in the downstream CocartesianSectionsLimit module is the same composite expressed using tensor functoriality; no duplicate map is declared and no downstream import is introduced. |
| For every a:A -> L_q the image is evaluation after id_S x a | `evaluation_represents`, on every test simplex and every (unique) Delta[0] parameter; its right side is literally `(𝟙 S ⊗ₘ a) ≫ MonoidalClosed.uncurry (...)`. |
| Coherence in A | `parameter_naturality` supplies the precomposition map on the full relative category, fixes it on all simplices, and equates the two composites with the same `curry`. |
| Coherence under cocartesian Q -> Q' over S | `postcomposition_naturality` binds both fibrations, the specified g and its equation over S, and exactly the hypothesis `preservesCocartesianEdges q q' g comm`. It supplies the induced section map r, fixes its evaluation, and for every A fixes the full relative map t and its commuting currying square. |
| Restriction along every functor v:T -> S | `restriction_naturality` assumes only T is a quasicategory and v is a simplicial map. It concludes, rather than assumes, quasicategory and cocartesian-fibration proofs for `pullback v q -> T`. It supplies the section map and relative mapping map, fixes both pullback projections on every simplex, and equates the currying composites. |
| Compatibility with every simplicial operator and higher coherence | Every comparison and induced map above is a simplicial map, and every normalization quantifies over all degrees and parameter simplices. Thus the displayed equations commute with every face and degeneracy. The formulas uniquely fix precomposition, postcomposition and pullback maps and retain their identity, composition and mixed higher compatibilities; no unrelated choices of equivalences substitute for these maps. |

Recorded dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `fullSubcomplex`, `core`,
  `diagramVertex`, `mappingSpace`, `IsFunctorEquivalence`,
  `AreNaturallyEquivalent`, `IsWeakHomotopyEquivalence`; Mathlib's `ihom`,
  `Quasicategory`, `KanComplex`, products and simplicial maps are reused.
- `Sheaf.CategoryTheory.EnhancedCartesianFibration`: `sectionSSet`,
  `sectionMap`, `cocartesianSections`, `CatInfinity`; their signatures and
  docstrings were read in full. The definition record's primary `sectionSSet`
  and its full-subcomplex specialization supply the actual section object.
- `Sheaf.CategoryTheory.CocartesianStraightening`:
  `CocartesianStraightening.Statement`, `coCart`, `object`, `classify`,
  `EquivalenceData`, `cocartesian_straightening`; uses its actual normalized
  relative-model enrichment and classifying equivalences. Its imported
  `catInfinityObject` decodes the constant value without replacing it.
- The existing `Marked.Over.cartesianFunctors`, `funOver`, `mapSharp`,
  `IsNaturallyFibrant`, `RelativeCartesianModelStatement.mapping_iso` and
  `mapping_core` are reused through the recorded straightening interface.
- Proof-dependency imports are `InfinityFibrationsOverSimplicialBases`,
  `CoherentNerveComparison`, `InfinityCocartesianCompositionInitiality`,
  `InfinityCocartesianMappingCriterion`, and `PointwiseCocartesianTransport`.
  The relevant horn definitions and full coherent-mapping-comparison signature
  were read before writing the normalization.

Edge cases checked mathematically against the definitions:

- A empty: both full functor objects are terminal, including higher simplices;
  no `Nonempty A` binder appears.
- S empty: q has empty total space and its section object is terminal. All
  normalizations remain meaningful, and the model nerve still has its
  empty fibration object.
- S a point: L_q agrees with Q, and currying is the ordinary full internal Hom
  comparison. The sharp mapping complex takes its core only in the spaces clause.
- S=Delta[1]: transformations between cocartesian sections may have
  noninvertible components; the full-subcomplex `families` and original section
  object retain them.
- Identity maps and composites in all three variables obey the same degreewise
  formulas. General v is retained, with no injectivity, equivalence or
  cocartesian-preservation restriction on the base functor.
- Universes: no equality between a site's object and morphism universes or
  independent smaller test universe is introduced. All inputs already lie in
  the common containing universe expressly chosen in the node.

Searches performed before writing:

- `msearch.py ... leanfinder`: “Cocartesian sections of a cocartesian fibration
  form a quasicategory and currying identifies parameter families with
  cocartesian maps from product fibrations”. Eight hits concerned ordinary
  categorical cocartesian arrows (`Functor.IsCocartesian.*`), with no match.
- `msearch.py ... loogle 'SSet.Quasicategory, MonoidalClosed.curry'`: no hits;
  the remote index did not recognize the unqualified MonoidalClosed.curry.
- `msearch.py ... leansearch 'Cocartesian section parameter currying equivalence
  of functor quasicategories'`: eight hits, including ordinary categorical
  `Functor.curry`, `Functor.curryingEquiv` and `Over.sectionsCurry`. These are
  not the quasicategorical relative mapping statement.
- `msearch.py ... grep 'cocartesian.*section|section.*cocartesian|section.*currying'
  AlgebraicTopology`: no hits in Mathlib.
- `rg` over the project's Lean, upstream WeilConjectures, and upstream-name
  index for currying, cocartesian sections, the item id, natural cocartesian
  markings, and the expected names: no theorem matching this item. Published
  downstream section-limit uses and its evaluation expression were inspected;
  they do not state the parameterized comparison. No existing cocartesian
  natural-marking constructor was found; the cartesian version in
  RelativeMarkedAnodyneCalculus was read but has opposite variance.

Source verification: opened HTT's actual PDF at Remark the project server (printed p.154,
PDF p.171), which distinguishes the full marked relative functor quasicategory
from its sharp mapping core. Opened Kerodon 05RX and 02TK, which use the same
cocartesian-section category. The parameterized formulas are the foundation
formulated by this node, exactly as its source record explains.

Validation: scompile.py compiled this delivered module individually in the sandbox
and as its library module, cleanly within the 60-second limit. No warning other
than the permitted postponed theorem warning, and no errors. Every variable and
universe is explicitly bound with `autoImplicit false`. All lines are at most
100 characters. The forthcoming dry run repeats per-file compilation and the
maintainer preflight.
## Dependency modules

The recorded dependency `lem-coef-space-valued-straightening` imports
`Sheaf.CategoryTheory.SpaceValuedStraightening`, whose existing declaration was unusable
under the delivery compiler: its `Diagrams` abbrev depended on the noncomputable
`smallSpaces` without a `noncomputable` modifier. I copied that dependency node and its
full module into this packet, changed only its `lean.note`, and repaired the declaration to
`noncomputable abbrev Diagrams`; all other declarations, signatures, and the theorem
statement are unchanged. The repaired module compiles before the target and is needed
transitively through `CocartesianStraightening -> CompleteAlgebroid ->
KanRelativeNerveLeftFibration`.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
