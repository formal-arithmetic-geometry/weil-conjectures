## Worker report

The item is stated by `AlgebraicGeometry.exists_isom_graph_representatives_zariski_gluing`
in `Sheaf.AlgebraicGeometry.IsomGraphRepresentativesZariskiGluing`. Its sole postponed
proof is this theorem. The accompanying definition module contains real data and
predicates only, with no `sorry`, axiom, chosen witness of an unproved existence
statement, or additional theorem. The item's natural-language statement is unchanged;
its `stmt_deps` gains the definition node described below.

Clause-by-clause correspondence:

- Schemes and separated structure maps: `{S X Y : Scheme.{u}}`, `x`, `y`,
  `[IsSeparated x]`, `[IsSeparated y]`. There is no properness hypothesis on either
  family. The import of Proper supplies the recorded separatedness notion.
- `F(T) = Isom_T(X_T,Y_T)`: `relativeIsomorphisms x y T` is only an abbreviation for
  `Over.mk (pullback.fst T.hom x) ≅ Over.mk (pullback.fst T.hom y)`.
  Thus `X_T` is the canonical `T ×_S X`; symmetry identifies the order used in the
  informal statement. No alternate notion of scheme, morphism, or isomorphism is defined.
- Canonical transitions: `RelativeIsomorphisms.Restricts h e' e` is the commutative
  square with the actual `(Over.pullback x).map h` and `(Over.pullback y).map h`,
  together with the inverse square. The forward square characterizes canonical
  pullback by its two projections; the inverse square follows by uniqueness of inverse.
  This relation specifies the transition without introducing an arbitrary action.
- Set-indexed base-open cover: `I : Type v`, `U`, `b`, their `IsOpenImmersion`
  instances, and `hcover`. Arbitrary schemes mapping by open immersions are equivalent
  to the open subschemes in the node. No finiteness or distinctness of indices is required.
- Local representatives: `Jᵢ i : Over (U i)` and the four instance families
  `IsSeparated`, `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated`.
  This is exactly the node's explicit meaning of separated and finite presentation.
- Given bijections on all local tests: `eᵢ i T` has domain `(T ⟶ Jᵢ i)` and
  codomain `F((Over.map (b i)).obj T)`. The latter test has the composite map to S,
  so the bijections use the original families, not an unrelated local functor.
  `hnatural` quantifies over every `U_i`-morphism and uses its actual image under
  `Over.map (b i)`, in both forward and inverse squares.
- Given graph classification: `hgraphs` uses `IsRelativeIsomGraphClassification`.
  Its first clause makes every actual graph `(1,e)` a closed immersion. Its projections
  are identity and the isomorphism by the defining pullback lift, hence invertible.
  Its second clause quantifies over every closed immersion `j` and every pair of
  projection isomorphisms `p`, `q`. It gives exactly one point with forward map
  `p.inv ≫ q.hom` and graph ideal equal to `j.ker`. Scheme presentations differing
  by source isomorphism are thereby the same closed subscheme. This is classification
  of closed subobjects, rather than literal equality of source schemes.
- Zariski sheaf property: the first conclusion is `IsRelativeIsomZariskiSheaf.{u,w}`.
  It quantifies over every test, every `Type w` covering index, open immersion chart
  maps, their pointwise covering assertion, and compatible isomorphisms. Compatibility
  is tested after any two maps from a common test into charts with equal composites
  to T. Taking that test to be the chart intersection gives usual overlap agreement;
  conversely overlap agreement pulls back to every such pair. The comparison is made
  in Y_T. Inclusions Y_chart → Y_T are monic, so this loses no equality. The unique
  global isomorphism restricts with BOTH forward and inverse squares. The universe
  `w` is independent of the given base cover's `v` and universally generalized.
- Global representing scheme: `∃ J : Over S, ∃ E : RelativeIsomGraphRepresentation x y J`
  with the same four morphism-property clauses. `E.equiv` is a bijection for every
  S-test; `E.natural` is its naturality; `E.graphs` states both directions of the
  graph and inverse-projection classification for the global bijection.
- Local open subfunctors and their representations: `j i` is an S-map from the
  local representing scheme, `IsOpenImmersion (j i).left`, and the square
  `IsPullback (j i).left (Jᵢ i).hom J.hom (b i)`.
  Thus an S-map T → J lifts to Jᵢ exactly when its structure map factors through U_i,
  uniquely because the immersion is monic. On U_i-tests, the displayed equality
  `E.equiv ... ((Over.map (b i)).map a ≫ j i) = eᵢ i T a` identifies the representation
  with the GIVEN local bijection. Hence it is precisely F_i, not merely an open
  subscheme with unspecified point classification.
- Natural representing isomorphisms: `χ i : (Over.pullback (b i)).obj J ≅ Jᵢ i` is
  an isomorphism OVER U_i; its displayed equation with `j i` identifies its other
  projection. These two equations characterize the canonical comparison and,
  together with the preceding equality of bijections, make it a representing comparison.
- Pullback of the inclusion by ANY element ξ of F(T): the next clause uses exactly
  `((E.equiv T).symm ξ).left`. Its fibre product with `j i` has open second projection.
  The comparison `c` with `pullback T.hom (b i)` specifies BOTH the T and U_i
  coordinates. Consequently this is precisely the canonical open `T ×_S U_i → T`,
  including when ξ is not a universal element.
- Overlap and global graph preservation: the same `E` is a graph classification and
  agrees with every `eᵢ` on every test through the specified `j`. On an overlap,
  its two local classifications therefore identify the SAME isomorphism and the
  SAME actual graph ideal; applying the inverse bijections gives both directions.
  The overlap identification is the unique representing comparison obtained from
  `χ i`, `χ j`; the statement does not replace the prescribed bijections with new ones.
- Arbitrary base change: the final clause quantifies over EVERY `B : Scheme.{u}`
  and `b' : B ⟶ S`. `EB` represents the functor for the actual second projections
  `pullback.snd x b'`, `pullback.snd y b'`, by `(Over.pullback b').obj J`.
  The point corresponding to `a` is tied to `E` by the inverse of
  `(Over.mapPullbackAdj b').homEquiv T J`, not an arbitrary bijection.
  `relativeIsomBaseChangeIso` is the concrete symmetry/pasting/symmetry comparison.
  The first two equations commute with the forward AND inverse isomorphisms.
  The last is an equality of the actual graph maps under the canonical ambient
  comparison `relativeIsomGraphBaseChangeMap`. `EB.graphs` includes closedness,
  equality of graph ideals, unique recovery of every graph, and exactly the formula
  `p.inv ≫ q.hom` after each base change. The same assertion applies to identity
  base changes and to any further base change; `EB.natural` covers arbitrary tests.
- The statement imposes no Noetherian, reducedness, quasi-compactness, or finiteness
  condition on S, B, or T. Only the specified local and global structure morphisms
  have finite-presentation conditions.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper` and its recorded
  `IsSeparated` clause, whose actual class is in Morphisms.Separated.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`, and `pullback.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; quasi-compact and quasi-separated retain their
  Mathlib meanings, as required by the node.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- New definition dependency: `Sheaf.AlgebraicGeometry.RelativeIsomGraphClassification`,
  `RelativeIsomGraphRepresentation`, with every helper listed in `lean.declarations`.
- Additional Mathlib constructions: `Over.mk`, `Over.homMk`, `Over.map`, `Over.pullback`,
  `Over.mapPullbackAdj`, `pullbackSymmetry`, `pullbackLeftPullbackSndIso`, and
  `Scheme.Hom.ker` (IdealSheaf.Basic through IdealSheaf.Functorial).

Proof-dependency imports are present for the recorded general scheme gluing theorem
`Scheme.exists_scheme_of_zariski_cocycle` in
`Sheaf.AlgebraicGeometry.ExistsSchemeOfZariskiCocycle`, morphism gluing in
`Mathlib.AlgebraicGeometry.Gluing`, and Yoneda full faithfulness in
`Mathlib.CategoryTheory.Yoneda`. The other proof dependencies are the Mathlib
base-change, locality, and separated/quasi-separated declarations supplied by the
public imports of OpenImmersion, Proper, ClosedImmersion, and FinitePresentation.
Their signatures and node records were read; no dependency module repair is needed.

Edge cases checked before drafting:

- Empty S admits an empty cover. No Nonempty or finite-index hypothesis is used.
  The empty test has a unique relative isomorphism, including its inverse; the empty
  covering case of the sheaf condition states precisely this unique gluing.
- Empty X and Y give singleton Isom sets; exactly one empty source/target over a
  nonempty test can instead give no isomorphism. No test Isom set is assumed inhabited.
- Infinite covers, repeated indices, empty charts, non-quasi-compact overlaps and
  non-quasi-compact S are allowed. Quasi-compactness is relative to the target.
- Nonreduced tests are retained: graph identity is equality of ideal sheaves, not
  equality of supports or of geometric-point sets.
- B → S may be an identity, an open immersion, or any other morphism, including
  maps from non-Noetherian or empty schemes. No flatness condition is imposed.
- All schemes/tests share arbitrary universe u; both cover index universes v and w
  are independently generalized. There is no restricted universe of test schemes,
  finite cover, field, characteristic, or classical pointwise surrogate.

Searches made (all before introducing the interface):

1. msearch LeanFinder: “Zariski gluing of local schemes representing the relative
   isomorphism functor preserves closed graphs and finite presentation”. Eight generic
   gluing/local-representability hits, principally `Scheme.LocalRepresentability.glueData`
   and `.toGlued`; none is the full theorem. Read Representability.lean, including
   `representableBy`/`isRepresentable`, which assume a sheaf and open covering subfunctors.
2. msearch Loogle: `Over.pullback, Iso` returned zero with unknown short identifier.
   Corrected query `"CategoryTheory.Over.pullback"` returned seven hits including
   the canonical pullback and composition API, reused here.
3. msearch grep: `isomFunctor|isomPresheaf|IsomScheme|graph.*[Rr]epresent` in
   Mathlib AlgebraicGeometry returned zero.
4. msearch LeanSearch: “The functor of isomorphisms between two schemes after base
   change”. Eight hits, including generic stability of isomorphisms, `Functor.mapIso`,
   and `Scheme.IdealSheafData.comapIso`; no relative Isom graph-classification interface.
5. msearch LeanFinder: “Natural bijections representing relative scheme isomorphisms
   with closed graphs and inverse projection recovery”. Eight scheme-isomorphism and
   ideal-sheaf-comparison hits; no packaged classification or representation.
6. msearch grep for the proposed names returned zero; direct rg of Mathlib, upstream
   WeilConjectures, Sheaf, and `dag/lean_names_upstream.json` likewise found none.
   Direct rg of graph/Isom concepts found RelativeMorphismsPresheaf,
   ProjectiveCurveIsomGraphs, GraphsOpenInHilbert, and BoundedDoubleGraphHilbertLocus.
   They were opened and read. They handle general morphisms in a different ambient
   product, or stronger projective/Hilbert hypotheses; none states this general result.
   The parent project's isomorphism type is reused literally as the abbreviation's RHS.
7. DAG definition-title search for isomorphism/graph notions found no general graph
   classification datum. `tools/blueprint_refs.py search 'relative isomorphism'`:
   zero blueprint-node matches. `blueprint_refs.py ancestor` returns `None`, as already
   recorded by the item; the new node inherits the item's unit/via chain.
8. Direct rg for this exact item id in upstream WeilConjectures found no match.
   Searches and their actual msearch JSON results are preserved in the new node.

No STATEMENT-DISPUTED flag, source-based statement correction, or dependency repair
was needed. This is stage 2: the theorem is intentionally `by sorry`, with the full
8-step source proof in its docstring. Validation uses scompile.py for each file,
then deliver2.py dry run and delivery; no library build or direct repository edit.

## New nodes

`def-sfb-relative-isom-graph-classification` introduces only the missing reusable
interface used by this item: the abbreviation for the existing Over-category
isomorphism type, canonical restriction relation, actual graph lift into
`X_T ×_T Y_T`, its two-sided closed-graph classification, natural representing
bijections, Zariski descent predicate, and canonical base-change comparisons.
Source: Stacks schemes.tex Tags 01JP, 01JJ and 01KT. The search record includes
LeanSearch, LeanFinder, successful Loogle, Mathlib/project grep, and the DAG search.
The existing relative-morphism presheaf is not duplicated: it contains ALL morphisms
and its graph ambient is `(X ×_S Y)_T`; this interface uses the existing isomorphisms
in Over T and the direct product over T from the present node. The base-change
maps are actual Mathlib symmetry/pasting and pullback.map constructions. All eight
declarations are owned by this one definition node, with source/blueprint docstrings.
The graph-classification and sheaf assertions are predicate definitions, not
postponed theorems or assumed constructions. No existing notion's mathematical data
is redefined. The main node cites this new node in `stmt_deps`.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
