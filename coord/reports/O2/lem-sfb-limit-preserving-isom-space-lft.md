## Worker report

The module `Sheaf.AlgebraicGeometry.LimitPreservingIsomSpaceFiniteType` states
`CategoryTheory.limit_preserving_isom_space_locallyOfFiniteType` and
`CategoryTheory.limit_preserving_isom_space_fibreProduct`. Both proofs are exactly
`by sorry`. There are no new definitions, axioms, dependency repairs or statement
corrections. The original mathematical statement and proof are unchanged. Five
already landed definition nodes are added to stmt_deps to name the existing
interfaces used explicitly in the signatures; no node besides this item is edited.

Sources read: `literature/stacks-project/artin.tex`, definition-limit-preserving
(Tag 07XL), lemma-diagonal (0CXI), and lemma-base-change-versal (0CXM), including
its first proof paragraph. The proof follows the item's accepted four steps:
identify the diagonal fibre with the discrete Isom functor; descend v/u and use
(a_j,id,delta_j) for the relative object-descent test; forget finite relations in
finite presentations; then apply base change, composition and the universal
etale chart test. Each statement's docstring records the full route. The two
proof prerequisites `lem-sfb-representable-lfp-object-limit-test` and
`lem-sfb-stack-finite-type-calculus` have no Lean record in the read repository;
they are only proof prerequisites, so neither missing declaration is needed to
type these signatures. Their imports will be added when their statements land.
All currently stated proof dependencies are imported (the three chart/locality
modules, plus Mathlib finite presentation and finite type).

Hypothesis and clause correspondence:

1. An arbitrary scheme S is `{S : Scheme.{u}}`. The size convention is explicit
   `universe u v w`, with no equality between u, v and w. Schemes and spaces are
   in the existing project's universe u; F has independently arbitrary total
   category morphism and object universes v,w. The existing limit predicate
   quantifies over nonempty directed preorders `I : Type u` and affine limit
   cones in `Over S`, exactly the stated small directed affine systems.
2. The fibred groupoid is `F : BasedCategory.{v,w} (Over S)` together with
   `hF : IsFibredInGroupoids F`. Its definition requires cartesian lifts and the
   strong cartesian universal property for every arrow; hence fibres are
   groupoids and identity/composition pullback coherence is the canonical one.
   No covering descent (`IsModuliStack`) is assumed.
3. Limit preservation is `hLimits : FibredGroupoidLimit.IsLimitPreserving F`.
   Reading its actual definition, it is the conjunction `ObjectsDescend F ∧
   ArrowsDescend F ∧ ArrowEqualitiesDescend F`, with the compatibility equations
   on the specified pullback lifts. No object-only substitute is used.
4. Representability of all Isom presheaves is `hDiagonal :
   HasAlgebraicSpaceDiagonal F`. This is the existing equivalent scheme-test
   formulation: every `h_T ×_F h_U` is equivalent over Sch/S to the discrete
   groupoid of an algebraic space. To pass from the node's formulation, take
   over T×_S U the Isom space between the two pulled-back objects. Conversely,
   pull such a presentation back along T→T×_S T to represent Isom(x,y).
   This equivalence requires only fibredness, not a stack or an atlas.
5. In the first theorem, `T : Over S`, `x y : Functor.Fiber F.p T` are the
   arbitrary fibre objects. `I : AlgebraicSpace S` with
   `p : I.obj.obj ⟶ yoneda.obj T` is an arbitrary proposed algebraic space over
   T. `hI` spells out that it represents the Isom presheaf. Its equivalence e
   identifies sections of I over q with isomorphisms `xU ≅ yU` for every choice
   of cartesian pullback lifts a,b. Its final equation
   `(e ... z').hom.val ≫ d = c ≫ (e ... z).hom.val` is naturality under further
   pullback, including a change of chosen lifts. This is the same explicit
   convention as the landed `dm_isom_space_unramified` signature, read in full.
   hI is not an extra restriction on an Isom space: it is its representing
   property, and hDiagonal supplies the existence assumed by the node. The
   theorem applies to every such I,p, not just one chosen representative.
6. The first conclusion is `MapIsLocally (@LocallyOfFiniteType)
   (ObjectProperty.homMk ⟨p⟩ : I ⟶ schemeSpace T)`. Expanding the recorded
   predicate, this tests local finite type on every compatible pair of
   representable etale scheme charts of I and T, exactly the space notion in
   the node. It does not assert finite presentation as an extra conclusion.
7. In the second theorem U,V are objects of `Over S`, with just
   `[LocallyOfFiniteType U.hom] [LocallyOfFiniteType V.hom]`. The objects x,y
   are encoded by `BasedFunctor (discreteModuli (yoneda.obj U)) F` and its V
   counterpart. Fibred Yoneda identifies these cartesian sections with
   arbitrary objects of F(U), F(V); this keeps the pullback data instead of
   taking isomorphism classes.
8. The existential Z is an `AlgebraicSpace S`. Its representing equivalence
   `e : BasedFunctor (discreteModuli Z.obj.obj) (moduliTwoFiberProduct x y)`
   with `e.toFunctor.IsEquivalence` represents precisely the triples of two
   base maps and a fibre isomorphism. No arbitrary point bijection is used.
   The two `Nonempty (ModuliTwoIso ...)` clauses identify its first and second
   projections with `p ≫ yoneda.map prod.fst` and `p ≫ yoneda.map prod.snd`.
   They are vertical natural isomorphisms, so the projections are pinned.
9. `U ⨯ V` is the product in `Over S`, whose underlying scheme is the chosen
   scheme pullback of U.hom and V.hom, i.e. U×_S V, with the two corresponding
   projections. `p : Z.obj.obj ⟶ yoneda.obj (U ⨯ V)` therefore specifies Z's
   actual map to that fibre product. The three successive `MapIsLocally
   (@LocallyOfFiniteType)` conclusions give Z→U×_S V, Z→U and Z→V, using the
   same p and its two composites.
10. The final quantifier is over every `W : Over S` and every
    `b : yoneda.obj W ⟶ Z.obj.obj` satisfying `AlgebraicSpace.IsEtale b`.
    There is no surjectivity requirement. The two `LocallyOfFiniteType`
    statements apply to the Yoneda inverse of b followed by p and the relevant
    projection. They are exactly W→Z→U and W→Z→V.

Dependency declarations used (source signatures and docstrings inspected):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, the affine-local finite-generation
  condition in def-weil-finite-type-morphism. QuasiCompact is not assumed here.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, used
  by the recorded space scheme-test definition; the affine-local etale notion.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`; products in Over S use this
  chosen construction. No competing fibre-product definition is introduced.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and `AlgebraicSpace.IsEtale`. Spaces are the existing full subcategory of
  fppf sheaves with representable diagonal and an etale surjective atlas.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `IsFibredInGroupoids`, `discreteModuli`, `discreteModuliMap`,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `ModuliTwoIso`,
  `HasAlgebraicSpaceDiagonal`. These are reused rather than redeclared.
- `Sheaf.AlgebraicGeometry.FibredGroupoidLimitPreserving`:
  `FibredGroupoidLimit.IsLimitPreserving`, the arbitrary-base version landed
  on 2026-10-24. The integer-base ArtinCriterion copy is not used.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `moduliTwoFiberSnd`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`; this is
  the existing Yoneda representable sheaf, not a newly chosen space.
- `def-weil-size-convention` is a metatheoretic convention with no declaration;
  the explicit universe binders implement it as its lean record instructs.

Edge cases checked before drafting and again against the finished signatures:
empty S, empty T, empty U or V, empty Isom functors, nontrivial automorphisms,
one-stage and non-strict directed systems, and nonsurjective etale charts.
No quasi-compactness, separation, Noetherianity, stack descent, restriction on
characteristic or equality of total-category universes appears. The naturality
condition handles identity restrictions and different lift choices. The chart
conclusion permits an empty W. There is no `let`, local notation, local instance,
private helper, or auto-bound variable. No STATEMENT-DISPUTED fault was found.

Searches made on 2026-10-24 with the prescribed msearch.py wrapper:

- LeanFinder: `A limit preserving category fibred in groupoids has locally
  finite type representable Isom algebraic spaces`. Eight hits, including
  LocallyOfFiniteType, LocallyOfFinitePresentation, scheme composition
  instances and the implication LFP→LFT; none is this fibred-groupoid theorem.
- Loogle: `"AlgebraicSpace", "FiniteType"`. Zero hits.
- Mathlib grep: `Isom.*[Ll]imit|[Ll]imit.*[Ii]som|AlgebraicSpace` in
  AlgebraicGeometry. Four unrelated scheme/categorical limit-isomorphism hits
  (AffineTransitionLimit, Gluing, AffineScheme); no algebraic-space theorem.
- LeanSearch: `Limit preservation of a fibred groupoid implies local finite
  type of its representable diagonal`. Eight hits on representable functors,
  categorical diagonal representability, filtered limits and Galois fibre
  functors; none contains the scheme local finite type conclusion.
- rg of lean/WeilConjectures and lean/Sheaf for limit-preserving diagonal,
  Isom/limit, and local-finite-type names, plus the exact blueprint id via
  grep: no existing statement. Project search located and reused
  FibredGroupoidLimitPreserving and the moduli/space vocabulary. The existing
  `DMIsomSpaceUnramified` theorem assumes a DM stack and concludes unramified,
  so it cannot replace this arbitrary fibred-groupoid theorem.

Validation: the initial complete module passed scompile.py in sandbox mode
(16.6 seconds) and module/library mode (10.9 seconds), without errors or
unexpected warnings. A plain proof-dependency import of Mathlib finite
presentation was then added; the required delivery dry run recompiles the final
file. All writes are confined to the assigned sandbox, and no direct git or
build command was run in the shared read clone.

## Second reading by O2

This is an in-session second pass, not an independent agent's review: the
explicit dispatcher brief forbids starting other agents. I reopened the node
and finished module and checked each of the ten correspondences above; the
maintainer's delivery review remains the independent review.

In particular I checked that hDiagonal is equivalent to Isom representability
without assuming stack descent, hI requires natural representing bijections
for all lifts (not an unrelated set equivalence), and hLimits includes arrows
and their equalities. I compared the first signature's hI with the existing
DM Isom interface and checked that its c,d equation has the same orientation.
The fibre-product equivalence retains both projections through vertical
ModuliTwoIso, and all three MapIsLocally conclusions use those same maps.
The last two conclusions quantify over all etale b, not only surjective
atlases. The product is taken in Over S, not over the terminal scheme.
No missing clause, strengthened finiteness assumption or additional universe
restriction was found. The only change after the first compile was adding
the plain finite-presentation proof import. No new or dependency module needs
a separate audit in this delivery.
