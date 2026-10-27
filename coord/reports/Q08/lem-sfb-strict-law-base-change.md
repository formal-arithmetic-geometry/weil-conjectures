## Worker report

The delivery states lem-sfb-strict-law-base-change in
Sheaf.AlgebraicGeometry.StrictLawBaseChange and supplies the missing relative notions in
Sheaf.AlgebraicGeometry.RelativeBirationalLaw. The item's natural-language statement is
unchanged. Its stmt_deps gains def-sfb-relative-birational-law. Every theorem has proof
`sorry`; all definitions have concrete data, with no postponed construction proofs.

Clause-by-clause correspondence:

- Schemes S,Y,T are `Scheme.{u}`, with explicitly bound universe u. The structure morphism
  is `f : Y ⟶ S`, or `Y.hom` for `Y : Over S`. An arbitrary `g : T ⟶ S` has no property
  assumptions. Products in `Over S` are the existing categorical products, constructed
  from scheme pullbacks, and `Over.pullback g` is the recorded scheme base change.
- S-density of U is `f.IsFiberwiseDenseOpen U`, namely
  `∀ s, Dense ((f.fiberι s) ⁻¹' (U : Set Y))`. The fibre and embedding are Mathlib's
  scheme-theoretic `Scheme.Hom.fiber` and `fiberι`, not set-theoretic fibres in place of schemes.
  `IsFiberwiseDenseRange` is the same condition on a chart image.
- The chart includes `domain : Over S`, `inclusion : domain ⟶ X` and `hom : domain ⟶ Y`.
  `IsRational` requires an open immersion inclusion with S-dense range.
  `Agrees` gives an open immersion i:E→X with S-dense range, maps into both domains,
  their two inclusion equations, and equality of the two maps to Y. RelativeRationalMap
  is the quotient of rational representatives by this agreement; Quot takes its equivalence
  closure, which equals the stated relation by intersection of fibrewise dense opens.
  Mathlib RationalMap.IsOver does not impose this relative density condition.
- `IsBirational` additionally requires the hom to be an open immersion with S-dense image.
  An open immersion is canonically an isomorphism onto its open image, so this expresses
  exactly an isomorphism between S-dense opens, without choosing a second copy of that image.
- Smoothness is `[Smooth f]`. Finite type is `[LocallyOfFiniteType f] [QuasiCompact f]`,
  the recorded conjunction. Separatedness is `[IsSeparated f]`, whose existing definition
  requires `IsClosedImmersion (pullback.diagonal f)`. Nonempty fibres are `[Surjective f]`;
  every point in a fibre maps to a point above its base point and, conversely, a point above
  s supplies a fibre point through Spec of its residue field. No geometric connectedness,
  integrality, reducedness or extra hypothesis is imposed.
- `leftTranslation = prod.lift (inclusion ≫ prod.fst) hom` is (x,y)↦(x,xy);
  `rightTranslation = prod.lift hom (inclusion ≫ prod.snd)` is (x,y)↦(xy,y).
  `IsStrictLaw` requires both translations to be open immersions, and all six
  fibrewise-density assertions for the ranges of inclusion, leftTranslation,
  rightTranslation under both projections. D is the chart domain, V and W the actual
  open translation images; open immersions supply D≅V and D≅W.
- `IsAssociative` quantifies an S-dense open chart A of `(Y ⨯ Y) ⨯ Y` and four lifts
  a,b,c,d to D. Its first equation says a=(x,y); the second b=(y,z); the third c=(xy,z);
  the fourth d=(x,yz); the final equation is (xy)z=x(yz). This is exactly the node's
  associativity as S-rational maps. BLR also describes equality wherever both sides are
  defined: in the present smooth/separated context the two formulations agree, since a
  fibrewise dense open of a smooth scheme is schematically dense and the equalizer of
  maps into a separated S-scheme is closed. No maximal rational domain is base-changed.
- `fiberwiseDenseOpen_baseChange` has `[Smooth f]`, U and its S-density hypothesis;
  its conclusion is T-density of `pullback.fst f g ⁻¹ᵁ U` under `pullback.snd f g`.
- `strictLawAmbient_baseChange` takes exactly the five ambient conditions and returns
  their five base-changed forms, including surjectivity/nonempty fibres.
- `relativeRationalChart_baseChange` records the representative-level operation and its
  independence: IsRational is preserved, Agrees is preserved for every second representative,
  and IsBirational is preserved. The operation on the quotient therefore is well-defined.
  This exposes the relative-map content used in the node's proof, without an arbitrary map
  or a chosen existence witness in place of the canonical construction.
- `strictBirationalLaw_baseChange` takes the ambient hypotheses, m with `hm : m.IsStrictLaw`,
  and arbitrary g. The conclusion says `(m.lawBaseChange g).IsStrictLaw` and explicitly
  identifies both new translations with the base change of the old translations followed
  by `prodComparison (Over.pullback g) Y Y`. This comparison is canonically an isomorphism
  since Over.pullback is a right adjoint and preserves products. The definition of
  lawBaseChange has domain `(Over.pullback g).obj m.domain`, so D_T is the actual chosen
  domain, and these identities identify its image charts with V_T and W_T.
- Iterated covering projections are covered by the unrestricted g; there is no covering
  assumption to exclude any of them.

Dependencies read and used:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- def-pc-base-change: WeilConjectures.AlgebraicGeometry.BaseChangeConventions, especially
  the documented `Over.pullback`, `pullback.fst/snd`, baseChange_fiber and baseChange_iterated.
  The node's main `Scheme.Modules.moduleBaseChange` concerns modules only and is not the
  scheme construction; the record explicitly instructs using the existing pullback.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth, `Smooth`.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  `LocallyOfFiniteType`, and Morphisms.QuasiCompact, `QuasiCompact`.
- def-weil-closed-immersion: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  `IsClosedImmersion`, used through Mathlib's `IsSeparated`.
- def-pc-fibre-product: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  `pullback`, `pullback.fst/snd/lift`; products in Over use this construction.
- Proof imports: Morphisms.UniversallyOpen supplies the instance that a scheme over a
  field is universally open (lem-sc-scheme-over-field-universally-open);
  Morphisms.Proper supplies IsProper.isStableUnderBaseChange and Smooth supplies
  smooth_isStableUnderBaseChange (lem-pc-proper-base-change); Separated supplies
  IsSeparated.isStableUnderBaseChange and the snd instance; FiniteType and QuasiCompact
  supply the composition and base-change instances; PullbackCarrier supplies
  Surjective's base-change and snd instances; OpenImmersion supplies
  isOpenImmersion_stableUnderBaseChange. These are the item's recorded proof dependencies;
  no source or dependency interface repair was needed.

Edge cases checked before writing: empty T (all relative fibre conditions vacuous), empty
S (the over-schemes are empty), n/a degrees and coefficients, nonempty-fibre condition
without connected or geometrically irreducible fibres, nonreduced T, inseparable and
transcendental residue extensions, and g the identity or an iterated overlap projection.
For a group scheme and the full chart, the definitions give its two usual invertible
translations and ordinary associativity; on an S-dense open group chart, the six relative
conditions retain the distinct projection-density requirements.
All schemes live in arbitrary one u, the existing Scheme category convention; test schemes
are not placed in an independent smaller universe. `set_option autoImplicit false` is in
both modules, and neither has local instances or file-local notation.

Searches for existing definitions/statements (2026-10-24):

- msearch leanfinder, “Strict birational laws over a scheme and fibrewise dense open subsets
  preserved by arbitrary base change”: eight property-stability hits, none the statement.
- msearch loogle, `"RationalMap", "pullback"`: zero hits.
- msearch grep, `strict.*birational|birational.*law|fiberwiseDense|fibrewiseDense`: zero hits.
- msearch leansearch, “Relative rational maps on fibrewise dense open subschemes and strict
  birational group laws”: RationalMap, PartialMap and IsOver hits. Reading their source
  shows that domains are absolutely dense; IsOver only asserts compatibility with S.
- msearch leanfinder, “Fibrewise dense open subsets relative rational maps strict birational
  laws”: the same absolute RationalMap operations, no relative notion.
- rg in lean/WeilConjectures and lean/Sheaf for strict/birational laws and relative rational
  maps: no existing declaration; unrelated fibre-density statements only. Exact proposed
  declaration-name searches and the item-id search in WeilConjectures return no hits.
- rg in DAG definitions: no matching definition node; statement nodes about strict laws
  introduce the notion in prose but have no recorded definition. blueprint_refs searches
  for “strict birational law”, “strict birational”, and “relative rational”: zero matches.
  blueprint_refs ancestor of the item reports None, preserved in the new node.

Source verification: downloaded the primary BLR scan in the sandbox and read printed p.55
and pp.112–115. This agrees with the item's source and definitions. In particular BLR warns
that the maximal domain need not commute with base change, which this interface avoids.
No STATEMENT-DISPUTED flag or statement correction is needed.

Validation: both files compiled separately through scompile.py in dependency order against
its private overlay of the live published build, with autoImplicit false, without errors
or warnings. Expected theorem sorry warnings are permitted; no proof has been supplied.

## New nodes

`def-sfb-relative-birational-law` provides the notions specified in the item's opening
sentences: fibrewise density, raw relative charts, rationality, common-open equivalence,
relative rational maps, birationality, universal translations, rational associativity and
strictness, together with the canonical raw-chart and law base changes. It follows BLR 2.5,
5.1 and 5.2 Definition 1 at the places above. The searches found only absolute Mathlib
rational maps; no DAG definition or project declaration provides the relative notion.
The node records the searches and has one owning module with all supporting declarations.
No theorem or sorry occurs in that definition module.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
