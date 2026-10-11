## Worker report

The module `Sheaf.AlgebraicGeometry.PicardH1ProductInjective` states
`AlgebraicGeometry.Scheme.picard_h1_product_injective`, with proof `sorry`.
The original mathematical statement is unchanged. One new definition node supplies the
canonical structure-sheaf cohomology pullback, whose data is fully defined without `sorry`.
No dependency module or statement correction is needed.

Hypothesis and conclusion correspondence:

- The field `k` is `(k : Type u) [Field k]`.
- The schemes are `(X Y : Scheme.{u})`. Their specified structure morphisms to
  `Spec (CommRingCat.of k)` are the two `Scheme.Over` instances, written `X ↘ Spec ...`
  and `Y ↘ Spec ...`.
- Properness over this very base is exactly the two `IsProper` instances on those morphisms.
- `H⁰(X,O_X)=k` is `Function.Bijective (globalSectionsRingHom k (X := X))`;
  the analogous hypothesis for `Y` is `hY`. This means that the canonical scalar map,
  rather than an arbitrary abstract ring isomorphism, identifies global functions with `k`.
  Degree-zero sheaf cohomology is global sections, as in `Sheaf.H.equiv₀` and the source's
  `Scheme.Modules.H.zeroLinearEquiv`. Bijectivity is precisely the isomorphism condition.
- The points `x` and `y` have types `(X ↘ Spec ...).fieldPoints k` and
  `(Y ↘ Spec ...).fieldPoints k`. Their underlying arrows are sections from `Spec k`;
  their subtype equations give the section identities after simplifying `algebraMap k k`.
- `pullback f g` is exactly `X ×_k Y` for the two specified structure maps `f` and `g`.
- `iX` is `pullback.lift (𝟙 X) (f ≫ y.1) ...`, so its projections are the identity on
  `X` and the constant map given by `y`. This is `(1,y)`.
- `iY` is `pullback.lift (g ≫ x.1) (𝟙 Y) ...`, so its projections are the constant map
  given by `x` and the identity on `Y`. This is `(x,1)`.
- `structureSheafCohomologyPullback iX 1` and its `iY` counterpart are the canonical
  pullbacks on first Zariski structure-sheaf cohomology. `AddMonoidHom.prod` pairs them
  into `H¹(X,O_X) × H¹(Y,O_Y)`, the usual model of the binary direct sum of abelian groups.
- `Function.Injective` of that paired homomorphism is precisely the asserted conclusion.

Dependencies read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`; its locally finite type formulation is
  equivalent to finite type because universal closedness gives quasi-compactness.
- `def-weil-scheme-over-base`: `AlgebraicGeometry.Scheme.Over`, in
  `Mathlib.AlgebraicGeometry.Over`; this is the data of the structure arrow, not a new copy.
- `def-pc-rational-point`: the docstring and full signature of
  `AlgebraicGeometry.Scheme.Hom.baseChangeFieldPoint`, in
  `WeilConjectures.AlgebraicGeometry.DensePoints`, explicitly identify rational points with
  `Scheme.Hom.fieldPoints`. The statement imports this module and uses that point type;
  base change of a point to another field is not needed here.
- The new definition uses Mathlib `Sheaf.H`, `Sheaf.H.map`, `Functor.sheafPullback`,
  `Functor.sheafAdjunctionContinuous`, `sheafCompose` and the standard forgetful functors.
  It reuses `Sheaf.H.mapFunctor` from
  `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` and
  `Functor.constantSheafsheafPullbackIso` from
  `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf`, whose signatures and
  docstrings were read in full. The latter is the canonical adjunction comparison, not an
  arbitrarily chosen constant-sheaf isomorphism. Exactness and additivity instances are
  supplied by existing preservation-of-limits/colimits and biproduct declarations.

Edge cases checked: an empty scheme has zero global ring and cannot satisfy the scalar
bijection from a field (nor have the specified rational point), so it is correctly excluded
by the stated hypotheses. If either scheme is `Spec k`, its first cohomology is zero and
one slice identifies the product with the other factor, giving injectivity. The result
allows characteristic zero and every positive characteristic, nonreduced proper schemes,
and schemes with nonzero first cohomology. No connectedness, smoothness, geometric
integrality, algebraic closure, finite-dimensionality, or new vanishing hypothesis is added.
There is a single arbitrary universe `u` for the field and its schemes, as in Mathlib's
scheme-over-a-ring API; it is explicitly bound. The supporting module uses the separately
bound universe `v` so the server's combined-file compilation also works.

Searches for an existing statement:

- `msearch.py ... leanfinder "For proper schemes over a field with global functions k,
  slice pullbacks on first structure sheaf cohomology of their product are injective"`:
  eight unrelated scheme-point, image-factorization, and restriction injectivity hits;
  no first-cohomology product theorem.
- `msearch.py ... loogle "Scheme, Sheaf.H, Function.Injective"`: zero hits,
  unknown identifier `Scheme`. A further `loogle '"cohomology"'` returned
  cochain-complex cohomology-class declarations, none about this product.
- `msearch.py ... grep "kunneth|Kunneth|H.pullback" AlgebraicGeometry`: 25 hits for
  pullback-associativity expressions, no Kunneth cohomology result.
- `rg` on `WeilConjectures` for cohomology/structure-sheaf and pullback declarations found
  the existing module-cohomology types and the generic exact-functor Ext map, but no
  structure-sheaf pullback wrapper or this injectivity result. Searching the item ID and
  `h1_product|slice.*injective|kunneth` under source algebraic geometry and `lean/Sheaf`
  found no existing statement. The proposed full declaration names also have no hits in
  Mathlib, the source repository, the project Lean tree, or `dag/lean_names_upstream.json`.
- The new definition's LeanSearch query was unavailable (Internal Server Error); its
  LeanFinder query returned eight sheaf/module-pullback and section-map declarations,
  not a map on cohomology. The exact queries and outputs are recorded in its JSON.

Source checked: Stacks `varieties.tex`, `lemma-kunneth` (Tag 0BED), read at lines
5442 onward in the available source copy `/home/ubuntu/c1-stacks-review/varieties.tex`
(the repository's literature checkout is absent). Its hypotheses are quasi-compactness
and affine diagonal and its proof explicitly defines the maps using functoriality of
cohomology and cup product. The item's properness supplies those hypotheses and its
H⁰ conditions give the stated degree-one specialization. The theorem docstring contains
all four proof steps with the original proof dependency IDs.

Validation: the two delivery modules were compiled together on the server by
`scompile.py E1 lem-sc-picard-h1-product-injective <support> <item>`: exit code 0,
no errors or warnings. Only the theorem has a `sorry`. The delivery dry run is the final check.

## New nodes

`def-sc-structure-sheaf-cohomology-pullback` defines the additive structure sheaf and its
canonical contravariant cohomology map for every scheme morphism and every nonnegative
degree. Its source is Tag 0BED's functoriality maps, with the general construction in
Cohomology of Sheaves, Section 01F7. It cites the existing scheme and topological abelian
cohomology nodes rather than redefining either notion. Its module specializes the existing
exact-functor cohomology and constant-sheaf comparison APIs, then uses the adjoint of the
actual structure-sheaf homomorphism `f.c`. All data is written in full; no supporting lemma
with `sorry` is needed. Mathlib/LeanFinder searches found only the component functors,
while LeanSearch was unavailable. DAG grep and `blueprint_refs.py search "structure sheaf
cohomology"` found no node carrying this specialization. The general module f-map node
`def-weil-pbc-module-cohomology-fmap` describes arbitrary modules via injective resolutions
and has no Lean record; the etale pullback node concerns a different site. This new node
provides only the missing canonical structure-sheaf specialization and reuses the generic
Lean declarations already available. The item's `stmt_deps` gains this node only.

## Second reading by E1

I independently opened both delivered JSON nodes and both Lean modules, the recorded
statement dependencies, and the relevant source declarations. I read Stacks
`varieties.tex`, `lemma-kunneth` (Tag 0BED), lines 5442–5520, and `cohomology.tex`,
`section-functoriality` (Section 01F7), lines 2328–2415, in the available local
`/home/ubuntu/c1-stacks-review/` source copy. No mathematical or typing mismatch was found;
I left the statements and definitions unchanged and added this independent review.

My object/hypothesis/conclusion checklist, in the node's order:

1. Field k: `(k : Type u) [Field k]` uses Mathlib's nontrivial commutative division
   ring notion, matching `def-weil-field`. Verdict: exact.
2. Schemes X and Y over k: `(X Y : Scheme.{u})` with the two `Scheme.Over` instances
   supplies precisely the specified structure arrows to `Spec (CommRingCat.of k)`.
   I opened `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over` is `OverClass`, and the
   notation `↘` selects its arrow. Verdict: exact; no extra structure hypothesis.
3. Properness: the two `IsProper` instances apply to those same arrows. I opened
   `Morphisms/Proper.lean` and the `UniversallyClosed → QuasiCompact` instance in
   `Morphisms/UniversallyClosed.lean`; locally finite type together with this
   quasi-compactness is finite type, exactly the dependency node's notion. Verdict: exact.
4. H⁰(X,O_X)=k and H⁰(Y,O_Y)=k: `hX` and `hY` are bijectivity of the canonical
   `globalSectionsRingHom`. I opened its definition in source `Cohomology/Defs.lean`:
   it composes `ΓSpecIso.inv` with the structure arrow's `appTop`. I also opened
   Mathlib `Sheaf.H.equiv₀`, identifying degree-zero Ext cohomology with global
   sections. Thus these hypotheses identify global functions with k as k-algebras,
   rather than assuming an unrelated abstract isomorphism. Verdict: exact.
5. Rational points x and y: the two `fieldPoints k` binders are sections. I opened
   the dependency's `Hom.baseChangeFieldPoint` signature and docstring in
   `DensePoints.lean`, then the actual `Hom.fieldPoints` definition in
   `Comparator/Weil/Definitions.lean`: `g ≫ f = Spec.map (algebraMap k k)`.
   The self algebra map is the identity. No base-change or density hypothesis from
   nearby declarations is imposed. Verdict: exact.
6. Product: `pullback f g` is the scheme fibre product over the common `Spec k`.
   Verdict: exact, with the field and structure morphisms already fixed.
7. First slice: `iX := pullback.lift (𝟙 X) (f ≫ y.1) ...` has projections id_X
   and y composed with the structure arrow. Its compatibility proof uses y's
   section equation. This is precisely `(1,y)`. Verdict: exact.
8. Second slice: `iY := pullback.lift (g ≫ x.1) (𝟙 Y) ...` similarly has
   projections x composed with the structure arrow and id_Y. This is `(x,1)`.
   Verdict: exact, in the same order as the node.
9. Cohomology groups and homomorphism: the new definition specializes `Sheaf.H` to
   the additive structure sheaf on `Opens.grothendieckTopology`. Thus its source is
   H¹ of the Zariski structure sheaf of the product, and its two targets are H¹ of
   the corresponding factors. `.prod` pairs the actual canonical slice pullbacks.
   The binary product of abelian groups is canonically their binary direct sum;
   no summand or map is missing. Verdict: exact.
10. Conclusion: `Function.Injective` asserts injectivity of this paired homomorphism
    for every field, pair of schemes satisfying the displayed hypotheses, and pair
    of rational points. There are no extra finiteness, smoothness, connectedness,
    reducedness, algebraic closure, or cohomological vanishing binders. Verdict: exact.

Source hypotheses checked: Tag 0BED assumes a field, quasi-coherent coefficient modules,
quasi-compact schemes and affine diagonals. The structure sheaves are quasi-coherent;
properness over the affine field spectrum supplies quasi-compactness and separatedness,
hence affine diagonals. In degree one the source's canonical cup-product decomposition
has only bidegrees (1,0) and (0,1). The displayed global-function hypotheses and rational
sections give precisely the slice maps of the node. There is no omitted source-wide
Noetherian, characteristic, or geometric integrality condition.

New node `def-sc-structure-sheaf-cohomology-pullback`: I read its full fields and source
place as a definition-node review. It introduces schemes, their additive structure
sheaves, and all natural-number degrees, and cites exactly the scheme and topological
abelian-cohomology nodes it uses. Its definition is the usual cohomological functoriality
of the structure-sheaf f-map described in Section 01F7 and used in Tag 0BED. The Ext
presentation is equivalent to derived global sections; it does not change coefficients
or site. In the module, `structureSheafAb` forgets multiplication via the standard
forgetful functors. `structureSheafCohomologyPullback` uses the exact inverse image
on abelian sheaves, the canonical integer-sheaf comparison, and the adjoint of the
whiskered actual `f.c`. I opened `Sheaf.H.mapFunctor` (its Ext precomposition formula),
`Functor.constantSheafsheafPullbackIso` (the adjunction comparison, with its direction),
and Mathlib `Sheaf.H.map`. Their composition has the node's direction Y to X and uses
the specified structure map, with no arbitrary isomorphism or hollow data. Exactness
and additivity instances are constructed from existing preservation results, without
sorry. The node has empty proof fields, all three search kinds, the required creation,
blueprint, audit, chapter, unit and Lean records, and is cited by the item. The general
`def-weil-pbc-module-cohomology-fmap` node already covers arbitrary module f-maps via
resolutions, but has no recorded Lean map; this new node supplies the missing explicit
structure-sheaf specialization using the existing generic Ext API. No dependency
module is delivered, and no statement correction or citer verdicts are needed.

Edge cases: the empty scheme cannot have a k-rational section and also fails scalar
bijectivity (a field is nonzero, whereas its global ring is zero). This exclusion is
already in the node's hypotheses. Zero H¹ groups, including either factor Spec k,
are allowed without new assumptions. There is no index set to require nonemptiness;
the only direct sum here has two terms. The main statement is explicitly degree one;
the new definition also covers n=0, where it is the ordinary global-section map.
All field characteristics are permitted. Universes u and v are explicitly bound;
the common Scheme universe is the one used by the recorded Scheme.Over/fieldPoints
APIs, and can be enlarged to contain all the objects. No unbound term or universe
variable occurs.

Independent searches with different queries from the first reader:

- LeanFinder through `msearch.py`: "Kunneth decomposition first Zariski cohomology
  proper scheme product restriction rational sections" returned eight unrelated
  scheme/pullback results, no matching theorem.
- Loogle through `msearch.py`: `"mapFunctor"` returned twelve generic over-category,
  bicategory and graded-object declarations, no structure-sheaf cohomology map.
- LeanSearch through `msearch.py`: "inverse image map cohomology sheaf of abelian
  groups continuous map" was unavailable (Internal Server Error), recorded as
  unavailable, without a negative search verdict.
- `rg -i` for `k.nneth|cohomology.*pullback|pullback.*cohomology|h1.*product|product.*h1`
  in source/project/Mathlib algebraic geometry found the source theorem-of-cube
  docstring mentioning the desired input, but its actual theorem is a local
  isomorphism statement about invertible modules, not this injectivity theorem.
  It also found `Curve/FieldExtension.lean`; I opened it and checked that its maps
  are `Etale.cohomologyMap` on small-etale torsion coefficients, not Zariski O_X.
- Additional searches in source/Mathlib topology sheaves found presheaf pullbacks,
  with no cohomological specialization. Searching the three proposed full names
  in Mathlib, source, project Lean and `dag/lean_names_upstream.json` found no hits.
  DAG searches distinguish the general module f-map and etale map nodes from this
  explicit specialization. No existing matching declaration was overlooked.

Conventions and validation: both module and declaration docstrings cite their source
and correct blueprint IDs. The theorem docstring carries all four DAG proof steps,
including all three proof-dependency names. The only sorry is the named main theorem;
the slice compatibility proofs construct well-typed morphisms and do not prove a
new mathematical theorem. Headers, namespaces, imports and line widths follow the
contract. I compared the recorded signatures with the actual files and the project's
signature reader: they agree. Independently recompiled both modules together with
`scompile.py E1 lem-sc-picard-h1-product-injective`, support module first: exit code 0,
24.4 seconds, no errors or warnings. No Lean or node repair was necessary.
