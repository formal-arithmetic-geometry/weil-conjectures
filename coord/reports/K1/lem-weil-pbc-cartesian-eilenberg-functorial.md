## Reviewer fix (R-cef1435, stage 2)

FIX of the delivered statement (H12, CARTAN–EILENBERG convention of coord/STATE.md, 08:44 UTC):
the delivery introduced a new definition node `def-weil-pbc-cartan-eilenberg-resolution`
(`IsCartanEilenbergResolution`, `IsInjectiveResolutionRow`) on `(up ℤ) × (up ℤ)` bicomplexes
with resolution index first and augmentation `ε : K ⟶ I.X 0`. CE consumers state the
resolution in the form of the landed `CategoryTheory.exists_cartanEilenberg_resolution`
(733ed5a76), inline, with no CE definition node. The new node is dropped (`--drop-nodes`)
together with its module. `cartanEilenberg_lift` now takes `I : HomologicalComplex₂ A (up ℤ) (up ℕ)`
(complex degree first, resolution degree natural: the node's condition (2) is the shape),
the bicomplex augmentation `eI` from the `single₀` complex, `∃ i, ∀ p < i, IsZero (I.X p)`
(condition (1)), `QuasiIso (eI.f p)` and injective terms (condition (3), the
`InjectiveResolution` fields), injective cycles/image/homology terms with `QuasiIso` of
`cyclesMap eI p`, `image.map (Arrow.homMk' (eI.f (p-1)) (eI.f p) _)`, `homologyMap eI p`
(conditions (4)–(6); the image at `p` resolves `B^p = Im(d_K^(p-1))`, i.e. the node's
`B^(q+1)` for `q = p-1`); likewise `J`, `eJ` over `L`. The augmentation identity
`φ ∘ F(ε_K) = ε_L ∘ u` is stated on the resolution-degree-zero components via
`singleObjXSelf` (equivalent, since a map out of a `single₀` complex is determined there).
Totals: the natural resolution degree is extended by zero to `ℤ`
(`ComplexShape.embeddingUpNat.extendFunctor`) so the landed `HomologicalComplex₂.firstFiltration`
of def-sp-double-complex-total applies; the node's "filtration by the second degree" (complex
degree) is `firstFiltration` in this index order. The worker's report below describes the
delivered (superseded) form.

## Worker report

The item is stated by `CategoryTheory.cartanEilenberg_lift` in
`Sheaf.CategoryTheory.CartanEilenbergFunctorial`. Its proof is `sorry`.
The new definition module `Sheaf.CategoryTheory.CartanEilenbergResolution`
contains the full six-condition predicate `CategoryTheory.IsCartanEilenbergResolution`.
No statement correction or dependency replacement is needed.

Hypothesis and clause correspondence:

- The two abelian categories are `A`, `B`, their explicit universe and category binders,
  and `[Abelian A] [Abelian B]`. Their object and morphism universes may differ.
- The exact additive functor is `F : A ⥤ B`, `[F.Additive]`,
  `[PreservesFiniteLimits F] [PreservesFiniteColimits F]`. In abelian categories,
  preserving both finite limits and finite colimits is exactly exactness of an additive functor.
  No preservation of injectives or enough-injectives hypothesis is imposed.
- The bounded-below integer-indexed complexes are `K`, `L`, with `hK`, `hL` expressing
  an arbitrary integer lower bound through `IsZero`, not equality to a chosen zero object.
- The given chain map is `u` from the termwise mapped complex to `L`.
- The commuting double complexes are Mathlib's `HomologicalComplex₂` with both
  shapes `ComplexShape.up ℤ`. The first index is resolution degree `p`;
  `I.X p` is the vertical complex and `I.d p p'` is the horizontal chain map.
- The augmentations are `ε : K ⟶ I.X 0`, `η : L ⟶ J.X 0`.
- CE condition (1) is the first conjunct of `IsCartanEilenbergResolution`:
  `∃ i, ∀ p q, q < i → IsZero ((I.X p).X q)`.
- Condition (2) is its second conjunct: `p < 0 → IsZero ((I.X p).X q)`.
- Condition (3) is `IsInjectiveResolutionRow (K.X q)` with the row objects,
  horizontal differential components, and `ε.f q`.
- Condition (4) uses `K.cycles q`, `(I.X p).cycles q`, `cyclesMap` of the
  horizontal chain maps, and `cyclesMap ε q`. Mathlib's cycles object is the kernel
  of the outgoing differential; its functorial maps are the canonical kernel maps.
- Condition (5) uses `image (K.d q (q+1))` and the corresponding images in each
  column. `image.map` on the commuting squares induced by `I.d` and `ε`
  gives exactly the boundary-row differential and augmentation.
- Condition (6) uses the vertical homology objects and their canonical
  `HomologicalComplex.homologyMap` maps and augmentation.
- For all four rows `IsInjectiveResolutionRow` means that the nonnegative restriction
  is isomorphic, including its augmentation and differential, to a Mathlib
  `InjectiveResolution` of the specified object. The isomorphisms are existential,
  so no chosen resolution is imposed. The negative row terms vanish by condition (2).
  This helper is a presentation of the dependency's existing resolution notion,
  not a separate replacement definition of injectivity or resolution.
- The resolutions satisfying all six conditions are `hI` and `hJ`.
- `FI` is the termwise application of `F` in both degrees. The conclusion provides
  both diagonal coproduct instances (`tI`, `tJ`), rather than assuming their existence.
  Only finitely many diagonal terms can be nonzero by conditions (1)--(2).
- `∃ φ : FI ⟶ J` is the morphism of commuting double complexes.
  Its first equation is the augmentation identity. Its second, degreewise equation
  states the specified compatibility of each augmented row with `u.f q`.
- `HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)` is the canonical total chain map.
  For every filtration index `r` and total degree `n`, the final three conjuncts
  express that both filtrations are subcomplexes and that this map preserves their steps.
  Each assertion is factorization through the target subobject's monomorphism,
  exactly the convention of `FilteredObject.Hom` from the recorded filtration dependency.

Dependency declarations read and used:

- `CategoryTheory.Abelian`, `Mathlib.CategoryTheory.Abelian.Basic`.
- `CategoryTheory.InjectiveResolution`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`; its cocomplex,
  augmentation, injectivity and quasi-isomorphism fields give the entire row notion.
- `HomologicalComplex₂`, `Mathlib.Algebra.Homology.HomologicalBicomplex`;
  `HomologicalComplex₂.total`, `HomologicalComplex₂.total.map`,
  `Mathlib.Algebra.Homology.TotalComplex`.
- The recorded `Sheaf.CategoryTheory.DoubleComplexTotal` is imported and
  `HomologicalComplex₂.secondFiltration` is used directly. The node's recorded
  main declaration is the first filtration, but its declaration list also records
  the second one used here. No private filtration formula is introduced.
- `CategoryTheory.DecreasingFiltration`, `Sheaf.CategoryTheory.Filtration`,
  is used through `secondFiltration`, including its `step` subobjects.
- `Functor.mapHomologicalComplex`, `Mathlib.Algebra.Homology.Additive`;
  cycles and homology maps are the canonical Mathlib ones.

Edge cases checked: zero complex and zero rows; identity functor/map;
complexes concentrated in a single integer degree, including a negative degree;
arbitrary negative lower bound; arbitrary unrelated bounds for `K` and `L`;
negative total degrees; empty finite diagonal support; unequal category universes.
The finite supremum for the second filtration runs from `r` to `n`. It is still
correct outside the first quadrant: if `q>n` then `p=n-q<0`, so the extra terms
are zero by condition (2). If `q<r` they are excluded precisely by the filtration.
Consequently we can reuse this actual definition even though the dependency's
first-quadrant theorems are not applicable verbatim. No first-quadrant hypothesis
was added. The total morphism is on `Tot(F(I))`, as the item specifies;
no unnecessary preservation of all infinite coproducts is assumed.

Searches performed via `/home/ubuntu/weil-launcher/msearch.py`:

- LeanFinder: `Cartan Eilenberg resolution comparison morphism exact additive functor`:
  eight generic resolution declarations, none states this item or defines the six conditions.
- Loogle: `CategoryTheory.InjectiveResolution, HomologicalComplex₂`: zero hits.
- grep Mathlib: `Cartan.Eilenberg|cartan.*eilenberg`: three historical
  bibliographic references, no Cartan–Eilenberg definition or theorem.
- LeanSearch: `Cartan Eilenberg resolution bounded below bicomplex`:
  unavailable, Internal Server Error; no mathematical verdict inferred.
- grep Mathlib for `IsCartanEilenbergResolution|IsInjectiveResolutionRow|cartanEilenberg_lift`:
  zero hits.
- `rg` of `WeilConjectures` and `lean/Sheaf` for Cartan/Eilenberg found only
  spectral-sequence explanatory docstrings in the source and unrelated Lie algebra files.
  No matching declaration. Searching for the item id in the source found nothing.
- `tools/lean_names_upstream.py show` and `dag/lean_names_upstream.json` search:
  no recorded upstream declaration for the item.
- DAG search for Cartan–Eilenberg found existence and comparison statement nodes,
  and this item's inline six-condition notion, but no reusable definition node.
  `tools/blueprint_refs.py search 'Cartan Eilenberg'`: zero blueprint-node matches.

Source read from the official Stacks pages because the local literature checkout has
no `derived.tex`: https://stacks.math.columbia.edu/tag/015H (six conditions),
https://stacks.math.columbia.edu/tag/015I (cycle/boundary horseshoe construction),
and https://stacks.math.columbia.edu/tag/015K (functorial filtered complexes).
The indexing is exchanged as already specified in the item. The complete four-step
proof of the node is rendered in the theorem docstring. No mathematical node fault found.

## New nodes

`def-weil-pbc-cartan-eilenberg-resolution` defines exactly the six-condition notion
from Stacks Tag 015H, with resolution index first as required by this item's statement.
It cites the existing abelian category, double-complex and injective-resolution nodes.
Its full definition has no `sorry`, and canonical cycles, image and homology maps fix
all row augmentations. Mathlib's actual `InjectiveResolution` data is reused through
existential row isomorphisms. The searches above (also recorded in the new node)
found no definition node or Lean declaration carrying this notion; the DAG's CE
existence/comparison theorems are statements, not definitions. It is directly added
to the item's `stmt_deps`. The original item statement is unchanged.

## Second reading by K1

I independently opened the item and new definition node, both delivered Lean files,
the four recorded dependency nodes, `DoubleComplexTotal.lean`, `Filtration.lean`,
and Mathlib's `InjectiveResolution`, `HomologicalComplex₂`, `mapHomologicalComplex`,
`cyclesMap`, `homologyMap`, and `total.map` declarations. I also read the landed
`exists_cartanEilenberg_resolution` and `cartanEilenberg_properties` signatures.
The local Stacks checkout is absent. I read the official 015H, 015I and 015K pages
and the actual `derived.tex` section `section-cartan-eilenberg` from
https://raw.githubusercontent.com/stacks/stacks-project/master/derived.tex.
There is no ambient assumption before the definition beyond an abelian category
and a bounded-below complex. Enough injectives is required for the existence
lemma, not for comparing resolutions already given here. The item explicitly
exchanges the source's two indices; this is the exchanged convention already
used by the landed properties node, not a silent index change.

My object/hypothesis/conclusion checklist, with Lean correspondence and verdict:

1. Two abelian categories: `{A : Type u₁} {B : Type u₂}`,
   `[Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]`. Exact match;
   all four universe parameters are independent and explicitly declared.
2. Exact additive functor: `(F : A ⥤ B) [F.Additive]`,
   `[PreservesFiniteLimits F] [PreservesFiniteColimits F]`. Exact match: in
   abelian categories this means preservation of kernels and cokernels and
   finite additive structure, equivalently exactness. No assumption that `F`
   preserves injectives or arbitrary coproducts has been added.
3. Integer-indexed bounded-below complexes: `(K : CochainComplex A ℤ)` and
   `(L : CochainComplex B ℤ)`, with the separate existential integer bounds
   `hK` and `hL` and `IsZero (K.X q)` / `IsZero (L.X q)`. Exact match;
   neither lower bound is forced to be zero or equal to the other.
4. Given map: `u : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L`.
   The inspected functor maps every object, differential and component by `F`.
   Exact match with the termwise complex `F(K)` and its chain map to `L`.
5. Given commuting double complexes: `I`, `J` have both shapes `up ℤ`.
   The inspected Mathlib abbreviation is a complex of complexes, hence
   `I.d p p'` is itself a vertical chain map. Its components commute with
   the vertical differential; the two square-zero laws are built in.
   Exact match with the dependency's commuting, not anticommuting, convention.
6. Given augmentations: `ε : K ⟶ I.X 0` and `η : L ⟶ J.X 0` are morphisms
   of vertical complexes. Exact match with the node's resolution index first.
7. CE condition (1): the first conjunct of `IsCartanEilenbergResolution` is
   `∃ i : ℤ, ∀ p q : ℤ, q < i → IsZero ((I.X p).X q)`.
   Exact match with a uniform complex-degree bound over every resolution degree.
8. CE condition (2): `∀ p q : ℤ, p < 0 → IsZero ((I.X p).X q)`.
   Exact match, including the negative integer resolution terms.
9. CE condition (3): `IsInjectiveResolutionRow (K.X q)` uses precisely
   `(I.X (n : ℤ)).X q`, `(I.d ...).f q` and `ε.f q`. The helper quantifies
   a Mathlib `InjectiveResolution` and objectwise isomorphisms commuting with
   every adjacent differential and the augmentation. Exact match; these
   equations express an isomorphism of augmented nonnegative row complexes,
   including exactness at degree zero and injectivity of each term.
10. CE condition (4): the same helper on `K.cycles q` and `(I.X p).cycles q`,
    with `cyclesMap (I.d ...) q` and `cyclesMap ε q`. Exact match; inspected
    `cyclesMap_i` identifies this as the canonical map on outgoing kernels.
11. CE condition (5): the same helper on `image (K.d q (q+1))` and the
    images of `(I.X p).d q (q+1)`. Both row differential and augmentation
    use `image.map (Arrow.homMk' ... ... (...comm q (q+1)))`.
    Exact match with outgoing boundaries `B^(q+1)`, not incoming `B^q`.
12. CE condition (6): the helper uses `K.homology q`, `(I.X p).homology q`,
    `homologyMap (I.d ...) q`, and `homologyMap ε q`. Exact match with the
    canonical induced cohomology row and its augmentation, including its
    actual horizontal differential. The hypotheses `hI` and `hJ` assert
    all six conditions for the two given resolutions.
13. Applying `F` to the given resolution: `FI` is obtained by applying
    `mapHomologicalComplex` twice, in the correct order. Exact match with
    `F(I_K)`; the conclusion does not replace the given resolutions by new ones.
14. Existence of finite-diagonal total complexes: the existential witnesses
    `tI : FI.HasTotal (up ℤ)` and `tJ : J.HasTotal (up ℤ)` provide the actual
    Mathlib diagonal coproducts. Exact match with the node's assertion that
    the totals exist. Only `0 ≤ p ≤ n-i` can contribute on a diagonal;
    abelian categories have the needed finite coproducts. These are conclusions,
    not extra hypotheses.
15. Comparison morphism: `∃ φ : FI ⟶ J` and
    `(F.mapHomologicalComplex ...).map ε ≫ φ.f 0 = u ≫ η`.
    Exact match with the augmentation identity, using Lean's composition order.
    The following `∀ q` equality is precisely the node's stated rowwise
    consequence. It is redundant mathematically, not a stronger requirement.
16. Filtered total morphism: `HomologicalComplex₂.total.map φ (up ℤ)` is
    already a chain map by its inspected definition. For every `r n : ℤ`,
    the first two existential factorizations say that both second filtrations
    are subcomplexes. The third factors its degree-`n` component through the
    target step. Exact match with the dependency's `FilteredObject.Hom.preserves`;
    monicity makes the restricted maps unique and their chain compatibility
    automatic. Checking adjacent differentials suffices for the `up ℤ` shape.

Edge cases: all zero terms and the zero complex are admitted, as is the identity
functor or the zero functor. A complex concentrated in degree -3 is admitted;
for example its degree -3 total diagonal has only the resolution-degree-zero
term. Generally, if the complex-degree bound is `i`, every nonzero diagonal
term satisfies `i ≤ q ≤ n`. The existing `secondFiltration` takes the finite
supremum over `[r,n]`, exactly the intended sum for `q ≥ r`: omitted `q>n`
terms have `p=n-q<0` and are zero, while extra terms below `i` are zero.
Empty intervals give the bottom subobject. Thus negative total degrees and
negative filtration indices are covered without the dependency's first-quadrant
hypothesis. No characteristic, scheme, ring or nonemptiness restriction occurs;
the scheme-specific edge cases are inapplicable to this abstract categorical
statement. All universes and variables are bound; no smallness restriction on
the categories is implicit.

New-node review (H12): `def-weil-pbc-cartan-eilenberg-resolution` faithfully
extracts the inline notion and the six conditions of 015H with exchanged
indices. Its stated bounded-below domain agrees with the predicate: the row
augmentation is monic, so condition (1) and condition (3) already imply that
`K` vanishes below the same bound. It adds no global enough-injectives hypothesis.
The helper `IsInjectiveResolutionRow` only presents the recorded Mathlib
resolution notion on the supplied row data; it introduces no alternative
injectivity or cohomology notion. Both definitions are explicit Prop formulas,
with no `sorry` data. Its dependency citations, empty proof fields, searches,
source, chapter, unit, created fields and Lean record satisfy §5. There are no
dependency replacement modules. The item statement is unchanged and has no
stage-2 statement correction; a corrected-statement citer audit is inapplicable.

Independent searches, using different wording from the first worker:

- LeanFinder via `msearch.py`: `extend chain map to injective double resolutions
  preserving cycles boundaries cohomology` returned eight ordinary injective
  resolution hits, including `InjectiveResolution.desc`, `descFOne`, `descFSucc`,
  and extension/homotopy declarations. None defines the six-condition double
  resolution or states this exact-functor comparison.
- Loogle via `msearch.py`: `HomologicalComplex₂, CategoryTheory.Functor` returned
  twelve structural bicomplex functors/isomorphisms (graded-object and flip
  functors). None is a CE predicate or comparison theorem.
- LeanSearch via `msearch.py`: `Injective resolution of all cycles boundaries
  cohomology of a double complex` again returned service unavailable (Internal
  Server Error). This is recorded as unavailable, not as a negative match.
- Independent `rg` over Mathlib, `WeilConjectures`, `lean/Sheaf`, the DAG and
  `dag/lean_names_upstream.json` searched `eilenberg`, `injective.*bicomplex`,
  `bicomplex.*injective`, `resolution.*comparison`, and the proposed declaration
  names. No matching predicate or comparison theorem exists. The project now
  does contain CE existence and properties statements; I opened both signatures.
  They neither define this predicate nor assert this comparison. Therefore they
  do not justify an `existing: true` record. The first worker's earlier claim
  that Sheaf had no CE declarations is outdated; the no-matching-definition
  conclusion remains correct.

The dry run refreshed the base and exposed a stale item's blueprint ancestry in
the sandbox copy: the current base includes
`lem-weil-pbc-etale-cohomology-limit-complex-systems` in its `via`, whereas the
sandbox item copy did not. I checked the new node's path against the refreshed
base and kept that intermediate entry, exactly matching the current item's
`via` prefixed by this item. My initial metadata edit against the stale sandbox
copy was reverted after the preflight identified the discrepancy. The ancestor
`prop-weil-pbc-strict-henselization-stalk-formula` was independently confirmed
with `tools/blueprint_refs.py ancestor`. The mathematical reading found no
statement mismatch. No Lean rewrite was needed. The node's
`lean.statement` strings were checked against the actual declaration signatures.
Every new declaration has the required source and blueprint docstring, and the
comparison docstring follows all four node proof steps. The only theorem body
is `by sorry`; neither definition has a hole. Both delivery modules compiled
together in dependency order on the server, exit 0, in 1.4 seconds, with no
warnings or errors. The delivery dry run below additionally checks records,
line widths, declaration ownership and file shape.
