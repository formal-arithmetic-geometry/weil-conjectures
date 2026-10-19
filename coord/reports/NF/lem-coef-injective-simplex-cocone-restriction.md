## Worker report

The module `Sheaf.CategoryTheory.InjectiveSimplexCoconeRestriction` states
`SSet.Enhanced.injective_simplex_cocone_restriction`, with its proof `sorry`.
It supplies three concrete helper declarations for the categories and inclusion introduced
in this very node. It adds no independent notion, new node, or dependency repair, and
changes only the item's `lean` record. There is no statement correction or dispute.

Clause-by-clause correspondence:

- A small simplicial set is `X : SSet.{u}`, with no quasicategory hypothesis.
  Mathlib's `X.Elements` has objects `([n], x : X_n)` and arrows the opposite ordinal
  operators carrying the source element to the target element under `X.map`.
  Thus it is precisely `S(X)^op`, including all degenerate simplices.
  This is Mathlib's existing category of elements, not a private redefinition or the
  preorder on simplex supports (`X.S`).
- `injectiveSimplexOppositeCategory X` is `WideSubcategory` of `X.Elements` for
  `((monomorphisms SimplexCategory).op.inverseImage (CategoryOfElements.π X))`.
  Objects of a wide subcategory are unrestricted. For an element-category arrow `f`,
  the predicate is exactly `Mono f.val.unop`. By `SimplexCategory.mono_iff_injective`,
  this means its underlying monotone map is injective. It imposes no condition on
  the simplex itself. Composition and identities are inherited from Mathlib's category
  of elements and wide subcategory. The multiplicativity instances come from Mathlib.
- `injectiveSimplexOppositeInclusion X` is `wideSubcategoryInclusion` for that property:
  it forgets the arrow predicate and leaves objects and ordinal maps unchanged.
  `injectiveSimplexNerveInclusion X` is its `nerveMap`, hence exactly `j_X`.
  There is no extra opposite here: both element categories are already opposite to
  the simplex categories in the displayed natural-language statement.
- An arbitrary quasicategory is `E : SSet.{max u v}` with `[Quasicategory E]`.
  `SSet.uliftFunctor.{v}` embeds the indexing nerves into this common universe.
  The separate `v` permits arbitrary enlargement, and `v = 0` permits the same size.
  This does not require any equality between independent size universes.
- The arbitrary diagram is `p : SSet.uliftFunctor.{v}.obj (nerve X.Elements) ⟶ E`;
  the arbitrary vertex is `T : E _⦋0⦌`.
- `diagramVertex p` and `diagramVertex (SSet.const T)` are the two vertices of the
  internal functor simplicial set. `SSet.const T` is the constant diagram on the
  domain inferred from `p`.
- `((MonoidalClosed.pre (SSet.uliftFunctor.{v}.map
  (injectiveSimplexNerveInclusion X))).app E)` is actual precomposition by `j_X`.
  `mappingSpaceMap` is its induced map on the dependency's right-pinched mapping spaces.
  Its target vertices are the images of `p` and the constant diagram under restriction,
  namely `p j_X` and the constant diagram on the injective indexing nerve.
  This is the same restriction expression used by the already recorded general
  `infinity_cofinal_comma_criterion`, not an arbitrary map between equivalent spaces.
- `IsWeakHomotopyEquivalence` is exactly the dependency's definition of equivalence
  of spaces by realization. The generic `enhanced_functor_cone_calculus` says the two
  functor objects are quasicategories and their specified mapping spaces are Kan;
  these are ambient facts, not additional assumptions in this theorem.
- There is no assumption of colimits in `E`, nonemptiness of `X`, or horn filling in `X`.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones` (the sole statement dependency,
  `def-cbc-enhanced-diagrams-cones`): `SSet.Enhanced.mappingSpace`, `mappingSpaceMap`,
  `diagramVertex`, `IsWeakHomotopyEquivalence`, and its quasicategory/internal-hom
  conventions. All are reused without a private replacement.
- The recorded proof dependencies are imported without `public`:
  `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`,
  `SSet.Enhanced.enhanced_functor_cone_calculus`;
  `Sheaf.CategoryTheory.InfinityCofinalCommaCriterion`,
  `SSet.Enhanced.infinity_cofinal_comma_criterion`;
  `Sheaf.CategoryTheory.IsofibrationPullbackLimit`,
  `SSet.Enhanced.isofibration_pullback_limit`;
  `Sheaf.CategoryTheory.NerveNaturalHomotopyEquivalence`,
  `CategoryTheory.nerve_natTrans_homotopy_equivalence`.
  Their full signatures and proof docstrings were read. The module's theorem docstring
  records all six proof steps, including the explicit prepended-zero contraction.
- Mathlib declarations read: `Functor.Elements`, `categoryOfElements`,
  `CategoryOfElements.π` in `Mathlib.CategoryTheory.Elements`;
  `WideSubcategory`, its category and `wideSubcategoryInclusion` in
  `Mathlib.CategoryTheory.Widesubcategory`; `MorphismProperty.op`, `inverseImage`
  and their multiplicativity instances; `SimplexCategory.mono_iff_injective`;
  `nerve` and `nerveMap`; `SSet.uliftFunctor` in simplicial-set Basic.

Edge cases checked before writing: empty `X` gives empty element categories and identity
restriction between the unique empty diagrams; a point has all degenerate simplices, so
its injective indexing category is still the full injective ordinal category; `n = 0`
and constant operators remain objects in the comma contraction. Repeated vertices and
degenerate simplices are never discarded. If `E` is empty there is no vertex `T`, as in
the original quantified statement. The binders explicitly quantify both universe levels.

Searches for an existing theorem (2026-10-17):

- `msearch.py ... leanfinder`, query "Restriction along opposite injective simplex
  category preserves coherent cocone mapping spaces in quasicategories": eight hits,
  concerning strict Segal coskeleta, standard simplices and realization Kan extension;
  none is this theorem.
- `msearch.py ... leansearch`, query "Cofinality of injective simplex operators for
  coherent cocones in quasicategories": eight hits, including Quasicategory,
  simplex degeneracy injection and ordinary cocone injection, none this theorem.
- `msearch.py ... loogle`, query `"SimplexCategory", "Final"`: zero hits.
- `msearch.py ... grep`, query
  `([Ii]njective|[Ss]emi[Ss]implicial).*(cocone|[Cc]ofinal|[Ff]inal)`:
  two unrelated hits (pushout injections in Types and tensor-product inclusions).
- Direct `rg` of the project's `lean/Sheaf`, upstream `WeilConjectures`, Mathlib,
  and `dag/lean_names_upstream.json` found no collision for the four delivered names.
  The upstream blueprint-id search found no declaration for this item.
- Searches for the category of simplices found Mathlib's `X.Elementsᵒᵖ` convention
  (documented in SimplicialSet/Simplices) and the project's
  `Sheaf.AlgebraicTopology.CategoryOfSimplicesLastVertex`, whose `simplexCategory`
  is just that abbreviation. We use `X.Elements` directly. We also read Mathlib's
  `SemiSimplexCategory`: it has no theorem about these coherent cocone spaces.
  Searches of DAG statements for category-of-simplices/injective-simplex notions
  located the existing last/first-vertex and cofinal-replacement lemmas; none
  independently defines this wide subcategory or already states this theorem.

Source checked online: https://people.math.harvard.edu/~lurie/papers/HTT.pdf,
Variant the project server step (3), printed pp. 255–256 (PDF pp. 273–274), and Lemma the project server,
printed p. 676 (PDF p. 694). The latter explicitly contracts all operators by
prepending a vertex, with a constant-to-intermediate-from-identity zigzag.
WANTED: archival HTT source, as already noted by this node's source record.
The sandbox/read-only contract prevents editing `literature/LIST.md` here.

Validation: `scompile.py NF lem-coef-injective-simplex-cocone-restriction <module>`
passed both its sandbox compile (1.5 s) and library-path compile (1.7 s), with no
warnings or errors. The only postponed proof is the main theorem. The node differs
from the repository copy only in `lean`, all four declarations are recorded, and
every Lean line is at most 100 characters. The prescribed delivery dry run follows.

## Second reading by NF

I independently opened the sandbox node and Lean file, the statement and Lean record
of every statement/proof dependency, and the corresponding declaration sources. There
is no repair note for this item. The delivered node changes only `lean`; it has no
`statement_change`, new nodes, or dependency modules. No mathematical or Lean mismatch
was found. I left the statement and its three concrete helpers unchanged.

Source reading: the node cites HTT, not Stacks. I read the primary PDF at
https://people.math.harvard.edu/~lurie/papers/HTT.pdf, Variant the project server (3), printed
p. 255 (PDF p. 273), Notation the project server and Lemma the project server, printed p. 676 (PDF p. 694),
and Proposition the project server, printed p. 226 (PDF p. 244), including the surrounding
hypotheses. The injective-operator category has all ordinal objects. The cofinality
argument uses the operator category over each ordinal and the prepended-vertex
contraction. The cocone restriction result assumes an arbitrary target quasicategory,
without colimit existence. The node's direct comma proof applies to arbitrary `X`;
the fact that the Variant uses a nerve as its particular `X` is not an extra hypothesis
of this general argument. The archival-source WANTED note remains applicable.

Object/hypothesis/conclusion checklist, matched in node order:

1. Small simplicial sets and permitted universe enlargement: `X : SSet.{u}`, with
   explicit `universe u v`, and `E : SSet.{max u v}`. `SSet.uliftFunctor.{v}` lifts
   both indexing nerves and their inclusion to the common universe. Verdict: exact.
2. All simplices of `X`, including degenerate ones: `X.Elements`, defined in Mathlib
   `CategoryTheory/Elements.lean` as a sigma type of an opposite ordinal and an element
   of `X` there. Yoneda identifies the element with `Delta[n] -> X`. There is no
   nondegeneracy predicate. Verdict: exact.
3. The full simplex-category arrows and composition: Mathlib `categoryOfElements`
   has arrows `f` satisfying `X.map f source = target`. Since its base category is
   `SimplexCategory` opposite, an arrow from `([m], tau)` to `([n], sigma)` is the
   opposite of `alpha : [n] -> [m]` with `X.map alpha.op tau = sigma`. Thus this is
   precisely `S(X)^op`, with inherited operator composition. Verdict: exact orientation.
4. Same objects and only injective operators: `injectiveSimplexOppositeCategory X`
   uses `WideSubcategory` of the inverse image under `CategoryOfElements.π X` of
   `(monomorphisms SimplexCategory).op`. I opened `MorphismProperty.op`,
   `inverseImage`, `WideSubcategory`, and `SimplexCategory.mono_iff_injective`.
   The arrow property reduces to `Mono f.val.unop`, equivalently injectivity of its
   order hom; objects have no condition. Verdict: exact, including degenerate objects.
5. The nerve inclusion `j_X`: `injectiveSimplexOppositeInclusion` forgets only the
   arrow property, and `injectiveSimplexNerveInclusion` is its actual `nerveMap`.
   The categories are already opposite, so no second opposite is needed. Verdict: exact.
6. Every quasicategory, diagram, and vertex, in that order: the binders are
   `(E : SSet.{max u v}) [Quasicategory E]`,
   `(p : SSet.uliftFunctor.{v}.obj (nerve X.Elements) ⟶ E)`, and `(T : E _⦋0⦌)`.
   No quasicategory assumption on `X`, colimit assumption, or extra instance appears.
   Verdict: exact.
7. Source cocone mapping space: `mappingSpaceMap` takes the vertices `diagramVertex p`
   and `diagramVertex (SSet.const T)` of the internal hom out of the lifted full nerve.
   I opened the dependency's `diagramVertex`, `mappingSpace`, and `mappingSpaceMap`:
   the entire initial face is constant at the source, and the final vertex is the
   target. Verdict: the recorded right-pinched mapping space, with correct direction.
8. Restriction itself and the specified target space: the simplicial map passed to
   `mappingSpaceMap` is `((MonoidalClosed.pre (SSet.uliftFunctor.{v}.map
   (injectiveSimplexNerveInclusion X))).app E)`. It precomposes every coherence simplex
   by the inclusion. Its two target vertices are the restricted `p` and the restricted
   constant map. Mathlib's `SSet.comp_const` identifies the latter with the constant
   map on the injective nerve. Verdict: actual restriction, not an arbitrary equivalence.
9. Equivalence of Kan complexes: `IsWeakHomotopyEquivalence` is the dependency's
   realization predicate, testing path components and all positive based homotopy
   groups. The existing `enhanced_functor_cone_calculus` gives quasicategory structures
   on both internal homs, and its `QuasicategoryMappingSpaceAssertions` gives Kan
   structures on these exact mapping spaces. These facts require only the existing
   `[Quasicategory E]`. Verdict: exact equivalence-of-spaces convention; no clause lost.
10. Empty case and absence of extra assumptions: the theorem has no nonemptiness,
    colimit, or condition on `X`. Verdict: exact.

Dependency audit: `def-cbc-enhanced-diagrams-cones` is reused through
`Sheaf.CategoryTheory.EnhancedDiagramsCones`; its definitions have concrete data.
The four nonpublic proof imports match their recorded modules and declarations.
In particular, `infinity_cofinal_comma_criterion` has exactly the same restriction
expression with the same `max u v` lift, and its comma convention is arrows from a
fixed target object into the inclusion. `isofibration_pullback_limit` permits an
arbitrary other leg and an empty pullback. `nerve_natTrans_homotopy_equivalence`
permits finite zigzags in either direction without invertible components. Their
interfaces support the node's proof; no dependency repair is needed.

Edge cases checked independently: if `X` is empty, both element categories and nerves
are empty and restriction compares the unique empty diagrams. If `X` is a point,
there is still an object in every dimension and every degenerate simplex is retained;
the injective category is the opposite injective ordinal category, not a singleton.
At `n = 0`, the comma contraction prepends zero to constant operators and still has
the two injective component maps. Repeated vertices do not collapse distinct simplex
operators in the element-category arrows. An empty `E` has no vertex `T`, precisely
as in the quantified natural statement. There is no ring, characteristic, scheme,
or additive zero-object condition. `v = 0` permits the common original universe;
arbitrary `v` permits enlargement, without an equality of independent universes.

Independent searches (2026-10-17), using different phrasing from the worker:

- `msearch.py ... leanfinder "Cofinal inclusion of face-only simplex category preserves
  maps to constant diagrams"`: eight hits about constant simplex maps, face
  representability, and ordinal formulas; no match.
- `msearch.py ... loogle '"Elements", "Final"'`: zero hits.
- `msearch.py ... grep '(face|[Ss]emi[Ss]implicial).*(cocone|[Cc]ofinal)|
  [Cc]ofinal.*[Ee]lements'`: two order-theory cofinality hits; no match.
- Direct `rg` in Mathlib, upstream `WeilConjectures`, and the project's `lean/Sheaf`
  for simplex/semisimplicial cofinality, cocones, and `injectiveSimplex`: only unrelated
  simplex-cocone constructions and ordinary categorical results; no duplicate helper
  or theorem. The four delivered full names have no upstream-name-index collision.
- The DAG search and the read of `CategoryOfSimplicesLastVertex.lean` identify the
  existing `SSet.simplexCategory` as exactly `X.Elementsᵒᵖ`. This file uses Mathlib's
  elements category directly, and does not redefine that notion. No existing node or
  declaration supplies the injective wide subcategory and this restriction theorem.

H5/H6/H8/H9 checks: the three helpers contain real constructions and no choice from an
unproved existence. The only postponed proof is the named theorem's `sorry`. Every
declaration and the module have source/blueprint docstrings. The theorem docstring
contains all six proof steps, including comma orientation, prepended-zero naturality,
opposite contraction, strict pullback, and actual restriction. Imports respect statement
versus proof dependencies; there are no private definitions, local notations or instances,
unbound universes, or overlong Lean lines. The node's `lean.statement` is verbatim the
signature before `:= by`. Changes from this second reading: this report section only.

Second-reader validation: the prescribed `scompile.py` passed the sandbox compile
(1.5 s) and library-path compile (1.6 s), with no warnings or errors. The prescribed
`deliver2.py --no-push` then printed `OK (dry run)`: server preflight and compilation
both passed. The wrapper's shared-fetch queue resolved without intervention.
