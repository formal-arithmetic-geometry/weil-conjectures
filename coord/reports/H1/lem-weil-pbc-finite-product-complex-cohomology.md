## Worker report

Item: lem-weil-pbc-finite-product-complex-cohomology. Module:
`lean/Sheaf/Algebra/Homology/FiniteProductCohomology.lean`.
Declaration: `HomologicalComplex.homology_finite_product_comparison_isIso`.
This is a statement only, with one named theorem whose proof is `sorry`.
No definition, new node, dependency module, or statement correction is needed.
The node copy changes only its `lean` field.

Hypothesis and clause correspondence:

- The finite set I is `(I : Type w) [Finite I]`. The index universe `w` is
  independent of the group universe `u`; no enumeration or nonemptiness is assumed.
- Each K_i is a cochain complex of abelian groups: the family is
  `(K : I → CochainComplex AddCommGrpCat.{u} ℤ)`.
- The componentwise product complex is `∏ᶜ K`, the domain product in
  `piComparison`. Mathlib's `HomologicalComplex.coneOfHasLimitEval`,
  `isLimitConeOfHasLimitEval`, and the evaluation limit-preservation instance in
  `Mathlib.Algebra.Homology.HomologicalComplexLimits` compute it degreewise.
  The differential is the map of the diagram of component differentials.
  The forgetful functor on abelian groups preserves limits, identifying its
  degreewise groups with ordinary tuple products.
- Every integer q is the unrestricted binder `(q : ℤ)`.
- H^q is `homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) q`.
  Its object value is `K.homology q`, the homology of the associated short complex.
- The isomorphism H^q(product K_i) → product H^q(K_i) is expressed by
  `IsIso (piComparison (homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) q) K)`.
  This identifies the actual canonical map, rather than asserting an unrelated
  isomorphism exists. `asIso` recovers its isomorphism once the proposition is used
  as an instance.
- Canonicity: `piComparison` is defined as
  `Pi.lift (fun i => G.map (Pi.π K i))`; thus each coordinate is the cohomology
  map of the corresponding projection, by `piComparison_comp_π`.
- Naturality: for maps f_i : K_i → L_i, compose both sides of the naturality
  square with each target projection. Both composites are H^q of
  `Pi.π K i ≫ f_i`, by `piComparison_comp_π`, the defining equation for
  `Pi.map`, and functoriality of `homologyFunctor`. Product uniqueness gives
  equality. This uses the existing canonical comparison's construction; the
  theorem asserts its invertibility. The comparison exists for each q; there
  are no additional maps between integer degrees in the node's statement.

Dependency declarations read and used:

- `def-sp-abelian` is a Mathlib leaf whose `mathlib_match` names
  `CategoryTheory.Abelian`, `Mathlib.CategoryTheory.Abelian.Basic`.
  Read its complete class signature and docstring: preadditive, finite products,
  kernels, cokernels, normal monos and epis. The abelian group instance is
  `AddCommGrpCat.instAbelian`, in `Mathlib.Algebra.Category.Grp.Abelian`.
  It supplies the abelian structure and hence homology needed here. There is no
  `lean` record on this leaf to import, and no dependency specialization needs
  replacement.
- `HomologicalComplex.homologyFunctor` and `HomologicalComplex.homology`,
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`, were read with
  their full signatures and docstrings.
- `CategoryTheory.Limits.piComparison`,
  `Mathlib.CategoryTheory.Limits.Shapes.Products`, was read with its definition,
  docstring, and projection identity. No new notion is introduced.

Edge cases checked before writing: empty I gives the zero complex and zero
cohomology, with the unique 0 → 0 comparison; singleton I gives the identity
comparison up to the canonical product identifications; zero complexes have
zero cohomology. Arbitrary positive and negative q, unbounded complexes, and
q = 0 are included. Finite indices in an arbitrary universe are supported by
Mathlib's finite-limit instances; the server compile confirmed the independent
universe binders need no extra smallness assumptions. No characteristic or
coefficient ring restrictions apply to abelian groups.

Searches made (2026-10-11):

- msearch.py leanfinder, query: `cohomology of finite products of cochain complexes
  of abelian groups is canonically naturally isomorphic to product of cohomology`.
  Eight hits, including `CochainComplex.HomComplex.homologyAddEquiv` and
  low-degree group-cohomology isomorphisms; none state this comparison's
  invertibility.
- msearch.py loogle, query: `homologyFunctor, PreservesLimitsOfShape`.
  No hits, unknown identifier `homologyFunctor` in the unqualified query.
- msearch.py leansearch, query: `cohomology functor preserves finite products
  of cochain complexes`. Service unavailable: Internal Server Error. No
  mathematical verdict is inferred from this unavailable service.
- msearch.py loogle, query: `CategoryTheory.Limits.piComparison`. Twelve hits,
  including `piComparison`, `piComparison_comp_π`, `map_lift_piComparison`,
  and `instIsIsoPiComparison`. The last requires an existing preservation
  instance, so does not itself assert the present cohomology result.
- msearch.py grep, query: `piComparison|homologyFunctor`, subdirectory
  `Algebra/Homology`. Twenty-five generic homology/functor hits; no theorem
  specializing product comparison invertibility to cochain complexes of
  abelian groups.
- Direct rg of Mathlib Algebra/Homology for
  `finite.*product|homology.*[Pp]roduct|product.*homology`: no exact statement.
  Read `HomologicalComplexLimits.lean` to verify degreewise products.
- Direct rg of the source `WeilConjectures` and project `lean/Sheaf` for the item
  id and `homology.*[Pp]roduct|product.*homology`: no exact declaration.
  The project `DerivedFiniteProduct.lean` cites this node in its proof docstring,
  but its statement concerns right derived functors, not cochain complex
  cohomology. The derived-category tower/product modules also have different
  objects and hypotheses.
- Name collision rg for
  `finite_product.*homology|homology.*finite_product|homology_piComparison`
  in Mathlib, the source, project Lean, and `dag/lean_names_upstream.json`:
  no collision with the new declaration.

The source place is the node's explicitly worker-supplied elementary formulation
in `literature/stacks-project/homology.tex`, not a numbered Stacks theorem.
This remote checkout contains citation lists but no downloaded Stacks tex file;
the complete elementary proof is in the node and is reproduced in the theorem
body's docstring, step by step. No source-based correction is necessary and no
statement is disputed.

Validation: scompile.py compiled the module on the server in 1.3 seconds,
exit code 0, with no warnings. Final delivery dry run follows below.

## Second reading by H1

Step-by-step comparison with the node:

- The finite set is rendered as `(I : Type w) [Finite I]`; this includes the empty and singleton
  index types and imposes no nonemptiness or enumeration. Verdict: exact.
- The family of cochain complexes of abelian groups is rendered as
  `(K : I → CochainComplex AddCommGrpCat.{u} ℤ)`. `AddCommGrpCat` is the abelian-group
  category supplied by Mathlib's `def-sp-abelian` dependency. Verdict: exact; no extra
  Noetherian, characteristic, or finiteness hypothesis is present.
- The componentwise product complex is the product diagram used by
  `piComparison ... K`, with products computed degreewise by the imported homological-complex
  limits. Verdict: exact canonical product object.
- For every integer degree, the node's `q : ℤ` is an unrestricted binder and the conclusion is
  `IsIso (piComparison (homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) q) K)`.
  This is precisely the canonical map from the cohomology of the product to the product of
  cohomologies; `piComparison_comp_π` identifies its coordinate maps. Verdict: exact, with no
  weakened or strengthened quantifier.
- Naturality and canonicity are represented by the canonical `piComparison` construction and
  its projection identities, as required by the node. Verdict: exact.

Edge cases checked: empty `I` (zero product and the unique zero comparison), singleton `I`
(identity comparison under canonical product identification), zero complexes, `q = 0`, positive
and negative integers, unbounded complexes, arbitrary coefficient universe `u`, and independent
index universe `w`. No characteristic restriction or scheme hypotheses occur in the node, and
none were added to Lean.

Existing-definition searches were independently checked with `msearch.py` (LeanFinder query for
finite-product cohomology of cochain complexes; Loogle queries for `homologyFunctor` and
`piComparison`; direct `rg` over Mathlib `Algebra/Homology`, `WeilConjectures`, and `lean/Sheaf`).
They found only generic homology, product-limit, and low-degree cohomology declarations; no
statement asserting invertibility of this canonical comparison. The declaration name also has no
collision in the project or upstream name index.

No mismatch was found, so no source, node statement, dependency, or Lean code was changed during
this second reading. The module was recompiled with `scompile.py` and completed with no errors or
warnings beyond the permitted `sorry` proof placeholder.
