## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.ClosedRationalSubgroupRealization`
states `AlgebraicGeometry.closed_rational_subgroup_realization` with `sorry`.
It introduces three helpers belonging to this same canonical construction:
`rationalSubgroupClosureIdeal` is the vanishing ideal sheaf of the topological
closure of the underlying S-points, `rationalSubgroupClosure` bundles its actual
closed subscheme over Spec k, and `rationalSubgroupClosureι` is the actual canonical
inclusion in the over category. They have real data, no existence choice and no
postponed proofs. These helpers are listed in `lean.declarations` and have source
and blueprint docstrings. No new notion or dependency repair is needed.

Hypothesis and clause correspondence (node unchanged):

- A field k is `{k : Type u} [Field k]`. The universe u is explicitly declared;
  `set_option autoImplicit false` rules out auto-bound variables.
- The k-group scheme is `(G : Over (Spec (.of k))) [GrpObj G]`, using exactly
  the recorded group-object interface, without commutativity.
- Separated is `[IsSeparated G.hom]`. Finite type is the conjunction of
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`. Properness is not assumed:
  the cited proper-morphism node also defines separatedness, and only this part
  of its vocabulary is needed.
- Rational points are `𝟙_ (Over (Spec (.of k))) ⟶ G`. The tensor unit in this
  cartesian over category is `Over.mk (𝟙 (Spec (.of k)))`, hence these are precisely
  k-morphisms Spec k to G, the recorded field-valued-point specialization.
- The map to underlying points is `fun s ↦ s.left (IsLocalRing.closedPoint k)`.
  Spec k has one point. Distinct k-sections have distinct underlying points:
  their residue-field maps are forced by their being k-morphisms. Thus using
  Hom instead of its image does not change the stated identification.
- The topology in hS is explicitly `TopologicalSpace.induced` by this map from
  G's Zariski topology. `@IsClosed` specifies that topology directly, so the
  statement does not depend on any ambient topology on a Hom type. This is the
  subspace topology after the preceding identification, including over finite k.
- `(S : Subgroup ...)` means exactly that S contains 1 and is stable under
  multiplication and inverses, with no extra topological-group hypothesis.
- T is `TopologicalSpace.Closeds.closure` of the image of `(S : Set _)` in G.
  `rationalSubgroupClosureIdeal` is the existing `vanishingIdeal` of this T.
  The helper `rationalSubgroupClosure` is `Over.mk (I.subschemeι ≫ G.hom)`:
  its underlying scheme is I.subscheme, exactly the reduced induced closed
  subscheme from the recorded dependency. No arbitrary reduced closed scheme
  has been substituted for it. Its canonical inclusion is `Over.homMk I.subschemeι rfl`.
- `∃ hH : GrpObj (rationalSubgroupClosure G S), ...` asserts actual multiplication,
  unit and inverse morphisms on this fixed H, with all group diagrams. Supplying
  hH explicitly to `@IsClosedSubgroupScheme` ties this same structure to j.
- `IsClosedSubgroupScheme j` is the recorded upstream class: it includes
  `IsMonHom j`, injectivity on R-points for all k-algebras R, and closed immersion
  of j.left. `IsMonHom` asserts that the unit and multiplication are restrictions
  of G's; the inverse is then also a restriction since group homomorphisms
  preserve inverses. Hence all three requested restricted morphisms are present.
- The final `Set.range (fun s ↦ s ≫ rationalSubgroupClosureι G S) = (S : Set _)`
  is exactly H(k)=S via the specified inclusion.
- No affineness, smoothness, connectedness, perfectness, algebraic closure,
  reducedness of G, or characteristic restriction is added. In particular the
  construction of H does not assume that G_red is a subgroup.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs.
- `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp, and the
  rational-point group instance `CategoryTheory.Hom.group` from
  Mathlib.CategoryTheory.Monoidal.Cartesian.Grp, publicly imported by the
  recorded upstream group-scheme module.
- `LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType;
  `QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `IsSeparated`, Mathlib.AlgebraicGeometry.Morphisms.Separated (the separated
  component of the recorded proper-morphism terminology).
- `CategoryTheory.Over`, Mathlib.CategoryTheory.Comma.Over.Basic, and its
  Hom type for field-valued points.
- `Scheme.IdealSheafData.reduced_induced_closed_subscheme`,
  WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme. Read its full
  signature and nine-step docstring; its actual Mathlib constructions
  `vanishingIdeal`, `subscheme`, `subschemeι` define the chosen H and j.
- `IsReduced`, Mathlib.AlgebraicGeometry.Properties: reduced sections, equivalent
  to reduced stalks, as recorded by def-pc-reduced-scheme. Here reducedness is
  furnished by the fixed vanishing-ideal construction, not an extra hypothesis.
- `IsClosedSubgroupScheme` (extending `IsSubgroupScheme`),
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. Read the full definitions
  and docstrings of both classes and their `IsMonHom` and R-point clauses.

Proof-only imports are the recorded field-point factorization module and
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion for
`IsClosedImmersion.existsUnique_fac_of_range_subset_range`. The product-density
proof dependency `lem-sfb-dense-rational-product-reduced` has no Lean record yet,
so it cannot be imported. Its role is explicitly retained in the proof docstring.
The proof docstring follows all five DAG proof steps, including the density in
the scheme product, reduced-source factorizations, and cancellation of the
closed immersion for all group diagrams.

Source checked: `literature/milne-algebraic-groups_iAG2017.pdf`, printed p.19,
PDF p.31, Theorem 1.45 and its proof, read with pdftotext. The source constructs
the same reduced closed subscheme with support closure S; density of H(k)
ensures geometric reducedness and reducedness of H times H. The node only
requests the existence/group/rational-point part, so uniqueness and geometric
reducedness are not added to its conclusion.

Edge cases checked before writing:

- S={1}: the closure construction gives the reduced identity subscheme, and
  the rational-point equality has its intended meaning.
- S=G(k): when rational points are not dense in G, H can be smaller than G_red;
  the construction closes the actual S-image and does not accidentally use G_red.
- A finite field: S is closed in its rational-point subspace; its finite reduced
  union is consistent with the conclusion even when G has positive dimension.
- Imperfect k: the assertion does not reduce an arbitrary subgroup scheme;
  dense rational points of this specific H justify the product step. A reduced
  scheme Spec k[x]/(x^p-a) without rational points cannot be this H.
- Nonreduced G such as mu_p: S={1} is realized by the reduced identity point.
- Nonaffine G, for example an abelian variety: no affine assumption occurs.
- Empty G cannot carry a group object over the nonempty Spec k; an empty S
  cannot be a Subgroup. These are consequences of the stated unit hypotheses,
  not additional exclusions. No assumption `[Nonempty G.left]` was introduced.

Searches for existing statements and constructions:

- msearch.py leanfinder: `closed rational point subgroup reduced closure group scheme`;
  eight hits, including closed-point lemmas, abstract topological subgroups,
  and a Galois automorphism embedding; no realization theorem.
- msearch.py leansearch: `The reduced Zariski closure of a closed subgroup of rational points
  is a closed subgroup scheme`; eight hits on IsReduced, subscheme, and ClosedSubgroup;
  no realization theorem.
- msearch.py loogle: `CategoryTheory.GrpObj, AlgebraicGeometry.IsClosedSubgroupScheme`;
  zero hits, unknown IsClosedSubgroupScheme (it is upstream, not Mathlib).
- msearch.py grep: `GroupScheme|group scheme|ClosedSubgroup` in Mathlib/AlgebraicGeometry;
  zero returned hits from that query. Direct source reads nevertheless verify
  the foundational group-object and scheme constructions actually used.
- rg over lean/WeilConjectures/AlgebraicGeometry, lean/Sheaf/AlgebraicGeometry and
  dag/lean_names_upstream.json: `rational.*subgroup|subgroup.*rational|closedRationalSubgroup|
  closed_rational_subgroup|closure.*subgroup|subgroup.*closure`. The matrix-group
  closure results specialize to GL_n, and the group-homomorphism image results
  concern actual homomorphism images, not arbitrary rational subgroups. None
  realizes S in general G over arbitrary k. The DAG upstream-name hit
  lem-wf-zariski-closure-subgroup is this matrix specialization.
- grep -rn of the item's id in lean/WeilConjectures returned no occurrence.
- rg of `rationalSubgroupClosure|closed_rational_subgroup_realization` in
  lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json returned no
  preexisting declaration. The three helpers only package the canonical objects
  of this node; they do not redefine ideal sheaves, reduced induced structures,
  rational points, group schemes or subgroups.

No statement dispute, correction, dependency-module delivery, or new node.

## Second reading by Q26

A second self-reading opened both the copied node and the complete Lean file.
There is no second worker in this dispatcher assignment, and the brief forbids
starting agents; the maintainer supplies the independent review after delivery.
The correspondence was checked again clause by clause: k/Field, G/Over+GrpObj,
separated/IsSeparated, finite type/LocallyOfFiniteType+QuasiCompact,
S/Subgroup plus explicitly induced-topology IsClosed, T/closure of the point
image, H/vanishingIdeal.subscheme over k, j/canonical subscheme inclusion,
restricted group laws/GrpObj plus IsClosedSubgroupScheme on that very j,
and H(k)=S/range of postcomposition on rational points. The helper definitions
were read through to the Mathlib vanishing ideal and subscheme, so this is not
an existentially chosen replacement H. No hypothesis or clause mismatch was
found. Elaboration repairs replaced an implicit default point by the explicit
unique `IsLocalRing.closedPoint k` and named the common ideal to prevent large
repeated unfolding; neither changes a mathematical statement. No proofs were
written: the theorem ends with sorry and the three definitions contain actual data.
