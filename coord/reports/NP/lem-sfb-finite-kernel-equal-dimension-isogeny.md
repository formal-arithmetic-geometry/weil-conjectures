## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.FiniteKernelEqualDimension` states
`AlgebraicGeometry.surjective_and_isFiniteLocallyFree_of_finite_ker_of_dim_eq`.
Its sole proof is `sorry`; there are no definitions or additional theorems.
The node's statement, statement dependencies, proof and proof dependencies are unchanged.

The source read was Milne, Abelian Varieties I, Proposition 7.1 and its proof,
printed p.32 (PDF p.38), especially (c) implies (d) and the concluding locally free
pushforward. Also read Stacks `morphisms.tex`, Tag 02KB, `lemma-finite-flat`,
which identifies finite flat morphisms over locally Noetherian schemes with finite
locally free morphisms. No correction or disputed statement was necessary.

Hypothesis and clause correspondence:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
  No characteristic restriction is imposed.
- The two k-schemes are `{A B : Over (Spec (.of k))}`; their group structures are
  `[GrpObj A] [GrpObj B]`.
- They are abelian varieties by `[IsAbelianVariety A] [IsAbelianVariety B]`:
  the recorded upstream class asserts properness, smoothness and connectedness.
  Commutativity is a theorem about these objects, not an additional assumption.
- The k-group homomorphism is `(f : A ⟶ B) [IsMonHom f]`. An Over morphism is
  a scheme morphism over k, and IsMonHom expresses compatibility with group laws.
- Equal dimension is `(hdim : A.left.dim = B.left.dim)`. The recorded Scheme.dim
  is the supremum of stalk ring dimensions, so no replacement notion is used.
- Finiteness of the scheme-theoretic kernel over k is
  `[IsFinite (GrpObj.ker f).hom]`. GrpObj.ker is the actual pullback of f
  along the target identity in the Over category; its hom is its map to Spec k.
  It is not a cardinality condition on the kernel's rational points.
- The conclusion is exactly `Surjective f.left ∧ f.left.IsFiniteLocallyFree`:
  surjectivity of the underlying scheme morphism and the recorded finite locally
  free predicate, which extends IsFinite, Flat and LocallyOfFinitePresentation.

The declarations and full interfaces read and used were:

- `Field`, Mathlib.Algebra.Field.Defs, line 180; `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic, lines 55–64.
- `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp, lines 40–48;
  `CategoryTheory.IsMonHom`, Mathlib.CategoryTheory.Monoidal.Mon, lines 210–216.
  These are the recorded def-sc-group-scheme declarations. The upstream module
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs documents their exact
  group-scheme specialization and imports the kernel construction.
- `CategoryTheory.GrpObj.ker`,
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp, lines 64–100,
  including the defining pullback and its cartesian square.
- `AlgebraicGeometry.IsAbelianVariety`,
  WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs, lines 35–49.
- `AlgebraicGeometry.Scheme.dim`, WeilConjectures.AlgebraicGeometry.Dimension,
  lines 47–56, together with dim_eq_topologicalKrullDim and its docstring.
- `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`,
  WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree, lines 889–900.
- `AlgebraicGeometry.IsFinite`, Mathlib.AlgebraicGeometry.Morphisms.Finite.

Statement dependency modules are public imports; already stated proof dependencies
are ordinary imports. These include the proper image, abelian-variety characterization,
isogeny degree, finite-type dimension and fibre/image dimension bounds, plus Mathlib
properness and Noetherian finite-presentation results. The signatures and docstrings
of these recorded results were read. The proof-only node
lem-sfb-finite-kernel-group-fibres has no Lean record yet, so has no import to add.
The theorem docstring preserves all five DAG proof steps and their named inputs.

Edge cases checked before writing:

- Dimension zero is allowed: the trivial abelian varieties and their unique
  homomorphism satisfy the conclusion; there is no positive-dimension hypothesis.
- The empty scheme cannot be an abelian group scheme with identity; no extra
  nonemptiness binder is needed. ConnectedSpace in the abelian-variety interface
  also supplies nonemptiness.
- Positive characteristic, inseparable isogenies and nonreduced finite kernels
  are included. In particular [p] is not excluded by any etaleness assumption.
- The zero map from a positive-dimensional abelian variety fails the finite-kernel
  hypothesis. A proper abelian-subvariety inclusion fails equal dimension.
- The arbitrary universe u covers the field and its schemes, following the
  recorded upstream interfaces; there is no independent test-universe quantifier.

Searches run for the statement and existing notions:

- msearch leanfinder, "A homomorphism between abelian varieties of equal dimension
  with finite scheme theoretic kernel is surjective and finite locally free":
  generic finite morphism results, no abelian-variety criterion.
- msearch leanfinder, "A homomorphism of abelian varieties with finite kernel and
  equal dimension is surjective": eight results, including
  AddMonoidHom.surjective_of_card_ker_le_div, MonoidHom.surjective_of_card_ker_le_div,
  CommGrpCat.epi_iff_surjective and FiniteDimensional.of_surjective; none concern
  scheme kernels and abelian varieties.
- msearch loogle, `"isogeny"`: zero hits (run twice).
- msearch grep, `isogeny|IsIsogeny|AbelianVariety` in AlgebraicGeometry: zero hits.
- rg of upstream abelian-variety sources for finite kernels, isogenies and equal
  dimension found the multiplication-by-n results and IsIsogeny finiteness/flatness,
  which already assume surjectivity and do not state this criterion.
- rg of lean/Sheaf and lean/WeilConjectures for the item id and finite-kernel
  criterion found only a proof-docstring reference in EndomorphismDegreeMultiplicative.
  The requested grep -rn for the item id in lean/WeilConjectures returned no hits.
- rg of dag/lean_names_upstream.json, lean/WeilConjectures and lean/Sheaf for the
  chosen declaration name returned no collision.

Validation: scompile.py compiled this module both as a sandbox module and at its
library module name against the live server build, cleanly (4.8 s and 6.7 s).

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
