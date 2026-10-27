## Worker report

Item: `lem-sfb-equal-dimension-isogeny-criterion`, group NY, stage 2.
The module `Sheaf.AlgebraicGeometry.AbelianVariety.EqualDimensionIsogenyCriterion`
states the two clauses of the node as two theorems, both with `sorry` proofs:
`AlgebraicGeometry.isIsogeny_iff_surjective_of_topologicalKrullDim_eq` and
`AlgebraicGeometry.not_isDominant_of_not_isIsogeny`. It introduces no definitions.
Only the item's `lean` field changes. No new nodes, dependency repairs, or statement corrections.

Source read directly: `literature/milne-abelian-varieties_AV.pdf`, PDF pp.38–39,
printed pp.32–33, extracted with `pdftotext -f 38 -l 39 -layout ... -`.
Proposition 7.1 explicitly equates (a) isogeny with (b) equal dimensions and
surjectivity. Its proof begins with the closed-image argument and explains
properness over the base point. Footnotes 6–7 stress the scheme-theoretic kernel
in characteristic p. The Lean uses precisely that kernel through `IsIsogeny`.

Hypothesis and conclusion correspondence:

- Any field k: `{k : Type u} [Field k]`, with explicit `universe u` and
  `set_option autoImplicit false`. No characteristic, perfectness, separability,
  or algebraic-closure assumption.
- A and B over k: `{A B : Over (Spec (.of k))}`. This uses the library's
  universe convention for k-schemes, also used by the dependency declarations.
- Group schemes: `[GrpObj A] [GrpObj B]`. The multiplication, inverse and unit
  and their axioms are the existing internal group structures in the over category.
- Abelian varieties: `[IsAbelianVariety A] [IsAbelianVariety B]`, whose recorded
  definition extends properness and smoothness of the structure morphism and
  connectedness of the underlying space. No extra commutativity binder is needed.
- Equal dimension: `(h_dim : topologicalKrullDim A.left = topologicalKrullDim B.left)`.
  These are exactly the underlying topological Krull dimensions, with no natural-number
  replacement or choice of a dimension parameter.
- k-group homomorphism: `(f : A ⟶ B) [IsMonHom f]`. The over-category arrow
  enforces compatibility with k, and `IsMonHom` preserves multiplication and unit;
  the group structures then also ensure inverse compatibility.
- Isogeny iff surjective on scheme points: `IsIsogeny f ↔ Surjective f.left`.
  The former already extends `IsMonHom f` and `Surjective f.left` and contains
  `IsFinite (GrpObj.ker f).hom`. The latter is Mathlib's class whose field is
  `Function.Surjective` for the underlying point map. This is not surjectivity
  on k-rational points, nor categorical epimorphism.
- In particular, an endomorphism of A: the second theorem independently binds
  `{A : Over (Spec (.of k))} [GrpObj A] [IsAbelianVariety A] (f : A ⟶ A)
  [IsMonHom f]`. No spurious B or dimension hypothesis remains.
- Not an isogeny implies not dominant: `(hf : ¬ IsIsogeny f) : ¬ IsDominant f.left`.
  `IsDominant` means dense range of the underlying scheme-point map.

Dependency declarations inspected and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (the class and its docstring).
- `def-sc-abelian-variety`: `AlgebraicGeometry.IsAbelianVariety`,
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs` (public import).
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  `Mathlib.Topology.KrullDimension` (public import); defined as `Order.krullDim`
  of the irreducible closed subsets.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  `Mathlib.CategoryTheory.Monoidal.Grp`, and `CategoryTheory.IsMonHom`,
  `Mathlib.CategoryTheory.Monoidal.Mon`; their full signatures and defining fields
  were read. These are publicly provided by the GroupScheme.Defs import.
- `def-sc-isogeny`: `AlgebraicGeometry.IsIsogeny`,
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` (public import).
  Its full signature, parents, finite-kernel field and docstring were read.

All already stated proof dependencies are imported without `public` where they
are not already statement imports: `WeilConjectures.AlgebraicGeometry.GroupScheme.Image`
(`exists_isMonHom_imageι`),
`Sheaf.AlgebraicGeometry.AbelianVariety.HomImageDimension`
(`isAbelianVariety_image_and_dimension`),
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
(`exists_topologicalKrullDim_le`),
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`
(`GrpObj.ker`), `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
(`IsClosedImmersion`),
`Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite`
(`closed_subscheme_finite_of_topologicalKrullDim_le_zero`),
`Mathlib.AlgebraicGeometry.Morphisms.Proper` (`IsProper.of_comp`), and
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed` (`Scheme.Hom.isClosedMap`).
The theorem docstrings reproduce the corresponding four proof steps of the DAG.

Edge cases checked mathematically before writing:

- Dimension zero: surjectivity still gives a finite kernel, and the equivalence
  includes the trivial abelian variety. No positive-dimension hypothesis appears.
- The zero homomorphism on a positive-dimensional A is neither surjective nor an
  isogeny and is not dominant. On the trivial abelian variety it is an isogeny;
  the premise of the second theorem is then false, as required.
- In positive characteristic, inseparable multiplication maps can have nonreduced
  finite kernels. The definition asks for finiteness of the actual kernel scheme,
  with no reducedness or etaleness assumption.
- Imperfect fields remain allowed. Neither the definitions nor our binders impose
  perfectness or separability.
- Empty schemes are not excluded by a new hypothesis: they cannot be group objects
  over Spec k because of the unit, and abelian varieties here are connected/nonempty.
- Unequal dimensions are excluded exactly by the written node hypothesis; a
  positive-dimensional kernel of a surjection onto a smaller abelian variety
  explains why the dimension hypothesis is essential.

Searches for an existing statement (all made with the prescribed wrapper):

- LeanFinder: `A homomorphism between equal dimensional abelian varieties is an
  isogeny if and only if it is surjective`: eight hits, including ordinary group
  epimorphism/surjectivity criteria, `surjective_iff` for schemes, and
  `FiniteDimensional.of_surjective`; no abelian-variety isogeny criterion.
- Loogle: `IsIsogeny, Surjective`: zero hits, unknown identifier `IsIsogeny`.
- Mathlib grep: `IsIsogeny|isogeny|IsAbelianVariety`, `AlgebraicGeometry`: zero hits.
- LeanSearch: `A surjective homomorphism between abelian varieties of equal dimension
  is an isogeny`: eight hits, including quotient-by-kernel equivalences for rings/groups
  and `AlgebraicGeometry.Surjective`; no matching theorem.
- `rg` of `lean/WeilConjectures` for `IsIsogeny`, isogeny/surjectivity and the proposed
  declaration names: definitions and special multiplication-isogeny theorems exist;
  `AbelianVariety/Isogeny.lean` concerns properties of given isogenies and [n], not
  the equal-dimension criterion. The item-id search has no matching declaration.
- `rg` of `lean/Sheaf` for the criterion and proposed names: only docstring references
  in DegreePolynomial, EndomorphismDegreeMultiplicative and
  AmplePolarizationPositiveSpectrum; no existing theorem with this statement.
- The proposed full names were also searched in `dag/lean_names_upstream.json` and
  in Mathlib; no clashes.

No `STATEMENT-DISPUTED` flag: the source agrees with the node, and the checked edge
cases do not reveal a fault.

## Second reading by NY

The dispatcher explicitly prohibits starting another agent; the maintainer supplies
the independent delivery review. This is a second reading by the same worker, not
a claim of independent review. Reopened the node and the module and checked each
clause: the first theorem has k, A, B, both group and abelian structures, the exact
Krull-dimension equality, the homomorphism, and both directions of the equivalence.
The second binds an endomorphism with the same field and abelian hypotheses and
states precisely the contrapositive nondominance consequence. It has no stray B
or added dimension restriction. The actual `Surjective` and `IsDominant` definitions
were checked to concern scheme points. No mismatch found and no source correction
needed. Every theorem is `by sorry`; no construction or definition was duplicated.

## Validation

Validation used only `scompile.py` and `deliver2.py`, as authorized by the brief.
`scompile.py NY lem-sfb-equal-dimension-isogeny-criterion <module>` passed both
sandbox and library compilation (1.6 s and 1.5 s), with no errors or unexpected warnings.
`deliver2.py NY lem-sfb-equal-dimension-isogeny-criterion --no-push` printed
`OK (dry run): commit 240a1690504 passes the preflight and compiles; nothing pushed`.
The exact delivery has only the module, item node, and this report. A direct JSON
comparison confirmed that `lean` is the only changed node field; every Lean line
is at most 100 characters. The final delivery reruns the compilation and preflight.
