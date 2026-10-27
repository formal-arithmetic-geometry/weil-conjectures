## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.WeilExtension` states
`AlgebraicGeometry.existsUnique_extension_to_abelianVariety`, with its proof `sorry`.
There are no definitions, extra lemmas, new nodes, dependency repairs or statement changes.
The module and theorem docstrings give Milne's source and all five proof steps of the DAG.

Hypothesis and conclusion correspondence:

- The field k is `(k : Type u) [Field k]`.
- The k-scheme X is `(X : Over (Spec (.of k)))`; its structure map is `X.hom`.
- Nonempty and integral are `[IsIntegral X.left]`. Mathlib's recorded `IsIntegral`
  includes nonemptiness, so a separate `Nonempty` assumption is unnecessary.
- Separated over k is `[IsSeparated X.hom]`.
- Finite type over k is `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`,
  the two parts fixed by the convention node and its finite-type definition leaf.
- Smooth over k is `[Smooth X.hom]`.
- The abelian variety B/k is `(B : Over (Spec (.of k))) [GrpObj B]
  [IsAbelianVariety B]`. The recorded upstream class supplies properness, smoothness,
  and connectedness; its own documentation requires the group structure separately.
- The open subscheme is `(U : X.left.Opens)`, whose scheme is `U.toScheme`.
  Denseness is `(hU : Dense (U : Set X.left))`.
- The given map is `(f : U.toScheme ⟶ B.left)`; being a k-morphism is exactly
  `(hf : f ≫ B.hom = U.ι ≫ X.hom)`.
- Existence and uniqueness are `∃! F : X.left ⟶ B.left, ...`.
- The extension is over k by `F ≫ B.hom = X.hom`.
- Restriction to U is exactly `U.ι ≫ F = f`.
  Uniqueness quantifies over maps satisfying both clauses, thus exactly over extensions
  as k-scheme morphisms. No group-homomorphism condition is imposed on f or F.

Statement dependencies read and used:

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties`; read its section-ring definition and
  nonemptiness field, not just its name.
- `def-weil-pbc-scheme-conventions`: this is explicitly a convention-only record,
  not a declaration. Its separated and finite-type clauses use
  `AlgebraicGeometry.IsSeparated` (`Mathlib.AlgebraicGeometry.Morphisms.Separated`),
  `AlgebraicGeometry.LocallyOfFiniteType` (`...Morphisms.FiniteType`) and
  `AlgebraicGeometry.QuasiCompact` (`...Morphisms.QuasiCompact`). Read each class's
  full signature and docstring: closed diagonal, affine-local finite type, and
  quasi-compact preimages respectively. The finite-type conjunction is also the
  recorded match of `def-weil-finite-type-morphism` in the proof dependencies.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`; its affine-local smooth-ring condition
  is the recorded equivalent definition of the node's lifting criterion.
- `def-sc-abelian-variety`: `AlgebraicGeometry.IsAbelianVariety`,
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`; read the complete definition
  and its explanation that `[GrpObj B]` is deliberately not a parameter of the class.
  The existing group-scheme interface is imported from
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.

Proof-dependency imports are included: `Sheaf.TraceFormula.SmoothGeometricallyNormal`,
`Sheaf.AlgebraicGeometry.IsRegularScheme`, finite-type/proper/reduced Mathlib modules,
`Mathlib.AlgebraicGeometry.Gluing` (the recorded `Scheme.Cover.glueMorphisms`),
`Mathlib.AlgebraicGeometry.Morphisms.Separated` (the recorded
`ext_of_isDominant_of_isSeparated`), `WeilConjectures.AlgebraicGeometry.Regular`,
`Mathlib.RingTheory.DiscreteValuationRing.Basic`,
`Sheaf.AlgebraicGeometry.RationalMapExtensionValuationPoint`, and
`Sheaf.AlgebraicGeometry.GroupRationalDivisorialIndeterminacy`.
No import cycle is introduced. The two latter modules were read, including their
explicit base-compatibility equations, which agree with this statement's encoding.

Source checked directly in the supplied PDFs: Milne, Algebraic Groups 8.16–8.18,
printed pp.151–152, and Abelian Varieties I, Theorems 3.1–3.2 and Lemma 3.3,
printed pp.16–18. The source combines codimension-at-least-two indeterminacy for
proper targets with pure-codimension-one indeterminacy for group targets. The DAG's
uniqueness clause follows from the recorded relative separated-target equality lemma.
The supplied source statement is correct and needs no correction.

Edge cases checked before writing: an empty X is excluded by the node and by
`IsIntegral`; consequently a dense open U cannot be empty. U equal to all of X
is allowed and gives the original morphism under the canonical open identification.
Dimension-zero sources and the dimension-zero abelian variety are included.
Neither a k-rational point of X nor geometric integrality of X is required.
No perfectness, algebraic closedness, characteristic restriction, properness of X,
or positive dimension is assumed. The explicit universe u ranges over arbitrary
sizes of k and its schemes, following the recorded scheme and abelian-variety APIs.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “Every morphism from a dense open of a smooth integral
  variety to an abelian variety extends uniquely to the whole variety”. Eight hits,
  principally `ext_of_isDominant_of_isSeparated`, `ext_of_isDominant`,
  `Scheme.PartialMap.fromFunctionField_restrict`, and other extensionality results.
  None asserts global existence of an extension to an abelian variety.
- `msearch.py ... loogle`: `"IsAbelianVariety", "extension"`. No hits.
- `msearch.py ... grep`: `AbelianVariety|rational.*extend|extend.*rational`,
  subdirectory `AlgebraicGeometry`. No Mathlib hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf`, by the node id and by abelian
  extension/rational-map language, found the citer MultipleRetraction's proof plan,
  abelian field-extension results, and unrelated sheaf extensions, but no statement
  giving this extension theorem. Read the relevant abelian-variety module declarations.
- Exact-name `rg` in Mathlib, both project roots and `dag/lean_names_upstream.json`
  found no `existsUnique_extension_to_abelianVariety` or `weil_extension_to_abelian_variety`.

Validation: `scompile.py Q60 lem-sfb-weil-extension-to-abelian-variety` compiled the
single delivered file in both sandbox and library module modes, with no errors or
warnings (18.2 s and 5.3 s). Every variable and universe is explicitly bound, with
`set_option autoImplicit false`.

## Second reading by Q60

I reread the node and the final signature after the first compile. This is a self-check;
the dispatcher's instruction forbids starting other agents, and the maintainer supplies
the independent review. Nonemptiness is already in `IsIntegral`; retaining both finite-type
components preserves the node verbatim. Both `[GrpObj B]` and `[IsAbelianVariety B]`
are necessary to mean the recorded abelian-variety definition. The equations for hf and
F use exactly the given structure maps, with no arbitrary replacement map or hidden
choice. The `∃!` predicate includes both base compatibility and restriction equality.
Thus the unique object is exactly a k-morphism extending f. No mismatch was found and
no statement or signature was changed during this rereading.
