## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso` defines the statement
`AlgebraicGeometry.isIso_of_finite_birational_normal` with proof `sorry`. It states
that a finite morphism between integral schemes is an isomorphism when it induces the
function-field isomorphism at the generic points and every target local ring is a
normal domain.

The node's hypotheses and their Lean rendering are:

- Integral schemes `X` and `Y` (`[IsIntegral X] [IsIntegral Y]`), using the recorded
  Mathlib declaration `AlgebraicGeometry.IsIntegral`.
- A scheme morphism `f : X ⟶ Y` (`(f : X ⟶ Y)`).
- Finiteness (`[IsFinite f]`), using the recorded Mathlib declaration
  `AlgebraicGeometry.IsFinite` from `def-weil-finite-integral-morphism`.
- The birational generic-point condition is rendered by
  `(hgeneric : f (genericPoint X) = genericPoint Y)` together with
  `hbirational : Function.Bijective (...)`. The displayed hom is
  `((Y.presheaf.stalkCongr (Inseparable.of_eq hgeneric)).inv ≫
  f.stalkMap (genericPoint X) : Y.functionField ⟶ X.functionField)`: the stalk
  congruence transports the actual generic stalk map to the function fields
  `Y.functionField` and `X.functionField`. Thus this is the map induced by `f`,
  rather than an arbitrary abstract field isomorphism.
- Normality of every local ring of `Y` is the inline recorded normal-domain form
  `(hnormal : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
  IsIntegrallyClosed (Y.presheaf.stalk y))`, using the `def-weil-pbc-normal-ring`
  interface (`IsDomain` and `IsIntegrallyClosed`).
- The conclusion is `IsIso f`.

The theorem docstring records the proof clause by clause. For every affine open of
`Y`, finiteness gives an affine inverse image and a finite ring map. The generic-point
and function-field bijectivity conditions give an injective map with a common fraction
field. The target local normal-domain condition and the local-to-global normal-domain
criterion make the target affine ring integrally closed. The finite source algebra is
integral over it, hence equal to it. Equality on affine opens glues to `IsIso f`, with
`f⁻¹(∅) = ∅` for the empty-open case. The proof dependencies named in the node are
therefore used in the docstring: `lem-sc-integral-function-field-affine-fraction`,
`lem-weil-pbc-affine-open-stalk-localization`,
`lem-weil-pbc-finite-algebra-is-integral`, and
`lem-weil-pbc-normal-domain-of-local-normal`.

Recorded dependency declarations used:

- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral` (Mathlib,
  `Mathlib.AlgebraicGeometry.Properties`).
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite` (Mathlib,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`); its companion integral predicate is
  not needed in this finite statement.
- `def-sc-function-field`: `AlgebraicGeometry.Scheme.functionField` and the
  existing `Scheme.Hom.stalkMap` (Mathlib `Mathlib.AlgebraicGeometry.FunctionField`
  and `Mathlib.AlgebraicGeometry.Scheme`), imported through
  `Sheaf.AlgebraicGeometry.FunctionField`.
- `def-weil-pbc-normal-ring`: `IsDomain` and `IsIntegrallyClosed` from
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, used in the inline
  conjunction above.

Edge cases checked: `f = 𝟙 X` with a normal integral scheme satisfies the generic
point and bijective-stalk hypotheses; a punctured-curve open immersion fails
finiteness; a cusp normalization shows target normality is necessary; a finite
non-birational cover fails bijectivity at the generic stalk; and no assumption on the
source normality or on a field of definition is present. The generic-point equality
keeps the birational map canonical and excludes an unrelated abstract field
isomorphism.

Searches made before writing:

- `msearch.py leanfinder` query “finite birational morphism of integral schemes with
  normal target is an isomorphism”: eight normalization/properness hits, none states
  this theorem (`no match`).
- `msearch.py leansearch` query “finite integral birational morphism onto normal
  scheme is an isomorphism”: eight `IsFinite`/normalization hits, none states this
  theorem (`no match`).
- `msearch.py loogle` query `AlgebraicGeometry.IsFinite, IsIso, IsNormal`: zero hits;
  Loogle reported unknown identifier `IsIso` (`unavailable` for this query).
- `msearch.py grep` query `birational|normal.*isIso|IsIso.*normal` in
  `Mathlib/AlgebraicGeometry`: zero hits (`no match`).
- `rg` over `WeilConjectures` and the project's `lean/Sheaf` for
  `finite_birational`, `birational.*normal`, and `isIso_of_finite_birational_normal`:
  no existing statement. The only nearby declaration is the separately stated
  proper-curve theorem in another sandbox, with extra curve/properness hypotheses.
- The recorded dependency modules and full signatures were read, including
  `Sheaf.AlgebraicGeometry.FunctionField` and Mathlib's
  `AlgebraicGeometry.Scheme.Hom.stalkMap` and `Scheme.functionField`.

No node correction, new node, dependency module, or `STATEMENT-DISPUTED` flag is
needed. The source statement is Tag 0AB1, and the Lean theorem has exactly its
integral-source, finite-birational, normal-target, isomorphism shape.

## Second reading by NZ

I reread the item JSON, the four dependency records, the module signature, and Tag
0AB1. Both integral-scheme binders, the finite morphism, the induced generic-point
function-field map, every target local normal-domain clause, and the `IsIso f`
conclusion are present. The transported stalk map is the canonical map attached to
`f`; no arbitrary field equivalence or source normality is introduced. The module
compiles cleanly with `scompile.py`, with only the expected `sorry` proof. No
statement correction or missing notion was found.
