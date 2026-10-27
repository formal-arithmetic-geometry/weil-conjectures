## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.StructureSheafH1Dimension` states
`AlgebraicGeometry.IsAbelianVariety.finrankH_one_structureSheaf_eq_dim`, with its whole proof
`sorry`. It introduces no definitions. The statement of the DAG node is unchanged.

Hypotheses and conclusion, clause by clause:

- “Let k be a field”: `{k : Type u} [Field k]`, with `universe u` explicitly declared.
- “algebraically closed”: `[IsAlgClosed k]`. This is the definition cited in the
  algebraic-closure dependency's `mathlib_match`, not a chosen algebraic extension.
- “A/k”: `(A : Over (Spec (.of k)))`. The underlying scheme is `A.left` and its specified
  structure morphism is `A.hom`; the standard `OverClass` instance uses that morphism when
  evaluating `finrankH`.
- “abelian variety”: `[GrpObj A] [IsAbelianVariety A]`. The recorded predicate means proper,
  smooth, connected; its docstring explicitly requires the group-object instance separately.
- “of dimension g”: `IsAbelianVariety.dim A` is the library's natural-number dimension of A.
  This substitutes its value for the informal name g, instead of adding a redundant binder
  and equality hypothesis. Its source theorem `IsAbelianVariety.topologicalKrullDim_eq`
  identifies it with topological Krull dimension.
- “H^1(A,O_A)”: `Scheme.Modules.finrankH k (SheafOfModules.unit A.left.ringCatSheaf) 1`.
  The unit module is O_A, and `finrankH` is `Module.finrank k (M.H 1)`. In the imported
  source definition, `M.H` is sheaf cohomology of the underlying abelian sheaf on the small
  Zariski site. `moduleHOfField` restricts scalars through `globalSectionsRingHom` of the
  given structure morphism. No etale or group cohomology is substituted.
- “dim_k H^1 = g”: the equality to `IsAbelianVariety.dim A`. Proper coherent finiteness is
  available as a proof dependency, so finrank has its usual finite-dimensional meaning here;
  finite dimensionality is not imposed as a new hypothesis.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: `IsAlgClosed`, in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, as explicitly specified by the dependency's
  `mathlib_match` record for algebraically closed fields.
- `def-sc-abelian-variety`: `AlgebraicGeometry.IsAbelianVariety` and
  `AlgebraicGeometry.IsAbelianVariety.dim`, in
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`.
- The cohomology is reused from `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `AlgebraicGeometry.Scheme.Modules.H`, `moduleHOfField`, and `finrankH`.

The statement dependencies have public imports. The modules of all currently recorded proof
inputs (including the Mathlib matches and both modules recorded for the global-section input)
have plain imports. The currently unstated proof nodes
`lem-sfb-abelian-closed-subgroup-reduced-component`, `lem-sfb-graded-primitive-product`, and
`lem-sfb-projective-picard-identity-representability` have no module to import; they are named
in the full proof docstring. They are not required to type the statement.

The docstring follows the node's nine steps: coherent finiteness and degree vanishing; the
primitive-product upper bound; the general Picard identity component and tangent space; the
normalized ample family and theorem of the cube; the reduced identity kernel; complete-system
ampleness on the subgroup; its zero dimension and finite kernel; the closed-fibre argument;
and the two dimension inequalities. In particular it does not assume smoothness of the Picard
identity component, nor does it divide by factorials in characteristic two.

Edge cases checked before writing:

- g = 0 is included: there is no positive-dimension hypothesis or nonzero-degree restriction.
  The trivial abelian variety Spec k has H^1(O) = 0 and dimension zero, as required.
- Characteristic two and all other positive characteristics are included. There is no
  characteristic, separability, polarization, or projectivity hypothesis added.
- The empty scheme is not an abelian variety: the existing connected-space condition and
  group identity exclude it; no separate nonemptiness hypothesis is imposed.
- The field and scheme use the same arbitrary universe u, the established library convention
  for schemes over fields; no small fixed universe or countability condition is imposed.

Searches for an existing declaration (all through the prescribed search wrapper or read-only
source searches):

- LeanFinder: “The first cohomology of the structure sheaf of an abelian variety has dimension
  equal to the dimension of the abelian variety”. Eight hits about cotangent cohomology or
  group cohomology, no match.
- Loogle: `IsAbelianVariety, Module.finrank`. No hits; Mathlib's index does not know the
  project-specific identifier `IsAbelianVariety`.
- LeanSearch: “Dimension of the first coherent cohomology of an abelian variety equals its
  dimension”. Eight group- or cotangent-cohomology hits, no match.
- Mathlib grep: `finrank.*H|H.*finrank`, under AlgebraicGeometry. Hits concern elliptic-curve
  coordinate rings and finite-flat morphism ranks, not structure-sheaf H^1.
- `rg` in both project roots: `finrank.*H|H.*finrank|h1.*dim|dim.*h1`, followed by the narrower
  `finrankH.*dim|dim.*finrankH|arithmeticGenus.*dim|dim.*arithmeticGenus`. The library already
  has `finrankH` and curve/Jacobian genus results, but no H^1 dimension theorem for an arbitrary
  abelian variety. The AbelianVariety directory was also searched separately.
- `grep -rn` for the item id in `WeilConjectures` found no attachment. Searching both roots,
  Mathlib and the upstream name index for the new declaration name found no existing name.

Source read: Milne, Abelian Varieties, I Remark 8.7(e), printed p.37 (PDF page 43), which
identifies H^1(O_A) with the tangent space of the dual and records equality of dimensions.
The node's complete proof supplies the noncircular coherent-dimension argument used in the
docstring. The requested example `Sheaf.CategoryTheory.CompactObject` is now withdrawn;
its node points to `WeilConjectures.CategoryTheory.CompactObject`, which was read for the
current public-module convention.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED issue is needed.

Validation: the prescribed server compile passed for the delivered module with no errors or
warnings (both the sandbox probe and the library-path compile).

## Second reading by Q147

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
