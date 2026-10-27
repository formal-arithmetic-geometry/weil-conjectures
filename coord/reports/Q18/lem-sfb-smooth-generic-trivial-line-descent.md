## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothGenericTrivialLineDescent` states
`AlgebraicGeometry.smoothGenericTrivialLineDescent`, with its sole proof `sorry`.
No definition, dependency interface, statement correction, or new node is needed.
The node is unchanged except for `lean`.

Clause-by-clause correspondence:

- The field is `(k : Type u) [Field k]`.
- The schemes are `(S Y : Scheme.{u})`. Their structures over k are
  `[S.Over (Spec (CommRingCat.of k))]` and the analogous binder for Y.
- Regularity is `(hS : IsRegularScheme S)` and `(hY : IsRegularScheme Y)`.
  The recorded definition includes local Noetherianity, as well as stalkwise regularity.
- Integrality is `[IsIntegral S] [IsIntegral Y]`, including nonemptiness.
- Separatedness over k is `[IsSeparated (S ↘ Spec (CommRingCat.of k))]` and
  its Y counterpart. `IsSeparated` says the diagonal is a closed immersion.
- Finite type over k is the pair `[LocallyOfFiniteType ...] [QuasiCompact ...]`
  on each structure morphism, precisely the recorded finite-type interface.
- The morphism is `(f : Y ⟶ S)`. Smoothness and surjectivity are `[Smooth f]`
  and `[Surjective f]`.
- Nonempty geometrically integral fibres are `[GeometricallyIntegral f]`.
  Mathlib's class means that every field-valued base change is integral;
  `GeometricallyIntegral.iff_geometricallyIntegral_fiber` identifies it with
  geometric integrality of every residue-field fibre. Integrality includes
  nonemptiness. Every field-valued point factors through the residue field of
  its image, so this is exactly the node's stated extension-field condition.
- The generic-point inclusion is `S.fromSpecStalk (genericPoint S)`. Its source
  is `Spec (S.presheaf.stalk (genericPoint S))`, definitionally `Spec S.functionField`.
  The `Field S.functionField` instance and
  `functionField_isFractionRing_of_isAffineOpen` identify this field with the
  fraction field of every nonempty affine coordinate ring as the node requires.
- The generic fibre is `pullback f (S.fromSpecStalk (genericPoint S))`;
  its map to Y is `pullback.fst f (S.fromSpecStalk (genericPoint S))`.
- The line is `(M : Y.Modules) [M.IsInvertible]`, using the recorded invertibility class.
- Generic triviality is `hM`: `Nonempty` of an isomorphism from the tensor
  pullback of M along this first projection to `SheafOfModules.unit` of the
  generic fibre's ring sheaf. This unit is the structure sheaf as a module.
- The conclusion is `∃ N : S.Modules, N.IsInvertible ∧ Nonempty (...)`, with
  the isomorphism `(Scheme.Modules.tensorPullback f).obj N ≅ M`. Thus the
  existential invertibility and isomorphism have exactly the required direction.

Dependency declarations inspected and used:

- `Field`, in `Mathlib.Algebra.Field.Defs` (publicly available through the imports).
- `AlgebraicGeometry.Scheme`, `Scheme.Hom`, in `Mathlib.AlgebraicGeometry.Scheme`.
- `AlgebraicGeometry.IsRegularScheme`, in `Sheaf.AlgebraicGeometry.IsRegularScheme`.
- `AlgebraicGeometry.IsIntegral`, in `Mathlib.AlgebraicGeometry.Properties`.
- `AlgebraicGeometry.LocallyOfFiniteType`, in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `QuasiCompact`, in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `AlgebraicGeometry.Smooth`, in `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `CategoryTheory.Limits.pullback` and `pullback.fst`, in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; scheme pullbacks
  come from the public algebraic-geometry imports.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible`, in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`.
- `AlgebraicGeometry.Scheme.Modules.tensorPullback`, the actual inverse-image,
  extension-of-scalars, and sheafification construction in
  `WeilConjectures.AlgebraicGeometry.TensorPullback`, publicly re-exported by
  the recorded dependency module `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`.

Additional existing interfaces are `GeometricallyIntegral` in
`Mathlib.AlgebraicGeometry.Geometrically.Integral`, `IsSeparated` in
`Mathlib.AlgebraicGeometry.Morphisms.Separated`, `Scheme.fromSpecStalk` in
`Mathlib.AlgebraicGeometry.Stalk`, and the generic stalk/function-field API in
`Mathlib.AlgebraicGeometry.FunctionField`. No duplicate notion is introduced.
The proof dependency `rem-pc-regular-normal` is imported privately from
`Sheaf.AlgebraicGeometry.RegularNormalDecomposition`; the smooth/finite-presentation,
pointwise finite-type, and function-field Mathlib proof dependencies are imported too.
`lem-sfb-normal-noetherian-generic-line-pullback` has no recorded Lean declaration,
so it cannot yet be imported; it is only a proof dependency, and no interface for
it is required to state this item. Its use remains documented in the theorem's
proof docstring. There is no dependency wait.

Source and edge cases:

Read Stacks `divisors.tex`, `lemma-in-image-pullback` (Tag 0BD7): it assumes local
Noetherianity of the source and normal integral base, flat integral nonempty fibres,
quasi-compactness or local finite type, and generic triviality. The node's regular
smooth setting implies these conditions exactly as the node's three proof steps say.
The docstring reproduces those three steps and their named DAG inputs.
The empty source or base is excluded by integrality in both the node and Lean.
Empty geometric fibres are also excluded by `IsIntegral`, not silently allowed.
The base can have dimension zero; the generic stalk map and pullback still exist,
and there is no positive-dimension or positive-relative-dimension hypothesis.
The identity family and the structure-sheaf line are included. All characteristics
are included, and k is not assumed algebraically closed or perfect. No properness,
projectivity, section of f, or compatibility of f with the separately given
k-structures is added: the node only names f as a scheme morphism. There is no
arbitrary generic map or arbitrary comparison in place of the canonical construction.
All universes and variables are explicitly bound and auto-implicit insertion is disabled.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "Line bundle trivial on generic fibre of smooth morphism
  with integral fibres is pulled back from the base"`: eight results, concerning
  topological bundle trivializations, integral morphisms, and pullbackId; no match.
- `msearch.py ... loogle "AlgebraicGeometry.Smooth, AlgebraicGeometry.IsIntegral"`:
  zero hits.
- `msearch.py ... leansearch "invertible module generically trivial on fibres is
  pulled back from base"`: eight results, including topological trivializations,
  ideal-sheaf comap, restrictStalkNatIso and additive pullback; no match.
- `msearch.py ... grep 'generic.*(line|[Ii]nvertible)|[Ii]nvertible.*generic|GeometricallyIntegral'
  AlgebraicGeometry`: nine hits on the geometric-integrality API, affine space,
  and abelian schemes; no descent statement.
- Local `rg` in both `lean/WeilConjectures` and `lean/Sheaf` with the same pattern,
  then the narrower generic/invertible pattern, found existing generic-stalk and
  divisor constructions and proof-docstring references in AffineCellPicardProduct,
  but no theorem with this statement. An exact item-id search in
  `lean/WeilConjectures` found no match. The equivalent exact recursive search
  `grep -rn` also found no match. Proposed camel-case and snake-case declaration
  names were searched in both source trees and `dag/lean_names_upstream.json`;
  neither already exists.

Validation: the complete module passed `scompile.py Q18
lem-sfb-smooth-generic-trivial-line-descent` against the live published build, in
both sandbox and library mode (1.9 s and 1.7 s), with no error or unexpected warning.
No `#check` commands, local notation, local instances, private definitions, or
proofs other than the one required `sorry` are present. No statement dispute found.

## Second reading by Q18

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
