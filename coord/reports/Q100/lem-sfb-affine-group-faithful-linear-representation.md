## Worker report

The module `Sheaf.AlgebraicGeometry.AffineGroupFaithfulLinearRepresentation` states
`AlgebraicGeometry.exists_closedImmersion_generalLinearGroup`, with `sorry`. It adds no
definition, dependency module, new node, or statement correction. Only the item's `lean`
record changes. The recorded signature is extracted verbatim from the delivered source.

Source read: Milne, *Algebraic Groups* (2017), printed pp.86–87 (PDF pp.98–99),
Proposition 4.7, Theorem 4.9 and Corollary 4.10; printed p.75 (PDF p.87), Corollary
3.35. Theorem 4.9 proves coordinate surjectivity, hence a closed immersion, without
smoothness or reducedness. The proof docstring gives all six DAG proof steps and
names every dependency used in those steps.

Hypotheses and clauses, in the order of the informal statement:

- The field k is `{k : Type u} [Field k]`, the Mathlib notion recorded by
  `def-weil-field`.
- The k-group scheme is `(G : Over (Spec (.of k))) [GrpObj G]`. Its given group
  operations are retained. The recorded group-scheme definition is the internal
  group-object structure, not a private algebraic-group predicate.
- Affineness is `[IsAffine G.left]`.
- Finite type is `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, precisely the
  conjunction recorded by `def-weil-finite-type-morphism`.
- The positive integer is `∃ (m : ℕ) (_ : 1 ≤ m)`.
- The representation is `ρ : G ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} m) k`
  together with `IsMonHom ρ`. Thus ρ is a morphism over Spec k compatible with the
  given multiplications. The index is the dependency's `ULift (Fin m)`, which has
  exactly m elements and fits the common universe of the upstream GL interface.
- Closed immersion is `IsClosedImmersion ρ.left`, on the underlying scheme map.
- For every commutative k-algebra is `∀ (A : Type u) [CommRing A] [Algebra k A]`.
  An A-point is `(Spec (.of A)).asOver (Spec (.of k)) ⟶ G`. The function whose
  injectivity is asserted sends x to `GeneralLinearGroup.homMulEquiv ... (x ≫ ρ)`.
  This is exactly the matrix-valued ρ_A, using the existing canonical equivalence.
- The scalar-extension conclusion quantifies `K : Type u`, `[Field K]`, `[Algebra k K]`,
  and every commutative K-algebra A. The map is postcomposition by
  `(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map ρ` on the
  A-points of the pullback of G. This is the actual scalar extension of the same ρ.
  Its target is the scalar extension of GL_m,k, canonically GL_m,K; injectivity as
  scheme-valued points is equivalent to matrix-valued injectivity under that canonical
  identification. No arbitrary map, additional representation, or scalar-tower choice
  is introduced. Test algebras and extension fields have the same universe as the base,
  as required by the published Scheme and GeneralLinearGroup interfaces; u is arbitrary.
- No smoothness, connectedness, reducedness, algebraic closedness, characteristic, or
  perfectness binder appears. There are no other assumptions.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (docstring and declaration at lines 170–180).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` (lines 46–51).
  `CategoryTheory.IsMonHom` is the existing multiplication-compatible morphism notion
  (`Mathlib.CategoryTheory.Monoidal.Mon`, line 213). The source conventions were checked
  in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, especially its module docstring.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
  The exact class definitions and docstrings were read.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes`: `AlgebraicGeometry.LinearGroupSchemes.Index`.
  Its source and node record explicitly reuse upstream GL. Accordingly the conclusion
  uses `AlgebraicGeometry.GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv` from
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`, publicly imported by that
  recorded dependency. Both full definitions and docstrings were read: GL is the spectrum
  of the determinant localization, and homMulEquiv identifies its points with invertible
  matrices. No replacement of GL was necessary.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (lines 42–46), with its actual closed-embedding
  and surjective-stalk definition.
- `Mathlib.CategoryTheory.Comma.Over.Pullback`: `CategoryTheory.Over.pullback`
  (lines 58–70), the real base-change functor whose map pulls back ρ.

All recorded and available proof-dependency modules are imported privately when they
are not already public statement dependencies: `Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra`,
`Sheaf.RingTheory.FiniteSubcomodule`,
`Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`,
`Mathlib.AlgebraicGeometry.Pullbacks`, and `Mathlib.RingTheory.TensorProduct.Maps`.
The remaining Mathlib proof interfaces are supplied transitively by these imports or the
public dependency imports: affine Hopf algebra, finite type, finite dimension, tensor product,
affine Spec, and closed-immersion affine criterion. No dependency module is omitted for a cycle.

Edge cases checked before writing:

- The trivial group and the case with no nonconstant algebra generators are included:
  adjoining 1 to the chosen finite subset makes the constructed dimension positive.
- The empty scheme cannot carry a group scheme over a field: the identity section would
  give a point of the empty scheme. No nonemptiness assumption is added.
- Dimension zero is deliberately excluded only by the required `1 ≤ m`; the existing
  GL construction also has m = 0 but the conclusion asks for positive dimension.
- The algebra A may be nonreduced or the zero ring, since only `CommRing A` and its
  algebra structure are required. No `Nontrivial A` or pointwise reducedness appears.
- Arbitrary characteristic and imperfect fields are retained. Infinitesimal groups such
  as alpha_p are not excluded, so faithfulness is on all algebra points, not only fields.
- Field scalar extension uses the same ρ functorially; K = k and A = K are included.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder`: “Every affine group scheme of finite type over a field
  admits a closed immersion into a positive dimensional general linear group”. Eight
  hits, including `IsClosedImmersion.of_surjective_of_isAffine`, affine properties and
  the topological SL-to-GL inclusion. None constructs the required representation.
- `msearch.py ... loogle`: `"GeneralLinearGroup", "IsClosedImmersion"`. Zero hits.
- `msearch.py ... leansearch`: “An affine group scheme of finite type over a field admits
  a closed immersion into GL of a finite dimensional vector space”. Eight hits: closed
  immersion criteria, affine schemes and related properties; no exact statement.
- `msearch.py ... grep`:
  `faithful.*representation|closedImmersion.*[Gg][Ll]|[Gg]roup[Ss]cheme.*representation`.
  Four hits, in Weyl groups, Lie algebra documentation and a closed-immersion identity
  theorem. None is a group-scheme representation existence theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the same conceptual terms,
  `exists.*[Gg]eneral[Ll]inear`, and this node id found references to faithful
  representations and a stronger central-torus weight-block theorem. The latter assumes
  an algebraically closed field, so it is not this statement. The node id has no existing
  declaration in those source trees. Searching `dag/lean_names_upstream.json` for the
  faithful-linear and affine-representation terms found no exact declaration.
- Read the existing GL module found by the source search, rather than recreating its
  coordinate algebra or point equivalence.

Validation: `scompile.py Q100 lem-sfb-affine-group-faithful-linear-representation <file>`
compiled both the sandbox module and its final library-module name cleanly on the server
(16.6 s and 1.6 s respectively). `set_option autoImplicit false` enforces explicit binders.
No statement dispute or node fault was found.

## Second reading by Q100

This is the author's second reading, under the direct-delivery brief; independent review
belongs to the maintainer. With the DAG statement and final Lean source open, I checked
that the hypotheses are exactly a field, a given group object over its spectrum, affine
underlying scheme, and finite-type structure morphism. The existential dimension is
positive, the very same ρ has multiplication compatibility and is a closed immersion,
and its points are sent to actual invertible matrices by the published homMulEquiv.
The final clause pulls back that same ρ, and quantifies every K-algebra, rather than only
K-rational points. Reading the pullback implementation confirms its object is the fibre
product over Spec k and its map is the canonical induced fibre-product map. The zero
algebra and nonreduced group schemes remain admitted. No extra hypothesis or missing
clause was found, and no correction was needed. All six natural-language proof steps
are present in the declaration docstring; its sole proof is `sorry`.
