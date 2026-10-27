## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.MultiplicativeUnipotentBaseAlgebraVanishing`
states `AlgebraicGeometry.multiplicative_unipotent_base_algebra_vanishing`, with its whole
proof `sorry`. It introduces no definitions. The existing node changes only in `lean`.

Read the item, every statement-dependency node and its recorded interface, the dependency
sources, and Milne, Algebraic Groups (2017), Proposition 15.18 (printed p.312) and
Theorem 14.5 (printed pp.281--282), by extracting the local PDF. Proposition 15.18
explicitly quantifies over a k-algebra R; Theorem 14.5 identifies unipotence with a
closed algebraic subgroup of a unitriangular group. The five proof steps from the node
are included in the theorem docstring, including the coefficient comparison over rings,
finite kernel induction, and faithfully flat descent. No assertion uses geometric
points as a substitute for all algebra-valued points.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| A field k | `{k : Type u} [Field k]` |
| D and U are k-group schemes | `(D U : Grp (Over (Spec (.of k))))`; the bundled objects carry `GrpObj` structures and morphisms carry `IsMonHom` |
| D and U are affine | `[IsAffine D.X.left]`, `[IsAffine U.X.left]` |
| Both groups are finite type | `[LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom]` and the corresponding U instances |
| D is of multiplicative type over the fixed algebraic closure | `hD : MultiplicativeType.IsMultiplicativeType D`, whose recorded definition uses `AlgebraicClosure k`, canonical field base change and `IsClosedSubgroupScheme` into `splitTorus` of arbitrary finite rank |
| U admits a closed group immersion into U_n with n at least one | `hU` quantifies `n : ℕ` with `1 ≤ n`, and a map `r : U.X ⟶ GeneralLinearGroup (ULift (Fin n)) k` with `IsClosedSubgroupScheme r`, satisfying the unitriangular equations on every algebra point |
| All entries below the diagonal vanish | For every commutative k-algebra B and every point x, every pair i,j with `j.down < i.down` has `(GeneralLinearGroup.homMulEquiv ... (x ≫ r)).val i j = 0` |
| Every diagonal entry is one | For every such B and x and every index i, the corresponding `.val i i = 1` |
| Every commutative k-algebra R | `(R : Type u) [CommRing R] [Algebra k R]`, with no `Nontrivial` or `Field` assumption |
| Scalar extension is fibre product with Spec R, with the induced group law | `((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).mapGrp).obj D` and the corresponding expression for U |
| Every R-group homomorphism f | `f` is a morphism between those two group objects in `Grp (Over (Spec R))` |
| f is the trivial morphism | `f.hom.hom = 1`; the scoped `MonObj` Hom unit is the map through the identity section |
| Every commutative R-algebra A and every d in D_R(A) | `∀ (A : Type u) [CommRing A] [Algebra R A] (d : (Spec (.of A)).asOver (Spec (.of R)) ⟶ ...), ...` |
| f_A(d) = 1 | `d ≫ f.hom.hom = 1` |
| R and A need not be reduced; groups need not be smooth or connected | No such hypotheses occur; the statement uses explicit unitriangular equations rather than the smooth-only predicate |

The closed faithful representation and all-algebra equations express exactly a closed
embedding into U_n. Since U_n is the closed subscheme of GL_n cut out by those equations,
testing on the universal affine U-point shows that the pulled-back equations vanish.
The morphism factors through the defining quotient, and its factor into U_n is closed
because its composite into GL_n is closed. Conversely, a closed embedding into U_n
supplies precisely these equations. No extra embedding or group-theoretic assumption is
introduced. This is an inline expansion of the item's own stated notion, not a second
project definition. In particular, `SolvableGroupStructure.IsUnipotent` was inspected
and deliberately not used: it includes `Smooth` and only tests geometric points.

Recorded dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`, and `Functor.mapGrp`;
  group homomorphisms are the bundled morphisms. `open scoped MonObj` enables the
  existing identity-valued map on the underlying Over hom-set.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsClosedSubgroupScheme`,
  extending `IsSubgroupScheme` and hence `IsMonHom`, and asserting `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `.QuasiCompact`, and
  `.ClosedImmersion`: `LocallyOfFiniteType`, `QuasiCompact`, `IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes` is the recorded general-linear node
  module and publicly imports the actual upstream `GeneralLinearGroup` and its
  `GeneralLinearGroup.homMulEquiv`, in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`. The latter is a
  group equivalence on arbitrary commutative algebra points, with a naturality lemma.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `MultiplicativeType.IsMultiplicativeType`, using its recorded `baseChange` and
  `splitTorus`. The latter uses `StandardGroupSchemes.multiplicative` from the
  recorded `Sheaf.AlgebraicGeometry.StandardGroupSchemes`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`, used by
  the existing multiplicative-type definition; `Mathlib.AlgebraicGeometry.Scheme`:
  `Spec`, `Spec.map`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` records that scheme
  base change uses the existing `Over.pullback`; its underlying object is precisely
  `pullback` with the second projection. `Mathlib.CategoryTheory.Comma.Over.Pullback`
  supplies `Over.pullback`; finite-product preservation lifts it with `Functor.mapGrp`.
  The field-only `MultiplicativeType.baseChange` is not used on a general ring R.

Plain imports retain stated proof dependencies: `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`
(`ringDiagonalizableGroup`), `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`
(`Module.FaithfullyFlat.instTensorProduct` and the free nontrivial module instance),
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
(`Module.FaithfullyFlat.tensorProduct_mk_injective`), and
`Mathlib.AlgebraicGeometry.Pullbacks` (`pullbackSpecIso`). The two proof-only nodes
`lem-sfb-split-torus-subgroups-diagonalizable` and
`lem-sfb-unitriangular-coordinate-filtration` currently have no recorded Lean module;
no import is fabricated for either. `def-pc-fibre-product` is the standard `pullback`
already available through the imported scheme base-change interface.

Edge cases checked before writing:

- The zero rings R and A are permitted by `CommRing`. Their spectra are empty and
  their coordinate algebras/point sets behave as in step 1 of the recorded proof.
- Nilpotent elements in R and A remain visible because points range over all
  commutative algebras, not just fields or reduced rings. For example dual-number
  algebras and characteristic-p infinitesimal groups are not excluded.
- For n=1 the lower-triangular constraints are empty and the only diagonal entry
  is one, so U is trivial. The theorem does not require n to exceed one.
- Rank-zero split tori and trivial D or U are included. `IsMultiplicativeType`
  quantifies over all natural ranks and uses the trivial group at rank zero.
- Finite nonsmooth multiplicative-type groups such as mu_p in characteristic p
  and nonsmooth unipotent groups such as alpha_p are retained; no smoothness,
  connectedness, or characteristic restriction is present.
- The matrix index is `ULift.{u} (Fin n)` so upstream GL and the base field/test
  algebras have the same explicitly bound universe. Rings are not quantified in
  a separate possibly smaller universe, and all binders are explicit under
  `set_option autoImplicit false`.

Searches actually run using the prescribed wrapper:

- LeanFinder: `Every homomorphism from a multiplicative type group scheme to a
  unipotent group scheme over an arbitrary base algebra is trivial` returned eight
  hits, including `Grp.uniqueHomFromTrivial`, `CommGrp.uniqueHomFromTrivial` and
  initial/terminal scheme facts. None concerns these nontrivial source and target groups.
- Loogle: `"IsUnipotent", "hom"` returned zero hits.
- Mathlib grep: `multiplicative.*unipotent|unipotent.*multiplicative|IsUnipotent`
  returned zero hits.
- LeanSearch: `Homomorphisms from multiplicative type group schemes to unipotent
  group schemes vanish over any commutative base algebra` returned eight hits on
  `MulHom`, `MulChar`, their conversions and related abstract multiplicative maps;
  none is the group-scheme assertion.
- Direct ripgrep of `lean/WeilConjectures` and `lean/Sheaf` for the item id found no
  declaration. Searches for `Unipotent`, `unitriangular`, and multiplicative/unipotent
  combinations found the smooth-only `SolvableGroupStructure.IsUnipotent`, proof-plan
  references and unrelated matrix diagrams, but no exact statement. The upstream
  declaration index was also checked. No duplicate theorem was found.

The first compiler check found only the missing scoped notation for the Hom unit;
adding `open scoped MonObj` repaired it without changing the signature's mathematics.
The server then compiled both its sandbox copy and the actual library module with
exit code zero and no diagnostics (22.9 and 21.1 seconds, within the default 60 seconds).
The delivery dry run recompiles the final file, including its minor docstring wording fix.
No statement correction, new nodes, dependency replacement modules, or disputed
mathematical assertions are needed.

## Second reading by Q26

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
