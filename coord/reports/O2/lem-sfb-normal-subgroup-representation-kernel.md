## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.NormalSubgroupRepresentationKernel`
states `AlgebraicGeometry.normal_subgroup_representation_kernel`, with its only proof
`sorry`. No definition, auxiliary theorem, node correction or new node was needed.
The docstring reproduces all six proof steps of the node, including finite descent
and the restriction-of-scalars matrix construction. I read Milne, Algebraic Groups
(2017), Lemma 5.17, Proposition 5.18 and Corollary 5.19, printed p.103, in the
repository PDF. They agree with the assigned statement.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`.
- The k-schemes are `G N : Over (Spec (.of k))`; `[GrpObj G] [GrpObj N]`
  supply the group schemes of `def-sc-group-scheme`.
- Affineness is `[IsAffine G.left]`. Finite type is exactly
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, as the dependency record specifies.
- The subgroup inclusion is `i : N ⟶ G`, with `[IsClosedSubgroupScheme i]` and
  `[IsNormalSubgroupScheme i]`. These supply the group homomorphism, closed immersion,
  injectivity on all algebra-valued points, and normality of their image. No
  separate affineness or finiteness assumption on N was added.
- The integer rank is `∃ (r : ℕ), 1 ≤ r ∧ ...`; this is exactly an integer r >= 1.
  The finite index set `LinearGroupSchemes.Index.{u} r` is the dependency's
  abbreviation `ULift.{u} (Fin r)`, with exactly r elements, in the field's universe.
- The representation is a scheme morphism
  `ρ : G ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} r) k`, with
  the existential witness `IsMonHom ρ` giving preservation of multiplication and unit.
- The scheme-theoretic kernel clause is
  `∃ e : N ≅ GrpObj.ker ρ, e.hom ≫ GrpObj.kerι ρ = i`.
  This identifies N with the fibre-product kernel as a subscheme of G, rather than
  merely asserting an abstract isomorphism of schemes.
- Every commutative k-algebra is quantified by
  `∀ (A : Type u) [CommRing A] [Algebra k A]`. This follows the dependency's universe
  convention for schemes, points and subgroup predicates; it includes every algebra
  in the universe of the ambient schemes and imposes no finiteness condition on A.
- A point g is a morphism `(Spec (.of A)).asOver (Spec (.of k)) ⟶ G`.
  Membership in N(A), viewed as a subset of G(A), is
  `∃ h : (Spec (.of A)).asOver (Spec (.of k)) ⟶ N, h ≫ i = g`.
  The right-hand side is precisely
  `GeneralLinearGroup.homMulEquiv ... A (g ≫ ρ) = 1`, the invertible identity matrix.
  The biconditional says both inclusions in the required equality.
- Naturality is inherent in the stated scheme morphisms: the inclusion, ρ and e
  induce maps of represented functors by composition. The matrix identification is
  the existing `GeneralLinearGroup.homMulEquiv_specMap_comp`, whose full signature
  was read: precomposition along `Spec` of an algebra homomorphism maps matrix entries
  along that homomorphism. Thus the equality is a natural equality of subfunctors,
  not an unrelated selection of pointwise identifications.
- There are no smoothness, reducedness, connectedness, perfectness or characteristic
  hypotheses. In particular `[Field k]` is the only field assumption.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`; the homomorphism
  class is `CategoryTheory.IsMonHom` from `Mathlib.CategoryTheory.Monoidal.Mon`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`,
  and their parent `IsSubgroupScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes`:
  `AlgebraicGeometry.LinearGroupSchemes.Index`; its public upstream import
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear` supplies
  `AlgebraicGeometry.GeneralLinearGroup`, `GeneralLinearGroup.homMulEquiv`,
  and `GeneralLinearGroup.homMulEquiv_specMap_comp`. The upstream coordinate
  algebra and its Hopf maps were also inspected; no second GL construction is used.
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`:
  `CategoryTheory.GrpObj.ker` and `GrpObj.kerι` (the fibre product and its inclusion).

The recorded, available proof-dependency modules are plain imports: Chevalley
character cancellation, algebraic closure, Spec/limits, affine finite-type algebra,
finite presentation over a Noetherian ring, affine tensor pullbacks, and spreading
out. The two proof-only nodes `lem-sfb-normal-subgroup-character-inversion` and
`lem-sfb-rational-fixed-space-base-change` had no declaration in the node records at
inspection; they introduce no object needed to type this statement, so there is no
prerequisite wait and no attempted duplicate module. They remain named in the proof
plan for stage 3.

Edge cases checked before writing:

- N = G: the trivial representation into GL_1 has the required full kernel.
- N the identity subgroup: the assertion is the usual faithful representation of an
  affine algebraic group. Rank 1 is not imposed; some positive rank is allowed.
- G the trivial group: rank 1 with trivial action works, so no nontriviality is assumed.
- A the zero ring: its spectrum is empty and both point sets and GL_r(A) are singleton;
  there is no `[Nontrivial A]` assumption.
- In characteristic p, N = mu_p in G_m is detected by t -> t^p into GL_1,
  including on nonreduced algebras. Checking just field-valued points would fail;
  the actual statement quantifies over all commutative algebras.
- Nonperfect fields and inseparable finite descent are allowed. The proof plan uses
  a vector-space retraction for injectivity, not separability.
- A rank-zero representation cannot force exclusion of N = G, because a trivial
  summand gives positive rank. ULift changes only the size of the index type.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "Every closed normal subgroup of an affine group scheme
  of finite type over a field is the kernel of a finite dimensional rational
  representation"`: eight hits, including `FDRep.instHasKernels`,
  `Representation.Coinvariants.le_comap_ker` and Galois-category quotient results;
  none construct a rational representation with a prescribed scheme-theoretic kernel.
- `msearch.py ... leansearch "A closed normal subgroup scheme of an affine algebraic
  group over a field is the kernel of a rational representation"`: eight hits on
  topological closed subgroups, scheme ideal kernels, abstract normal cores and
  coinvariants; no exact match.
- `msearch.py ... loogle '"GeneralLinearGroup", "ker"'`: one hit,
  `Matrix.GeneralLinearGroup.kronecker`; no match.
- `msearch.py ... grep 'normal.*subgroup|representation.*kernel' AlgebraicGeometry`:
  zero hits in Mathlib's algebraic geometry directory.
- `rg` with `normal.*subgroup|representation.*kernel|normal_subgroup.*kernel|
  representation_kernel` in both `lean/WeilConjectures` and `lean/Sheaf` found
  subgroup definitions, unrelated abstract representations and downstream proof
  references. No theorem states this result. A focused search of the group-scheme
  directories and `dag/lean_names_upstream.json` gave no existing result.
- `grep -rn 'lem-sfb-normal-subgroup-representation-kernel' lean/WeilConjectures`:
  no attachment. `rg` for the intended declaration name in Mathlib, the upstream
  source and `lean/Sheaf` likewise found no collision.

No statement dispute or node fault was found. The example Sheaf compact-object
module is now withdrawn; I also read its recorded upstream module for the current
header and public-import convention.

Validation: the prescribed `scompile.py O2 lem-sfb-normal-subgroup-representation-kernel`
completed successfully for the delivered module in both sandbox and library modes,
with exit status 0 and no compiler errors or unexpected warnings.

## Second reading by O2

This is the author's separate rereading; the dispatcher brief assigns independent
review to the maintainer and forbids starting another agent. With the node and
completed module open, I checked the field, both group objects, affine and finite-type
conditions, closed normal inclusion, positive rank, actual scheme homomorphism,
kernel identification over G and equality on all algebra-valued points. Each appears
in the signature above. The kernel is not merely abstractly isomorphic to N: the
commuting-inclusion equation is present. Identity is the group unit of invertible
matrices, and the natural identification is the existing upstream one. No additional
hypothesis or missing clause was found, and no statement change was made.
