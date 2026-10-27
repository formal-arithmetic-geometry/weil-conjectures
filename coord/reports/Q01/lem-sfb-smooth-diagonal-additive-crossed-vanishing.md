## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothDiagonalAdditiveCrossedVanishing` states
`AlgebraicGeometry.smooth_diagonal_additive_crossed_principal`. Its sole theorem has proof
`sorry`; there are no new definitions, instances, or auxiliary theorem statements. The item
statement and its accepted four-step proof plan are unchanged. The declaration docstring carries
all four steps, including division inside a nonsmooth subgroup, the sign of averaging, the
trivial-character case, and the lcm compatibility for the nontrivial character.

Hypothesis and conclusion correspondence:

- The algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The two F-group schemes are `(D N : Over (Spec (.of F))) [GrpObj D] [GrpObj N]`.
  Their affineness is `[IsAffine D.left] [IsAffine N.left]`; their finite type is
  `[LocallyOfFiniteType D.hom] [QuasiCompact D.hom]` and the corresponding two instances for N.
  This is exactly the recorded finite-type convention, including its quasi-compactness.
- Smoothness is `[Smooth D.hom]`, for the structure morphism over F.
- `hdiag` supplies an additive abelian group M, `AddGroup.FG M`, and a group-object isomorphism
  `Grp.mk D ≅ diagonalizableGroup F M`. This is an isomorphism of group schemes, not just of
  underlying schemes. The existing `diagonalizableGroup` uses the canonical Hopf structure of
  `AddMonoidAlgebra F M`, with exactly the basis, product, coproduct, counit and antipode in the
  node. M has universe u, the same as F and the affine schemes; every finitely generated group
  has such a small presentation. This imposes no rank, torsion or connectedness restriction.
- The character is `(chi : D ⟶ multiplicative F) [IsMonHom chi]`.
- The closed additive subgroup is `(i : N ⟶ additive F) [IsClosedSubgroupScheme i]`.
  Its existing class supplies the homomorphism, pointwise injectivity and closed immersion.
- `hstable` quantifies over every commutative F-algebra A, every `d : affine F A ⟶ D`, and
  every x in A. Membership x in N(A) is the actual factorization
  `∃ z : affine F A ⟶ N, z ≫ i = additiveCoordinatePoint F A x`. The conclusion gives the
  same factorization for `multiplicativeCoordinateValue F (d ≫ chi) * x`.
- `(f : D ⟶ N)` is a morphism over F. There is intentionally no `IsMonHom f` assumption.
- `hcrossed` quantifies over A, d, d', and the coordinates x,y of the two image points. Its
  conclusion is `(d * d') ≫ f ≫ i = additiveCoordinatePoint F A (x + chi(d) * y)`, using
  the recorded Laurent-coordinate value for chi(d). The two antecedents merely identify x,y;
  each always exists uniquely because algebra maps out of F[T] are classified by the image
  of T. Thus this is exactly the crossed identity, without any extra hypothesis on f.
  The scoped Mathlib `MonObj` Hom-group multiplication denotes D(A)'s genuine group law.
- The conclusion `∃ a : F, (∃ z : affine F F ⟶ N, z ≫ i = additiveCoordinatePoint F F a) ∧ …`
  is an element of N(F) expressed as its scalar coordinate with a lift along its inclusion.
  The final universal equality uses `algebraMap F A a` for scalar extension and the expression
  `a_A - multiplicativeCoordinateValue F (d ≫ chi) * a_A`, with the required sign. These are
  equalities of A-points of G_a, and the closed subgroup map is injective on A-points.
  Scalar stability and the subgroup operations ensure the right side is an N(A)-point, so this
  gives precisely the identity in N(A). No smoothness or connectedness of N and no connectedness
  of D is imposed anywhere.

Recorded dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraically closed clause of
  `def-weil-algebraic-closure`; no choice of an algebraic closure is needed).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, together with `IsMonHom` and the
  scoped Hom-group operations exposed by the Cartesian group-object API.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and the imported
  `QuasiCompact` convention; `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`, as furnished by
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.IsClosedSubgroupScheme` (the declaration
  namespace is `AlgebraicGeometry`). The full recorded class signatures and docstrings were read.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `StandardGroupSchemes.affine`, `.map`,
  `.multiplicative`, `.multiplicativeGroup`, `.additive`, `.additiveGroup`; their actual
  coordinate constructions and the structure-map characterizations were read.
- `Sheaf.AlgebraicGeometry.DiagonalizableGroup`: `AlgebraicGeometry.diagonalizableGroup`.
- `Sheaf.AlgebraicGeometry.AdditiveSubgroupPolynomialQuotient`:
  `StandardGroupSchemes.additiveCoordinatePoint` and `.multiplicativeCoordinateValue`.
  This module also carries the existing proof dependency
  `.exists_additiveSubgroup_polynomial_quotient`.

The two already-landed nodes `def-sfb-diagonalizable-group` and
`def-sfb-standard-group-coordinate-points` were added to `stmt_deps` to record the reused
Hopf spectrum and coordinate APIs. Their statements and Lean records were read. No node is
created or restated. The torsion-density proof dependency has no Lean record in the read clone;
there is no module of it to import. Its statement is read and its use is retained in the proof
plan; it is not needed to type the statement.

Edge cases checked: D trivial (M=0) forces f=0 by the crossed identity; trivial chi gives the
zero map and permits a=0; N trivial gives a=0; N=G_a is included; finite additive subgroups,
including infinitesimal alpha_p, are included; smooth disconnected diagonalizable groups
such as mu_l with l prime to the characteristic are included. Characteristic zero and every
positive characteristic are permitted. Nonreduced A and the zero test algebra are allowed
(`[CommRing A]` has no nontriviality assumption). The algebra universe equals the fixed
scheme/base universe and includes the coordinate algebras and their tensor products, so the
universal-point tests are available and the conditions cannot become vacuous through an
independent smaller test universe. There are no numerical bounds, empty-index exclusions,
or characteristic restrictions. No statement fault or dispute was found.

Searches actually run:

- `msearch.py … leanfinder "Every regular crossed homomorphism from a smooth diagonalizable
  group scheme to a scalar-stable closed subgroup of the additive group is principal"`:
  eight hits, including Hilbert90 multiplicative Galois coboundaries, Tannaka finite-group
  regular-representation results, and finite cyclic representation norm exactness. None
  is a regular group-scheme cocycle theorem into an arbitrary closed additive subgroup.
- `msearch.py … loogle '"IsCocycle", "AddMonoidAlgebra"'`: zero hits.
- `msearch.py … leansearch "Every regular crossed homomorphism from a smooth diagonalizable
  algebraic group to an additive subgroup is a principal cocycle"`: eight hits in abstract
  group cohomology, especially `groupCohomology.cocycles₁`, `.mem_cocycles₁_iff`, and related
  definitions. None imposes regularity or has this algebraic group conclusion.
- `msearch.py … grep 'crossedHom|crossed_hom|diagonalizable.*cocycle|cocycle.*diagonalizable'`:
  zero Mathlib hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for the
  item id, `smooth_diagonal.*crossed`, `crossedHom`, `crossed_hom`, diagonalizable constructions
  and additive coordinate APIs found no existing target theorem. The diagonalizable search
  found the recorded `DiagonalizableGroup` module and its ring variant; the coordinate search
  found `AdditiveSubgroupPolynomialQuotient`. These were reused, not duplicated.

Source read: local Milne PDF printed pp.303–304 (Proposition 15.3, Lemma 15.2 and group-functor
cochains) and pp.334–335 (Summary 16.29). The source's principal-cocycle convention is
chi(d)m-m; our a=-m gives exactly the node's a-chi(d)a convention. The node's lcm-directed
argument is retained rather than the source's displayed sequence of M(n).

Validation: `scompile.py Q01 lem-sfb-smooth-diagonal-additive-crossed-vanishing <module>`
compiled the sandbox and actual module path cleanly (1.6 s and 1.5 s). The first compile
identified the scoped Hom multiplication instance; adding `open scoped CategoryTheory.MonObj`
fixed it without changing any hypothesis or conclusion. All variables/universes are explicit,
`autoImplicit` is disabled, and every line is at most 100 characters.

## Second reading by Q01

The dispatcher forbids starting other agents, so this is an explicit second pass by the same
worker, not an independent-agent review. The maintainer's independent delivery review remains
separate. I reopened the complete node and completed module and checked the field, all six
finite-type/affineness hypotheses, smooth D, the group-scheme diagonalization, the character,
the closed subgroup and its scalar stability, the scheme morphism f, the crossed identity,
the N(F) witness, scalar extension, universal-algebra conclusion, and absence of N smoothness
or either connectedness assumption. The coordinate-point implications in hcrossed are
nonvacuous by the fully faithful affine spectrum and polynomial evaluation universal property.
The witness lift is genuinely along i, rather than membership in an unrelated subgroup.
The principal sign and the group-object rather than scheme-only diagonalization agree.
The module uses the recorded dependencies, and the one postponed theorem matches this DAG
node. No additional mismatch was found and no mathematical statement was changed.

## Returned delivery repair

H2 (returned immutable head `30253a188189`): replaced the statement dependency
`lem-sfb-additive-subgroup-polynomial-quotient` with the newly landed definition node
`def-sfb-standard-group-coordinate-points` (Q69, `be04af62`). I read its statement and
existing Lean record and reopened the two coordinate definitions in
`AdditiveSubgroupPolynomialQuotient.lean`. They are plain constructions using polynomial
evaluation and the affine-Spec preimage of the Laurent coordinate. They do not depend on
the polynomial quotient theorem's conclusion. That theorem remains in `proof_deps`, where
the finite-subgroup averaging argument uses its additive defining polynomial.

The module and complete `lean` record are unchanged from the returned delivery, as requested.
The mathematical statement, proof plan and every other node field are unchanged; only this
statement-dependency substitution and this report repair the returned work. The delivery
wrapper refreshes the base and creates the repaired commit on current main without direct
Git mutations in the shared read-only checkout. All other checks passed the maintainer's
independent review; this repair changes no hypothesis, conclusion, universe or edge case.
