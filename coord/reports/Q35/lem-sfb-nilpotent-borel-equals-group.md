## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.NilpotentBorelEqualsGroup` states
`AlgebraicGeometry.isIso_of_borel_of_nilpotent`, with its sole proof `sorry`.
The node is unchanged except for its `lean` record. No new notions or dependency
repairs are required: the central series is written explicitly in the hypothesis.

Read Milne, Algebraic Groups (2017), Section 17b, printed p.353, Proposition
17.23(b) implies (c), p.359, and Proposition 6.38, p.133. The source proves
G = B, precisely the conclusion here. Read the current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
and direct-images proof paragraph (3); this is the inherited algebraic-group
prerequisite in its alteration/GIT support chain, not a change to the unit.

Hypothesis and clause correspondence:

- The algebraically closed base field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- G and B are k-group schemes: `G B : Grp (Over (Spec (.of k)))`.
  The bundled `Grp` uses the recorded `CategoryTheory.GrpObj` definition, and
  its morphism `i : B ⟶ G` is a group-scheme homomorphism.
- G is affine, smooth, connected, and finite type: `[IsAffine G.X.left]`,
  `[Smooth G.X.hom]`, `[ConnectedSpace G.X.left]`,
  `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`.
- `hB : IsBorelGroupScheme i.hom.hom` includes that this very map is a closed
  subgroup embedding, B is smooth, connected and scheme-theoretically solvable,
  and the exact factorization maximality condition of the dependency node.
  These are not replaced by solvability of rational points.
- A nonnegative integer length is `∃ m : ℕ`. The m+1 group-scheme terms are
  `C : Fin (m + 1) → Grp (Over (Spec (.of k)))`; their maps into B are `c`.
  `∀ j, IsClosedSubgroupScheme (c j).hom.hom` makes all of them closed.
  Viewing the terms inside B or inside G is equivalent: B is closed in G,
  composites are closed, and a closed subscheme of G contained in B is closed
  in B. Thus this presentation does not add a hypothesis.
- `B = B_0` is `IsIso (c 0)`: the first specified inclusion fills B.
  `B_m = 1` is `Nonempty (C (Fin.last m) ≅ Grp.trivial _)`.
  Isomorphism to the trivial group determines its image in B to be the unit
  subgroup, so this is the stated endpoint, not an arbitrary trivial subgroup.
- Descending inclusions are `∀ j : Fin m, ∃ l : C j.succ ⟶ C j.castSucc,
  l ≫ c j.castSucc = c j.succ`. The compatibility identifies their images
  inside B. Such l are automatically closed subgroup embeddings, being the
  factorization of a closed embedding through a closed embedding; no extra
  hypotheses on l, or on smoothness of C_j, are added.
- Every index 0 ≤ j < m is covered by `j : Fin m`, with `j.castSucc` and
  `j.succ` the two consecutive indices. Every commutative k-algebra is
  `(A : Type u) [CommRing A] [Algebra k A]`. Its test object is explicitly
  `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))`.
- The universal binders `b` and `x` are exactly B(A) and C_j(A).
  `∃ z, z ≫ (c j.succ).hom.hom =
  b * (x ≫ (c j.castSucc).hom.hom) * b⁻¹ * (x ≫ (c j.castSucc).hom.hom)⁻¹`
  says that the commutator lies in the next subgroup, retaining all scheme
  structure. The Hom groups are Mathlib's actual group-object functors of points.
- The conclusion `IsIso i` says that the specified Borel inclusion itself is
  an isomorphism. Closed subgroup schemes are identified by their inclusions,
  so this is precisely B = G as closed subgroup schemes. It does not merely
  assert an unspecified abstract isomorphism of two group schemes.
- No characteristic or dimension hypothesis occurs. The field, schemes and
  test algebras share universe u as in the recorded subgroup-scheme API. This
  includes all test algebras of the small site, in particular coordinate rings
  that detect scheme-theoretic factorization. Larger test algebras also satisfy
  the same containment by pulling back the resulting morphism factorization;
  no independent smaller test-algebra universe makes this hypothesis vacuous.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraically
  closed clause of def-weil-algebraic-closure, rather than constructing a closure).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`,
  `Grp.trivial`, and the bundled homomorphisms.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme` and their
  homomorphism/closed-immersion fields. Imported publicly through Borel.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including nonemptiness.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.GroupScheme.Borel`:
  `AlgebraicGeometry.IsBorelGroupScheme`. Its complete definition and the
  underlying scheme-theoretic derived-series definitions in Semisimple were read.

Proof-only imports preserve all currently stated proof dependencies:
`BorelQuotientProperGeometry` (`homogeneousQuotient_geometry`),
`BorelHomomorphismRigidity` (`hom_ext_of_borel_baseChange`),
`AffineNormalQuotientGeometry` (`affine_normal_quotient_geometry`), and
`Mathlib.AlgebraicGeometry.Morphisms.Proper`
(`IsFinite.iff_isProper_and_isAffineHom`). The remaining proof dependency,
`lem-sfb-quotient-borel-torus-images`, has no Lean attachment on the read base,
so no unavailable module is imported. The theorem docstring records all five
proof steps and cites that node at the Borel-image step.

Edge cases checked before writing: m = 0 has a single term, simultaneously
isomorphic to B and to the trivial group, and `Fin 0` gives no spurious
commutator condition. For m = 1 the last containment is commutativity of B,
with no false positive-length requirement. Repeated terms are allowed.
The trivial ambient group is covered. Connectedness excludes an empty ambient
scheme. Positive characteristic and nonreduced intermediate groups (such as
mu_p) and nonreduced algebras are allowed; no rational-point-only equality,
reducedness, smoothness, or connectedness of the C_j is assumed. The zero
algebra is included as a commutative algebra; the empty test scheme has unique
points in the Hom groups and satisfies the containment.

Searches performed:

- `msearch.py ... leanfinder`: "A nilpotent Borel subgroup of a connected smooth
  affine algebraic group equals the whole group" returned eight abstract-group
  or Lie-algebra results, including `Group.isNilpotent_top` and
  `LieAlgebra.top_isCartanSubalgebra_of_nilpotent`; none is this theorem.
- `msearch.py ... loogle '"Borel", "IsNilpotent"'`: zero hits.
- `msearch.py ... grep 'Borel|nilpotent|Nilpotent' AlgebraicGeometry`: 13 hits,
  all concerning nilpotent sections or imports; no algebraic Borel theorem.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf`, by Borel, nilpotence and
  central-series names, found the existing Borel definition and
  `central_maximal_torus_nilpotent`. The latter constructs a central series
  from a central maximal torus; it does not say a nilpotent Borel equals G.
  Its finite-series presentation was read to check consistency with this one.
- Search for the exact node id in `lean/WeilConjectures` found no declaration.
  Search of `dag/lean_names_upstream.json` for the relevant Borel/nilpotent
  names found no exact statement. No private copy of a definition is introduced.

Validation: `scompile.py Q35 lem-sfb-nilpotent-borel-equals-group <module>`
compiled both sandbox and library forms cleanly, with no errors or additional
warnings (3.7 s and 3.6 s). `set_option autoImplicit false` rejects unbound
variables. All lines are at most 100 characters. No statement dispute or
statement correction is necessary.

## Second reading by Q35

I reread the node and the completed module in this worker session; the
maintainer's independent review remains separate. No second agent was started,
as required by the dispatcher brief.

The base-field, G-geometry and Borel hypotheses agree clause by clause as
listed above. In particular Borel contributes the closed subgroup and the full
scheme-theoretic solvability/maximality clauses, so neither is missing despite
not being a separate binder. The bundled Grp morphisms preserve multiplication.
The finite indexing includes both endpoints even at m = 0. The first endpoint
uses the actual c_0, not merely an arbitrary isomorphism with B. The last endpoint
is the trivial group, whose inclusion into B is uniquely the identity section.
The consecutive factorization equations force a descending chain in that same
B. The commutator is ordered b x b⁻¹ x⁻¹, with x mapped into B before multiplying,
and its lift is in C_(j+1), not merely in B. All commutative test algebras are
quantified over; there is no substitution of only k-points. Finally `IsIso i`
asserts fullness of the given closed inclusion, precisely the intended equality.
No mismatch was found and no mathematical changes were made on this rereading.
