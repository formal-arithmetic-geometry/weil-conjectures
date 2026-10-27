## Worker report

States `AlgebraicGeometry.finite_commutative_group_scheme_order_annihilator` in
`Sheaf.AlgebraicGeometry.FiniteGroupSchemeOrderAnnihilator`. The sole theorem has
proof `sorry`; no definitions or additional postponed results are introduced.
The node's accepted statement, split, and dependencies are unchanged. Only its
`lean` record is set.

Source read: Milne, *Algebraic Groups* (2017), Proposition 11.32 and its proof,
printed p.221 (PDF page 233). It asserts that the order annihilates all
algebra-valued points and equivalently that the power morphism is trivial.
The DAG specializes to commutative group schemes, so the statement retains
that hypothesis. Also read the current blueprint's `def-sc-group-scheme`
in `literature/blueprint/latest/blueprint/sec-abelian-varieties/` and the
recorded group-scheme API documentation in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.

Every hypothesis and clause is represented as follows:

- The field is `{k : Type u} [Field k]` (`def-weil-field`).
- A group scheme over that field is `G : Over (Spec (.of k))` with `[GrpObj G]`.
  The base structure map is `G.hom`; the group operations and all diagrams are
  the existing group-object structure, not a new encoding.
- Commutativity is precisely `[IsCommMonObj G]`.
- Finiteness is `[IsFinite G.hom]`, the existing scheme-morphism predicate,
  and not a finite set of geometric or rational points.
- The order `n = dim_k Γ(G, O_G)` is `G.hom.finrankΓ`, whose definition uses
  `G.hom.ΓAlgebra` and `Module.finrank k Γ(G.left, ⊤)`. It is written out
  each time, avoiding an extra parameter or a statement-local let.
- `n ≥ 1` is the first conjunct `1 ≤ G.hom.finrankΓ`.
- The scheme morphism obtained by adding the identity `n` times is
  `(𝟙 G : G ⟶ G) ^ G.hom.finrankΓ`. The second conjunct equates this to
  `1`, which in the pointwise Hom group is the morphism through the identity
  section, hence the zero homomorphism in the node's additive convention.
  It is not the categorical identity `𝟙 G`.
- Every commutative k-algebra is quantified by
  `∀ (R : Type u) [CommRing R] [Algebra k R]`.
  Its points are exactly the morphisms
  `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ G`.
  The final conjunct says `x ^ G.hom.finrankΓ = 1` for every such `x`.
  The upstream API writes group laws multiplicatively, so this is exactly
  `n x = 0`. No finiteness assumption on `R` or on its group of points occurs.
- Both equivalent formulations are asserted. The morphism equality gives
  every pointwise equality by precomposition. Conversely, points over the
  coordinate algebra, including its universal point, recover equality of
  morphisms. Thus the conjunction does not strengthen the node's
  “equivalently” clause. This explanation is also in the proof docstring.
- No reducedness, etaleness, algebraic closedness, perfectness, characteristic,
  or invertibility hypothesis occurs. The one universe `u` is explicitly
  declared and shared by the base field, schemes, and test algebras, as in the
  existing group-scheme API; there is no independent smaller test universe.

Dependency declarations used, with their full signatures/docstrings read:

- `def-weil-field`: Mathlib `Field`, defined in `Mathlib.Algebra.Field.Defs`;
  it is a commutative ring and division ring with nontriviality.
- `def-sc-group-scheme`: its recorded `CategoryTheory.GrpObj` in
  `Mathlib.CategoryTheory.Monoidal.Grp`, together with the recorded
  `CategoryTheory.IsCommMonObj`, `CategoryTheory.Hom.group`,
  `AlgebraicGeometry.IsFinite`, and `AlgebraicGeometry.Scheme.Hom.finrankΓ`.
  Read `GrpObj` and `IsCommMonObj` in the Mathlib monoidal files,
  `Hom.group` and `Hom.monoid` in the Cartesian files, `IsFinite` in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, and `finrankΓ` and `ΓAlgebra`
  in `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`.
  The public import `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`
  supplies the existing interface and explicitly documents all these
  specializations, including the meaning of `𝟙 G ^ n`.

Proof dependencies already carrying declarations are imported without
`public`: `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`,
`Mathlib.LinearAlgebra.TensorProduct.Defs`,
`Mathlib.AlgebraicGeometry.Pullbacks`, `Mathlib.GroupTheory.OrderOfElement`,
`Mathlib.RingTheory.Nakayama`, and
`WeilConjectures.AlgebraicGeometry.GroupScheme.Finite`.
The finite-etale-algebra criterion's module is already the public statement
import. The local-constant product and faithful-regular-matrices prerequisites
have no Lean records in the read clone, so there is no module to import yet;
they are proof dependencies only and do not prevent this statement.
The declaration's docstring gives all seven accepted proof steps, naming their
DAG inputs, including the corrected matrix-power interpretation.

Edge cases checked before writing:

- The trivial group scheme has order one and both formulations assert that
  its identity is the trivial morphism, as required.
- The empty scheme cannot have a unit section over the nonempty spectrum of
  a field. Likewise a zero coordinate algebra cannot have a counit to the
  field. Thus order zero is correctly ruled out by the conclusion, not by an
  extra hypothesis.
- Characteristic zero, arbitrary positive characteristic, nonperfect base
  fields, and nonreduced finite schemes are included. For example alpha_p
  and mu_p in characteristic p are covered with order p; their rational
  point cardinality must not be used instead of the coordinate dimension.
- The zero test ring is allowed: `CommRing R` does not impose nontriviality.
  Its spectrum is empty and there is a unique point, satisfying the identity.
- Infinite and nonreduced test algebras are allowed. In particular the
  coordinate algebra is a permitted test algebra, validating the converse
  from points to the morphism equality.

Searches actually run through `msearch.py NJ` for this item:

- `leanfinder`: “The order of a finite commutative group scheme over a field
  annihilates all its points over every algebra”. Eight hits, including
  `card_nsmul_eq_zero`, `exists_zsmul_eq_zero`,
  `card_dvd_exponent_nsmul_rank'`, and finite-field/torsion results.
  None concerns scheme order or nonreduced group schemes.
- `loogle`: `AlgebraicGeometry.IsFinite, CategoryTheory.GrpObj`.
  Successful search, zero hits.
- `grep`: `finrank.*(npow|nsmul)|order.*annihilat|npow.*finrank`
  in `AlgebraicGeometry`. Successful search, zero hits.
- `leansearch`: “The rank of a finite commutative group scheme over a field
  annihilates every algebra-valued point”. Eight hits concerning abstract
  group ranks, fixed-field rank, simple-module rank, and
  `card_dvd_exponent_pow_rank`; none states this theorem.
- Local `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib checked
  `finrankΓ`, powers/annihilation/order patterns, and the proposed declaration
  name. The exact node-id search in `lean/WeilConjectures` found no match.
  The upstream-name index also has no proposed-name match. The existing
  `GroupScheme.Defs` supplies the notions, and `GroupScheme.Finite` supplies
  connected-order and etaleness results, but neither states this theorem.

Validation: `scompile.py NJ lem-sfb-finite-group-scheme-order-annihilator`
compiled the file successfully in sandbox mode (18.6 seconds) and its library
module mode (5.5 seconds), without errors or warnings. Every variable and
universe is explicitly bound. No statement fault or disputed assertion was
found. The inherited stage-1 unchanged-node failure does not apply to this
stage-2 delivery: the node now gains its Lean record.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
