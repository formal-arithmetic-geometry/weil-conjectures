## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SemisimpleRootsSpan` states
`AlgebraicGeometry.semisimple_iff_roots_span`, with one `sorry` and no new definitions.
The node is unchanged except for its `lean` record. No statement correction or
new/dependency node is needed.

Clause-by-clause correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The reductive F-group is `H : Grp (Over (Spec (.of F)))` with
  `hH : ReductiveTorusCentralizer.IsReductive H`. This is the exact reductive
  convention used by the recorded Borel-pair dependency. Its geometric formulation
  agrees with the stated formulation over an algebraically closed field.
- The fixed split maximal torus is `T`, its inclusion `iT`, `hT`, and `hsplit`.
- The actual character lattice is
  `Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))`;
  the cocharacter lattice is the reversed Hom group. The commutativity witnesses
  and both `Module.Finite ℤ` instances expose the lattice structures supplied by
  the recorded Borel-pair result, rather than restrict its scope.
- `Φ` is the finite set of characters; `P : RootDatum Φ ... ...`, `hred`,
  and `hroot` expose the dependency's reduced integral root datum. `aH` and
  `hconj` pin its torus action to conjugation. `hweights` says that Φ is exactly
  the nonzero character weights on the tangent space of H. `hpair` pins the
  perfect integer pairing to composition with the integer power map.
  Thus none of these binders is an extra arbitrary structure hypothesis.
- Semisimplicity is the existing `IsSemisimpleGroupScheme H.X`. Its definition
  includes smoothness, connectedness, affineness, finite type, and triviality of
  every smooth connected solvable normal closed subgroup. Its existing
  `IsSolvableGroupScheme` uses termination of the scheme-theoretic commutator
  series, exactly the node's convention, including nonreduced subgroup schemes.
- The first conjunct is precisely the equivalence with
  `Submodule.span ℚ (Set.range (fun α : Φ ↦ 1 ⊗ₜ[ℤ] P.root α)) = ⊤`.
- The second conjunct applies under the equivalent semisimple condition and
  supplies `Q : RootPairing Φ ℚ (ℚ ⊗[ℤ] X) (ℚ ⊗[ℤ] X_*)`.
  Its first two clauses fix roots and coroots to the canonical lattice images;
  its third fixes its pairing on every pair of integral lattice tensors to the
  rational cast of the given integer pairing. Bilinearity uniquely determines
  that extension on the whole tensor products. The root embeddings and pairing
  also determine the reflection permutations through their formulas and
  injectivity. Hence this is the specified rational extension, not an unrelated
  root system. Mathlib's BaseChange file explicitly lists extension of scalars
  as TODO, so no existing scalar-extension constructor is bypassed here.
- `Q.IsRootSystem` includes BOTH root spanning and coroot spanning of these exact
  tensor spaces. `Q.IsReduced` and `Q.IsCrystallographic` give the remaining
  properties. Finiteness is carried by the same finite indexing type Φ;
  `RootPairing` carries the perfect pairing, injective roots/coroots, normalization
  2 and simultaneous reflection permutations. Thus the entire root-system clause
  and the particular coroot-span clause are included.

The rational factor is written first, as in the landed sibling
`SimplyConnectedCharacterLattice`, using canonical tensor symmetry. No Borel is
introduced since this node only fixes a maximal torus, and no positive roots occur.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; and
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraic-closure
  dependency explicitly records this component notion).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, specialized to
  `Over (Spec (.of F))`. The project group-scheme definitions module is exposed
  by the recorded Borel-pair import.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `reductive_borel_pair_structure` and its actual Hom-lattice/root interfaces.
  Its transitive public modules supply `ReductiveTorusCentralizer.IsReductive`,
  `IsMaximalTorus`, `TorusCharacterTangent.weightSpace`,
  `StandardGroupSchemes.multiplicative`, `MultiplicativeType.splitTorus`, and
  `IsSemisimpleGroupScheme` (in `GroupScheme.Semisimple`). Their definitions
  and docstrings were read, including the derived-series definition.
- `Mathlib.LinearAlgebra.RootSystem.Defs`, `.Reduced`, `.IsValuedIn`:
  `RootDatum`, `RootPairing`, `IsRootSystem`, `IsReduced`, `IsCrystallographic`.
- Proof imports: `Mathlib.GroupTheory.FiniteAbelian.Basic` for the recorded
  `AddCommGroup.equiv_free_prod_directSum_zmod`, and
  `Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate` for the recorded
  `RootPairing.rootSpan_eq_top_iff`. The Borel-pair result is already public.
  The centre-root-quotient, diagonalizable-group-geometric-criteria and
  reductive-radical-quotient proof nodes have no Lean records or Mathlib matches
  in the read repository, so no module is available to import for them.
  Their mathematical steps are fully retained in the theorem docstring.

Edge cases checked before writing: H = 1 has zero character and cocharacter
spaces and empty Φ, so the empty finite root system is allowed. A positive-rank
split torus has empty Φ but nonzero character space, making both sides of the
semisimplicity equivalence false; no spanning assumption is imposed in the
binders. Products with a central torus behave likewise. Positive characteristic,
including SL₂ in characteristic 2 with nonreduced centre, is allowed: no assumption
on characteristic or reducedness of centres is present, the coefficient space
is rational, and weights are characters rather than their differentials. No
Nonempty assumption excludes rank zero. All universes and variables are explicit.

Searches made (through the required msearch wrapper and direct source search):

- LeanFinder: `A reductive algebraic group is semisimple exactly when its roots
  span the rational character lattice`. Eight hits concern Lie-algebra
  semisimplicity, not this algebraic-group theorem.
- LeanSearch: `The roots of a semisimple algebraic group span the rational
  character space of its maximal torus`. Eight hits include
  `RootPairing.IsRootSystem.span_root_eq_top`, `rootSpan_eq_top_iff` and abstract
  root-span facts; none relates the root datum to group-scheme semisimplicity.
- Loogle: `"RootPairing", "rootSpan"`. Twelve hits give root/coroot span
  definitions and facts, not the group criterion.
- msearch grep `semisimple|Semisimple|rootDatum` in Mathlib AlgebraicGeometry:
  zero hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for semisimple/span/root and
  the item id found only sibling proof-plan references and different Lie-algebra
  results, not an existing theorem. Searching the proposed declaration name
  and upstream declaration index found no collision.
- Read Mathlib `RootSystem/BaseChange.lean`: it supports restriction of scalars
  but explicitly leaves extension of scalars as TODO. The existential, fully
  characterized rational pairing avoids needing a duplicate construction.

Source checked directly in `literature/milne-algebraic-groups_iAG2017.pdf`
using pdftotext: Proposition 21.48, C.34--C.35 and 22.9 agree with the node.
No STATEMENT-DISPUTED issue was found.

Server validation: prescribed scompile.py compiled the sandbox and module-mode
library file cleanly (2.8 s and 2.6 s); only the intended theorem is postponed.

## Second reading by Q22

A separate review pass reopened the full node and final module. This is a
self-review: the dispatcher forbids starting other agents, and the maintainer's
independent review follows delivery.

Checked the field and reductive hypotheses against the node and the exact
Borel-pair dependency signature. Checked each torus, Hom-lattice, conjugation,
root-set, and pairing binder against the corresponding data from that signature.
No Borel/base choice is required in this statement. Checked that semisimplicity
uses the existing scheme-theoretic commutator-series predicate, not pointwise
abstract-group solvability or a Lie-algebra predicate.

Checked the first conjunct is an iff, not only semisimple-implies-spanning.
Checked the second conjunct is conditional on that same semisimplicity and uses
the full ambient rationalizations, not root spans. The equalities fixing the
rational roots, coroots and pairing prevent an arbitrary witness. Expanded the
Mathlib class signatures: `IsRootSystem` contains the coroot-spanning clause,
`IsReduced` gives reducedness, and `IsCrystallographic` means integer-valued
root-coroot pairings. Empty Φ remains permitted. No mismatch or correction
was found on this pass; no definitions, new nodes or dependencies were added.
