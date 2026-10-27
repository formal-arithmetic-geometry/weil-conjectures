## Worker report

Item: `lem-sfb-torus-centralizer-smooth-connected`; group Q142; 2026-10-24 UTC.

The module `Sheaf.AlgebraicGeometry.GroupScheme.TorusCentralizerSmoothConnected`
states `AlgebraicGeometry.exists_torus_centralizer_smooth_connected`, with exactly
one postponed theorem proof (`sorry`) and no new definitions. The theorem docstring
contains all seven steps of the accepted DAG proof, with their dependencies and sources.
Source checked directly in `literature/milne-algebraic-groups_iAG2017.pdf` using
`pdftotext -layout`: Proposition 1.92 and its field-base-change paragraph,
Corollary 13.10, and Theorem 17.38. The latter assumes an arbitrary torus in a
connected group variety, with no reductivity or maximality hypothesis.

Hypotheses and clauses, in statement order:

| Node text | Lean rendering |
| --- | --- |
| A field k | `{k : Type u} [Field k]` |
| Group schemes G and T over k | `(G T : Grp (Over (Spec (.of k))))`; this bundles the recorded `CategoryTheory.GrpObj` structure and its group laws |
| All groups affine | `[IsAffine G.X.left]`, `[IsAffine T.X.left]`; `IsAffine C.X.left` in the conclusion |
| All groups of finite type | `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`, and the corresponding T hypotheses; `LocallyOfFiniteType C.X.hom ∧ QuasiCompact C.X.hom` in the conclusion |
| All subgroup schemes closed; T is a subgroup of G | `(i : T ⟶ G) (hi : IsClosedSubgroupScheme i.hom.hom)`; the morphism is a group homomorphism, and the predicate gives its closed immersion and injectivity on algebra points |
| G smooth | `[Smooth G.X.hom]` |
| G geometrically connected, meaning connected over the algebraic closure | `[ConnectedSpace ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj G).X.left]` |
| T is a torus, split over the algebraic closure with rank r ≥ 0 | `(hT : MultiplicativeType.IsTorus T)`; the existing definition is existence of `n : ℕ` and a group-scheme isomorphism after algebraic-closure base change to `splitTorus (AlgebraicClosure k) n` |
| The centralizer is represented by a subgroup scheme C of G | `∃ (C : Grp (Over (Spec (.of k)))) (j : C ⟶ G), ...`; for each test algebra, its image of points equals the prescribed centralizer |
| C is closed | `IsClosedSubgroupScheme j.hom.hom` |
| C is smooth | `Smooth C.X.hom` |
| C is geometrically connected | `ConnectedSpace ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj C).X.left` |
| Centralizer on every commutative k-algebra A | `∀ (A : Type u) [CommRing A] [Algebra k A], ReductiveTorusCentralizer.centralizerPoints i A = Set.range (fun c : StandardGroupSchemes.affine k A ⟶ C.X ↦ c ≫ j.hom.hom)` |
| Commutation after every A-algebra extension A' and with every point of T(A') | The reused `centralizerPoints i A` unfolds to `∀ (B : Type u) [CommRing B] [Algebra k B] (f : A →ₐ[k] B) (t : StandardGroupSchemes.affine k B ⟶ T.X), Commute (StandardGroupSchemes.map k f ≫ g) (t ≫ i.hom.hom)` |
| No reductivity or maximality is assumed | Neither predicate occurs among the hypotheses; importing the shared terminology module imposes neither hypothesis |

The equality of ranges represents the functor, not just its field-valued points.
Closed subgroup inclusion makes each map C(A) → G(A) injective. Equality of its
range with the specified subset therefore identifies C(A) with that subset;
these identifications are natural because they are induced by the single scheme
morphism j, and the commuting condition is stable under algebra extension.
An A-algebra extension is equivalently a k-algebra B together with a k-algebra
map A → B, the encoding used in the existing centralizer definition.

All variables and the universe `u` are explicit (`set_option autoImplicit false`).
The test algebras live in the same universe as k and the schemes, so this does
not introduce an independent smaller universe or a vacuous test class. The
algebraic closure, coordinate algebras, tensor products, and universal points
used to characterize the affine subfunctor fit in this universe. Universes may
be enlarged to state the same assertion for any chosen set of test algebras.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`,
  `CategoryTheory.Grp`, the existing bundled group-object interface.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme`;
  the latter includes the former and `IsClosedImmersion` of the underlying map.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`, the recorded
  finite-type conjunction.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`,
  the recorded affine-local smooth-ring-map definition (also agreeing with
  the dependency's current blueprint update).
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including nonemptiness.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `StandardGroupSchemes.affine`, `.map`, `.multiplicative`, and its group law.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `MultiplicativeType.baseChange`, `.splitTorus`, `.IsTorus`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.centralizerPoints`.

The last two are existing landed definition nodes, now added to `stmt_deps`
under brief-stage2 §5 (statement dependencies may gain landed nodes). They
supply exactly the notions already described in the item's unchanged statement.
There are no new nodes, dependency repairs, or statement corrections.

Proof-only imports cover the recorded modules of all already-stated proof
dependencies: affine tensor-product spectra (`Mathlib.AlgebraicGeometry.Pullbacks`),
closed immersions, proper morphisms, affine spectra, pullbacks, the constant-source
closed-factorization locus, torus fixed-scheme smoothness, the common-Borel theorem,
the regular semisimple torus-point theorem, and the upstream Nullstellensatz module
`WeilConjectures.Mathlib.RingTheory.Nullstellensatz`. The finite-type and connectedness
modules are already public imports. The DAG proof dependency
`lem-sfb-solvable-semisimple-centralizer-connected` has no recorded Lean declaration
or mathlib match in the read clone, so there is no stated module to import for it.
It is a proof prerequisite, not a missing notion needed to state this item.

Edge cases checked before writing:

- Rank zero is allowed: `splitTorus k 0` is the trivial group. Its centralizer
  is G, which has all the assumed properties; no positive-rank hypothesis appears.
- G and C have identity sections and are nonempty; `ConnectedSpace` retains
  nonemptiness rather than silently using preconnectedness of the empty scheme.
- Arbitrary characteristic and imperfect fields are allowed; no characteristic,
  perfection, or algebraic closedness restriction is added to k.
- A may be the zero ring or a nonreduced algebra; both A and extension B are
  unrestricted commutative k-algebras. No test is reduced to geometric points.
- Nonsplit tori are allowed because only the algebraic-closure scalar extension
  must split. No splitting over k is assumed.
- Nonreductive G and nonmaximal T remain included. For example, the trivial
  torus in an additive group is permitted by the hypotheses.

Searches (the prescribed msearch wrapper was run with Q142 and this item):

- LeanFinder: `The centralizer of a torus in a smooth geometrically connected affine group scheme is smooth and geometrically connected`.
  Eight hits, including `ConjAct.fixedPoints_eq_center`, abstract-group
  commutator/centralizer lemmas and Lie-algebra lemmas; no group-scheme result.
- LeanSearch: `The centralizer of a torus in a smooth connected algebraic group is smooth and connected`.
  Eight hits: abstract `Subgroup.centralizer`, its additive versions and
  normality lemmas, plus `Set.isClosed_centralizer`; no matching theorem.
- Loogle: `"centralizer", "Smooth"`. Zero hits.
- Mathlib grep: `centralizer|Centralizer`, subdirectory `AlgebraicGeometry`.
  Zero hits.
- Project ripgrep: `centralizerPoints|IsTorus|GeometricallyConnected|torus.*centralizer`
  in `lean/Sheaf/AlgebraicGeometry` and `lean/WeilConjectures/AlgebraicGeometry`;
  followed by narrower centralizer searches. Found the exact shared definitions
  listed above and downstream uses, but no existing statement of this item.
- Upstream exact-id search for `lem-sfb-torus-centralizer-smooth-connected`
  in `lean/WeilConjectures` found no declaration.
- Read the existing definition nodes
  `def-sfb-tori-multiplicative-type` and
  `def-sfb-reductive-torus-centralizer-terminology`, including their source
  modules and full signatures/docstrings, before adding their statement edges.

Validation: `scompile.py Q142 lem-sfb-torus-centralizer-smooth-connected <module>`
compiled both the sandbox form and the actual library module cleanly (2.0 s and
1.9 s). No diagnostic commands remain; there are no overlong Lean lines.
No node faults or disputed mathematical claims were found.

## Second reading by Q142

Self-review only; the dispatcher prohibits spawning agents, and the maintainer
performs the independent review. Re-read the node statement and full Lean signature:
every field, affineness, finite-type, subgroup, smoothness, connectedness and
point-functor clause has the correspondence above. In particular geometric
connectedness is tested over the recorded algebraic closure on both sides,
and the centralizer definition quantifies over all extensions B of A.
The module defines no replacement of an existing notion and introduces neither
reductivity nor maximality. The two existing definition edges are the only
change outside the item's `lean` record. No mismatch was found in this rereading.
