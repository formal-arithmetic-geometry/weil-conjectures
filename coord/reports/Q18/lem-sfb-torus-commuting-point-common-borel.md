## Worker report

States `AlgebraicGeometry.exists_borelGroupScheme_torus_commuting_point` in
`Sheaf.AlgebraicGeometry.GroupScheme.TorusCommutingPointCommonBorel`, with the single
proof `by sorry`. No definitions or subsidiary theorems are introduced. The accepted
stage-1 statement, proof and proof dependencies are unchanged. The statement dependencies
only gain the two already-landed definition nodes `def-sfb-borel-subgroup-scheme` and
`def-sfb-tori-multiplicative-type`, whose declarations are used directly.

The previous BLOCKED ending was a stage-1 handoff error. The current standing brief §0
explicitly permits stating a reviewed split in stage 2. The live item has reviewed PASS
by Q43, no Lean record, a stage-2 queue entry, and no released repair note. There is no
attempt to re-split it.

Source read: the local Milne Algebraic Groups (2017) PDF, Lemma 17.37 and its entire proof,
printed p.363, and Definition 17.6, p.353, with the section's algebraically closed-field
and connected group-variety convention. The claim here is the common-Borel conclusion
actually proved there. As in the accepted node, the erroneous parenthetical assertion
that only finitely many Borels contain an arbitrary torus is not asserted. The eight-step
proof docstring reproduces the accepted quotient, fpqc lifting, proper fixed locus,
restricted torus action, fixed point, and conjugation argument and names its DAG inputs.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- k-group schemes G and T, with their operations: `G T : Grp (Over (Spec (.of k)))`.
  This is the bundled form of the dependency's `CategoryTheory.GrpObj`; a bundled
  morphism is a homomorphism, with underlying over-scheme morphism `i.hom.hom`.
- Affine finite-type ambient group: `[IsAffine G.X.left]`,
  `[LocallyOfFiniteType G.X.hom]`, and `[QuasiCompact G.X.hom]`. Finite type is the
  recorded conjunction, not an algebraically finite field-extension assumption.
- Smooth connected ambient group: `[Smooth G.X.hom] [ConnectedSpace G.X.left]`.
- Closed torus inclusion: `(i : T ⟶ G) (hi : IsClosedSubgroupScheme i.hom.hom)`.
- The node defines a torus over this algebraically closed field as an actual k-isomorphism
  to G_m^r: `hT : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k r)`.
  This deliberately uses the existing split-torus construction, without replacing the
  node's k-isomorphism by a scalar-extension hypothesis. `splitTorus` is built recursively
  from the recorded `StandardGroupSchemes.multiplicative k`; its rank-zero case is the
  tensor unit, i.e. the trivial group. Closed subgroups of the affine finite-type G are
  affine finite type, so those properties of T and the output B need no extra assumptions.
- Rational point: `c : 𝟙_ (Over (Spec (.of k))) ⟶ G.X`. The tensor unit of this cartesian
  over-category is Spec k with its identity structure map, so this is G(k).
- Commutation after every commutative k-algebra extension: `hc` quantifies over
  `(A : Type u) [CommRing A] [Algebra k A]` and every
  `t : StandardGroupSchemes.affine k A ⟶ T.X`. The expression
  `toUnit (StandardGroupSchemes.affine k A) ≫ c` is c_A; `t ≫ i.hom.hom` is t in G(A).
  `Commute` asserts precisely c_A t = t c_A. Test algebras are in the SAME universe as k,
  so this is the dependency's non-vacuous scheme-points convention, with no reducedness,
  domain, nontriviality, or characteristic restriction on A.
- Existence of a Borel B: the conclusion supplies `B : Grp (Over (Spec (.of k)))`,
  `j : B ⟶ G` and `IsBorelGroupScheme j.hom.hom`. Reading that definition gives closedness,
  smoothness, connectedness, termination of the scheme-theoretic derived series, and
  maximality among closed smooth connected solvable subgroups. Its imported solvability
  predicate is `IsSolvableGroupScheme`, not solvability just on rational points.
- Containment T ⊆ B as subgroup schemes: `∃ f : T ⟶ B, f ≫ j = i`. A group-scheme morphism
  factoring the closed inclusion gives the specified subgroup containment; it is not
  merely containment of k-points.
- Membership c ∈ B(k): `∃ b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X, b ≫ j.hom.hom = c`.
- No maximality of T is imposed, and no extra assertion about the number of Borels occurs.

Dependency declarations read and reused:

- `Field` in `Mathlib.Algebra.Field.Defs`; `IsAlgClosed` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic` (the algebraic-closure dependency explicitly
  records this component of its terminology).
- `CategoryTheory.GrpObj`, `CategoryTheory.Grp` and bundled homomorphisms in
  `Mathlib.CategoryTheory.Monoidal.Grp`; group-valued Hom instances are used through
  `open scoped MonObj`. These are the recorded group-scheme interface, not a private copy.
- `AlgebraicGeometry.IsClosedSubgroupScheme`, including its `IsSubgroupScheme` and
  `IsMonHom` parents, in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `AlgebraicGeometry.LocallyOfFiniteType`, `QuasiCompact`, and `Smooth` in the recorded
  Mathlib morphism modules, and `ConnectedSpace` in `Mathlib.Topology.Connected.Basic`.
- `AlgebraicGeometry.StandardGroupSchemes.affine`, `multiplicative` and its group instance
  in `Sheaf.AlgebraicGeometry.StandardGroupSchemes`.
- `AlgebraicGeometry.MultiplicativeType.splitTorus` in
  `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`, via the added dependency node.
- `AlgebraicGeometry.IsBorelGroupScheme` in `Sheaf.AlgebraicGeometry.GroupScheme.Borel`,
  including `IsSolvableGroupScheme`, `GroupSchemeDerivedLength`, `IsDerivedGroupScheme`
  and `groupSchemeCommutator` in its public import `GroupScheme.Semisimple`, via the added
  Borel definition node. Their full bodies and docstrings were read.

The public imports expose statement notions. Plain imports retain available proof inputs:
`MultiplicativeTypeLargestSubtorus`, the Mathlib proper/closed-immersion, Noetherian,
quasi-separatedness, flatness, surjectivity/pullback, and fpqc-covering modules. The proof
nodes borel-conjugation-cover, homogeneous-orbit-quotient-geometry,
borel-quotient-proper-geometry and solvable-proper-fixed-point currently have no recorded
Lean declaration, so their names remain in the proof docstring rather than inventing
imports or new statements for proof-only prerequisites.

Edge cases checked mathematically before writing: rank zero gives T = 1 and arbitrary c,
so the statement specializes to existence of a Borel containing any rational point;
G = 1 gives B = 1; for a smooth connected solvable G one can take B = G; a central scalar
torus in GL₂ permits every c and places no hidden maximal-torus assumption; in positive
characteristic the same conclusion holds, and nonreduced test algebras are retained. The
zero algebra is permitted and has its usual unique empty-spectrum point; the commutation
condition is then automatic only at that test algebra. An empty ambient scheme is already
excluded by its group identity and by `ConnectedSpace`. T = 1 in GL₂ also checks why no
finite-union-of-Borels assertion was accidentally retained.

Searches actually run:

- `msearch.py`, LeanFinder: “A torus and a commuting rational point in a smooth connected
  affine algebraic group lie in a common Borel subgroup”: 8 hits, including modular-form
  strict periods, number-field unit systems and nonarchimedean topological groups; none
  states the algebraic group-scheme claim. Returned types were read.
- `msearch.py`, Loogle: `"Borel", "Subgroup"`: 0 hits.
- `msearch.py`, grep: `BorelSubgroup|borelSubgroup|IsTorus|IsSolvable`, subdirectory
  `AlgebraicGeometry`: 0 hits.
- `msearch.py`, LeanSearch: “A torus and a commuting element of a smooth connected
  algebraic group lie in a common Borel subgroup”: 8 hits, including Iwasawa structures,
  additive topological tori, measurable Borel quotients, and smooth algebra descent;
  no exact result. Returned signatures were read.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for Borel, IsTorus, solvability,
  torus commuting and commonBorel names, and the exact node id: no existing theorem.
  This found the existing Borel and split-torus definition modules, which are reused.
- DAG searches for Borel subgroups, scheme-theoretic commutators and split tori located
  the already-landed two definition nodes now added to `stmt_deps`; no new node is needed.

No statement correction, disputed statement, dependency repair, hollow definition or
additional axiom is introduced. The sole postponed proof is the theorem of this item.
Compilation uses only `scompile.py`; the initial module compiled cleanly in both sandbox
and library mode. Required final wrapper validation is recorded below after completion.

Final validation: `scompile.py` compiled the final source in sandbox mode (16.8 s)
and library mode (2.7 s), with no errors or warnings. `deliver2.py --no-push` reported
`OK (dry run)` for commit `44d3632238a`: server preflight and per-file compile passed.
The local record comparison confirms that only `lean` and the two added `stmt_deps`
differ, and the recorded signature is byte-for-byte identical to the Lean source.

## Second reading by Q18

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
