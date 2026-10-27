## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.NilpotentCentralTorusQuotient` states
`AlgebraicGeometry.nilpotent_central_torus_quotient`. Its sole theorem has proof `sorry`;
there are no definitions or auxiliary postponed theorems. The natural-language statement,
proof and proof dependencies are unchanged. Two already landed definition nodes were
added to `stmt_deps`: `def-sfb-tori-multiplicative-type` and
`def-sfb-fppf-group-quotient-presentation`, because the statement uses their exact notions.
No new node, dependency repair, or statement correction is required.

Sources read: Milne, Algebraic Groups (2017), Theorem 16.47(a),(c), printed p.341,
and the surrounding Lemmas 16.45--16.46; Theorem 14.5(a),(b) and Corollaries 14.6--14.9,
pp.281--282; Propositions 5.25--5.29 and the trivial-kernel quotient criterion 5.33,
pp.105--106. The current blueprint directory is `literature/blueprint/latest`, pointing
to main-20261024, commit ef6f9619fdbffa59e88528fb56483d76c70258c8. This item is an
auxiliary Milne statement, not a blueprint unit statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The arbitrary field is `(k : Type u) [Field k]`. There is no perfectness, characteristic,
  separability or algebraic-closedness hypothesis. The fixed closure is Mathlib's
  `AlgebraicClosure k`, used inside the existing torus predicate; it is not an extra
  assumption or a restriction to groups already split over k.
- A k-group scheme is `G : Grp (Over (Spec (.of k)))`. This bundles exactly the recorded
  `GrpObj` structure, and morphisms in `Grp` are group-scheme homomorphisms.
- Affine finite type is `[IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [QuasiCompact G.X.hom]`. Output T and Q have the same three properties explicitly.
  Terms of the input series are closed subgroups of the affine finite-type G, hence
  automatically affine finite type; the input does not require smooth intermediate terms.
- Smoothness and connectedness are `[Smooth G.X.hom] [ConnectedSpace G.X.left]`.
  The same properties of Q are explicit conjuncts. ConnectedSpace includes nonemptiness.
- Nilpotence is the binder `hseries`. It provides a length `s : ℕ`, group schemes
  `H : Fin (s + 1) → Grp ...`, and inclusions `i j : H j ⟶ G`.
  `IsClosedSubgroupScheme` and `IsNormalSubgroupScheme` for every `i j` mean closed normal
  subgroup schemes of the ambient G. `IsIso (i 0)` says the initial subgroup is all of G,
  with its actual inclusion. `Nonempty (H (Fin.last s) ≅ Grp.trivial _)` is the terminal
  trivial subgroup. The morphisms `l` with `l ≫ i j.castSucc = i j.succ` express descent
  of the series. For every j, every commutative k-algebra A, and every g and h in G(A)
  and H_j(A), the displayed witness z in H_(j+1)(A) maps to `g*h*g⁻¹*h⁻¹` in G(A).
  These are the exact commutator containments, including nonreduced test algebras.
- The conclusion's existential variables `T Q iT q` give the torus subgroup, quotient
  group, specified inclusion and specified quotient homomorphism.
  `IsClosedSubgroupScheme iT.hom.hom` makes the inclusion closed.
- `MultiplicativeType.IsTorus T` means the actual base change of T to AlgebraicClosure k
  is isomorphic as a group scheme to the recorded finite product of G_m. Its rank is
  an arbitrary natural number, including zero.
- Centrality is `Commute (t ≫ iT.hom.hom) g`, universally over every commutative
  k-algebra A and every pair of points t and g. This is scheme-theoretic centrality,
  rather than centrality only on k-points or geometric field points.
- Unipotence of Q is the explicit existential `n`, `0 < n`, and homomorphism
  `r : Q.X ⟶ GeneralLinearGroup (ULift (Fin n)) k`, with
  `IsClosedSubgroupScheme r`. For every commutative k-algebra A, all matrices of its
  image have each diagonal entry 1 and every below-diagonal entry 0. A closed immersion
  into GL_n satisfying these equations on all algebras is exactly a closed immersion
  into its closed unitriangular subgroup U_n. This formulation uses the existing GL_n
  and its natural `homMulEquiv`; it neither defines a second U_n nor substitutes
  geometric unipotence. ULift changes only the index universe, not the n matrix indices.
- Faithfully flat q is `Flat q.hom.hom.left ∧ Surjective q.hom.hom.left`, the usual
  scheme-theoretic meaning. `IsFppfGroupQuotient iT q` supplies the actual cartesian
  kernel square with the unit of Q, the torsor comparison with its prescribed two
  projections, local surjectivity for the fppf topology, and the sheafification universal
  property of the coset coequalizer. Its restriction to affine tests is precisely
  A ↦ G(A)/T(A), with faithfully flat finitely presented coverings. Thus this includes
  the scheme-theoretic kernel and represented quotient clauses, not just pointwise exactness.
- `Nonempty (T ≅ Grp.trivial _) → IsIso q` is the final T=1 clause; the isomorphism
  is asserted for the same quotient morphism q, not for some unrelated map.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj` and `Grp`, used through the bundled
  objects and homomorphisms.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsClosedSubgroupScheme` and `IsNormalSubgroupScheme`, with their full signatures
  and pointwise subgroup definitions read in the upstream source. Their superclass
  supplies `IsSubgroupScheme` and the group-homomorphism condition.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `QuasiCompact`:
  `LocallyOfFiniteType` and `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine`, `multiplicative`, and
  `multiplicativeGroup`; the latter two are used by the existing split torus construction.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `IsTorus`, `baseChange`, and
  `splitTorus`, read in full. The empty product is the trivial group.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes` is the recorded general-linear node's
  module; it publicly imports the upstream GL_n. The directly used declarations are
  `AlgebraicGeometry.GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv` from
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`, contained
  in `IsClosedSubgroupScheme`; no private copy of a closed-immersion notion is introduced.
- `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`:
  `IsFppfGroupQuotient`, the already registered declaration of
  `def-sfb-fppf-group-quotient-presentation`. Its full definition was read, including
  the sheafification universal property.

Already stated proof dependencies are imported privately: affine group centre,
affine normal quotient geometry (public because its predicate is also in the statement),
base-change stability from Proper and Smooth, the connected-rational-point criterion,
and the largest-subtorus theorem. The remaining eight proof-dependency nodes have no
recorded Lean declaration; they are named in the proof docstring and no import is fabricated.
All seven proof steps are reproduced in the theorem docstring, including the explicit
inverse calculation over the algebraic closure and the trivial-kernel final argument.

Edge cases checked before writing: for G=1, a length-zero series is allowed and the
output has T=Q=1, with the unitriangular size n=1. For a torus, choose T=G and Q=1;
rank-zero tori are included. For smooth connected unipotent G, choose T=1 and q=id.
The group G_m×G_a has the expected torus and additive quotient. No characteristic is
excluded. Over imperfect fields the quotient is not required to split, and G is not
asserted to be a direct product. Nonsmooth or disconnected intermediate central-series
terms are permitted. Testing on all commutative algebras retains infinitesimal group
structure and the zero algebra. No theorem or definition is disputed.

Searches actually run with `msearch.py Q152 lem-sfb-nilpotent-central-torus-quotient`:

- leanfinder: “A smooth connected nilpotent affine algebraic group has a central torus
  with unipotent fppf quotient”. Eight hits, headed by `nilpotent_center_quotient_ind`
  and `of_quotient_center_nilpotent`; all are abstract group or Lie-algebra results,
  not this algebraic-group statement.
- loogle: `"IsNilpotent", "Scheme"`. Three hits about nilpotent scheme sections;
  none concerns nilpotent group schemes.
- grep in Mathlib/AlgebraicGeometry: `IsNilpotent|Unitriangular|IsUnipotent`.
  Ten hits about nilpotent sections and ideals, not this statement.
- leansearch: “A smooth connected nilpotent affine algebraic group has a central torus
  with unipotent quotient”. Eight abstract-group or Lie-algebra nilpotence results;
  no matching group-scheme theorem.

Local rg searches of `lean/WeilConjectures` and `lean/Sheaf` used the item id,
`torus|Torus|Unipotent|unipotent|Nilpotent|nilpotent|fppfQuotient|FppfQuotient`,
and the more focused
`def (IsNilpotent|IsUnipotent|IsCentral)|[Nn]ilpotent.*: Prop|unitriangular|Unitriangular|central series`.
They found the existing torus and quotient definitions and the geometric matrix
unipotence predicate in SolvableGroupStructure. The latter is not silently used for
this node's unitriangular formulation. Existing nilpotence statements
NilpotentConnectedCentralSeries and CentralMaximalTorusNilpotent expand their central
series directly; this delivery follows that established representation. The unitriangular
conclusion follows the exact algebra-point formulation already used in
AdjointKernelCentralQuotientUnipotent and CharZeroCommutativeUnipotentVectorGroup.
The item id had no upstream declaration. DAG searches of definition nodes likewise
located the already landed torus and fppf quotient nodes cited above.

Validation: the prescribed scompile.py compiled the delivered file in sandbox mode and
its actual library module mode with no errors or warnings (1.7 s and 2.0 s respectively).
No diagnostic commands remain. All variables and universe u are explicitly bound,
autoImplicit is disabled, all Lean lines are at most 100 characters, and the sole
postponed proof is the named theorem for this DAG node.

## Second reading by Q152

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
