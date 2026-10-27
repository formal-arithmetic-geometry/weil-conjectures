## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SplitSemisimpleGeometricRootComparison`
states `AlgebraicGeometry.splitSemisimple_geometric_root_comparison`, with proof `sorry`.
No definitions, new nodes, dependency replacements, or statement correction are needed.
The node's natural-language statement and proof remain unchanged. Seven landed terminology
nodes were added to stmt_deps to record the existing notions actually used.

### Hypotheses and objects

- The characteristic-zero field k is `{k : Type u} [Field k] [CharZero k]`.
  Its fixed algebraic closure is `{F : Type u} [Field F] [Algebra k F]
  [IsAlgClosed F] [IsAlgClosure k F]`. The explicit closedness instance supplies the
  already recorded geometric semisimplicity API. No particular algebraic closure is chosen.
- G and T are `Grp (Over (Spec (.of k)))`, the recorded group-scheme interface.
  `hGs`, `hGc`, `hGa`, `hGft`, and `hGqc` state smoothness, connectedness,
  affineness, local finite type and quasi-compactness. The last two jointly say finite type.
- `hGss` is the recorded `IsSemisimpleGroupScheme` on the actual scalar extension G_F.
  This says exactly that no nontrivial smooth connected solvable normal closed subgroup
  exists over F; solvability is termination of the scheme-theoretic commutator series.
  Its smoothness/connectedness/affineness/finite-type components follow already from the
  preceding assumptions and base change. They are an equivalent packaging, not an
  extra reductivity assumption. The geometric semisimplicity conclusion repeats this
  same meaning, as does the natural-language statement.
- `hsc` quantifies over every affine smooth connected finite-type group H over k
  whose extension to F is semisimple, and every surjective group homomorphism `f : H ⟶ G`.
  `IsFinite (GrpObj.ker f.hom.hom).hom` is the scheme-theoretic finite central kernel's
  finiteness (equivalently its coordinate algebra is finite dimensional). Centrality
  quantifies over every commutative k-algebra A, every kernel A-point x and H(A)-point g,
  requiring `(x ≫ kerι f) * g = g * (x ≫ kerι f)`. The conclusion `IsIso f` is precisely
  simple connectedness by central isogenies, without imposing kernel smoothness.
- `i : T ⟶ G`, `hi`, `hsplit` and `hmax` give the closed split torus of rank `r : ℕ`
  and its geometric maximality. The scalar extension is the recorded
  `MultiplicativeType.baseChange`; split tori use `MultiplicativeType.splitTorus`.
- Characters and cocharacters are `Additive (RankOneRoots.Character T)` and
  `Additive (RankOneRoots.Cocharacter T)`: actual group-scheme Hom groups, with
  their pointwise group laws written additively. The explicit `IsCommMonObj` instances
  expose commutativity of the torus and G_m, which follows from splitness and their
  group laws; no new arbitrary action or lattice is assumed.
- `aG` with `haG` pins the action to the actual restricted conjugation map
  `RankOneRoots.adjointMap i`. It is not an arbitrary representation hypothesis.
- `Φ` indexes exactly the nonzero adjoint character weights by `hweights`.
  `P : RootDatum Φ X Y` is on those actual Hom groups; `hroot` pins its root embedding
  to the included character and `hpair` pins the perfect integer pairing to composition
  with integer power maps. This is an interface for the root datum already introduced
  in the node, not an extra group-structure hypothesis. In a finite semisimple root
  system the coroots are determined by its roots and perfect pairing (equivalently the
  unique rank-one reflections of Milne 21.11(e)); thus these are the normalized coroots,
  not freely chosen cocharacters satisfying only pairing two. This agrees with the
  landed `reductive_borel_pair_structure` character-lattice interface.
- `b : P.Base` encodes the chosen simple-root base. Mathlib's Base includes the coroot
  condition as well as the root condition; for the finite reduced geometric root system
  these are equivalent to the node's usual simple-root condition (see Base.lean's
  module docstring). `b.IsPos α` is its nonnegative integral positive-root condition.

### Conclusions

- The first conjunct `IsSemisimpleGroupScheme G_F.X` explicitly includes smoothness,
  connectedness, affineness and finite type over F, as well as semisimplicity.
  The next conjunct states simple connectedness over F by the same all-algebra finite
  central-kernel condition, now for all semisimple F-groups H.
- Maximality of T_F is the recorded `IsMaximalTorus` on the actual base-changed inclusion;
  `Nonempty (T_F ≅ splitTorus F r)` gives splitness with the same rank, including zero.
- `m` identifies the base change of G_m with G_m over F. The first equation pins it to
  the canonical map: projecting its inverse to G_m over k pulls back the Laurent
  coordinate t to t. Together with its being an F-map this fixes all Laurent monomials
  and constants, hence fixes the comparison completely.
- `ex` and `ey` are integer linear equivalences of actual Hom groups. Their displayed
  equations say exactly that they apply the base-change functor and the canonical m
  comparison. Thus they are bijections furnished by extension of characters and
  cocharacters, not arbitrary lattice equivalences.
- `PF.toLinearMap (ex χ) (ey ν) = P.toLinearMap χ ν` preserves the integer pairing;
  its composition interpretation follows also from the explicit ex/ey equations.
  `PF.root α = ex (P.root α)` and `PF.coroot α = ey (P.coroot α)` identify roots and
  normalized coroots. The two following universal equations identify root reflections
  on X and coroot reflections on Y. `PF` uses the original Φ as its indexing type,
  so no unspecified permutation of roots is hidden.
- `aF` is again pinned to conjugation by the base-changed torus inclusion. The range
  of `PF.root` is exactly the nonzero adjoint character weights over F by the next iff.
- The ring map `d : DualNumber k →+* DualNumber F` is pinned on BOTH coordinates:
  `(d z).fst = algebraMap k F z.fst`, likewise for snd. This uniquely specifies the
  scalar-extension map on dual numbers, including its effect on epsilon.
- `l : F ⊗[k] Lie G.X ≃ₗ[F] Lie G_F.X` is pinned on pure tensors `1 ⊗ v` by the equality
  of their actual tangent points after the pullback projection. Its F-linearity pins
  every pure tensor and hence the entire comparison. No mere existence of an abstract
  linear isomorphism replaces the canonical tangent comparison.
- For EVERY character χ, including zero, `((weight χ).baseChange F).map l.toLinearMap`
  equals the corresponding geometric character weight space. This is precisely
  equivariance for the split torus: its character decomposition is a direct sum,
  the induced tensor action acts on each summand through the extended character,
  and ex is surjective onto every F-character. In particular it carries every extended
  root space onto its corresponding root space. Tensor factors are written F first
  using the canonical symmetry convention.
- `B`, `iB`, `j`, `IsBorelGroupScheme iB.hom.hom` and `j ≫ iB = baseChange.map i`
  give a maximal smooth connected solvable closed subgroup containing T_F.
  For every original root α, `b.IsPos α` iff its geometric root space lies in the
  differential range of Lie(B). By Milne Definition 21.35 these are exactly the
  specified positive roots of B. The statement does not choose a different positive
  system with only an abstract isomorphism to the given one.
- `U`, `iU`, its closedness, normality, smoothness, connectedness and
  `SolvableGroupStructure.IsUnipotent U` give the unipotent radical. The universal
  factorization clause makes it the LARGEST such subgroup. Unipotence uses actual
  faithful finite-dimensional matrix representations and geometric unipotence on
  every algebraically closed extension, as in the recorded definition.
- `p`, `j ≫ p = 𝟙 _`, the kernel `IsPullback`, and `IsIso` of multiplication
  `U × T_F → B` give the specified semidirect product with the given torus and radical.
  The normality already stated supplies the conjugation semidirect law.
- The final `iSupIndep` and equality of the differential range of `iU ≫ iB` with the
  supremum indexed by `{α : Φ // b.IsPos α}` give the INTERNAL DIRECT SUM of precisely
  the positive geometric root spaces as the subspace Lie(U) in Lie(G_F).
  Using the inclusion's differential fixes the ambient subspace, rather than merely
  asserting an abstract vector-space isomorphism. The maximality property makes any
  other representative of the largest radical uniquely isomorphic over B, so the
  existential representative states the same assertion as the node's 'if U is its
  largest ...' formulation.

### Dependencies used

Original dependencies:
- `Mathlib.Algebra.Field.Defs`: `Field` (field axioms).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, `IsAlgClosure` (fixed closure).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.Grp`, `GrpObj` and `IsMonHom`;
  their specialization and kernel are documented in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `MultiplicativeType.baseChange`,
  `splitTorus`, `IsTorus`.

Added already-landed statement dependencies:
- `def-sfb-semisimple-group-scheme`, module `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`:
  `IsSemisimpleGroupScheme`, `IsSolvableGroupScheme`, derived-series predicates.
- `def-sfb-borel-subgroup-scheme`, module `Sheaf.AlgebraicGeometry.GroupScheme.Borel`:
  `IsBorelGroupScheme`.
- `def-sfb-torus-character-tangent-weights`, module
  `Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights`: `weightSpace` through `RankOneRoots.weight`.
- `def-sfb-reductive-torus-centralizer-terminology`, module
  `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`: `IsMaximalTorus`.
- `def-sfb-solvable-group-structure`, module `Sheaf.AlgebraicGeometry.SolvableGroupStructure`:
  `IsUnipotent`.
- `def-sfb-rank-one-root-interfaces`, module
  `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces`:
  `Character`, `Cocharacter`, `weight`, `adjointMap`.
- `def-sc-gm-ga`, module `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `multiplicative`, `affine`, and their group structures.

Mathlib's `RootDatum`, `RootPairing.Base`, `reflection`, `coreflection`,
`Submodule.baseChange`, `Submodule.map` and `iSupIndep` express the existing
root datum, simple-root base and internal direct sum without private copies.
`WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential` supplies
`GrpObj.Lie`, `GrpObj.differential` and `GrpObj.tangentPoint`.

All already-stated proof-dependency modules are imported without `public`; the
unstated proof dependencies are explicitly retained in the seven-step proof docstring.
There is no waiting on them and no dependency-interface replacement.

### Sources, searches, edge cases and validation

Read the original node and every statement dependency's statement and lean/mathlib
record, their defining source declarations and docstrings. Read Milne's local PDF,
printed pp.428--435 and 501--502 (PDF pages 440--447 and 513--515), including 21.17's
explicit invariance under field extension and the chamber/Borel and weight-lattice
criteria. The paper's stated source supports the unmodified node.

Searches made with msearch.py:
- LeanFinder: "Scalar extension of a split semisimple simply connected algebraic group
  preserves its root datum and root spaces". Eight hits, including
  `RootPairing.restrictScalars*` and Lie-algebra root-space declarations; none states
  this geometric group-scheme result.
- Loogle: "RootDatum, IsSemisimpleGroupScheme, IsSimplyConnected". Zero hits;
  `IsSemisimpleGroupScheme` is project terminology, not a Mathlib identifier.
- Mathlib grep: "rootDatum|IsSimplyConnected|baseChange.*tangent" in AlgebraicGeometry.
  Zero hits.
- LeanSearch: "Base change of split semisimple algebraic groups preserves characters
  coroots and tangent root spaces". Eight hits: root-pairing restriction, bilinear-form
  base change, special-linear-group base change, Lie ideal base change, transvections
  and tensor bases. No matching statement.
- rg of WeilConjectures and Sheaf for the item id, rootDatum, IsSimplyConnected,
  normalized coroots, and Lie/tangent base-change names. No statement duplicate.
  Found and read the landed Borel-pair structure, simply-connected character-lattice,
  central-isogeny root compatibility, rank-one root interfaces, and Lie differential.
  The group-scheme definitions, tori, Borel, unipotence, characters and weight spaces
  found in these searches are reused. No new notion is introduced.
- rg of dag/nodes for the root terminology and recorded declaration names verified
  their existing ownership; no duplicate definition node was written.

Edge cases checked: rank r=0 and Φ empty are allowed (no Nonempty or positivity
assumption on the rank or root index); Base.support and the positive subtype may be
empty, iSup is bottom and iSupIndep vacuous, so Lie(U)=0 and the radical is the trivial
group. Reducible root systems are allowed, with no irreducibility assumption.
Zero weight is explicitly included in tangent compatibility. k need not be algebraically
closed or equal to F. F can be any specified algebraic closure, including an identity
extension for an already closed field. Central kernels may be nonreduced; centrality
is tested over arbitrary rings, not merely geometric points. The field and scheme
universes share the explicit u permitted by the recorded scalar-extension API; any
pair of fields is accommodated by raising both to a common universe. There are no
auto-bound variables or universes, file-local notation, local instances, or hollow data.

The first scompile.py run compiled both sandbox and real module names successfully,
with no errors or warnings. The normal per-file limit was retained. The theorem has
one expected sorry and no other postponed declarations. Delivery preflight and its
independent per-file compile are run through deliver2.py.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
