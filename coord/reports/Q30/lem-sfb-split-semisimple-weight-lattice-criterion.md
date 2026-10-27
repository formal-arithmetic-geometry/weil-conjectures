## Worker report

The single module states `AlgebraicGeometry.splitSemisimple_weightLattice_criterion`,
with its entire proof postponed by `sorry`. It adds no definition or auxiliary theorem.
The node's mathematical statement is unchanged. Three already landed definition nodes
are added to `stmt_deps` to name the exact semisimplicity, maximality, and tangent-weight
interfaces used. No dependency record is modified.

Source checked directly: Milne, Algebraic Groups (2017), Proposition 23.59 (printed
p.502, PDF p.514), Proposition 23.29 (printed p.493, PDF p.505), and the existence
Theorem 23.55 / Corollary 23.56 (printed p.501, PDF p.513). These give both directions
over the original split field. The chapter's field is arbitrary; the node retains
its characteristic-zero restriction. Proposition 19.15 is the central-cover convention.

Clause-by-clause correspondence:

- The base is `{k : Type u} [Field k] [CharZero k]`. The fixed algebraic closure is
  Mathlib's `AlgebraicClosure k`, with its canonical field and algebra structure.
  Any fixed algebraic closure is equivalent to this choice by `IsAlgClosure.equiv`.
- Group schemes `H,S` are `Grp (Over (Spec (.of k)))`: the bundled version of the
  recorded `GrpObj`. All arrows `i,q` are actual group-scheme homomorphisms.
- `hH : SolvableGroupStructure.IsAlgebraic H` unfolds to affine, locally finite type
  and quasi-compact, hence exactly affine finite type. `hHs` is smoothness and `hHc`
  is connectedness over k, both explicit.
- `hHss` applies the recorded `IsSemisimpleGroupScheme` to the actual pullback group
  over the algebraic closure. This predicate includes the absence of nontrivial
  smooth connected solvable normal closed subgroup schemes. Its solvability is
  `IsSolvableGroupScheme`, defined by termination of the scheme-theoretic commutator
  series, and triviality is terminality over the field. Its additional geometric
  regularity clauses follow from the original regularity assumptions and the identity
  point; they are the same geometric semisimple notion, not rational-point simplicity.
- `i : S ⟶ H` and `hi : IsClosedSubgroupScheme i.hom.hom` are the torus inclusion.
  `hsplit` is an isomorphism to the recorded rank-r split torus for some natural r.
  `hmax` is maximality of its actual scalar extension among torus subgroup schemes
  over the fixed algebraic closure. No maximality is replaced by a largest-torus claim.
- `IsCommMonObj S.X` exposes the uniquely determined commutative group structure
  already implied by splitness, so that cocharacters carry their pointwise abelian
  group law. The analogous witness for G_m exposes its standard commutative law.
  These are structure witnesses for the notation, not additional geometric restrictions.
- `Additive (S ⟶ Grp.mk (StandardGroupSchemes.multiplicative k))` is exactly X;
  `Additive (Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ S)` is exactly Y.
  `StandardGroupSchemes.multiplicative` is the actual Laurent Hopf group scheme.
- `a : ModObj S.X H.X` and `ha` specify the actual adjoint action by restricting
  conjugation along i. The action is not free auxiliary representation data.
- `Φ` indexes the roots as a finite subset of actual characters. `hweights` says
  precisely that membership is equivalent to a nonzero character with nonzero
  tangent character weight space. The existing tangent space is `GrpObj.Lie H.X`;
  no abstract unrelated Lie algebra is used. The weightSpace tests actual dual-number
  tangent points. Characteristic zero makes k infinite; the k-points of a split torus
  are Zariski dense, so these are exactly the adjoint character weights over k.
- `P : RootDatum Φ X Y` packages the node's integral root/coroot data. `hroot`
  identifies every root with its actual character and `hpair` identifies the perfect
  pairing with composition equal to the integer power map on G_m. Thus this is the
  same canonical root datum, not an arbitrary root system imposed on the group.
  The coroot normalization is pinned by this finite root datum: its roots, pairing,
  and root-preserving reflections uniquely determine its coroots. Indeed on the
  rational span, the finite reflection group gives an invariant positive definite
  form; a reflection with prescribed root α must have functional
  2(α,-)/(α,α). Semisimplicity makes roots span the whole rationalization, so no
  extra component of that functional is possible. Consequently `P.coroot` is the
  opposite-rank-one normalized coroot, as in Milne 21.11--21.12. The root-datum
  parameter simply exposes the objects introduced in the node; it does not require
  a Borel, a base, a pinning, or splitness of the covers.
- The left side quantifies over every `H' : Grp (Over (Spec (.of k)))`, with the same
  affine finite type, smooth, connected and geometrically semisimple conditions.
  It quantifies over every `q : H' ⟶ H`, assumes `Surjective q.hom.hom.left`, and
  `IsFinite (GrpObj.ker q.hom.hom).hom`. The latter is finiteness of the actual
  scheme-theoretic identity fibre, equivalent to a finite-dimensional coordinate
  algebra over a field. There is no separability or split-torus hypothesis on H'.
- Centrality is the displayed commuting identity for every commutative k-algebra
  A, every A-point x of the actual kernel and every A-point g of H'. The inclusion
  is `GrpObj.kerι`; nonreduced algebras are allowed. It does not only test k-points.
  `IsIso q` is the required group-scheme isomorphism conclusion.
- The outer `↔` is both directions of the criterion. The right side quantifies over
  every `v : ℚ ⊗[ℤ] X`. Tensor symmetry canonically identifies this with the node's
  `X ⊗[ℤ] ℚ`. `∃ χ, TensorProduct.mk ℤ ℚ _ 1 χ = v` is membership in the actual
  image of X. The inner `↔` equates this with membership in the full weight lattice.
- `P.coroot' α` is the integer functional χ ↦ pairing(χ,coroot α). Composition
  with `Int.castAddHom ℚ` and `liftBaseChange ℚ` is its canonical rational extension.
  `∀ α : Φ, ∃ n : ℤ, ... v = (n : ℚ)` is exactly integrality at every coroot.
  It is not equality with the root lattice or with a rational vector space.

Dependency declarations used (their docstrings and full signatures read):

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`; and
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, `IsAlgClosure`,
  `IsAlgClosure.equiv` (def-weil-algebraic-closure).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`, with
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` for `IsClosedSubgroupScheme`,
  the scheme-theoretic kernel, and finite-group terminology (def-sc-group-scheme).
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `MultiplicativeType.baseChange` and `MultiplicativeType.splitTorus`
  (def-sfb-tori-multiplicative-type).
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`:
  `IsSemisimpleGroupScheme`, with `IsSolvableGroupScheme`, `GroupSchemeDerivedLength`
  and `IsDerivedGroupScheme` in its definition (def-sfb-semisimple-group-scheme).
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsMaximalTorus`; its imported
  `Sheaf.AlgebraicGeometry.SolvableGroupStructure` gives
  `SolvableGroupStructure.IsAlgebraic`
  (def-sfb-reductive-torus-centralizer-terminology).
- `Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights`:
  `TorusCharacterTangent.weightSpace` (def-sfb-torus-character-tangent-weights).
- `Mathlib.LinearAlgebra.RootSystem.Defs`: `RootDatum`, `RootPairing.coroot'`,
  `RootPairing.toLinearMap`. `Mathlib.RingTheory.TensorProduct.Basic` provides the
  rational extension interface used by the lattice membership formula.

Edge cases checked mathematically before writing:

- Rank zero and empty Φ are permitted: r is any natural, there is no nonempty
  root index, no positive rank assumption, and the integrality test is vacuous.
  Semisimplicity forces X and its rationalization to be zero in that case, so
  the displayed membership statement has its intended meaning.
- The trivial group H is included; the argument and empty root datum apply.
- Non-algebraically-closed k is included; only `AlgebraicClosure k` has the
  algebraic-closedness instance. Covers H' need not be split over k.
- Central kernels can be nonreduced as far as their definition is concerned;
  no reducedness, étaleness, rational-point cardinality, or prime-to-characteristic
  surrogate for scheme-theoretic finiteness is substituted.
- Arbitrary characteristic-zero fields, with arbitrary universe u, and every
  commutative k-algebra in the field's scheme universe are tested. The null algebra
  is allowed among test algebras. No unrelated smaller test-algebra universe occurs.
- Roots are genuine characters, not their differentials; the rationalization
  embedding is the integral-character image, not a chosen lattice basis.

Searches made through the authorized msearch.py wrapper:

- leanfinder: "A split semisimple algebraic group is simply connected if and only
  if its character lattice is the full weight lattice". Eight hits, concerning
  abstract Lie-algebra semisimplicity and Geck root-pairing constructions; none
  states the group-scheme criterion.
- loogle: `"RootPairing", "weightLattice"`. No hits.
- grep: `weightLattice|IsSimplyConnected`, Mathlib/AlgebraicGeometry. No hits.
- leansearch: "Central isogenies onto a split semisimple algebraic group are
  isomorphisms exactly when every integral weight is a torus character". Eight
  hits concerning Lie weight spaces, Killing-form coroots, and abstract group
  centers; none is the criterion for split algebraic groups.
- rg in both `lean/WeilConjectures` and `lean/Sheaf`, plus
  `dag/lean_names_upstream.json`, for `weightLattice|IsSimplyConnected|` followed
  by this item's exact id. No upstream criterion. Existing Sheaf hits include
  `RootDatumLattice.weightLattice`, which lives in the rational root span and
  belongs to a different abstract-lattice result, and
  `simplyConnected_character_lattice`, which states only a consequence in the
  algebraically closed case and requires a Borel and simple-root base. Neither
  says the present biconditional over the original field. Their full files were read.
- rg of upstream for the exact item id: no match. rg of Mathlib, Sheaf and upstream
  for the proposed declaration name: no match.
- `tools/blueprint_refs.py search 'weight lattice'`: zero blueprint matches.
  Existing DAG definition nodes for all used group notions were located and reused.

The entire eight-step DAG proof is in the declaration docstring, including geometric
comparison, finite-index lattices, descent of the actual arbitrary cover, and the
obstructing cover over k. Already recorded proof dependency modules are plain imports.
The following proof dependencies have no recorded Lean module yet and are therefore
not imported (none is needed to type this statement):
- `lem-sfb-geometric-neutral-reductivity-field-invariance`.
- `def-sfb-pinned-split-root-realization`.
- `lem-sfb-affine-group-lie-tangent-calculus`.
- `lem-sfb-arbitrary-base-root-lines-coroots`.
- `lem-sfb-regular-cocharacter-borel-description`.
- `lem-sfb-semisimple-roots-span`.
- `lem-sfb-isogeny-root-power-laws`.
- `lem-sfb-root-datum-isogeny-realization`.
- `lem-sfb-pinned-split-root-classification`.
- `lem-sfb-split-central-isogeny-lifting`.

No statement correction, new node, dependency repair, disputed statement, or known
node fault is needed.

Validation: `scompile.py Q30 lem-sfb-split-semisimple-weight-lattice-criterion` passed
for the delivered module, with no error or warning. The wrapper compiled the sandbox
and library forms against the live published build; the library compile took 5.0 s.
The long preliminary elapsed time included waiting for the shared compile slot.
`deliver2.py Q30 lem-sfb-split-semisimple-weight-lattice-criterion --no-push` returned
`OK (dry run): commit f97e62e8a39 passes the preflight and compiles; nothing pushed`.
The final signature is verbatim in the node record, every line is at most 100 characters,
and auto-bound implicit variables are disabled.

## Second reading by Q30

Author's separate second pass; no independent agent was started, as the dispatcher
brief explicitly forbids that. The maintainer supplies the independent review.
Re-read the node and the resulting declaration side by side. In particular checked
that hmax is applied after scalar extension, the base k itself is not assumed
algebraically closed, every cover is quantified over k without a splitness assumption,
finite and central refer to the full kernel scheme on all algebra points, both
biconditionals have the intended scope, and no rank-zero case is excluded. Checked
that root-datum roots and pairing are tied to the actual character Hom groups and
adjoint weights; coroot uniqueness rules out arbitrary substitute coroots. No
mathematical mismatch was found on this second pass.
