## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveCentreRootQuotient`
states `AlgebraicGeometry.reductive_centre_root_quotient`. Its sole theorem proof
is `sorry`. It introduces no definitions and makes no statement correction.

Source read: Milne, *Algebraic Groups* (2017), Propositions 21.7 and 21.8,
printed p.427 (PDF p.439). Proposition 21.7 places the centre in the maximal
torus and identifies it with the restricted adjoint kernel. Proposition 21.8
identifies this with the intersection of root kernels and computes the character
quotient. The examples on that page include SL₂, PGL₂, and GLₙ. The module
includes all five proof steps of the DAG, with their named prerequisites.

Hypothesis and clause correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
  Mathlib's `Field` includes nontriviality and inverses; `IsAlgClosed` says every
  polynomial splits, equivalent to every nonconstant polynomial having a root.
- The affine reductive group is `H : Grp (Over (Spec (.of F)))` with
  `hH : ReductiveTorusCentralizer.IsReductive H`. This is exactly the recorded
  predicate used by the Borel-pair dependency. It includes algebraicity
  (affine finite type), smoothness, geometric connectedness, and triviality of
  the unipotent radical after algebraic closure. Over this algebraically
  closed F this is the node's reductivity convention.
- The fixed torus inclusion is `iT : T ⟶ H` with `hT : IsMaximalTorus iT`.
  That predicate includes the closed subgroup condition and torus property.
  `hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r)`
  states splitness, including rank zero. No Borel choice is required.
- `X` is the actual character group
  `Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))`.
  The existential `IsCommMonObj` witness is a conclusion giving its canonical
  pointwise abelian group law, following the Borel-pair interface. There is no
  assumed arbitrary abstract lattice or chosen unrelated torus presentation.
- The existential action `aH : ModObj T.X H.X` is constrained by
  `aH.smul = (iT.hom.hom ⊗ₘ 𝟙 H.X) ≫ GrpObj.conj H.X`.
  Thus it is the actual conjugation action used by the dependency, rather
  than a supplied arbitrary action or an extra mathematical hypothesis.
- The finite root set `Φ` is specified by the biconditional
  `χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace ... aH χ.toMul ≠ ⊥`.
  These are character weights on the actual tangent space, not differentials
  of characters. The action, finite root set, and lattice are existentially
  provided with these defining equalities as conclusions; hence the theorem
  cannot become vacuous through a nonexistent finite root set.
- `L = AddSubgroup.closure (Φ : Set X)` gives precisely the integral root
  span: additive subgroup closure is the set of all finite integer sums.
  The specified root set and L are uniquely determined once the conjugation
  action is fixed, so their existential presentation expresses the node's
  definitions of Φ and L without additional choices or assumptions.
- The centre is represented by an actual group scheme `Z` and inclusion
  `j : Z ⟶ T`. `IsClosedSubgroupScheme j.hom.hom` asserts closedness in T;
  its composite with the already closed iT is the closed inclusion in H.
- For every `A : Type u` with `[CommRing A] [Algebra F A]`, the first set
  equality identifies `centralizerPoints (𝟙 H) A` with the image of the
  composite `j ≫ iT`. The recorded centralizer definition quantifies over
  every F-algebra map A → B and every point of H(B). Thus this is the full
  scheme-theoretic centre functor, not the centre of H(A) alone.
- The second equality identifies the image of j on every A with exactly
  `{t | ∀ α ∈ Φ, t ≫ α.toMul.hom.hom = 1}`. This says the closed subgroup
  is the intersection of all root kernels. `1` is the identity point of Gₘ.
  Equality of these subfunctors on all affine test schemes is equality of
  their represented closed subgroup schemes.
- `e : Z ≅ diagonalizableGroup F (X ⧸ L)` is a group-scheme isomorphism.
  The existing definition uses the actual Hopf spectrum of
  `AddMonoidAlgebra F (X ⧸ L)`, with the basis multiplication, group-like
  coproduct, counit, and antipode in the node, not an unspecified Hopf law.
- `c : Additive (Z ⟶ Gₘ) ≃+ (X ⧸ L)` identifies the character group of Z
  with that quotient. The equation
  `c (Additive.ofMul (j ≫ χ.toMul)) = QuotientAddGroup.mk' L χ`
  renders restriction as precisely the quotient map, for every χ in X.
- The final equation pulls the Laurent generator t back along
  `e.inv ≫ χ.toMul`, converts global sections with `Scheme.ΓSpecIso`, and
  equates the result to `AddMonoidAlgebra.single (c χ) 1`. This ties c to
  the same group-scheme isomorphism e: a character labelled m is exactly
  the basis character e_m on D(X/L). The quotient assertion is therefore
  canonical under the displayed isomorphism, rather than an unrelated
  abstract isomorphism of character groups.
- All test algebras are arbitrary commutative F-algebras, with no reducedness,
  nontriviality, or characteristic restriction. Scheme and algebra universes
  are consistently u; u is arbitrary, and no smaller independent test
  universe is introduced. The existing centralizer interface uses this
  universe convention as well.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` and its root
  characterization; the algebraic-closure dependency records
  `AlgebraicClosure`, with `IsAlgClosed` explicitly among its component notions.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, through
  its bundled `CategoryTheory.Grp`; and
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsClosedSubgroupScheme`. This is the group-scheme convention of
  `def-sc-group-scheme`, not a duplicate group-scheme definition.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`;
  `GammaSpecAdjunction`: `Scheme.ΓSpecIso` for the coordinate condition.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `reductive_borel_pair_structure`. Its actual character group, conjugation
  action normalization, finite nonzero-weight root set and torus conventions
  are used verbatim. Its public dependencies supply
  `ReductiveTorusCentralizer.IsReductive`, `IsMaximalTorus`,
  `TorusCharacterTangent.weightSpace`, `MultiplicativeType.splitTorus`,
  and `StandardGroupSchemes.multiplicative`, `affine` and `map`.
- `Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange`:
  `exists_affine_group_centre_baseChange`, and its public dependency
  `ReductiveTorusCentralizer.centralizerPoints` (identity inclusion).
- `Sheaf.AlgebraicGeometry.DiagonalizableGroup`: `diagonalizableGroup`,
  already owned by `def-sfb-diagonalizable-group`. That landed definition
  node is added to stmt_deps under brief-stage2 §5's permission to add
  landed notions; its declaration is used without any new definition node.
- `Mathlib.GroupTheory.QuotientGroup.Basic`: `QuotientAddGroup.mk'` and
  quotient additive-group instances. `AddSubgroup.closure` gives the
  integral span directly, without a second root-lattice definition.

Already stated proof dependencies are imported privately:
`Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer`
(`ReductiveTorusCentralizer.reductive_torus_self_centralizer`),
`Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections`
(`RankOneRoots.reductive_rankOne_reflections`),
`Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality`
(`MultiplicativeType.multiplicative_character_antiduality`), and
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` (`IsClosedImmersion`).
The centre-base-change proof dependency is public because its centralizer
interface also occurs in the statement. The original proof-only nodes
`lem-sfb-split-torus-subgroups-diagonalizable`,
`lem-sfb-adjoint-kernel-central-quotient-unipotent`, and
`lem-sfb-diagonalizable-to-unipotent-trivial` have no recorded Lean module
in the read repository, so no import can yet be added for them. They are
retained in proof_deps and documented in the proof plan; none is a missing
statement prerequisite for this delivery.

Edge cases checked before writing:

- Empty roots, including a torus or the trivial group: closure of the empty
  set is zero; the kernel condition is vacuous, giving Z = T and D(X/0).
- SL₂ in characteristic 2: the root lattice is 2ℤ, giving D(ℤ/2) = μ₂.
  Nilpotent-valued points remain visible, and no smoothness is imposed on Z.
- PGL₂: the roots generate X, giving D(0), the trivial centre.
- GLₙ: the root differences generate the sum-zero lattice, so the quotient
  is ℤ and the centre is Gₘ. Central torus directions have not been removed.
- The zero test algebra is permitted, as are dual numbers and all other
  nonreduced test algebras. No condition on the order of torsion in X/L
  or on the characteristic is present.

Searches performed for an existing statement:

- `msearch.py ... leanfinder`, query "The scheme theoretic centre of a split
  reductive algebraic group is the diagonalizable group of the character
  lattice modulo the root lattice": 8 hits, all formulas for the centre of
  the abstract special linear group, not this general group-scheme result.
- `msearch.py ... loogle`, query `"GroupScheme", "center"`: 0 hits.
- `msearch.py ... grep`, query `reductive|Reductive|rootDatum|RootDatum`,
  subdirectory `AlgebraicGeometry`: 0 hits in Mathlib.
- `rg` in the project and upstream Lean trees for reductive/Reductive,
  root quotients, and centre/root combinations found the existing Borel,
  rank-one, character-antiduality, centre, and diagonalizable interfaces
  used here; none states this node. Upstream also has Lie-algebra results
  and unrelated local-polynomial root quotients, which do not match.
- Searching upstream `WeilConjectures` for this exact node id returned no
  occurrence. Searching `dag/lean_names_upstream.json` and the Lean trees
  for `reductive_centre_root_quotient` found no existing declaration.

Validation: the prescribed `scompile.py` compiles the delivered module as a
single file against the live server build. Both its sandbox and library-module
checks passed with no errors or warnings. No proofs were added. No
STATEMENT-DISPUTED finding or dependency-interface repair was needed.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
