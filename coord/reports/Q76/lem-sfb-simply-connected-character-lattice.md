## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SimplyConnectedCharacterLattice`
states `AlgebraicGeometry.simplyConnected_character_lattice`. Its sole theorem has
`by sorry`; no definition or instance is introduced. The node's statement,
dependencies and proof are unchanged. There is no statement dispute or correction.

Source read: Milne, Algebraic Groups (2017), 22.8--22.11, printed pp.464--465;
Proposition 23.59, p.502; C.26, p.613, together with C.28--C.34 on root data.
These identify the weight lattice, its fundamental-weight basis and X=P for
simply connected semisimple groups. The latest blueprint direct-images proof
(3), in `sk-thm-sf-ctf-stability-direct-images.proof.md`, was also read; this item
is a supporting lemma below that unit, not the unit's statement.

Hypotheses and clauses, matched individually:

- F is an algebraically closed field: `{F : Type u} [Field F] [IsAlgClosed F]`.
- The F-group scheme is `G : Grp (Over (Spec (.of F)))`. Its group law and
  all structure morphisms are those of the recorded `CategoryTheory.GrpObj`.
- Semisimplicity is `hG : IsSemisimpleGroupScheme G.X`: its definition includes
  smoothness, connectedness, affineness, finite type (`LocallyOfFiniteType` and
  `QuasiCompact`) and terminality of every smooth connected solvable normal
  closed subgroup. Solvability uses the algebraic derived series.
- Simple connectedness is written in full as `hsc`, with exactly the same
  interface as the landed `exists_rho_section_modules`: every semisimple G',
  every homomorphism f, `Surjective f.left`, finite scheme-theoretic kernel
  `IsFinite (GrpObj.ker f).hom`, and centrality on points over every commutative
  F-algebra imply `IsIso f`. Finiteness is the existing scheme notion; over a
  field this is equivalently finite-dimensional coordinate algebra. The kernel
  is the actual fibre product with the identity, not its set of F-points.
- T is a split maximal torus: `hT` is the existing `IsMaximalTorus iT`, and
  `hsplit` is an isomorphism with `MultiplicativeType.splitTorus F r` for some r.
- B is a Borel containing T: `hB : IsBorelGroupScheme iB.hom.hom` and
  `hj : j ≫ iB = iT`. The predicate includes closedness and maximality among
  smooth connected solvable subgroups.
- The root-datum data are exactly in the recorded Borel-pair interface. X is
  `Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))`; X_* is
  `Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)`. The two
  commutativity witnesses are the witnesses exposed by that dependency, not
  extra restrictions on a split torus or G_m. `P : RootDatum Φ X X_*` and
  `b : P.Base` retain the pairing, reflection axioms, simple roots and coroots.
  `hroot` pins each root to the actual character indexed by Φ; `hpair` pins
  the perfect integer pairing to composition equal to an integer power map.
- Roots and positive roots are the actual character weights: `aG`, `aB`,
  `haG`, `haB` fix conjugation by the given inclusions; `hweights` says Φ is
  exactly the nonzero character weights on Lie(G); `hpositive` fixes the
  positive system to the weights on Lie(B). These are data from the dependency,
  not an abstract replacement of G's root datum. Its finite reduced
  crystallographic property is already supplied by that dependency; no
  characteristic-zero Lie-algebra substitution is made.
- V is `ℚ ⊗[ℤ] X`. This is canonically X tensor ℚ by tensor symmetry;
  `TensorProduct.mk ℤ ℚ _ 1` is the canonical character-lattice map.
- Simple roots form a rational basis: existential `ar : Module.Basis
  b.support ℚ (ℚ ⊗[ℤ] X)` with `ar i = 1 ⊗ P.root i` for every simple index.
- The corresponding coroots form the dual root-system base: `b` includes
  independence and same-sign nonnegative integral generation for both roots
  and coroots (`b.flip` is the coroot base). The existential `ac` is a rational
  basis of `ℚ ⊗[ℤ] X_*` with `ac i = 1 ⊗ P.coroot i`. In particular this
  asserts rational spanning, not just independence in a proper subspace.
- The pairing identifies X with all integral-evaluation vectors: for EVERY
  `v : ℚ ⊗[ℤ] X`, the final iff says `v = 1 ⊗ χ` for some actual character χ
  exactly when each coroot evaluation equals an integer n. Evaluation is the
  canonical rational extension
  `((Int.castAddHom ℚ).toIntLinearMap.comp (P.coroot' α)).liftBaseChange ℚ`.
  This extends the specified perfect integer pairing by the tensor universal
  property; no arbitrary linear functional or map is substituted.
- The displayed integral direct sum is `ω : Module.Basis b.support ℤ X`.
  A Module.Basis identifies X with finitely supported integer coordinates, so
  it asserts existence and uniqueness of the integral expansion in these very
  fundamental weights, not just a spanning assertion.
- Fundamental-weight normalization is
  `P.toLinearMap (ω i) (P.coroot j) = if i = j then 1 else 0`.
  Rational extension gives the same equation on their images in V.
- Each fundamental weight is an actual group-scheme character: the values of
  ω are in the actual additive Hom group X, so `(ω i).toMul` is that character.
  There is no characteristic restriction, `CharZero F`, separability condition,
  prime-to-characteristic kernel bound, or positive-rank assumption.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field` (extends CommRing and DivisionRing).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (every polynomial
  splits, equivalent to the node's root formulation). The algebraic-closure
  node explicitly records this component; choosing an extra closure is unneeded.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: group-scheme conventions,
  kernel, `IsFinite` and subgroup predicates. These arrive through the public
  import of the recorded Borel-pair module.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `AlgebraicGeometry.reductive_borel_pair_structure` and
  `AlgebraicGeometry.semisimpleGroupScheme_isReductive`, full signatures and
  proof docstrings read. The former supplies exactly the pinned P, b and actions
  used by this statement. Its quotient and unipotent-complement conclusions are
  not extra hypotheses required for the weight-lattice assertion.
- That module's existing terminology modules supply `IsSemisimpleGroupScheme`,
  `ReductiveTorusCentralizer.IsMaximalTorus`, `IsBorelGroupScheme`,
  `TorusCharacterTangent.weightSpace`, `MultiplicativeType.splitTorus`, and
  `StandardGroupSchemes.multiplicative`, all used directly without private copies.
- Proof dependency `lem-sfb-root-base-rational-integral-spans` is a Mathlib
  leaf: `RootPairing.Base.mk'`, `.toWeightBasis`, `.toCoweightBasis`, and the
  integral-span results in Base/BaseExists; signatures and docs read. The
  BaseExists proof import is retained for that proof dependency. The recorded
  semisimple-roots-span and central-lattice-enlargement nodes have no Lean
  declarations yet; they are not statement prerequisites here. Their proof
  use is retained in the complete natural-language proof docstring.

Edge cases checked before writing: the trivial group gives empty Φ and empty
b.support, bases of zero rational spaces and the zero character group, and
v is in the character image iff all the vacuous coroot conditions hold (the
space itself is zero). For SL2 the normalization gives the actual fundamental
character, with root twice that character, in every characteristic including
2. A non-simply-connected adjoint rank-one group fails hsc and is correctly
excluded; its half-root cannot be incorrectly declared a character. Products
have independent simple-root indices with delta pairings. Positive characteristic
retains nonreduced central kernels; testing only rational points was avoided.
The common universe u for F, schemes and test algebras matches the dependency
and includes test coordinate algebras; there is no independently smaller universe
that could make centrality vacuous.

Searches for an existing statement (all via the prescribed msearch.py wrapper):

- LeanFinder: "The character lattice of a maximal torus in a simply connected
  semisimple algebraic group is the weight lattice with basis the fundamental
  weights"; 8 hits, including abstract RootPairing.Base bases and Lie-algebra
  results. None asserts equality with actual group-scheme characters.
- Loogle: "RootDatum, RootPairing.Base.toWeightBasis,
  RootPairing.Base.toCoweightBasis"; OK, zero hits.
- LeanSearch: "character lattice simply connected semisimple group fundamental
  weights"; 8 hits on abstract root pairing bases and Lie-module weights, none
  giving the asserted algebraic-group character-lattice equality.
- Mathlib grep: `weightLattice|fundamentalWeight|SimplyConnected|simply.connected`
  in LinearAlgebra/RootSystem; OK, zero hits.
- Project rg: the same names plus `IsSemisimple` in lean/WeilConjectures and
  lean/Sheaf. No existing theorem matches. The existing
  `RootDatumLattice.weightLattice` was read: it is in the root span for an
  abstract lattice and does not assert that a simply connected algebraic group's
  actual character lattice equals it. The final iff uses ordinary tensor
  extension and integer membership inline, without defining a second weight
  lattice. The landed rho theorem assumes simple connectedness inline and
  uses this item in its proof plan; importing it would create a cycle, so
  its existing terminology is used through its owning dependency modules.
- Name and item searches in lean/WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json found no existing declaration of the proposed
  theorem name and no upstream attachment to this node.

Validation: scompile.py checked both the sandbox and actual module path against
the live server library, one file at a time. An initial open-Classical style
warning was repaired by narrowing it to `open Classical in` on this theorem.
The only intended postponed proof is this node's theorem.

## Second reading by Q76

This is the author's separate second reading; the dispatcher explicitly forbids
starting another agent. The independent mathematical review is the maintainer's.
Reopened the node and the finished module and checked the hypotheses and every
clause against the correspondence above. In particular the two bases `ar` and
`ac` are bases of the entire rationalized actual Hom lattices, ω is an integral
basis of the actual character group, the iff quantifies over every rational
vector and every root, and both sides use the specified canonical pairing.
The delta equation uses actual integral characters rather than postulated
vectors or a finite-index sublattice. The coroot-base clause is supplied by the
existing `P.Base` fields together with the new rational-basis conclusion; it
was not silently replaced by only a dimension equality. All Borel-pair data
are pinned to the supplied inclusions and conjugation actions. The argument
has no char-zero assumption and no nonempty-root assumption. No mathematical
mismatch or node edit was needed; the style warning was the only compile repair.
The file contains exactly one theorem and one whole-proof sorry, with a source
and the full four-step node proof in its docstring. No new or dependency module
is part of this delivery.
