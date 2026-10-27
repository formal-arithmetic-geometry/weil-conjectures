## Worker report

The delivery states `AlgebraicGeometry.RhoSection.rho_section_self_duality` in
`Sheaf.AlgebraicGeometry.RhoSectionSelfDuality`. Its only proof is postponed with
`sorry`. The original item statement, proof and proof dependencies are unchanged.
It also supplies the canonical identity comparison of the two already-published
coordinate-algebra scalar structures; this has real identity ring-equivalence data,
with its scalar-compatibility proof separately named and postponed.

Source checked: Alper, *Adequate moduli spaces*, Section 9.7, the definition immediately
before Lemma 9.7.2 and Lemma 9.7.4(1),(2),
https://arxiv.org/html/1005.2398v3#S9.SS7. The source uses the actual regular-function
subspace, not an abstract vector space of the same dimension. Its characteristic-zero
case includes every positive weight; its positive-characteristic case is restricted
to the Steinberg weights. The DAG explicitly asks for the field specialization of
this DVR result. The module docstring retains the DAG's four-step proof via primitive
lines, complete reducibility, Steinberg irreducibility and highest-weight duality.

Hypotheses and clauses, matched with the Lean signature:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The group scheme is `S : Grp (Over (Spec (.of F)))`; `hS` is the existing
  `IsSemisimpleGroupScheme S.X`, whose definition requires smoothness, connectedness,
  affineness, finite type and triviality of smooth connected solvable normal closed
  subgroups. `[IsAffine S.X.left]` exposes exactly the affine conjunct of `hS` for
  the existing coordinate-Hopf interface. It adds no mathematical restriction.
- Simple connectedness is `hsc`, verbatim the condition in the recorded
  `exists_rho_section_modules` signature: every surjective map from a semisimple
  group with finite central kernel is an isomorphism. Centrality is tested over
  every algebra, not only over F-points.
- The fixed split maximal torus, Borel and their compatible inclusions are
  `T B i j k hpair`, using the existing `IsRhoBorelPair` predicate. Its clauses
  are maximal torus, split torus, Borel, and `k ≫ j = i`.
- The conjugation action is `a` and `hconj`, copied from the dependency interface.
  `Φ`, `hΦnodup` and `hΦ` specify each positive character root exactly once via
  the nonzero tangent weight spaces for that very action.
- `ρ` and `hρ` specify twice rho as the sum of the positive roots, using
  multiplication in the character group. `ρB`, `hρB` and `hU` specify its Borel
  extension, restriction to the torus, and triviality on the unipotent radical.
  These are the dependency's own conditions, not newly assumed representation
  properties. In particular no division by two in F is used.
- The actual W is `sectionModule S B j ρB m`. This is precisely the existing
  intersection of the semi-invariance kernels in `Coordinate S.X` over every
  commutative F-algebra; no abstract induced module replaces it.
- The characteristic-zero clause is `CharZero F ∧ 0 < m`.
- The positive-characteristic clause is
  `∃ (p ν : ℕ), 0 < p ∧ CharP F p ∧ 0 < ν ∧ m = p ^ ν - 1`.
  Natural positive ν are exactly the positive integers in the node. The
  disjunction in the antecedent combines the two clauses without asserting
  self-duality for arbitrary positive-characteristic m.
- `IsSelfDualLeftTranslation` is a helper predicate for this item's conclusion,
  listed in `lean.declarations`. It existentially presents c and d, requires
  `HopfAction.Coassociative` and `HopfAction.Counital` on both, and identifies c
  by its exact evaluation formula `f(s⁻¹ * g)` for every algebra A, s, g, and f.
  On a pure tensor `w ⊗ h`, the left side is `ev_g(w) * ev_s(h)`. Thus this is
  the canonical rational left-translation action, not a freely chosen coaction.
  The all-algebra evaluation identity uniquely determines it by affine Yoneda
  and tensor injectivity for the subspace W.
- The dual is literally `Module.Dual F W`. The existing
  `RationalHighestWeight.IsContragredient c d` characterizes d by antipode
  contractions, hence by `(s ell)(w) = ell(s⁻¹ w)` after scalar extension.
  The final `e : W ≃ₗ[F] Module.Dual F W` and
  `e.toLinearMap.rTensor ... ∘ₗ c = d ∘ₗ e.toLinearMap` assert the requested
  equivariant linear isomorphism as an identity of coactions.
- The explanatory invariant and diagonal-tensor conventions in the prose do
  not introduce extra conclusions: no invariant-space or tensor-square theorem
  is asserted by this node. The existing Hopf interface supplies their meaning.

Dependency declarations read and used:

- Mathlib `Field` (`Mathlib.Algebra.Field.Defs`) and `IsAlgClosed`
  (`Mathlib.FieldTheory.IsAlgClosed.Basic`), and `CategoryTheory.GrpObj` / `Grp`
  (`Mathlib.CategoryTheory.Monoidal.Grp`). The latter are specialized to schemes
  over `Spec F`, exactly as recorded for `def-sc-group-scheme`.
- `Sheaf.AlgebraicGeometry.RhoSectionModules`: `IsRhoBorelPair` and
  `exists_rho_section_modules`, whose full signature and docstring were read.
- Its dependency `Sheaf.AlgebraicGeometry.RhoSectionModuleData`: `Coordinate`,
  `evaluate`, `sectionModule`, `HasRationalLeftTranslation`. All definitions and
  docstrings were read; the matrix interface does not expose a chosen coaction.
- `Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData`:
  `coordinateAlgebra`, `coordinateHopf`, `IsContragredient`. Its landed node
  `def-sfb-rational-highest-weight-data` is added to statement dependencies.
  The scalar comparison's node cites both existing coordinate-interface nodes.
- Proof-only imports: the recorded modules
  `Sheaf.AlgebraicGeometry.GroupScheme.CharacteristicZeroCompleteReducibility`
  and `Sheaf.AlgebraicGeometry.GroupScheme.SimpleModuleDualHighestWeight`.
  Their signatures and proof docstrings were read. The primitive-line and
  Steinberg-irreducibility nodes currently have no Lean record, so no guessed
  modules for them are imported. They remain in the proof plan and DAG.

Edge cases checked before writing:

- Characteristic two: the half-sum equation is in the character lattice; no
  inverse of 2 in F is requested. The positive-characteristic branch permits
  p = 2 and ν = 1, hence m = 1.
- p = 0 is excluded in the positive-characteristic branch; p = 1 cannot satisfy
  `CharP F 1` for a field. Positive ν gives the required positive Steinberg weight.
- m = 0 and ν = 0 are outside the stated conclusions. The definition of the
  actual section subspace itself remains available at m = 0, as upstream.
- The trivial group/rank-zero case is retained: `Φ` may be empty and the split
  torus rank in `IsRhoBorelPair` may be zero. This gives the one-dimensional
  constant-function module and its ordinary dual.
- Nonreduced test algebras are included. Every scheme and coefficient algebra
  lives in the recorded universe u, including the coordinate algebra needed
  for the universal-point test. There is no independent smaller testing universe.
- The helper predicate also makes sense on the zero subspace; nonzeroness and
  finite dimensionality for the actual positive W are consequences of the
  rho-section dependency, not extra hypotheses here.

Searches made:

- `msearch.py leanfinder`: “The regular function induced module of weight m rho
  for a semisimple simply connected algebraic group is self dual in
  characteristic zero and at Steinberg weights”. Eight hits on root pairings,
  Lie modules and `FDRep.char_dual`; none states the group-scheme result.
- `msearch.py loogle`: `Representation.dual, Module.Dual`. Eleven hits include
  `Representation.dual` and `Representation.Equiv.dualTensorHom`. These construct
  duals of abstract-group representations; they do not assert the specified
  self-duality of the actual rational section module.
- `msearch.py grep`: `self.?dual|[Ss]teinberg|rho.*[Dd]ual` in
  `Mathlib/RepresentationTheory`. Three hits, in Character, Intertwining and
  Basic, none the requested statement.
- `rg` in project `Sheaf` and upstream `WeilConjectures` for rho-section duality,
  `IsContragredient` and `HasRationalLeftTranslation`, and literal blueprint-ID
  search in upstream, found the interfaces listed above and no existing theorem.
- The coordinate-comparison searches (LeanSearch, LeanFinder, Mathlib grep,
  project/upstream grep and blueprint search) are recorded with their returned
  output in the new node's `mathlib_searches`. They found the canonical Gamma
  and affine Hopf constructions, but no comparison between these two particular
  scalar structures. `blueprint_refs.py search "rho coordinate comparison"`
  returned zero matching nodes.

No statement correction or disputed statement is necessary. The two postponed
proofs are `rho_section_self_duality` and `coordinateScalarCompatibility`; each
has its matching DAG statement and a natural-language proof docstring.

## New nodes

`def-sfb-rho-coordinate-comparison` defines the identity algebra equivalence
between `RationalHighestWeight.coordinateAlgebra S` and `RhoSection.Coordinate S.X`.
Source: Milne Section 3a, the scalar structure on global functions by pullback
along the structure map, concretely Mathlib's `algΓ` and affine coordinate-Hopf
interfaces. The underlying ring equivalence is `RingEquiv.refl`; it is never
chosen from an existence theorem. Only its scalar compatibility is postponed,
as the named theorem explicitly included in this node's statement. The first
compile exposed distinct scalar instances even though the ring carriers agree.
The comparison solves that typing problem without changing F, S, W or the action.
Searches in its `mathlib_searches` show no existing node or exact declaration for
this bridge. The item directly cites this new definition node and imports its
module `Sheaf.AlgebraicGeometry.RhoCoordinateComparison`.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
