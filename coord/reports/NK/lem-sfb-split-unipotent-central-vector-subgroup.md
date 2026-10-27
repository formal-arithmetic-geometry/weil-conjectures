## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SplitUnipotentCentralVectorSubgroup`
states `AlgebraicGeometry.exists_splitUnipotent_central_vector_subgroup` with a single
`sorry` proof. No definition, construction, or auxiliary theorem is introduced.
The natural-language statement and accepted proof split are unchanged.

Clause-by-clause reading:

- The arbitrary field is `{k : Type u} [Field k]`; there is no characteristic,
  perfection, infinitude, or algebraic-closedness hypothesis.
- A group scheme is `U : Grp (Over (Spec (.of k)))`. Its actual group object
  structure, multiplication, inverse and identity are the recorded `GrpObj` interface.
  `hU : SolvableGroupStructure.IsAlgebraic U` means exactly affine, locally of
  finite type, and quasi-compact, i.e. affine of finite type.
- `hunipotent : SolvableGroupStructure.IsUnipotent U` includes smoothness and
  a closed group embedding in a finite-dimensional GL whose matrices over all
  algebraically closed extensions satisfy `(r(x)-1)^N = 0` for a positive N.
- `hsplit : ∃ n : ℕ, SplitUnipotentLength U n` gives the finite descending
  smooth connected closed subnormal series with represented fppf G_a quotients.
  Each connected group term has its identity rational point. The existing
  `GeometricallyConnected.of_connectedSpace_of_section` therefore makes each
  term geometrically connected, exactly as required by the inline definition in
  this item. This equivalence introduces no weaker notion or additional assumption.
  `IsFppfQuotient` identifies the actual kernel and is flat, surjective and locally
  finitely presented, hence gives the stated represented fppf coset sheaf.
- `hne : ¬ Nonempty (U ≅ Grp.trivial _)` means U is not the trivial group scheme;
  it does not assert that U(k) has two distinct rational points.
- `s : ℕ` and `MultiplicativeType.splitTorus k s` give E=G_m^s, including s=0.
  `[a : ModObj E.X U.X]` supplies a k-morphism E times U to U and the internal
  unit/associativity diagrams. `hautomorphism` says on every commutative
  k-algebra that action by e preserves multiplication. The action of e inverse
  is the inverse by the action identities, so this is exactly action by group
  automorphisms, including identity and inverse preservation. No unrelated map
  replaces the action. Mathlib's monoidal left self-action is the tensor product,
  the categorical product on this over-category.
- `∃ d : ℕ, 1 ≤ d` is the required positive integer dimension.
- `∃ (C : Grp ...) (i : C ⟶ U)` together with
  `IsClosedSubgroupScheme i.hom.hom` gives the closed k-subgroup, with actual
  group homomorphism inclusion. Affineness and finite type of C follow from this
  closed immersion into U; they are not extra hypotheses.
- `Smooth C.X.hom ∧ GeometricallyConnected C.X.hom` states the two prescribed
  geometric properties. Mathlib geometric connectedness includes nonemptiness.
- `Nonempty (C ≅ ∏ᶜ (fun _ : Fin d ↦ Grp.mk (StandardGroupSchemes.additive k)))`
  is a k-group isomorphism with the categorical power of the recorded G_a.
  It has no linearity or equivariance condition, as required.
- The first parenthesized universal conclusion quantifies over every R, every
  e in E(R), and c in C(R), and gives `c'` mapping to `a(e,i(c))`. This is
  scheme-theoretic stability: it holds on all algebras, including nonreduced
  ones, rather than just on geometric or rational points. Since the inclusion
  is a closed immersion, the lift is unique and natural; testing on the affine
  coordinate algebra of E times C shows precisely factorization of the
  restricted action morphism through C. Inverses of e give equality, not only
  one-sided preservation. The restricted action identities follow by monicity.
- The final universal conclusion is literally
  `x * (c ≫ i.hom.hom) * x⁻¹ = c ≫ i.hom.hom`, for every R, x and c.
  Thus centrality is on all algebra points and retains nilpotents.

Dependency declarations read and used:

- `Field` in `Mathlib.Algebra.Field.Defs`.
- `CategoryTheory.Grp`, `GrpObj` and `Grp.trivial` in
  `Mathlib.CategoryTheory.Monoidal.Grp`; `Grp` packages the dependency's group object.
- `IsClosedSubgroupScheme` and its `IsSubgroupScheme` parent in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `LocallyOfFiniteType`, `QuasiCompact` in the corresponding Mathlib morphism
  modules; `Smooth` in `Mathlib.AlgebraicGeometry.Morphisms.Smooth`;
  `ConnectedSpace` in `Mathlib.Topology.Connected.Basic`.
- `StandardGroupSchemes.affine`, `additive`, `additiveGroup`, `multiplicative`
  and `multiplicativeGroup` in `Sheaf.AlgebraicGeometry.StandardGroupSchemes`.
  Their definitions fix the actual coordinate Hopf laws of G_a and G_m.
- `SolvableGroupStructure.IsAlgebraic`, `IsUnipotent`, `IsFppfQuotient`
  in `Sheaf.AlgebraicGeometry.SolvableGroupStructure`.
- `SplitUnipotentLength` in
  `Sheaf.AlgebraicGeometry.GroupScheme.SplitUnipotentSeries`.
- `MultiplicativeType.splitTorus` in
  `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`.
- `GeometricallyConnected` in `Mathlib.AlgebraicGeometry.Geometrically.Connected`;
  `ModObj` in `Mathlib.CategoryTheory.Monoidal.Mod`; group-object finite products
  in `Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits`.

The item gains four already-landed definition dependencies naming the existing
interfaces now used: `def-sfb-solvable-group-structure`,
`def-sfb-split-unipotent-series`, `def-sfb-tori-multiplicative-type`, and
`def-pc-geometrically-irreducible`. This is the authorized addition of landed
statement dependencies, not a change to the mathematical statement.

The available proof dependencies are imported privately:
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`
(`GeometricallyConnected.of_connectedSpace_of_section`),
`WeilConjectures.AlgebraicGeometry.GroupScheme.Cartier`
(`smooth_of_grpObj_of_charZero`, resolved from its closed audit),
`Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange`
(`exists_affine_group_centre_baseChange`),
`Sheaf.AlgebraicGeometry.CharZeroCommutativeUnipotentVectorGroup`
(`charZero_commutative_unipotent_vectorGroup`), and
`Mathlib.RingTheory.Flat.Basic` (`Algebra.TensorProduct.includeLeft_injective`).
The other proof-only nodes have no recorded module or usable declaration at this
reading: identity-subgroup, geometric unitriangular embedding, perfect-field
central-additive subgroup, cckp kernel criterion and vector/wound factor.
No statement depends on those postponed proofs, and their proof steps are retained
in the declaration docstring for stage 3. Their later modules can be imported when
stated. No import cycle was introduced.

Edge cases checked before writing: U=1 is excluded scheme-theoretically; U=G_a
allows C=U and d=1, including finite fields; s=0 is the rank-zero split torus
with its unit action; d=0 is excluded by the positive lower bound; the empty
scheme cannot be a group scheme over a field and cannot satisfy geometric
connectedness. Inseparable and imperfect fields in positive characteristic are
included. Nonlinear polynomial group automorphisms of a vector group are allowed.
All test algebras have the same universe u as k and the schemes, avoiding a
quantification over a separately too-small universe. Finite powers use Fin d,
which imposes no size restriction. The connected-series interface is equivalent
to the item's geometrically connected series because every term is a group over k.

Searches for an existing statement (all via msearch.py with this group and item):

- LeanFinder: `A nontrivial split unipotent algebraic group over a field has a
  nonzero central vector subgroup invariant under a split torus action`.
  Eight hits, about special-linear group centres, Lie algebras and invariant
  vector spaces; none states the scheme-theoretic result over arbitrary fields.
- Loogle: `GrpObj, IsUnipotent`. No hits; unknown identifier GrpObj at that
  endpoint. This unsuccessful name query alone is not treated as absence evidence.
- Mathlib grep: `unipotent|Unipotent`, subdirectory `AlgebraicGeometry`.
  Zero hits.
- LeanSearch: `A split unipotent algebraic group over an arbitrary field has a
  nontrivial central vector subgroup invariant under a split torus action`.
  Eight hits, about abstract group centres, central series and representation
  invariants; none has this statement.
- Local rg in `lean/WeilConjectures` and `lean/Sheaf` for `IsSplitUnipotent`,
  `SplitUnipotent`, `splitUnipotent`, unipotence, vector groups, actions and
  the exact node id found the landed split-series and solvable terminology,
  and the characteristic-zero vector-group theorem, but no existing version
  of this arbitrary-field torus-invariant central-subgroup theorem.
  The upstream declaration-name index likewise has no declaration with this name.
  The closed-subgroup and standard group modules were opened in full.

Source check: read the latest blueprint direct-images proof (3) and its unit,
then the node's complete accepted proof. Read Conrad--Lichtenstein Appendix D.3
p.86 online at https://math.stanford.edu/~conrad/252Page/handouts/alggroups.pdf
(the maximal characteristic central vector subgroup argument) and Conrad
Theorem 2.6/Corollary 2.7/Definition 3.1/Proposition 3.2 online at
https://math.stanford.edu/~conrad/papers/appbnew.pdf. These support the arbitrary
field statement and do not require linearity of the chosen vector coordinates.
No statement dispute, correction, hollow definition or unusable dependency found.

Validation: scompile.py compiled the sandbox module and its library-name form
cleanly (33.4 s and 2.1 s). The initial failed compile revealed the missing
`open scoped MonObj`, required for the existing groups on Hom sets; it was added.
Every variable and universe is bound explicitly, with autoImplicit disabled.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
