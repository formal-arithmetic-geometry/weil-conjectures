## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.FiniteJetNormalizerDetection` states
`AlgebraicGeometry.GroupScheme.finiteJet_normalizer_detection`, with its sole theorem
proof `sorry`. The five accompanying definitions are actual constructions from Mathlib's
ideal sheaves, powers, subschemes and pullbacks. They belong to this theorem's canonical
jet construction, are listed in `lean.declarations`, and introduce no alternative scheme,
group, connectedness, finite locally free or closed-subscheme notion. In particular no
jet group structure is assumed: in positive characteristic or at general orders a jet
need not be a subgroup.

The assigned node has no Lean record and no `reviewed_lean`. Its Q130 PASS is a
stage-1 split review. The inherited BLOCKED ending concerned that accepted split,
not a stage-2 delivery; brief-stage2 section 0 explicitly allows this handoff. No
repair note for this item was present. The node's statement, dependencies and proof
are unchanged; only `lean` is set.

Source read: Brian Conrad, *Reductive group schemes*, online at
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Proposition 2.1.6 and its
proof (printed pp.61--63) and the beginning of the proof of Theorem 2.3.6 (printed
pp.73--74). The latter identifies the normalizer using finite identity neighborhoods
before invoking its self-normalizer hypothesis for the quotient construction. The
former supplies universal density and finite flatness. Thus neither a self-normalizer
hypothesis nor connectedness of G is needed here.

Hypothesis correspondence:

- A commutative ring and its spectrum: `A : CommRingCat.{u}` and `Spec A`.
  This includes the zero ring. Every scheme and test scheme uses the same explicit
  universe u; there is no separate smaller test universe.
- Group schemes over S: `G H : Over (Spec A)` with `[GrpObj G] [GrpObj H]`.
  This is exactly the recorded `CategoryTheory.GrpObj` of def-sc-group-scheme,
  applied over the base of this node rather than only over a field. GrpObj itself
  has no field restriction, so no dependency-interface repair is needed.
- G affine, smooth and finitely presented over S: `[IsAffine G.left]`,
  `[Smooth G.hom]`, `[LocallyOfFinitePresentation G.hom]`. Since both source and
  base are affine, G.hom is affine, hence quasi-compact and quasi-separated;
  locally finite presentation is consequently equivalent to finite presentation
  here. No finite-presentation case has been discarded.
- The finitely presented closed subgroup: `(i : H ⟶ G) [IsMonHom i]`,
  `[IsClosedImmersion i.left] [LocallyOfFinitePresentation i.left]`.
  A closed immersion is quasi-compact and separated, so this is finite
  presentation, not an added quasi-compactness assumption. Closed immersion gives
  the monomorphism. IsMonHom supplies compatibility with the group law and unit
  (and therefore inverse). H is affine as a closed subscheme of affine G.
- Smooth H with nonempty geometrically connected fibers: `[Smooth H.hom]` and
  `[GeometricallyConnected H.hom]`. Mathlib's geometric connectedness requires
  `ConnectedSpace` after every field-valued base change, hence includes
  nonemptiness. This is equivalent to checking algebraic closures of residue
  fields. There is no connectedness requirement on G.

Clause correspondence, in the order of the conclusion's conjunctions:

1. For every `n` with `1 ≤ n`, both neighborhood structure maps satisfy the
   dependency's `Scheme.Hom.IsFiniteLocallyFree`. This is the node's finite,
   flat, locally finitely presented assertion.
2. `identityNeighborhoodIdeal K n` is literally the `(n+1)`st ideal-sheaf power
   of the kernel of `(1 : Over.mk (𝟙 S) ⟶ K).left`, the identity section.
   `identityNeighborhood K n` is its actual Mathlib closed subscheme with the
   composite map to S; `identityNeighborhoodι` is its actual closed inclusion.
   `baseChangedIdentity` is the pullback lift of that same identity. For every
   W the two ideal equalities assert that its `(n+1)`st kernel power is the
   pullback of the original jet ideal, for G and H separately. Mathlib's
   `Scheme.IdealSheafData.comapIso` identifies the subscheme of the pulled-back
   ideal with the pullback closed subscheme and respects its inclusion. Thus
   these equalities state formation commutes with arbitrary base change with
   its canonical quotient maps, rather than mere isomorphism of abstract schemes.
3. Conjugation preserves each G_n: for every W, g and every further test V over
   W the two displayed ranges are equal. The conjugation expression is exactly
   `(v ≫ g) * h * (v ≫ g)⁻¹` with h included from G_n. This includes the
   universal element W=G and hence the action itself. These are equality
   stabilizers of closed *subschemes*, not just their underlying sets of points:
   all V and all v are quantified, so Yoneda sees their scheme structures.
4. For every n the existential j is constrained by
   `j ≫ identityNeighborhoodι G n = identityNeighborhoodι H n ≫ i`.
   It is therefore the unique induced inclusion of jets, since the ambient
   closed inclusion is mono. Its closed immersion property and
   `Function.Surjective j.left.appTop.hom` give the coordinate-algebra quotient
   in its correct contravariant direction, from G_n to H_n.
   `baseChangedArrow j W` is the canonical pullback map preserving both
   projections, not an arbitrary selected comparison. Its map of global
   sections is surjective for every affine W. The assertion applies to every
   affine chart of any base-changed U_i, and is exactly the requested quotient
   after general base change. The ideal equalities of clause 2 identify these
   pullbacks with the newly formed jets.
5. The coordinate modules of every G_n and H_n are locally finite free: for each
   base point s there is an affine neighborhood U and finite bases indexed by
   `Fin M` and `Fin r` of the respective coordinate rings. Their scalar action
   is explicitly `(pullback.snd ...).appTop.hom.toModule`, the action induced by
   their structural maps to U, not a chosen abstract module structure.
6. The final existential gives a finite affine open cover `U : Fin k → S.affineOpens`,
   with coverage `∀ s, ∃ a, s ∈ (U a).1`; `n M r : Fin k → ℕ` are the local
   orders and ranks. For each chart it requires `1 ≤ n a`, `1 ≤ r a`, `r a ≤ M a`
   and finite bases over Γ(U_a,O) of the coordinate rings of both base-changed
   jets. This is finite constant rank, with no global constant-rank hypothesis.
   A general U_a-scheme is a `W : Over S` whose structural map factors through
   `(U a).1.ι`; this factorization is the displayed existential w. For every
   such W and every g the final iff equates the range-equality condition for H_n
   included into G with the same condition for H. Quantifying every V over W
   makes both conditions closed-subscheme equalities as in clause 3.
   This also states the same iff after *any* base change U'→U_a: any U'-scheme
   is already a U_a-scheme by composition, with the identical tests over W.
   No flatness, reducedness, Noetherian or affineness restriction is imposed on W.
   Together with clause 4 this covers the node's final quotient/base-change sentence.

Dependency declarations read and used (including through their defining imports):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`;
  `Mathlib.CategoryTheory.Monoidal.Mon`: `CategoryTheory.IsMonHom`;
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `CategoryTheory.GrpObj.Hom.group`.
  The full recorded group-scheme interface is documented in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, read for the interpretation.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, used by the existing
  `AlgebraicGeometry.GeometricallyConnected` in
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`. The latter is an existing
  property of the exact structural morphism, not a new predicate in this delivery.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`, whose definition extends
  IsFinite, Flat and LocallyOfFinitePresentation.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  used by the canonical inclusions of the affine open subschemes.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.map`
  and `pullback.lift`; scheme pullbacks from `Mathlib.AlgebraicGeometry.Pullbacks`.
- Construction APIs read in `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`,
  `Subscheme` and `Functorial`: `Scheme.Hom.ker`, ideal-sheaf powers,
  `Scheme.IdealSheafData.subscheme`, `subschemeι`, `comap` and `comapIso`.

Available proof dependency modules are imported without public visibility:
`WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward`,
`Mathlib.AlgebraicGeometry.Gluing`, `Mathlib.AlgebraicGeometry.Noetherian`,
`Mathlib.RingTheory.Noetherian.Defs`. Closed-immersion and finite-locally-free
proof dependencies are already statement imports. The four proof-only nodes
lem-sfb-smooth-section-finite-jets, lem-sfb-smooth-connected-subgroup-noetherian-model,
lem-sfb-finite-locally-free-source-factorization-locus and
lem-sfb-smooth-section-universal-jet-density have no recorded Lean module yet;
there is no existing proof import to add for them. No missing statement dependency
is being postponed behind one of these proofs.

Searches for reuse:

- msearch LeanFinder, query `Finite infinitesimal neighborhoods detect the normalizer
  of a smooth connected closed subgroup scheme`: 8 hits on abstract topological
  normal subgroups and Krull topology; no scheme-level finite-order result.
- msearch Loogle, `CategoryTheory.GrpObj, AlgebraicGeometry.Scheme`: 7 hits,
  including group objects under pullback, affine Hopf algebras, and smoothness of
  reduced field group schemes; none states jet normalizer detection.
- msearch LeanSearch, `A finite identity neighborhood of a smooth connected subgroup
  scheme has the same normalizer as the subgroup universally after base change`:
  8 hits, including Subgroup.normalizer and Subgroup.setNormalizer; no such
  group-scheme theorem. SetNormalizer alone would not supply the universal-test
  or jet constructions and is not a substitute for the claimed statement.
- msearch grep, `normalizer|infinitesimal` in Mathlib/AlgebraicGeometry: 2 comments
  on the formally unramified lifting criterion; no matching theorem or construction.
- rg on the project's WeilConjectures/AlgebraicGeometry and Sheaf/AlgebraicGeometry
  for infinitesimal, Jet, normalizer, conjugation, and definitions named with
  neighborhood/neighbourhood: no matching theorem and no general identity-jet
  construction. `RankOneRootInterfaces.normalizer` is field-based rational-point
  torus normalizer data; `BorelSchemeNormalizer` treats self-normalizing Borels;
  `AffineGroupDistributionCalculus.conjugationPolynomial` is polynomial test data.
  None supplies this arbitrary-base finite-jet statement. FormalHilbertStratumMinors
  uses finite polynomial jets, and completion thickenings are along other ideals.
- rg for `lem-sfb-finite-jet-normalizer-detection` in upstream WeilConjectures:
  no match. The five helper names are absent upstream and in Mathlib/Sheaf.

Edge cases checked before and after writing:

- A=0: Spec A is empty. The final cover permits k=0, and all rank conditions
  are then vacuous; no Nonempty hypothesis on S has been introduced.
- H=G and H=1: normalizer comparisons become the appropriate identical/all-G
  conditions; the trivial subgroup has rank-one jets on nonempty charts.
- Disconnected G is allowed. Only fibers of H are geometrically connected.
- Positive characteristic, nonreduced base and test schemes, arbitrary nonflat
  base change: no reduction or rational/geometric-point replacement is present.
- n=0: the helper constructions are defined, but the theorem asserts its
  conclusions only for n≥1 as the node requires. No need to give the jets group laws.
- Rank jumps are allowed between affine charts. The finite cover allows empty
  charts to be discarded and does not assert that the index set is inhabited.
- The subgroup inclusion j is fixed by its commuting equation, and all coefficient
  actions use the actual structural homomorphisms; there is no hollow choice.

No statement correction or STATEMENT-DISPUTED flag is needed.

Validation: prescribed scompile.py compiled the module in module mode both as
sandbox and library source, each in under 3 seconds, with no errors or warnings.

## Second reading by Q96

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
