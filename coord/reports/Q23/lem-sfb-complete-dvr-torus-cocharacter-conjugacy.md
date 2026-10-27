## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.CompleteDVRTorusCocharacterConjugacy`
states `AlgebraicGeometry.completeDVR_torus_cocharacter_conjugacy`, with `sorry` as
its entire proof. It constructs no new notion. The accepted natural-language
statement and six-step proof are unchanged. The proof docstring transcribes all
six steps, including the residue-field rational containment, integer-exponent
lifting, twisted action, compatible square-zero lifts, affine effectivity and
Laurent coefficient separation.

Source read: Alper--Halpern-Leistner--Heinloth, *Cartan--Iwahori--Matsumoto
decompositions*, author-hosted https://sites.math.washington.edu/~jarod/papers/iwahori.pdf,
Remark 3.5, printed p.5 (PDF page index 4). Its forward implication is the
integral-conjugacy input isolated by this node. The accepted split supplies a
separate proof through residue-field containment and fixed-point lifting; no
additional claim from the remark's referenced proof is used here.

Hypothesis and clause correspondence:

- The commutative DVR is `A : Type u`, `[CommRing A]`, `[IsDomain A]`,
  `[IsDiscreteValuationRing A]`. This is the recorded Mathlib local principal
  ideal domain with nonzero maximal ideal; fields and the zero ring are excluded.
- The specified uniformizer is `π : A` with
  `hπ : IsLocalRing.maximalIdeal A = Ideal.span ({π} : Set A)`. In a DVR this
  is exactly the recorded uniformizer condition, equivalently irreducibility.
- Completeness through the canonical map to the inverse limit of the quotients
  is `[IsAdicComplete (Ideal.span ({π} : Set A)) A]`. This is the dependency's
  companion notion. Index zero adds the trivial quotient and does not change
  the inverse limit over positive indices.
- `H S : Grp (Over (Spec (.of A)))` are actual group objects in A-schemes,
  with multiplication, identity, inverse and their diagrams. This uses the
  recorded `CategoryTheory.GrpObj` through its bundled `Grp` form over Spec A.
  It does not use the field-restricted subgroup predicates on the ring base.
- Smoothness, affineness and finite type of H are respectively
  `[Smooth H.X.hom]`, `[IsAffine H.X.left]`, and
  `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`.
- `hred` tests every algebraically closed field `Ω : Type u` and ring map
  `f : A →+* Ω`. The pullback group object is the geometric fibre over that
  map. `ReductiveTorusCentralizer.IsReductive` supplies geometric connectedness
  and absence of nontrivial smooth connected normal unipotent subgroups, using
  the existing faithful-matrix unipotence predicate. Its affine/smooth/finite
  type clauses are already consequences of the global hypotheses by base
  change, so add no mathematical restriction. The geometric fields live in
  A's universe, as in the landed Cartan consumer; residue fields, algebraic
  closures and their relevant finite-type geometric tests all fit there.
- `i : S ⟶ H` is a group-scheme homomorphism, and
  `[IsClosedImmersion i.hom.hom.left]` is precisely the closed inclusion.
- `r : ℕ` and the supplied group-scheme isomorphism
  `e : S ≅ RingGroupSchemes.splitTorus A r` encode the specified splitting.
  `splitTorus` is the actual finite product, including the trivial group at
  rank zero. `RingGroupSchemes.multiplicative A` is Spec of the Laurent
  polynomial ring, with the existing Laurent Hopf group law.
- `hmax` says that the pullback of i to every such geometric field is a maximal
  torus: closed torus inclusion maximal for inclusion of subgroup schemes,
  using `ReductiveTorusCentralizer.IsMaximalTorus` verbatim.
- The arbitrary cocharacter is `mu : RingGroupSchemes.multiplicative A ⟶ H`.
  No injectivity, nontriviality or separability condition is imposed.
- The existential `c : 𝟙_ (Over (Spec (.of A))) ⟶ H.X` is an integral H(A)
  point: the tensor unit in the over category is the identity of Spec A.
  `ν : RingGroupSchemes.multiplicative A ⟶ S` is the required cocharacter.
- `toUnit (RingGroupSchemes.multiplicative A).X ≫ c` is the canonical constant
  morphism with value c. The product and inverse in the Hom group give exactly
  `c mu c⁻¹`, and the right side `ν.hom.hom ≫ i.hom.hom` is the composite
  inclusion. This is equality of A-scheme morphisms. Both sides are group
  homomorphisms, so it is equivalently equality as group-scheme morphisms.
  Precomposing with every Spec B point gives the node's all-B-points formulation,
  including nonreduced and zero test algebras; the node states this as an
  equivalent interpretation, so no independent extra conclusion is needed.

Recorded dependencies used and sources inspected:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing` and
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, lines 58--60 and 93--98.
- `def-weil-pbc-adic-completion`: `IsAdicComplete`,
  `Mathlib.RingTheory.AdicCompletion.Basic`, lines 45--56.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, its bundled `Grp`, its
  morphisms and induced Hom groups, `Mathlib.CategoryTheory.Monoidal.Grp`.
  Read also `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`' group-scheme
  and closed-subgroup interfaces; the latter require a field and are used
  only inside the existing geometric-fibre predicates.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, lines 60--66.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, lines 39--45, and
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  lines 38--46. They are publicly available through the reductive terminology.
- `def-weil-connected-scheme`: `ConnectedSpace`,
  `Mathlib.Topology.Connected.Basic`, lines 705--708, inside `hred`'s recorded
  predicate. Its nonempty clause is retained.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, lines 43--47.
- Two existing landed definition nodes are added to `stmt_deps`, as explicitly
  permitted by brief-stage2 section 5. `def-sfb-split-torus-over-ring` supplies
  `AlgebraicGeometry.RingGroupSchemes.multiplicative` and `.splitTorus` from
  `Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing`.
  `def-sfb-reductive-torus-centralizer-terminology` supplies
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive` and `.IsMaximalTorus`
  from `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`.
  Read both nodes and the entire defining declarations and docstrings.
  The landed `splitReductive_dvr_cartan_decomposition` uses exactly these
  geometric-fibre interfaces over a DVR; this statement supplies its intended
  conjugacy prerequisite with compatible types, without importing that consumer.
- Proof dependencies `lem-pc-proper-base-change` and
  `def-weil-affine-spectrum`: the former's Proper module is imported privately;
  its Smooth clause and the latter's `AlgebraicGeometry.Spec` and `Spec.map`
  are already publicly available from statement imports. Read the recorded
  signatures and defining source. The proof nodes
  `lem-sfb-field-split-torus-rational-containment` and
  `lem-sfb-gm-fixed-square-zero-lifting` have no recorded declarations in the
  read checkout; they are proof prerequisites only, so no import is available
  yet. Their identifiers and full roles remain in the proof docstring.

Edge cases checked before writing: r=0 is allowed by `r : ℕ` and by the trivial
rank-zero product. The trivial cocharacter is allowed. No completeness or
characteristic condition is imposed on the residue field, which may be finite
or imperfect. The splitting concerns all fibres, not only the generic fibre.
The maximal torus must be geometrically maximal, not just maximal split over
the residue field; `hmax` retains the stronger, stated hypothesis. No generic
point or field of fractions is required in this statement. The all-algebra
interpretation retains nilpotents. Uniformizers cannot be zero in a DVR with
nonzero maximal ideal. All universe variables and binders are explicit and
`autoImplicit` is disabled.

Searches actually run:

- `msearch.py ... leansearch "Conjugacy of cocharacters into a fixed maximal split
  torus over a complete discrete valuation ring"`: eight hits about IsConjRoot
  and GroupExtension conjugacy; none concerns reductive group schemes over DVRs.
- `msearch.py ... leanfinder "Over a complete discrete valuation ring every
  cocharacter of a reductive group is integrally conjugate into a specified
  split maximal torus"`: eight hits on root-pairing conjugation, Lie coroot spaces
  and Hilbert 90; no group-scheme cocharacter conjugacy result.
- `msearch.py ... loogle '"IsLocalRing", "IsConj"'`: zero hits.
- `msearch.py ... grep 'cocharacter|torus.*conjug|conjug.*torus'
  AlgebraicGeometry`: zero hits.
- `rg` in `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry` for
  `Reductive|IsReductive|SplitTorus|Cocharacter|cocharacter|Unipotent|unipotent`:
  found the field cocharacter-conjugacy theorem, field reductive terminology,
  faithful unipotence and ring-base split-torus construction. The field theorem
  assumes an algebraically closed field, so is not this statement.
- Search for the exact node identifier in `lean/WeilConjectures`: no match.
  Search of `dag/lean_names_upstream.json` for splitTorus/Cocharacter/IsReductive:
  no match. Search of DAG node names and texts found the two already landed
  notion nodes used above. No new nodes or dependency repairs are needed.

No statement correction or statement dispute is required. The first compile
caught the reserved Lean token `λ` used as a binder; it was renamed `mu` without
changing any mathematical content. Only the theorem proof is postponed.

Validation: `scompile.py Q23 lem-sfb-complete-dvr-torus-cocharacter-conjugacy
<module>` passed both sandbox and final-module compilation (6.6 s and 4.5 s),
with no error or unexpected warning. No second worker was started: the dispatcher
brief explicitly prohibits subagents, and independent review is by the maintainer.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
