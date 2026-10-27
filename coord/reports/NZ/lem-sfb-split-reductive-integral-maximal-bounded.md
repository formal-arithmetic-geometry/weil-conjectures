## Worker report

The main module `Sheaf.AlgebraicGeometry.GroupScheme.SplitReductiveIntegralMaximalBounded`
states `AlgebraicGeometry.splitReductive_integral_maximal_bounded`, with precisely one
postponed theorem and its four-step natural-language proof. No theorem is proved.
The original mathematical statement is unchanged. Its stmt_deps gains the already
landed split-torus and reductivity terminology nodes and one new definition node.
No dependency interface needed repair and no statement correction was needed.

Hypothesis and clause correspondence:

- The ring R is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. Henselianity is `[HenselianLocalRing R]` and
  algebraic closedness of its actual residue field is
  `[IsAlgClosed (IsLocalRing.ResidueField R)]`.
- The fraction field is `(L : Type u) [Field L] [Algebra R L] [IsFractionRing R L]`.
  There is no topology, completeness or local compactness hypothesis.
- The normalized valuation extended to zero is
  `(v : AddValuation L (WithTop ℤ))`. Its zero value is already infinity by
  AddValuation's definition. The binder `hv` says its restriction to R is the
  integer-valued image of `IsDiscreteValuationRing.addVal R`, via `WithTop.map`.
  This specifies the valuation associated to this DVR, including normalization:
  a uniformizer has value one, every unit has value zero, and fractions are
  determined by multiplicativity. It is the stated normalized DVR valuation,
  not an arbitrary valuation on L, and adds no mathematical assumption.
- The model and its torus are bundled group objects `(D T : Grp (Over (Spec (.of R))))`.
  Their group laws and diagrams are those of `CategoryTheory.GrpObj`.
- Smoothness is `[Smooth D.X.hom]`, affineness `[IsAffine D.X.left]`, and finite
  type is `[LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom]`.
- The closed subgroup is `(i : T ⟶ D) [IsClosedImmersion i.hom.hom.left]`.
  Its splitting is `(r : ℕ) (e : T ≅ RingGroupSchemes.splitTorus R r)`.
- `hred` tests every map from R to an algebraically closed field Ω and requires
  `ReductiveTorusCentralizer.IsReductive` on the actual base-changed group.
  This predicate includes smooth affine finite type, geometric connectedness,
  and absence of nontrivial smooth connected normal unipotent closed subgroups.
  The recorded unipotence uses a faithful matrix representation and geometric
  points; it is not an abstract reductivity placeholder.
- `hmax` requires `ReductiveTorusCentralizer.IsMaximalTorus` on the actual
  base-changed inclusion for every such geometric point. This is the recorded
  closed torus with no properly larger torus, not merely a split subgroup.
- `ValuativelyBoundedPoints.genericPoints R L D` is the type of R-morphisms
  Spec L → D. The pullback universal property identifies it with G(L) for
  G = D ×_R Spec L, with the same pointwise group law.
- `ValuativelyBoundedPoints.integralPoints R L D` is the range subgroup of
  `pointsPrecomp D.X (toUnit ...)`. This is exactly generic restriction of
  D(R), not a chosen inclusion or an arbitrary homomorphism. For affine D over
  a domain it is injective, as explained in proof step 1. Using its range needs
  no additional injectivity theorem or sorry-bearing definition.
- `ValuativelyBoundedPoints.evaluation` pulls a global function on the generic
  fibre back along the actual point `pullback.lift x.left (𝟙 _) x.w`, then applies
  `Scheme.ΓSpecIso` to obtain its value in L. It quantifies over every regular
  function on G, including functions with denominators from R. For affine G,
  these global sections are precisely L[G].
- `IsBounded` is `∀ f, ∃ n : ℤ, ∀ x ∈ M, (n : WithTop ℤ) ≤ v (evaluation ... x f)`.
  The bound may depend on f and is uniform over x. The first conjunct applies
  this to the integral subgroup. The second conjunct quantifies over every
  subgroup M and says boundedness and containment of the integral subgroup
  imply equality. Thus both conclusions, and the exact containing-subgroup
  maximality formulation, are preserved.

Dependency declarations read and used:

- Mathlib.RingTheory.DiscreteValuationRing.Basic: `IsDiscreteValuationRing`,
  `IsDiscreteValuationRing.addVal` (read the defining signatures and valuation docstring).
- WeilConjectures.Mathlib.RingTheory.Henselian: the recorded henselian terminology;
  `HenselianLocalRing` is the Mathlib class reexported there. Read that class and
  `IsStrictlyHenselianLocalRing`; only henselianity is assumed explicitly.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`, reached through the
  recorded reductivity module; algebraic closure is `AlgebraicClosure` as recorded.
- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj` and `Grp`, over Spec R.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `AlgebraicGeometry.Smooth`.
- Mathlib.Topology.Connected.Basic: `ConnectedSpace`, used by recorded reductivity.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing:
  `AlgebraicGeometry.RingGroupSchemes.splitTorus` and its Laurent Hopf multiplicative group.
- Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology:
  `ReductiveTorusCentralizer.IsReductive`, `ReductiveTorusCentralizer.IsMaximalTorus`;
  also read the referenced `SolvableGroupStructure.IsAlgebraic` and `IsUnipotent` bodies.
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Spec`;
  Mathlib.AlgebraicGeometry.Pullbacks: `pullbackSpecIso` and scheme pullbacks;
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, `pullback.lift`.
  These realize the already recorded affine spectrum and fibre-product proof inputs.
- Sheaf.AlgebraicGeometry.GroupScheme.SplitReductiveDVRCartanDecomposition:
  `AlgebraicGeometry.splitReductive_dvr_cartan_decomposition` (proof-only import),
  read in full including its source and proof-plan docstring.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPoints:
  `AlgebraicGeometry.pointsPrecomp`, the existing actual restriction homomorphism.
- Mathlib.RingTheory.Valuation.Basic: `AddValuation` for the established
  integer-with-infinity additive valuation, rather than another valuation definition.

Edge cases checked before writing: rank zero uses the recorded zero-fold product
and no coordinates; the proof then makes t the identity. The trivial reductive
group is included. An empty model is excluded by its group identity over the
nonempty spectrum of a DVR; connectedness is the existing nonempty connectedness.
Zero regular functions and zero evaluations have value infinity and satisfy every
finite lower bound. Nonzero constants have their own finite bounds. Negative
valuations and all positive powers are included; a uniform bound for both torus
coordinates and inverses forces valuation zero. Equal and larger bounded subgroups
are both covered. No restriction on residue characteristic is present. All scheme,
ring and geometric-test universes are explicitly bound as u, as in the landed
Cartan interface; each geometric fibre has an algebraic closure in that universe,
so these tests are not vacuous. `autoImplicit false` is set in both modules.

Searches: msearch.py leanfinder queried the full maximal-boundedness statement
(8 unrelated valuation, inertia, Selmer and adele subgroup hits); loogle queried
`"Valuation", "Subgroup"` (scalar additive subgroup and discrete-value-group hits);
grep queried `maximal.*bounded|hyperspecial|SplitReductive` under AlgebraicGeometry
(no hits). Additional leansearch queried regular-function valuation boundedness
(scalar valuation subgroup hits), leanfinder queried bounded group-scheme generic
points (integrality and S-integers), and grep queried
`valuat.*bound|bound.*valuat|integralPoints|pointsPrecomp` (valued topology and
unrelated scalar inequalities). Exact service outputs are in the new node's
mathlib_searches as recorded by msearch.py. Local rg searched the DAG, all
lean/Sheaf and lean/WeilConjectures for these notions and the item's id. No exact
existing statement or boundedness definition was found. The searches did locate
the newly landed Cartan theorem and its shared split-torus definitions, which are
reused. `tools/blueprint_refs.py search bounded` found uses, not a definition node;
`ancestor` returns null for the inherited ancestry, which is retained.
The newest blueprint directory was searched; the mathematical source for this
auxiliary prerequisite is the Prasad--Yu paper, read online at
https://arxiv.org/pdf/math/0405381, Lemma 3.7 and Proposition 4.3. No unit statement
or source statement was altered. No STATEMENT-DISPUTED fault remains.

Validation: both files compiled separately, in dependency order, using only the
prescribed scompile.py server wrapper. The definitions have real data and no
postponed proof; the main theorem's sole `sorry` is intentional for stage 2.

## New nodes

`def-sfb-valuatively-bounded-group-points` owns
`Sheaf.AlgebraicGeometry.GroupScheme.ValuativelyBoundedPoints`. Its four
declarations introduce the actual generic point type, canonical range of integral
points, evaluation on the generic fibre, and regular-function valuation boundedness.
The source is Prasad--Yu Lemma 3.7 and Proposition 4.3 with the explicit boundedness
convention of the assigned node. Existing `pointsPrecomp`, scheme pullbacks,
`Scheme.ΓSpecIso` and `AddValuation` are reused, with no chosen map and no hollow data.
Searches above find no existing node or declaration defining this combination;
DAG statements using boundedness are not definition nodes. All four helpers
belong to this single notion. Generic points, integral ranges and evaluation are
naturally defined for commutative L as well; the boundedness predicate uses a field.
The item cites this definition node and the already landed split-torus and
reductivity definition nodes in its stmt_deps.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
