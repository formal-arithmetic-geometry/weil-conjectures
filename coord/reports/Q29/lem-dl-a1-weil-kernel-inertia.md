## Worker report

Item: lem-dl-a1-weil-kernel-inertia. Stage 2 only. The main module
Sheaf.Paper.WeilKernelHenselianInertia states
AlgebraicGeometry.Scheme.FiniteEtale.weilRestriction_ker_eq_henselianBoundaryInertia,
with its single proof `sorry`. The dependency module
Sheaf.Paper.HenselianBoundaryLocalData contains one structure with fully specified
local-field and homomorphism data, no sorry and no kernel-generation field.

Source read: Stacks pione.tex, Tag 0BTD, lemma-normal-pione-quotient-inertia,
including the three equal subgroups and proof; Tag 0BSW, lemma-identify-inertia,
including the preceding henselization diagram and residue kernel. Also read the
current blueprint rem-dl-a1-conventions.md, second paragraph, and d-real-boundary.md.
The main docstring reproduces all six proof steps, including the arithmetic
conjugation argument g = w d and the empty-boundary case. The two new proof nodes
for 0BTD and the henselian/global comparison have no Lean records yet, so there is
no module of either to import. Their proof roles are retained in the docstring.

Hypothesis and clause correspondence:

- k0 = F_q: `{k₀ : Type u} [Field k₀] [Finite k₀]`. Every finite field is covered;
  no characteristic or coefficient prime is imposed.
- C0 a smooth geometrically connected separated curve of finite type:
  `C : Scheme.{u}`, its structural morphism `p`, `[Smooth p]`,
  `[GeometricallyConnected p]`, `[IsSeparated p]`, `[LocallyOfFiniteType p]`,
  `[QuasiCompact p]`, and `hC : C.IsPureDimension 1`. The explicit structural
  morphism is the input needed by the recorded Weil group API.
- j0 a dense open immersion: `j : U ⟶ C`, `[IsOpenImmersion j]`,
  `hj : DenseRange j.base`. The structural morphism of U is precisely `j ≫ p`.
  No independent connectedness, normality, finite-type or curve hypothesis on U
  is added: these follow from the stated geometry. No separate finiteness of the
  boundary is assumed.
- S0 = C0 minus U0: index `x : ↥((Set.range j.base)ᶜ)`.
- Fundamental base point: `b : Spec (.of Ωb) ⟶ U`, `[Field Ωb] [IsSepClosed Ωb]`.
  It is arbitrary, with no generic-point assumption.
- W(U0) and W(C0): exactly the fibre-product expressions
  `(constantCoverAction ... (Aut (fiber ...))).weilGroup (geometricFrobenius ...)`
  that define the recorded scheme Weil group. As in the dependency's dense-open
  theorem, using the bodies of the abbreviations avoids an additional geometric
  connectedness assumption on U merely to elaborate the abbreviation.
- Induced degree-preserving homomorphism: `ρ` has those exact domain/codomain
  Weil groups. `hρ` fixes its pair formula to
  `(fiberAutBaseChange j b w.val.1, w.val.2)` for EVERY w, so it is the canonical
  map on the arithmetic component and the identity on the degree component.
  It is not an arbitrary degree-preserving homomorphism. The pair formula
  uniquely determines ρ; the recorded dense-open theorem supplies its existence.
- Local inertia of d-real-boundary: `L x : HenselianBoundaryLocalData j b x.val`.
  `H`, `isHenselization` give the existing local henselization universal property;
  `K`, `fractionK` its fraction field; `Ω`, `closureΩ`, `algClosedΩ` a chosen
  algebraic closure. The local integral closure has its genuine local-ring
  structure and residue algebraic closure. `integralAction_spec` characterizes
  restriction of every automorphism on every integral element;
  `residueAction_spec` characterizes reduction. Thus `residueAction.ker` is
  precisely ker(Gal(Kbar/K) -> Gal(kbar(x)/k(x))). The residue of H agrees with
  the stalk residue by the henselization universal property; the target model
  is the residue of the integral closure, a canonical model of its closure.
- The decomposition-group map: `localGenericPoint_spec` fixes the map from
  Spec K through the stalk of C and j. `path` is an arbitrary isomorphism of
  finite-etale fibre functors. `decomposition_spec` fixes the decomposition
  homomorphism by its transported action on EVERY finite-etale cover and
  EVERY fibre element, using exactly the formula in the existing landing
  theorem. No hypothesis about its image or the restriction kernel is assumed.
- Images of I_x in W(U0): the displayed set of w has `w.val.2 = 1` and a witness
  `σ : (L x).Ω ≃ₐ[(L x).K] (L x).Ω` with `residueAction σ = 1` and
  `decomposition σ = w.val.1`. In multiplicative integer notation 1 is degree
  zero. The landing lemma ensures these are precisely all inertia images;
  the pair coordinates make the lift unambiguous without adding a new map or
  assuming a landing theorem as part of the local datum.
- Kernel is the smallest closed normal subgroup containing all those images:
  `ρ.ker = (Subgroup.normalClosure (⋃ x, {...})).topologicalClosure`.
  Normal closure gives the least normal subgroup and its topological closure
  is again normal in a topological group. The topology is inherited from
  Aut(fiber b) times the discrete integer group, the usual Weil topology.

Dependency declarations read and used:

- d-real-boundary originally records
  WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary,
  AlgebraicGeometry.BoundaryDatum.conj, boundaryStalk_conj and
  boundaryStalkConjEquiv. Read the structure BoundaryDatum and those definitions
  and signatures. They concern abstract inertia subgroups with a kernel-equality
  field. The dependency supplement is described below.
- def-wf-weil-group records
  WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup,
  Scheme.FiniteEtale.constantCover, constantCoverAction, arithmeticFrobenius,
  geometricFrobenius, weilGroup, weilGroupDeg. Read their signatures and docstrings.
  Also read MonoidHom.weilGroup, weilGroupDeg and kerToWeilGroup in
  WeilConjectures.GroupTheory.WeilGroup: the product's second coordinate is
  Multiplicative ℤ and identity is zero degree.
- lem-wf-dense-open-pi1-surjective records
  Sheaf.Paper.DenseOpenPiOneSurjective,
  Scheme.FiniteEtale.weilGroup_dense_open_surjective (and geometric/other clauses).
  Read the full signature/docstring of its first three declarations: its Weil
  clause supplies exactly the pair-characterized map used here.
- Local presentation reuses Algebra.IsHenselizationAtPrime' in
  Sheaf.RingTheory.GeneralizedHenselizationAtPrime, and the genuine integral
  closure/residue constructions of Mathlib. Read its universal property in full.
- Read RealSheaves.exists_boundary_decomposition_landing in
  Sheaf.Paper.RealBoundaryDecompositionLanding: local fields, integral action,
  residue action and fibre formula are exactly its interfaces, packaged in a
  structure so an independent presentation can be supplied for every x.
- Read RealSheaves.boundary_local_constants in
  Sheaf.Paper.RealBoundaryLocalConstants, including its reduction characterization
  and arithmetic-square conclusion, for the proof plan's conjugation step.
- Read Scheme.FiniteEtale.fiberAutBaseChange in
  Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleWeilTransport, the canonical
  whiskering/conjugation construction used by hρ. Pure dimension is the existing
  Scheme.IsPureDimension in Sheaf.AlgebraicGeometry.PureDimension, not a copy.

Edge cases checked before writing and on rereading:

- Empty S0 / j = identity: the union is empty, its normal closure and closure are
  trivial; canonical restriction is an isomorphism and its kernel is trivial.
- Empty U is excluded by density and geometric connectedness of C; no redundant
  nonemptiness hypothesis was added. The empty curve is excluded by geometric
  connectedness, even though pure dimension alone is vacuous on an empty scheme.
- C may be nonproper and need not be affine; no compactification assumption occurs.
- Boundary residue degree greater than one is permitted: no rational-point
  hypothesis or choice of degree-one local Frobenius was introduced.
- All characteristics, including characteristic two, and arbitrary local paths
  are permitted. The arithmetic conjugation argument uses finite residue degree,
  not a false assertion that the Weil subgroup is closed in the profinite group.
- Both signs of integer degree and zero degree are retained by the fibre product.
- Local maps cannot be replaced by trivial arbitrary maps: all are constrained by
  their elementwise formulas, and the residue action is fixed on a surjective
  quotient. No assumption of ker ρ generation appears anywhere in the local data.

Searches actually made (msearch.py, group Q29, this item):

- leanfinder: "The kernel of restriction of Weil groups of an open smooth curve
  is the closed normal subgroup generated by henselian local inertia": 8 hits,
  including ValuationSubring.inertiaSubgroup, IntermediateField.restrictNormalHom_ker,
  IsDedekindDomain.selmerGroup.valuation_ker_eq and absolute Galois commutator
  closure. None is this curve or Weil kernel theorem.
- loogle: `Subgroup.normalClosure, MonoidHom.ker`: 7 hits on presented groups and
  presentation kernels, no curve/Weil or henselian inertia match.
- grep: `WeilGroup|normalClosure.*inertia|inertia.*normalClosure`: 0 Mathlib hits.
- rg of WeilConjectures and Sheaf for the old theorem name, boundaryInertia,
  henselian inertia and the proposed local structure names: found the old
  BoundaryInertia.lean and current RealBoundaryDecompositionLanding/LocalConstants
  interfaces, no exact statement or package of local data. The old theorem at
  BoundaryInertia.lean:559 uses boundaryInertia at :456, built from integral-closure
  inertia. It has no henselian comparison, as the item's split_report and
  reviewed note explicitly diagnose. It cannot be attached as an exact match.
- `grep -rn lem-dl-a1-weil-kernel-inertia lean/WeilConjectures`: no hits.

No source or item statement correction was needed. Only the item's lean record
and the unusable d-real-boundary interface record are changed. No new DAG node.
Both files compiled separately in dependency order using the prescribed
scompile.py against the live server; final result rc 0, no warnings or errors.
The only postponed proof is the item theorem. Structure data contain no sorry.

## Dependency modules

`d-real-boundary`: the prior record names BoundaryDatum.conj and invariant/path
conjugation operations in the upstream Boundary module. BoundaryDatum.inertia is
an unconstrained family constrained jointly by the kernel-generation field
ker_restrict_eq, rather than being defined from henselian residue kernels.
Using it here would assume the very theorem being stated. Under §1(B),
Sheaf.Paper.HenselianBoundaryLocalData publicly imports the original module and
supplements it with Scheme.FiniteEtale.HenselianBoundaryLocalData. It packages
precisely the henselization, local fraction field, residue Galois homomorphism,
canonical local generic point and path-induced decomposition map specified in
d-real-boundary and the existing decomposition-landing interface. Its fields
contain the defining equations, never a generation assumption. Existing direct
image, invariant and conjugation declarations remain accessible through the
public import, and no private replica of the henselization, fundamental group,
Weil group, residue field or inertia kernel is introduced. The dependency JSON
changes in lean only and explains this interface defect in lean.note.

## Second reading by Q29

Final worker rereading (the dispatcher explicitly prohibits starting other agents;
the maintainer's independent reading follows delivery). I reread the item, the
three statement dependencies, both complete delivered modules and the source
places listed above. The first compile exposed that IsAlgClosure does not make
IsAlgClosed globally available to instance search; the local datum now exposes
that already implied instance so its geometric fibre functor elaborates.
The final server compilation was clean. I checked that rho is fixed on both
coordinates; L is supplied independently for every boundary point; the residue
kernel is the actual reduction kernel; the decomposition map is fixed on all
finite fibres; the inertia lift is degree zero; and normal closure is taken
inside the Weil group with the discrete-degree topology. No original geometric
hypothesis or conclusion clause was removed, and no generation hypothesis was
added. No statement correction, new node or additional sorry was introduced.
