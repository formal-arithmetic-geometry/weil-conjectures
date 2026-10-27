## Worker report

Q116 states `lem-sfb-line-section-first-order-obstruction` in
`Sheaf.AlgebraicGeometry.LineSectionFirstOrderObstruction`. No statement correction
or dependency replacement was needed. All theorem proofs are `sorry`. Definitions
have real data. Choices of epsilon inclusion and coordinate comparisons are from
uniqueness statements; the trace is the residue-normalized trace in the recorded
Picard theorem, not an arbitrary perfect pairing. The helper declarations belong
to the canonical constructions explicitly specified in this item.

### Hypotheses and clauses

- The field is `{k : Type u} [Field k]`, algebraic closedness is `[IsAlgClosed k]`.
  `C : Scheme.{u}`, `f : C ⟶ Spec (.of k)`, `[IsConnectedCurve f]`, `[Smooth f]`,
  and `[IsHProjective f]` give exactly the smooth projective connected curve.
  Smoothness is explicit: `IsConnectedCurve` alone does not include it.
- `L : C.Modules` with `[L.IsInvertible]` is the line bundle.
  `DualNumber k` is A, and `lineDualBase f` is the actual scheme pullback along
  `Spec.map (algebraMap k A)`. `lineDualZero f` is its canonical reduction immersion,
  defined by the pullback lift of the ring reduction, not an arbitrary immersion.
- `LA : (lineDualBase f).Modules`, `[LA.IsInvertible]`, and
  `e : (tensorPullback (lineDualZero f)).obj LA ≅ L` give the deformation and fixed
  reduction identification. No trivialization of the whole deformation is assumed.
- `lineReduction` is adjoint to e, transported through the split projection p.
  `lineEpsilon` is multiplication by the actual image of `DualNumber.eps` under
  the structural map A → Γ(C_A,O). `lineInclusion` is the unique factor of epsilon
  through reduction. `lineEpsilonSequence_shortExact` states exactness of this
  actual sequence. `lineSectionBoundary` is its recorded ordinary-module
  connecting map, restricted from Γ(C,O) to k.
- `U : ι → C.Opens`, `hU : iSup U = ⊤`, and
  `a : (lineCech U (𝟙_ C.Modules)).cycles 1` specify the additive transition cocycle.
  `LineTransitionData.frame` and `.generator` are actual local line frames of LA
  on p inverse images. `.transition` consists of units t_ij on intersections.
  `.relation` is exactly e_A,j = t_ij e_A,i + epsilon(a_ij t_ij e_A,i).
  Applying the specified reduction gives e_j = t_ij e_i. The a_ij are the displayed
  components of a, identified with functions by `unitSectionsEquiv`. Thus an
  arbitrary class v is not supplied in place of the deformation class.
- `lineDeformationClass f U hU a` is the actual image of [a_ij] under the canonical
  ordinary-module Čech comparison. `lineCechComparison` uses `cechH1Map_natural`,
  whose `IsModuleCechComparison` characterization determines the map uniquely.
  No assumption that this particular cover computes all cohomology is made.
- For every `s : scalarCohomology f L 0`, the first conjunct of
  `line_section_first_order_obstruction` supplies a Čech cycle z whose components
  are a_ij times s restricted to the intersection, and whose canonical comparison
  image is `lineSectionBoundary ... s`. In the j-frame this is a_ij s_j e_j,
  equivalently t_ij a_ij s_j e_i. The second conjunct identifies the same class with
  `H¹(m_s)(v)`, using `scalarCohomologyMap f (lineSectionMap f L s) 1`.
- The differential module is exactly `f.relativeDifferentials`; the inverse is
  the recorded `dual L`. `lineResidueTrace` is chosen from
  `Scheme.picard_duality_one`, retaining its componentwise residue normalization.
  `lineCurve_relativeDimension` supplies the dimension-one specialization from
  the curve hypotheses; projectivity supplies properness.
- The third conjunct uses the exact recorded `picardTracePairing` for L and O_C,
  with this same trace. It holds for every t in H⁰(dual L tensor omega).
  This is H⁰(omega tensor L inverse) through the canonical symmetry of tensor.
  The section product st is the cohomology map of `dualMap m_s ▷ omega`, so no
  arbitrary multiplication map or unnormalized Serre equivalence is assumed.
- The fourth conjunct negates both the actual boundary and the deformation class
  in the same pairing equation. This expresses the simultaneous opposite Čech
  and boundary convention; it also covers characteristic two.
- `line_section_first_order_obstruction_model` quantifies over every two-term
  complex `E : CochainComplex (ModuleCat (DualNumber k)) ℤ`, using
  `E.IsStrictlyGE 0`, `E.IsStrictlyLE 1`, and `Module.Free` and `Module.Finite` on
  every term. This is finite free over A, not merely finite dimensional over k.
  `lineReducedComplex E` is termwise `ModuleCat.extendScalars` along A → k;
  its differential is exactly d_0. `lineTermReduction` is the actual tensor unit.
- A model comparison is an A-linear `φ : E ⟶ lineACech f U LA` with `QuasiIso φ`.
  `lineACech` is built from the actual LA section presheaf restricted along p,
  with its actual A structural action; it is extended by zero in negative degrees.
  An affine-intersection cover in this clause is only a presentation of RΓ, not
  an additional geometric hypothesis. Such covers exist for the given separated
  projective curve and its nilpotent thickening.
  `lineModel_chainRepresentative` states that every derived finite-free model
  admits this comparison. `lineModel_specifiedComparison` additionally lifts
  every specified derived isomorphism to the Čech representative, with equality
  after localization. Thus the formula applies to all specified derived models.
- The scalar coordinate comparison `lineACechForget` is uniquely normalized on
  every section coordinate, not an unspecified vector-space isomorphism.
  `lineModel_reducedComparison` states existence and uniqueness of β with
  β(red x) = red(φ x). The model theorem accepts exactly this characterized β
  and asserts it is a quasi-isomorphism. `lineModel_reduction_existsUnique`
  gives the same quotient construction for a k-linear epsilon-equivariant map.
- `IsLineModelComparison` pins c₀ and c₁ to the recorded
  `IsPicardScalarCechComparison` and the canonical `extendHomologyIso`.
  `lineModel_cohomologyComparison` supplies their existence; they are not arbitrary
  isomorphisms. The natural cohomology identifications are c_n after H^n(β).
- `lineModel_kernelCokernel` identifies cycles in degree zero with `kernel d_0`
  by the actual kernel inclusion and homology in degree one with `cokernel d_0`
  by the actual quotient map. The model theorem also states that homologyπ in
  degree zero is an isomorphism and every degree-one element uniquely lifts to
  a cycle. These facts give H⁰ = ker d_0 and H¹ = coker d_0.
- For every reduced cycle x the theorem asserts existence of a lift y. For every
  such lift y it asserts existence of z with d_A y = epsilon z, and for every
  such z and its reduced cycle z' the equality in the conclusion is precisely
  c₁(H¹β([red z])) = boundary(c₀(H⁰β([x]))). Thus epsilon inverse means the
  canonical identification epsilon E_A¹ = E¹, without choosing a division map.
  The universal quantification over y, z, E, φ, β and normalized comparisons
  states independence of lift, epsilon preimage, and complex model.

### Recorded dependencies used

- Mathlib `Field`, `IsAlgClosed`, `DualNumber` and `DualNumber.eps`.
- `WeilConjectures.AlgebraicGeometry.Curve`: `IsConnectedCurve` and its `IsCurve`
  parent; `Morphisms.Projective`: `IsHProjective` and its properness instance.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, the actual sheaf tensor and unit.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `RingedSpace.moduleCohomology`, with `scalarCohomology` and its scalar operations
  through `FieldLinearModuleCohomologyOperations`.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`; recorded dual, `dualMap`, `evalTensor`
  and `homOfGlobalSection` are reused, not copied.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `schemeDerivedCategory`; actual derived global sections use its same canonical
  sheaf-module category and `rightDerivedFunctor`, not a second derived category.
- The finite locally free dependency's sheaf notion is the recorded
  `SheafOfModules.IsFiniteLocallyFreeOfRank`. In the finite-free A-complex clause
  the objects are modules over A, so the exact module predicates are Mathlib's
  `Module.Free` and `Module.Finite`; this adds no rank or basis hypothesis.
- `Sheaf.AlgebraicGeometry.Curve.PicardDuality`:
  `Scheme.picard_duality_one`, `picardTracePairing`, `picardCohomologyZ` and the
  componentwise residue normalization. No private duality pairing is defined.
- Canonical interfaces additionally reused: `exists_tensorPullbackAdjunction`,
  `tensorPullback`, `pushforwardComp`, `pushforwardId`, `pushforwardCongr`,
  `RingedSpace.moduleCohomologyBoundary`, `cechH1Map_natural`,
  `IsModuleCechComparison`, `picardCechFunctor`, `IsPicardScalarCechComparison`,
  `ModuleCat.extendScalars`, `ModuleCat.extendRestrictScalarsAdj`, and
  `ComplexShape.embeddingUpNat`. All recorded proof-dependency modules are imported.

### Edge cases

The original convention gives lift_j minus lift_i and hence plus a_ij s_j; reversing
both conventions negates both sides. For the trivial deformation, a = 0 gives zero
boundary. A zero section or a zero dual section gives zero in the displayed pairing.
Characteristic two is allowed. H⁰ or H¹ may vanish; no positive genus or nonzero
section is assumed. Complex terms may have rank zero, and d_0 may have any rank.
Changes of lift give an image of d_0, so the cokernel class is unchanged. Different
A-linear comparisons of the same model induce the corresponding natural reduced
identifications; quantifying over all of them is essential. An empty cover would
force C empty and is incompatible with `IsConnectedCurve`, so no exceptional empty
curve hypothesis has been silently admitted. Empty intersections give zero sections.

### Searches and source checks

The prescribed `msearch.py` searches were run (raw results are in the sandbox's
`searches.jsonl`, not a delivered file):

- LeanFinder: “For an invertible sheaf deformed over dual numbers on a smooth
  projective curve, the boundary of a section is its Cech cocycle times the section
  and Serre duality identifies this with multiplication of sections”: eight hits,
  all cotangent-complex/differentials declarations; no matching theorem.
- Loogle: `"DualNumber", "homology"`: zero hits.
- Mathlib grep: `firstOrder|first_order|SerreDual|picardTracePairing` in
  `AlgebraicGeometry`: zero hits.
- LeanSearch: “The connecting map of a dual-number deformation of a line bundle
  on a smooth proper curve is cup product with its first cohomology deformation
  class”: eight hits (`DualNumber.lift`, cotangent connecting maps, and group
  cohomology), no matching geometric assertion.
- `rg` in upstream `lean/WeilConjectures` and project `lean/Sheaf` for the same
  first-order/duality/transition patterns, and the exact node id search: no exact
  existing assertion. Existing Picard, boundary, Čech, scalar and coefficient
  interfaces found by these searches were read and reused.

Read the full target statement and proof and every statement-dependency record and
signature. Read Stacks 0C6R in `more-morphisms.tex` (units 1+f), 0BS2 and 0BS4 in
`curves.tex` (natural duality), and the degreewise split cochain boundary description
011J/011K in `homology.tex`. The node's explicitly identified agent expansion is
rendered as stated, rather than attributed verbatim to 0C6R. No disputed statement
was found. No new nodes or dependency modules were necessary.

## Second reading by Q116

The dispatcher forbids additional agents; this is a separate self-review with the
node and final file open, not a claimed independent second worker. Checked each
clause above against the node. The initial unconstrained boundary/product maps were
removed in favor of canonical constructions. The model interface was strengthened
to an actual A-linear chain comparison, the uniquely reduced β, normalized scalar
Čech comparisons, and explicit kernel/cokernel identifications. The final statement
retains both the Čech and the arbitrary finite-free model clauses. Every helper
proof is a named theorem with source and complete proof docstring; no definition
contains postponed object data. The Lean file compiles via the prescribed server
wrapper; final delivery preflight supplies an additional independent check.

### Validation

The final file compiled cleanly through `scompile.py` in both sandbox and library
module modes. `deliver2.py --no-push` printed OK: commit `9cd0b671320` passed
maintainer preflight and per-file compilation. No node fields except `lean` changed.
