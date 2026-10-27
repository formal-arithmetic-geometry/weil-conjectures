## Worker report

The delivery states `AlgebraicGeometry.exists_flatLCIPresentationBaseChange` in
`Sheaf.AlgebraicGeometry.FlatLCIPresentationBaseChange`. Its proof is `sorry`.
All other declarations unpack this node's models and conclusions; their data are
actual records and composites, not choices from existence sorries. No mathematical
statement or dependency interface is corrected.

Hypothesis and clause correspondence:

- Schemes and morphisms are Mathlib `Scheme.{u}` and categorical morphisms.
  `[IsNoetherian S]` is the finite-affine-cover Noetherian condition, not just locally
  Noetherian. `[Flat f]` and `[LocallyOfFinitePresentation f]` are the recorded notions.
  `d : ℕ` includes zero. `hcover` says every point belongs to an open with a
  `FlatLCIPresentation f d U`. That existing record retains n,c, n=c+d, the actual
  open immersion into relative affine n-space, the closed immersion, its factorization
  through f, and length-c generators regular in the ambient local rings along U.
- `FlatLCIPresentation.RegularEquationsBaseChange` quantifies over arbitrary new
  schemes, the actual two cartesian squares, and every old affine chart with its
  given length-c regular equations. For every new affine chart mapping into that
  chart, it states equality of the new generated ideal with the new kernel ideal,
  `RingTheory.Sequence.IsKoszulRegular` of the pulled-back sections, and
  `IsRegular` in every prime localization containing the new ideal. This covers the
  local rings at every point of U'. Koszul-regularity quantifies over positive
  homological degrees on the entire affine ambient chart, including its complement
  of U'. The chart map is the actual `q.appLE`, not an arbitrary ring homomorphism.
- The second conjunct gives `PullbackStalkTensor.IsTorIndependent f B.b` for every
  cartesian base-change record B. This existing predicate quantifies over every pair
  of points with the same image and every positive Tor degree.
- `FlatLCIIntrinsicDeterminantData.chart` gives the conormal module C and restricted
  differentials V their ranks c,n on every presentation after every change of base.
  These are precisely the existing `FlatLCIPresentation.conormal` and
  `.differentials`, hence the recorded tensor pullbacks of the kernel ideal and
  relative differential sheaf. `model` is their actual two-term double complex;
  `differential_normal` is the formula [s] ↦ ds.
- `Comparison.bridge` identifies that double complex with the existing conormal model
  of the SPECIFIED `LciIdentifications` family E. Its negative and zero equations are
  identities on the actual modules. `restriction_inv` fixes open restriction by
  `CotangentPresentation.derivedChange`, so `Comparison.iso` is the intrinsic
  conormal comparison, rather than an arbitrary global map agreeing on affines.
- `twoTerm`, `intrinsic`, and `system.invertible` identify the system's line with
  the determinant of this intrinsic cotangent complex on every base change.
  `baseIso` and `base_normal` state invertibility of the natural derived comparison
  for every cartesian arrow among these bases. Its hom is exactly `derivedChange`
  of the canonical ring-sheaf square furnished by `D.square`.
- `base_determinant` identifies the system's base-change map with, in order, tensor
  pullback of the intrinsic identification, `T.pullbackIso`, and the determinant of
  this same `baseIso`. This renders both arrows in the displayed intrinsic formula.
- `local_normal` says the local line comparison is inverse `modelIso`, determinant
  of the fixed intrinsic conormal comparison, and inverse determinant restriction.
  Thus it is the displayed `(∧^c C)^∨ ⊗ ∧^n V`, using the actual sheaf exterior
  power, internal Hom dual and monoidal tensor.
- `LocalCompatibility` constructs a `FlatLCIPresentationPullback` for each cartesian
  pair of old/new ambient charts (with equal c,n). Its existing ideal and universal
  differential section formulas specify the canonical maps, on all ideal sections
  and all ambient differentials, hence in particular on equation classes and dx_j.
  `IsFlatLCIPullbackDeterminantComparison` says those two maps are isomorphisms and
  sends a pulled-back dual normalized basis wedge tensor a differential basis wedge
  to its new counterpart. This fixes the inverse-transpose direction on the dual
  conormal exterior factor. The source pullback modules therefore also have ranks c,n.
- Presentation transitions are the composites of `system.localIso` through the one
  global line. `local_normal` identifies them with determinants of the specified
  intrinsic conormal comparisons. `system.localBaseChange` is defined by these same
  local comparisons and the same global base-change map. Consequently its composites
  with two transitions agree, by cancellation of the intermediate local comparison:
  delta_j ◦ g^*t_ij = t'_ij ◦ delta_i. This applies after restriction to every common
  open, including nonaffine overlaps. No extra unspecified transition is supplied.
- `FlatLCIAdjunctionSystem.identity` and `.composition` give the identity and
  composition equations for exactly these base-change maps with the normalized
  `tensorPullbackSectionId`/`tensorPullbackSectionComp`. Together with
  `localBaseChange` they give the same equations for local expressions.
- No new base has an `IsNoetherian`, flatness, finite-presentation, separatedness,
  nonemptiness, or finite-type hypothesis. The universal derived-category and
  cotangent/determinant construction parameters are the dependency interfaces;
  their existence is already stated independently of this geometry.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Noetherian: `IsNoetherian` (locally Noetherian + compact).
  Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing` is Noetherian over itself.
- Mathlib.AlgebraicGeometry.Morphisms.Flat / FinitePresentation / ClosedImmersion:
  `Flat`, `LocallyOfFinitePresentation`, `IsClosedImmersion`.
- Mathlib.RingTheory.Regular.RegularSequence: `RingTheory.Sequence.IsRegular`,
  including the nonzero final quotient, and `IsWeaklyRegular`.
- WeilConjectures.RingTheory.KoszulRegularSequence:
  `RingTheory.Sequence.IsKoszulRegular`, positive-degree homology of the actual
  `ExteriorAlgebra.koszulComplex`.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction:
  `tensorPullbackSectionAdjunction`, `tensorPullbackSection`,
  `tensorPullbackSectionId`, `tensorPullbackSectionComp`; the functor itself is the
  actual tensor construction publicly imported from
  WeilConjectures.AlgebraicGeometry.TensorPullback.
- WeilConjectures.AlgebraicGeometry.Modules.Differentials:
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsDerivation`.
- Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf: `exteriorSheaf`, `exteriorSheafSection`.
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom:
  `SheafOfModules.homObj`; WeilConjectures.AlgebraicGeometry.Modules.Dual:
  `Scheme.Modules.dual` is its abbreviation.
- WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`.
- WeilConjectures.AlgebraicGeometry.BaseChangeConventions: the actual pullback
  scheme and maps, with `Scheme.Modules.moduleBaseChange` the induced module pullback.
- Sheaf.AlgebraicGeometry.LciCotangentPresentation: `System`, `BaseSquare`,
  `LciPresentation`, `LciIdentifications`, `Properties`, `conormalTerm`,
  `ambientDifferentials`, `IsKoszulImmersion`, `cotangent`, `derivedChange`.
- Sheaf.TraceFormula.CanonicalTwoTermPerfectDeterminant: the recorded canonical
  `TwoTermPerfectDeterminantData.IsCanonical`; its imported data module supplies
  `TwoTermDeterminantModel`, `twoTermDeterminantValue`, `twoTermDeterminantIso`, and
  the normalized `modelIso`, `pullbackIso`, identity and composition comparisons.
- Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction: ONLY the definition records
  `FlatLCIPresentation`, `FlatLCIBaseChange`, `FlatLCIAdjunctionSystem`,
  `FlatLCIPresentationPullback`, their maps, and
  `IsFlatLCIPullbackDeterminantComparison`. These now have definition-only DAG
  attachments `def-sfb-flat-lci-base-change` and
  `def-sfb-flat-lci-adjunction-system`, both added to stmt_deps. No use of the
  parent canonical-adjunction existence theorem occurs. The owner module cannot
  acquire a reverse proof import of this item: that would make an import cycle.

The module imports all available proof dependency modules (some publicly because
also statement dependencies). `lem-trf-base-flat-polynomial-tor-bound` and
`lem-trf-relative-differential-sheaf-base-change` currently have no Lean record;
no declaration from them is needed to TYPE this statement. They remain in the
unchanged proof plan. Existing Mathlib proof leaves are imported by their recorded
files; `def-weil-pbc-koszul-complex` is publicly available through the Koszul API.

Sources opened: local Stacks divisors.tex, remark-relative-regular-immersion-elements
(0FUD); more-algebra.tex, lemma-relative-regular-immersion-algebra (0CEP);
cotangent.tex, lemma-flat-base-change-cotangent-complex (08QQ);
perfect.tex, remark-functorial-det (0FJY). The prime restriction in the node is
retained: regularity is only asserted at primes containing the equations, whereas
Koszul exactness is asserted everywhere.

Edge cases checked: c=0 and n=d=0 use empty finite sequences and exterior powers
of degree zero; the final nonzero quotient in regularity is only required at primes
of the closed locus. Empty X, empty opens, empty base changes, and the zero ring are
allowed; the Koszul assertion on a zero ring still holds. A chart missing U has unit
ideal and the contractible unit-equation case, not a falsely asserted regular sequence
in its local rings. Non-Noetherian S' and nonflat S'→S remain included. The flatness
hypothesis rules out the usual counterexample Z/(2) pulled back to F_2. Coordinates
and equations themselves are used by appLE and the universal-derivation formulas.

Searches (the exact wrapper outputs are in sandbox searches.jsonl):

- leanfinder: "Flat local complete intersection arbitrary base change regular
  equations conormal differential determinant cotangent comparison". Eight hits,
  chiefly standard smooth base change and cotangentComplexBaseChange injectivity;
  no regular-presentation intrinsic determinant theorem.
- loogle: "cotangentComplexBaseChange, IsRegular, tensorCotangentHom", then
  "cotangentComplexBaseChange". No exact hit (the latter identifier not indexed).
- leansearch: "regular sequence quotient flat arbitrary base change conormal
  determinant cotangent complex". Eight hits: regular sequences under faithfully
  flat changes and flat scheme base change; none states this arbitrary-base
  regular-equation/conormal/determinant assembly.
- msearch grep, RingTheory: `cotangentComplexBaseChange|IsKoszulRegular|tensorCotangentHom`.
  Hits include Ideal.tensorCotangentHom and its flat equivalence and the naive
  cotangent linear map, not the full statement; their source signatures were read.
- rg of lean/WeilConjectures and lean/Sheaf for flat.lci/FlatLCI/flatLCI and this
  node id found the existing presentation records and parent theorem; neither
  states this full intrinsic presentation-base-change lemma. Exact new declaration
  searches in both source trees and dag/lean_names_upstream.json found no collision.
- rg of dag/nodes found the newly attached definition-only sfb nodes, which are reused.
  `tools/blueprint_refs.py search 'regular presentation'` found no blueprint match.
  No new definition node is necessary.

Validation: scompile.py compiled both the isolated sandbox name and the intended
library module successfully. The only initial elaboration issue was Lean-generated
record projections unfolding the irreducible cotangent System. Keeping its existing
`System.model` accessor locally opaque resolves this without changing any interface.
The delivered signature has no auto-bound variables or file-local notation/instances.

## Second reading by Q119

A separate self-check pass reread the node and the final source (no sub-agent was
started, per dispatcher instructions). The independent mathematical review remains
with the maintainer. Checked the n=c+d condition, regularity only along the closed
locus, whole-chart Koszul exactness, ranks on both sides, actual ideal/differential
maps, inverse transpose on the dual factor, and the common intrinsic maps underlying
local transitions and base-change identity/composition. Checked the bridge equations
against `LciIdentification` and the line equations against `modelIso`/`pullbackIso`.
The extra sfb records are existing definitions, not the downstream adjunction theorem.
No discrepancy requiring a statement correction or dependency repair was found.
