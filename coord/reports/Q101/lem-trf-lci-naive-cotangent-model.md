## Worker report

The module `Sheaf.RingTheory.NaiveCotangentComparison` states
`Algebra.CotangentResolution.Naive.exists_comparison`. All theorem proofs are `sorry`;
all definitions contain actual data. The auxiliary presentation records, coordinate
identifications and comparison record belong to this node's specified construction.
There are no independent new notions, new DAG nodes, dependency repairs or statement changes.

Clause-by-clause reading (the namespace below is `Algebra.CotangentResolution.Naive`):

- The ring map A → B is `f : Arrow CommRingCat.{u}`. Its endpoints are arbitrary
  commutative rings, with no nontriviality, Noetherian, flatness or finiteness assumption.
- The surjective A-algebra presentation P → B is `Presentation f`: `ring`, `base`,
  `augmentation`, `triangle`, and `surjective` give exactly that data. `extension P`
  packages those same maps as Mathlib's `Algebra.Extension.ofSurjective`.
- Polynomial A-algebras on any set, or their localizations, are
  `IsLocalizedPolynomial P`. This quantifies over an arbitrary `E : Type u`,
  a multiplicative subset `W : Submonoid (MvPolynomial E f.left)` and a map `a`
  whose coefficient map is `P.base`, and requires `IsLocalization W P.ring`
  for the algebra structure induced by `a`. Polynomial algebras occur by taking
  W = {1}. This includes polynomial algebras up to A-algebra isomorphism, not
  merely rings literally written as `MvPolynomial`. All rings and variable sets
  are in a common arbitrary universe, as in the recorded standard-resolution interface.
- J = ker(P → B) and J/J² are `RingHom.ker P.augmentation.hom` and `conormal P`.
  The latter is Mathlib's `Algebra.Extension.Cotangent`, not a second quotient.
  `kernelClass P ⟨h,hJ⟩` is its quotient map.
- Ω¹[P/A] ⊗_P B is `differentials P`, the symmetric tensor order
  B ⊗_P Ω¹[P/A], using `ModuleCat.extendScalars` and
  `CommRingCat.KaehlerDifferential P.base`. The latter is exactly the recorded
  KaehlerDifferential with the algebra structure induced by the specified map.
  `tensorGenerator P b x` is b ⊗ dx. The symmetry of modules identifies this
  with dx ⊗ b in the node.
- The differential [h] ↦ dh ⊗ 1 is `differential P`, using the existing
  `(extension P).cotangentComplex`. Its value on `kernelClass` is definitionally
  Mathlib's `cotangentComplex_mk`: 1 ⊗ dh. No arbitrary differential is supplied.
- `term`, `boundary` and `complex` construct the actual complex in degrees -1,0,
  with zero terms elsewhere. `conormalIso` and `differentialsIso` merely expose
  its coordinates. The three elementary helper theorems identify these terms and
  assert boundary² = 0; each has its matching clause in the node and a proof docstring.
- The standard L[B/A] is the dependency's `cotangentComplex C f`, for the supplied
  standard-resolution coherence data `C : Coherence`. We do not choose a derived
  object from an unconstrained existence assertion. Its underlying complex is
  `differentialComplex (C.differentials (C.standard f))`.
- `Comparison.comparison` is the map L[B/A] → Q(C(P)). Its canonicity is specified
  by `projection_zero`, `projection_neg_one` and `comparison_formula` for EVERY
  lift `a` of the standard presentation. These prescribe b ⊗ dx ↦ b ⊗ d(a(x))
  in degree zero and b ⊗ df ↦ b[a(d₀f-d₁f)] in degree -1. All remaining target
  degrees vanish. `lift_exists` ensures that the normalization is not vacuous.
  The proof arguments `hx` and `hx'` used to form kernel classes follow from
  augmentation compatibility; quantifying over them does not add a ring hypothesis.
- `Comparison.truncation` is an isomorphism
  Q(K.truncGE (-1)) ≅ Q(C(P)); `factorization` says the given map is the good
  truncation projection followed by that isomorphism. Mathlib's `truncGE` uses
  opcycles (the cokernel of the incoming differential) at -1, and zero below;
  it is not stupid truncation. We assert neither a complex isomorphism before
  localization nor a quasi-isomorphism of the entire L[B/A] with C(P).
- A compatible square of A, B and P maps is `q : f ⟶ g` and
  `h : PresentationMap q P P'`. `base` and `augmentation` are exactly its two
  commutative squares. `NaiveMap.map` is a chain map to the target restricted
  along q.right. `conormal_formula` gives [h] ↦ [h'] and `tensor_formula` gives
  b ⊗ dp ↦ β(b) ⊗ dp'. These formulas are specified even for localized presentations.
- `Comparison.naturality` is the required equation in D(B), using the recorded
  `cotangentMap C q` on L and the exact restriction-of-scalars functor on the
  target. `mapDerivedCategoryFactors.inv` identifies Q of the restricted complex
  with restriction of its derived object. No implicit base-change isomorphism
  or equality of coefficient rings is assumed.
- No vanishing below -1, finite generation of differentials, finite variable set,
  regular sequence or LCI assumption occurs in any field or theorem hypothesis.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`. The family of size assumptions is
  the one in the recorded cotangent-resolution interface; its standard instances
  exist for every ModuleCat in universe u+1.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`,
  `KaehlerDifferential.D`, `KaehlerDifferential.linearMapEquivDerivation`;
  its bundled map version is `CommRingCat.KaehlerDifferential` from
  `Mathlib.Algebra.Category.ModuleCat.Differentials.Basic`.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`,
  `MvPolynomial.algHom_ext`, `MvPolynomial.aeval`.
- `Sheaf.RingTheory.CotangentResolutionCoherence`: the full `Coherence` signature
  and its docstring were read, particularly `standard_spec`,
  `standard_resolution`, `differentials`, `complexGenerator`, `restrictComplex`,
  `cotangentComplex` and `cotangentMap`.
- The proof imports `Sheaf.RingTheory.PresentationsHomotopyEquivalent`
  (`Algebra.Extension.presentations_homotopy_equivalent`),
  `Mathlib.RingTheory.Smooth.Basic` (`Algebra.FormallySmooth.of_isLocalization`,
  `.comp_surjective`) and `Mathlib.RingTheory.Kaehler.Polynomial`
  (`KaehlerDifferential.mvPolynomialBasis`, its generator and derivative formulas)
  implement the recorded proof dependencies. The main theorem's docstring gives
  all ten steps of the node's proof, including the explicit degree -1 inverse,
  the square-zero localization lift and the semilinear naturality argument.

Source checks: read cotangent.tex lines 1937–2016 (08RB, 08UP), algebra.tex
lines 35200–35368 (the presentation square and 00S1), and 35692 onward (00S7).
The comparison orientation agrees with the explicit projection in 08UP.

Edge cases checked: the zero ring and the zero quotient are permitted; empty E
is the localization of A and can have zero differential module; infinite E has
no finite generation requirement; W may contain zero, allowing the zero
localization; identities and arbitrary maps of base and quotient rings are
allowed. Degree -1 is a cokernel rather than the unchanged standard term;
lower cohomology is unrestricted. The formulas also apply to b = 0 and h = 0.

Searches performed on 2026-10-19:

- msearch LeanFinder: `naive cotangent complex truncation conormal differentials
  polynomial presentation natural comparison`: eight hits, including
  `Algebra.Presentation.differentials.hom₁`, `.comm₂₃`,
  `Algebra.PreSubmersivePresentation.cotangentComplexAux`, and
  `Algebra.Generators.H1Cotangent.δ_eq_δAux`. None is the comparison with L[B/A].
- msearch Loogle: `Ideal.Cotangent, Algebra.Extension.cotangentComplex`:
  zero hits for the combined query. Read `Extension/Basic.lean` and
  `Extension/Cotangent/Basic.lean` directly: their conormal quotient and
  differential are reused here.
- msearch LeanSearch: `canonical projection cotangent complex to naive
  cotangent complex isomorphism truncation`: eight general truncation hits
  (`CochainComplex.truncateAugment`, `CochainComplex.quasiIso_truncGEMap_iff`,
  and related truncation isomorphisms); no cotangent comparison.
- msearch grep Mathlib/RingTheory: `cotangentComplex|naive.*cotangent`:
  25 hits, in Etale/Kaehler, Kaehler/JacobiZariski and Smooth files. These
  concern the existing conormal differential and its H1, not standard L[B/A].
- rg of upstream WeilConjectures and side lean/Sheaf for
  `naive.*[Cc]otangent|[Cc]otangent.*[Tt]runc|lem-trf-lci-naive-cotangent-model`:
  side hits include `PresentationsHomotopyEquivalent`, localization and
  conormal-basis modules; no upstream or side declaration states this node.
  Also checked the proposed namespace/module names against those source trees
  and `dag/lean_names_upstream.json`: no duplicate.

No STATEMENT-DISPUTED flag or node fault was found.

Validation: scompile.py compiled the complete module in both sandbox and library
modes in about four seconds each, with no errors or warnings. The delivery dry
run is recorded below after execution.

## Second reading by Q101

Author's second pass, with the node and full module open; the maintainer provides
an independent review. Checked each binder and clause against the mapping above.
The first pass needed the ZeroObject scope and two unused binder renames; these
were repaired and the module then compiled cleanly. The core semantic checks are:
actual Extension.Cotangent and the existing differential, good truncation through
πTruncGE, normalization on both standard-resolution generators for every lift,
and the full semilinear naturality square. The tensor order is symmetrically
reversed but represents the same module and formulas. Polynomial/localization
presentations are A-compatible and neither finite nor restricted to domains.
No mathematical statement mismatch or node correction was needed. No separate
agent was started, in accordance with the dispatcher brief.

Dry run: `deliver2.py Q101 lem-trf-lci-naive-cotangent-model --no-push`
returned `OK (dry run): commit 4a478c0b2d passes the preflight and compiles;
nothing pushed`. The dry run compiled the final imports in both sandbox and
library modes, with no errors or warnings.
