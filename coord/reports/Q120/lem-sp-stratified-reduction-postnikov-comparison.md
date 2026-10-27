## Worker report

The delivery states `AlgebraicGeometry.ProEtale.sp_stratified_reduction_postnikov_comparison`
in `Sheaf.Paper.StratifiedReductionPostnikovComparison`. It uses ordinary unbounded
`DerivedCategory` of actual ringed-site module sheaves. Every theorem proof is `sorry`.
All definitions contain actual constructions or choices determined by a universal
property, with named proof obligations. No mathematical statement correction is made.

The input prime, finite extension and ring of integers are `l`, `Fact l.Prime`, `E`,
`Field E`, `Algebra ℚ_[l] E`, `FiniteDimensional ℚ_[l] E`, and
`Padic.coefficientExtensionIntegers l E`. Both the scheme and field are in a common
ambient universe u; the actual pro-etale site retains object universe u+1 and Hom
universe u. No equality between those site universes is imposed.

The requested rings are `spStratifiedRing`, literally `limit (spCoefficientCommRings ...)`,
and `spStratifiedScalar n` with its existing constant ring sheaf. Index n means exponent
n+1, so every positive exponent is included. `spStratifiedScalarMap` is the limit lift
of the actual quotient maps. `spStratifiedRingMap` is the limit lift of inverse-image
projections followed by canonical finite constant-section comparisons; its named
invertibility assertion supplies `asIso`, without choosing an arbitrary ring map.
`spStratifiedPull` is the existing exact ringed inverse image with that scalar transport.
`spStratifiedReductionModel` is the existing universal cochain-derived scalar extension,
including the ordinary sheaf tensor object/map equations, K-flat computation and counit.

The finite cohomological interval is `r s : ℤ` and `hsupport`, which says exactly that
homology vanishes outside [r,s]. No r≤s assumption is added. `P` is the recorded
`Scheme.FiniteLocallyClosedStratification T`; `hconstructible` separately requires each
stratum constructible. Its domains, actual immersions, images, disjointness and covering
are retained. `hlocal` applies `HasFiniteConstantRingedLocalModel` to the restriction
of every q-th homology sheaf. The scalar presentation is chosen over O_E before
extension, not over an arbitrary sheaf-section ring.

For each original stratum a and each n, the conclusion supplies a natural isomorphism
of the full functors `spStratifiedReducedPull` and `spStratifiedPullReduced`.
`SpStratifiedComparisonFormula` pins it on K-flat representatives to the universal
counits and `spStratifiedOrdinaryComparison`. The latter is uniquely pinned to the
pure-tensor formula, including the quotient coefficient action. `NatTrans.CommShift`
states compatibility with shifts; the derived scalar model is triangulated and
restriction is exact. Thus the natural iso is compatible with distinguished triangles.

The canonical sequence is `t.triangleLTLTGELT q (q+1)`, for r≤q≤s. Its first two
objects are τ<q M = τ≤q-1 M and τ<q+1 M = τ≤q M. The third is canonically double
truncated cohomology, and the explicit third-vertex isomorphism identifies its image
with the image of `(singleFunctor ... 0).obj (H^q M)⟦-q⟧`. `F.mapTriangle.obj Δ`
is asserted distinguished. The first endpoint `F(τ<r M)` is zero; the image of
`truncLEι s` is invertible, fixing the final endpoint as F(M). The four per-k
finitely-presented locally constant predicates cover all three vertices and the
shifted fourth term. Over the finite scalar ring finite presentation equals finite
type. The final all-k predicate includes F(M), even when r>s makes the sequence
empty. Its cohomology vanishes outside [r-1,s]. No τ(F M) appears.

The separate `sp_stratified_reduction_homology_comparison` gives the required
per-degree corollary: its maps are homology of the components of the same normalized
derived natural isomorphism, with invertibility asserted.

Finally each reduced homology is `IsConstructibleProEtaleModuleSheaf`. The additional
quantification over the original P, all n and all k explicitly gives local constancy
and finite geometric stalks on this same partition. No qcqs, Noetherian scheme,
étale-origin, completeness or flatness hypothesis on M is added.

Dependency declarations used: `Sheaf.Paper.SmoothPurityCoefficientTowers` supplies
`spEllIdeal`, `spCoefficientConstantQuotient`, `spCoefficientRings`;
`Sheaf.Paper.SmoothPurityCoefficientTowersAbelian` supplies `spCoefficientCommRings`;
`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` publicly supplies
`SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem;
`Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification` supplies the given partition;
`Sheaf.Paper.ProEtaleFixedModuleConstructible` publicly retains the intrinsic
`IsConstructibleProEtaleModuleSheaf`; `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
supplies the normalized constant-ring comparison and exact module pullback;
`Sheaf.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModels` supplies the existing
finite-type local condition (equivalent here since the scalar ring is finite Noetherian);
Mathlib's `DerivedCategory.TStructure.t`, `triangleLTLTGELT`, homology and single functors
supply the canonical derived structures. The ordinary tensor-generator API is
`SheafOfModules.systemModelTmul`; the actual inverse-image section API is
`AlgebraicGeometry.ProEtaleTensorComparison.inverseSection`. Proof imports include
all recorded available proof modules and Mathlib localization/homology interfaces.
The matrix reduction proof dependency has no Lean record and is used in the proof
docstring only: it is not an unstated notion needed to type this statement.

Edge cases read against the formula: zero M; empty T including a single empty stratum
and an empty partition; r=s; r>s (support forces M=0); n=0 representing exponent one;
ramified E; torsion constant model O_E/π (the degree r-1 contribution must remain);
free and zero local models; arbitrary non-qcqs and non-Noetherian schemes with the
given partition; positive finite-type modules over the zero ring as a harmless
coefficient-site convention. The separate all-k endpoint clauses preserve the zero
case when there are no q with r≤q≤s.

Searches (2026-10-24): msearch LeanFinder on derived coefficient reduction commuting
with exact inverse image/finite Postnikov filtration gave eight unrelated homological
and restriction results; Loogle `DerivedCategory, CategoryTheory.Sheaf` gave no hit;
grep `Postnikov|[Cc]onstructible|locally[Cc]onstant` in Mathlib/Algebra/Homology gave none;
LeanSearch on restriction/reduction and finite Postnikov filtrations gave unrelated
complex restrictions. For the dependency scalar local-model interface, LeanFinder
on extension from a finitely presented constant scalar module found general
`SheafOfModules.IsFinitePresentation` and quasicoherent presentations, which permit
arbitrary section matrices and do not say finite constant scalar model; Loogle
`SheafOfModules, Module.FinitePresentation` and Mathlib grep gave no exact match.
Repository rg in WeilConjectures and Sheaf and DAG searches found the existing
condensed internal model and the section-matrix model, neither accepting the literal
limit ring of this item; the added dependency interface retains the original via
public import and states its scalar-extension characterization directly.

## Dependency modules

`sk-def-sfb-constructible`: its recorded `HasFiniteConstantLocalModel` accepts internal
modules over a pulled-back condensed ring. The item uses ordinary module sheaves over
the literal ell-power limit. The new `Sheaf.Paper.FiniteConstantRingedLocalModel`
publicly retains every original declaration and adds `HasFiniteConstantRingedLocalModel`,
the scalar-extension formulation in clause (1), parametrized by its actual scalar
ring map. It uses a covering sieve on the terminal site object and on each member
an isomorphism to extension of a finitely presented scalar module. This is equivalent
to the cover formulation because pro-etale coverings are stable under base change.
Only the dependency's `lean` record is changed.

## Second reading by Q120

The dispatcher explicitly prohibits starting another agent. This is a separate second
reading by the same worker, not an independent-agent review. The maintainer's requested
independent review remains necessary. I reopened the node and compared every clause
against the final signature: the hypothesis list has exactly the given partition,
constructibility, local models and support; all n and all degrees share P; every
triangle is the image of the original truncation triangle; endpoint, shifted fourth
term, [r-1,s], finite stalk and no geometry hypotheses are explicit. The comparison
was strengthened in its *specification*, not its mathematical content, by the
pure-tensor representative equation so a scalar-twisted arbitrary isomorphism cannot
stand for the canonical comparison. Empty and zero cases do not require P.n>0.
No statement dispute was found.
## Repair of return H2

The returned delivery was reviewed at immutable head `82d4d7ba8956`. Compared with
the current base, the delivered item changes only `lean` and `stmt_deps`; the
existing dependency repair changes only its `lean` record. This repair updates the
item's declaration ownership edges as requested, using definition nodes already on
the current base. The Lean modules and their mathematical statements are unchanged.

- Replaced `lem-pur-system-scalar-model` with
  `def-weil-pbc-system-scalar-model`, whose existing declaration record owns
  `SheafOfModules.SystemScalarModel` and `SheafOfModules.systemModelTmul` in
  `Sheaf.CategoryTheory.SystemScalarModel`. The statement uses the pure-tensor
  definition; it does not use the scalar-model existence theorem.
- Added `def-sfb-proetale-inverse-image-unit-section`, which owns
  `AlgebraicGeometry.ProEtaleTensorComparison.inverseSection` in
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`.
- Added `def-weil-proetale-inverse-image`, which owns
  `AlgebraicGeometry.Scheme.proEtaleCoefficientInverseImageMap`,
  `AlgebraicGeometry.Scheme.proEtaleCoefficientDirectImageMap`, and
  `AlgebraicGeometry.Scheme.proEtaleConstantModulePullback` in
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- Added `def-pc-kflat-complex`, which owns
  `CochainComplex.IsKFlatIndependentCoefficients` in
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.

I read these owners' current node records and the declarations' full signatures and
docstrings. Their data are exactly the existing constructions used by this item;
no new notion or node is needed. The existing imports already expose them. Both
delivered modules are recompiled against the current live build before the repaired
delivery, followed by the required dry run.
