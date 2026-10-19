## Worker report

Existing-declaration delivery: no new Lean module, definition, theorem or sorry.
The two predicates introduced by `sk-d-dl-a1-setup` already occur in
`WeilConjectures.DeligneLaumon.AffineLine.Defs`, lines 63–102, with docstrings
explicitly citing this blueprint item. The node's `lean.declarations` records
both `AlgebraicGeometry.WeilSheaf.IsGeometricallyConstant` and
`AlgebraicGeometry.WeilSheaf.IsUnramifiedAtInfinity`; the primary signature is
copied verbatim. The existing `rem-dl-a1-conventions` dependency records the
same two predicates (and its additional irreducibility predicate). Recreating
these definitions would violate the one-definition-per-notion rule.

Read the item's complete node, its current main-20261015 `_section.md`, every
statement-dependency node and recorded primary signature/docstring, the source
of both attached definitions, and the already delivered conventions report.
Confirmed `AffineLine.Defs` through `scompile.py --source`, not just the older
local checkout. No repair note for this item was found.

Hypothesis and clause matching, in source order:

1. The finite field is `{k₀ : Type u} [Field k₀] [Finite k₀]` in the existing
   definitions; `q` is its cardinality. The fixed geometric field is the
   algebraic closure used by `Scheme.Hom.geometricFiber`. The dependency's
   `FiniteFieldDatum` permits any specified model of that closure. The
   coefficient assumptions are `{l : ℕ} [Fact l.Prime]
   [Fact (ringChar k₀ ≠ l)]`, exactly primality and inequality to the base
   characteristic. An arbitrary universe `u` is retained.
2. The coefficient isomorphism `iota : Qbar ≃+* ℂ` belongs to the punctual-weight
   dependency. Neither of the two predicates being attached depends on a complex
   embedding. Not adding an unused embedding argument preserves their meaning.
3. `A₀` is `AlgebraicGeometry.affineLine k₀`, the existing one-coordinate
   `AffineSpace` over `Spec (.of k₀)`; the geometric affine line is its
   `Scheme.Hom.geometricFiber`. The primed affine line is a second copy of this
   same scheme, not a second construction. The chart in the infinity predicate
   is literally `ProjectiveLine.affineChart (Spec (CommRingCat.of k₀))`,
   whose coordinates are `[x : 1]` and complement `[1 : 0]`.
4. Geometric cohomology and geometric Frobenius reuse the recorded cohomology
   and Frobenius dependencies. In the existing sheaf realization the carrier
   lives on the geometric fibre, and `WeilSheaf.frobeniusPullback` is pullback
   by geometric Galois Frobenius, realized as inverse-Frobenius pushforward.
   The recorded common-stage complex is `IsoAlgebra` of the geometric
   Frobenius pullback, not the derived category of arithmetic Weil pairs.
5. Purity is the recorded `SfIsPunctuallyPureOfWeight`: its body reads
   `∀ y α, SfPunctualEigenvalue ... F y α →
   ‖iota α‖ = (Nat.card (Y₀.left.residueField y.val) : ℝ) ^ (w / 2)`.
   Thus it quantifies over closed points and every local geometric-Frobenius
   eigenvalue, with exactly the displayed norm and residue cardinality.
   The source's punctual upper bound replaces this equality by `≤`.
   This is a convention on eigenvalues; it is not an assertion that this
   inequality is definitionally the finite-filtration mixedness predicate.
6. The existing Tate construction is `tateTwistSheaf`, from the cyclotomic
   character with geometric Frobenius scalar `q⁻¹` on the Tate line.
   `tateTwist_weight_shift` has weight `w - 2 * n` for every integer `n`.
   Substituting `n = -1` gives exactly `w + 2`, including negative weights.
7. The open immersion has arguments `(j : U ⟶ affineLine k₀)
   [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))]` and
   `[U.Over (Spec (CommRingCat.of k₀))]`. The source uses these predicates on
   dense opens and lisse sheaves. Density and lisseness remain the standing
   situation, not additional conditions inside geometric constancy. The
   existing `LisseOnDenseOpen` bundle has `isDominant` and `lisse` fields.
8. Ordinary `j_*` is supplied by the recorded
   `qbarCurveWeilOrdinaryPushforward` and its forgetful comparison with
   `qbarCurveOrdinaryPushforward`. It is the right adjoint of ordinary inverse
   image on the sheaf heart; its section formula is `G(V ×_C U)`.
   This convention does not replace the ordinary image by `Rj_*`.
   The source's boundary-stalk identification is the separately recorded
   `lem-wf-boundary-stalk-invariants`, with inertia from `d-real-boundary`.
   The stale-record observation below is kept explicit.
9. `qbarCurveIntermediateExtension` supplies the curve statement
   `j_{!*}(F[1]) ≅ (j_*F)[1]`, with the identity restriction, boundary
   minimality, naturality and Weil compatibility. Its shifted ordinary image
   uses the geometric derived category and cohomological shift by `(1 : ℤ)`.
   It applies to the affine-line curve in the source. No new perverse-extension
   assertion is packaged in either of the two attached predicates.
10. Unramified at infinity is exactly `IsUnramifiedAtInfinity F j`.
    For the standard chart `ι` its body is an existential open `W` with
    `ι ⁻¹ᵁ W = j.opensRange` and `ι.opensRange ⊔ W = ⊤`, followed by
    `∃ G : WeilSheaf k₀ l W, G.IsLisse ∧ Nonempty (j'^*G ≅ F)`.
    The first equality fixes its affine part to `U₀`; the covering equality
    includes infinity. Together they force exactly `W = U₀ ∪ {∞}`.
    The restriction morphism `j'` is `IsOpenImmersion.lift` applied to
    `j ≫ ι`, not an arbitrary map. The isomorphism is in Weil sheaves,
    so it preserves Frobenius. No explicit lisseness argument on `F` is needed
    inside the predicate: restriction of such a lisse `G` is lisse.
11. The equivalent trivial-inertia description is the existing
    `lisse_extension_iff_trivial_inertia`, applied to the smooth curve
    `C₀ = U₀ ∪ {∞}` and boundary `{∞}`. Its statement says both that a lisse
    Weil extension exists exactly when inertia fixes every generic-stalk
    vector, and that the ordinary image then gives the uniquely compatible
    extension. This is a cited characterization, not a redefinition by a
    freely chosen representation.
12. Geometric constancy is literally
    `∀ V : (U ↘ Spec (.of k₀)).geometricFiber.Opens, ConnectedSpace V →
    ∃ n : ℕ, Nonempty ((V.ι)^*ᵃ[l].obj F.obj.carrier ≅
    ⨁ fun _ : Fin n ↦ ProEtale.AdicSheaf.unit l V.toScheme)`.
    `F.obj.carrier` forgets Frobenius; the finite biproduct is the finite sum
    of the constant adic coefficient sheaf. The quantification is over every
    connected geometric open. For connected `U`, taking the whole open says
    the geometric sheaf is constant. The constant-sheaf/trivial-monodromy
    interpretation is `galois_lisse_representations`. No Weil-equivariant
    trivialization is required, so the Frobenius module can be nontrivial.

Dependency declarations read (module; declaration):

- `Sheaf.Paper.FiniteFieldFiber`; `WeilConjectures.FiniteFieldDatum`,
  `.geometricFiber`, `.CoefficientDatum`.
- `Mathlib.AlgebraicGeometry.AffineSpace`; `AlgebraicGeometry.AffineSpace`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`;
  `AlgebraicGeometry.ProjectiveLine.TwistData`; the standard chart itself is
  in the publicly available `ProjectiveSpace.Charts` module.
- `Sheaf.Paper.CommonStageCompactWeilCohomology`;
  `WeilConjectures.commonStageCompactWeilCohomology`,
  `adicOrdinaryCohomology`, `adicCompactCohomology`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`;
  `WeilConjectures.FiniteFieldDatum.geometricFrobenius`.
- `Sheaf.Paper.SfWeilSheafComplex`; `WeilConjectures.sfWeilComplex`,
  `sfCommonStageWeilSheaf`, `sfCommonStageWeilFrobeniusPullback`.
- `Sheaf.Paper.LisseIntegralSmallCoefficients`;
  `AlgebraicGeometry.Scheme.LisseIntegralSheafOfUniverses`, retaining the
  rational/algebraic coefficient interfaces of `LisseAdicSheaves`.
- `Sheaf.Paper.AdicPunctualWeights`;
  `WeilConjectures.SfIsPunctuallyPureOfWeight`, `SfPunctualEigenvalue`.
- `WeilConjectures.WeilSheaf.TateTwist`;
  `AlgebraicGeometry.WeilSheaf.cyclotomicUnit`, `tateTwistSheaf`.
- `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift`;
  `AlgebraicGeometry.WeilSheaf.tateTwist_weight_shift`.
- `Sheaf.Paper.CommonStageCurveWeilMiddleExtension`;
  `WeilConjectures.qbarCurveWeilOrdinaryPushforward` and its forgetful comparison.
- `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary`;
  `AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_upperStar_middleExtension`
  (the record's primary declaration), `AlgebraicGeometry.BoundaryDatum.conj`,
  `.boundaryStalk`, `.boundaryStalk_conj`, `.boundaryStalkConjEquiv`.
- `Sheaf.Paper.CurveIntermediateExtension`;
  `WeilConjectures.qbarCurveIntermediateExtension`.
- `Sheaf.Paper.EtaleWeilFundamentalRepresentation`;
  `AlgebraicGeometry.Scheme.etaleFundamentalRep`.
- `Sheaf.Paper.LisseExtensionInertia`;
  `AlgebraicGeometry.WeilSheaf.lisse_extension_iff_trivial_inertia`.
- `Sheaf.Paper.GaloisLisseRepresentations`;
  `AlgebraicGeometry.Scheme.galois_lisse_representations`.
- `WeilConjectures.DeligneLaumon.AffineLine.Defs`;
  the two predicates already recorded by `rem-dl-a1-conventions`.

Presentation and dependency metadata observations: the existing predicates use
upstream `WeilSheaf`, `PadicAlgCl l`, and the canonical geometric closure.
The separately recorded cohomology, punctual-weight and perverse dependencies
also offer fixed-pair common-stage presentations and arbitrary chosen coefficient
closures. This delivery attaches the already existing two sheaf predicates; it
constructs no equivalence between these presentations, and asserts no equivalence
between a derived category of Weil sheaves and geometric Frobenius pairs.

The `lem-wf-boundary-stalk-invariants` record lists extra
`BoundaryChart.boundaryStalkEquivInvariants` declarations which were not found
in the `Boundary` source returned by `scompile.py --source` during this run.
Its primary declaration's docstring explicitly calls that finite-local-constancy
statement weaker than the full invariants comparison. This is a dependency-record
fault to flag for the maintainer, not evidence that the full comparison is proved.
Neither of the two attached definitions invokes this comparison: extension at
infinity is defined by a genuine lisse extension, and geometric constancy by the
actual geometric carrier. Consequently no duplicate comparison theorem or
unnecessary dependency repair is delivered, and this report does not claim that
the weaker declaration establishes the missing comparison. The `BoundaryDatum`
conjugation declarations were absent in the old local source but present in the
source retrieved through the prescribed wrapper, whose signatures were read.

Edge cases checked by reading the real definition bodies: zero rank is included
by `n = 0`; zero extends as zero. A geometrically constant rank-one object with a
nonidentity invertible Frobenius scalar satisfies constancy. Disconnected fibres
are checked on every connected open without imposing equal ranks on components.
When `j` is the identity affine chart, `W` must be all of the projective line;
extension is still required, so an Artin–Schreier local system ramified at infinity
is not automatically unramified. Kummer ramification on a punctured affine line
also need not vanish at infinity. No characteristic is excluded beyond `l = p`.
The empty scheme is not a dense open of the nonempty affine line, but the existing
predicates themselves need no artificial nonemptiness restriction. All real
weights and both positive and negative Tate twists remain covered.

Searches run on 2026-10-18:

- `msearch.py ... leanfinder "A Weil sheaf on an open affine line is
  geometrically constant or unramified at infinity if it extends lisse across
  infinity"`: eight Mathlib results, about formally unramified morphisms and
  affine limits; no matching Weil-sheaf predicate.
- `msearch.py ... loogle "IsGeometricallyConstant, IsUnramifiedAtInfinity"`:
  zero hits, unknown identifier `IsGeometricallyConstant`.
- `msearch.py ... leansearch "geometrically constant Weil sheaf unramified
  infinity affine line"`: eight results, including generic constant-sheaf
  predicates; none is either specialized Weil-sheaf condition.
- `msearch.py ... grep "IsGeometricallyConstant|IsUnramifiedAtInfinity|WeilSheaf"`:
  zero Mathlib hits.
- `rg -n` of the two predicate names in upstream DeligneLaumon and project
  `lean/Sheaf`: exact upstream definitions and their consumers, no private
  replacement in the side library. `rg -n "sk-d-dl-a1-setup"` upstream finds
  their source docstrings. `dag/lean_names_upstream.json` and the item's audit
  independently identify this existing module and both declarations.

Validation: the sandbox scratch probe uses `autoImplicit false`, imports only
`WeilConjectures.DeligneLaumon.AffineLine.Defs`, and `#check`s both fully
qualified predicates with all implicit arguments exposed. Both sandbox and
published-library checks passed cleanly (9.5 s and 18.7 s), without warnings.
It is a scratch check,
not a delivered module. The required delivery wrapper repeats those checks.
No statement correction, new node, dependency module or statement dispute.

## Second reading by N3

No second reading by a worker: the dispatcher brief forbids starting other
agents, and the maintainer's independent review reads this delivery.
