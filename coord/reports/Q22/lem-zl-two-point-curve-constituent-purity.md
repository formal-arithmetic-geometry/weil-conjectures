## Worker report

Delivered module: `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity`.
Main declaration: `WeilConjectures.twoPointCurveConstituentPurity`.
The sole postponed proof is that theorem, with the eight proof steps from the node in its
docstring. All auxiliary definitions contain actual data or explicit predicates. There
is no arbitrary local operator, no chosen lattice, and no Frobenius-stable integral-lattice
hypothesis. No mathematical statement correction or dependency-module repair was needed.

I read the complete item, its statement dependencies and their records, their recorded
interfaces and docstrings, and the current source
`literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`,
paragraphs 2--4. The older upstream real-sheaf theorem only states mixedness and its
curve-testing theorem has another coefficient category: neither states this node.

Hypothesis and clause correspondence:

- The prime power, finite field and algebraic closure are `D : FiniteFieldDatum.{u}`.
  The distinct prime is `l`, `[Fact l.Prime]`, `hl : l ≠ D.p`. The algebraic closure
  of Q_l is `Ω : Type v`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`,
  `[IsAlgClosure ℚ_[l] Ω]`. The specified isomorphism is `iota : Ω ≃+* ℂ`.
  Scheme and coefficient universes are independent.
- `X₀ : Over (Spec (.of D.k₀))` is the finite-field model; the actual geometric scheme
  is `(D.geometricFiber X₀).left`. `LocallyOfFiniteType` and `QuasiCompact` encode the
  standing finite-type convention of the weights node. `IsAffine X₀.left`,
  `GeometricallyConnected X₀.hom`, `Nonempty X₀.left`, `hd : 1 ≤ d` and
  `SmoothOfRelativeDimension d X₀.hom` give all the geometric hypotheses.
  `IsSeparated X₀.hom` is automatic for the affine source and affine field spectrum;
  it supplies the recorded characteristic-factor interface, not a restriction on X₀.
  On a connected smooth scheme the relative dimension is constant, so this d encoding
  includes every positive-dimensional smooth scheme in the node.
- The classical lisse Weil sheaf is `F : sfCommonStageWeilSheaf D l hl X₀ Ω` together
  with `hF : IsCommonStageLisse ... F.obj.carrier`; reality is exactly
  `hreal : SfIsReal D l hl Ω X₀ iota F`. The existing classical/completed and rational
  realization comparison nodes identify this lisse common-stage encoding with the
  classical sheaves, compatibly with pullback, Weil structures and fibres.
- The filtration is `r`, `G : Fin (r+1) → ...`, and the adjacent Weil morphisms `φ`.
  `hzero`, `hlast`, `hmono` and `hlisse` assert its zero endpoint, its endpoint F up
  to isomorphism, its inclusions and the lissity of all its terms. Its quotients are
  exactly `cokernel (φ j)` in the recorded abelian Weil heart. Thus no splitness or
  semisimplicity is assumed.
- `hirr` uses `TwoPointGeometricallyIrreducible` to assert lissity, nonzero, and no
  nonzero proper lisse geometric subobject. The latter quantifies over the actual
  `sfCommonStageHeart` and the underlying geometric carrier, forgetting Frobenius.
  It does not ask for simplicity among all constructible subsheaves (which would be
  wrong even for a constant local system with extension-by-zero subsheaves).
- The conclusion supplies a single `w : Fin r → ℝ`. Its first conjunct is
  `SfIsPunctuallyPureOfWeight ... (cokernel (φ j)) (w j)` for every j on all X₀.
  In particular this is exactly the final formula for every local eigenvalue β:
  `‖iota β‖ = (Nat.card (X₀.left.residueField x.val) : ℝ) ^ (w j / 2)`.
- For every closed `anchor`, every j and every nonzero punctual eigenvalue α, the
  second conjunct is `w j = 2 * Real.logb (Nat.card κ(anchor) : ℝ) ‖iota α‖`.
  It uses `SfPunctualEigenvalue`, so the eigenvalues are those of the recorded actual
  finite-stage H^0 geometric Frobenius after coefficient extension.
- The next conjunct quantifies over every positive m and every `TwoPointCurve`
  through any specified lift of the anchor. If any restricted quotient has purity
  weight v, it asserts `v = w j`. This explicitly states independence of the curve,
  the finite extension, and the chosen anchor eigenvalue.
- The final conjunct quantifies over all closed `anchor x`, compatible residue
  embeddings `ιa, ιx`, and their compatibility equations `ha, hx`. These encode every
  chosen geometric lift, via the existing `localClosedPoint`, without identifying
  scheme morphisms that differ by a field automorphism.
- It supplies `m`, `hm : 1 ≤ m`, and `C : TwoPointCurve ... m hm` simultaneously for
  all the quotients. `C.curve` is over the actual subfield `D.extensionSubfield m hm`,
  `C.immersion` is into `constantExtensionModel`, and the fields `closed`, `affine`,
  `smooth`, `connected` assert precisely the stated curve properties. The finite-type
  and quasi-compact fields follow from being an affine closed curve and provide the
  coefficients/weights API. A curve is nonempty by geometric connectedness.
- The two existential factorizations through `C.geometricMap` say that its geometric
  image contains both chosen lifts. They include the coincident-lift case. Because
  the geometric immersion is over Spec k, these factorizations are automatically
  over k. Their image points on C are closed: their residue fields embed into k and
  are algebraic over the finite field, by the recorded closed-point-field criterion.
- `C.restriction` satisfies `ConstantExtensionRestrictionSpec`, which fixes its
  underlying functor and the m-fold Weil return on every object and arrow by the
  canonical geometric-fibre identification. It is not an uncharacterized functor.
  `C.pull` then composes this normalized constant restriction with the existing
  `zlWeilPull` of the closed immersion. No equivalence is chosen from mere existence.
- `C.Tests` asserts reality of `C.pull.obj F`, geometric irreducibility and punctual
  purity of every restricted quotient at w j, and uniqueness of its purity weight.
  It also gives the local power and residue-size clauses for F and every quotient,
  at every closed z over a closed x, including the two marked points.
- `C.arithmeticMap` is the closed immersion followed by the finite constant projection.
  `C.residueDegree z` is the actual field-extension `Module.finrank`, using the algebra
  structure induced by that map's `residueFieldMap`. `C.Tests` asserts it is positive,
  `#κ(z) = #κ(x)^f`, and equality of the spectrum at z with the multiset map
  `a ↦ a^f` of the spectrum at x. At the anchor this is e and at x it is f, as in
  the node. Multiplicities are retained, including eigenvalues whose powers collide.
- `twoPointSpectrum` is the roots of the reverse of the existing characteristic factor.
  Local Frobenius is invertible, so that factor has full degree and reversing it
  recovers the monic characteristic polynomial. This uses the same determinant and
  actual local operator as `SfIsReal`, not separate spectral input.

Dependency declarations used (all recorded source interfaces, with no private copies):

| Node | Module | Declaration/interface |
| --- | --- | --- |
| def-weil-punctual-weights | Sheaf.Paper.AdicPunctualWeights | SfPunctualEigenvalue, SfIsPunctuallyPureOfWeight |
| def-pod-lisse-l-adic-sheaves | Sheaf.Paper.LisseIntegralSmallCoefficients | Scheme.LisseIntegralSheafOfUniverses, classical systems used through the recorded realization comparisons |
| def-weil-weil-sheaf-complex | Sheaf.Paper.SfWeilSheafComplex | sfCommonStageWeilSheaf, sfCommonStageWeilComplex |
| def-wf-iota-real | Sheaf.Paper.AdicLocalCharacteristicFactor | SfIsReal, sfLocalCharacteristicFactor |
| def-weil-local-frobenius-trace | Sheaf.Paper.LocalFrobeniusTrace | localClosedPoint; finite-stage operator used by SfPunctualEigenvalue and the characteristic factor |
| def-sbc-smooth-morphisms | Mathlib.AlgebraicGeometry.Morphisms.Smooth | SmoothOfRelativeDimension |
| def-pc-geometrically-irreducible | Mathlib.AlgebraicGeometry.Geometrically.Connected and .Integral | GeometricallyConnected (connected clause in mathlib_match) |
| def-weil-affine-spectrum | Mathlib.AlgebraicGeometry.Scheme | Spec, Spec.map |
| def-weil-closed-immersion | Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion | IsClosedImmersion |
| def-pc-base-change | WeilConjectures.AlgebraicGeometry.BaseChangeConventions | Over.pullback, Limits.pullback and its projections, as the node record specifies |
| def-real-common-stage-lisse | Sheaf.Paper.CommonStageLocallyFree | IsCommonStageLisse |
| def-zl-weil-ind-sheaf-category | Sheaf.Paper.WeilIndSheafCategory | zlWeilPull, zlFiberMap, common-stage abelian-heart instance |
| def-dl-a1-constant-extension-data | Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | constantExtensionModel, constantExtensionDatum, constantExtensionFiberIso, constantExtensionProjection (existing: true) |
| def-zl-constant-extension-restriction-local-data | Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | ConstantExtensionRestrictionSpec (existing: true) |

The last four already-landed definition nodes were added to stmt_deps to record the
interfaces used explicitly by the statement. The constant-extension equivalence theorem
remains in proof_deps; its plain auxiliary definitions are owned by the two existing
definition nodes above, and no choice from that theorem is used in the statement. Existing fields and all original statement/proof
text are preserved. Every recorded proof dependency with a published module is imported;
PrimeSpectrum.comap_surjective_of_faithfullyFlat uses its Mathlib module instead.

Edge cases checked before writing and again against the final signature:
length r=0 (Fin 0 supplies no quotient or weight assertions but the curve/reality clause
survives), zero F, x=anchor and coincident lifts, relative dimension d=1, rank-one
quotients, nonsplit unipotent extensions for F, arbitrary positive m, residue degrees
larger than one, powers with colliding eigenvalues, and empty spectra on zero stalks.
No zero eigenvalue enters the logarithm formula. No nonempty family of constituents,
second distinct point, global lattice, or equality of coefficient/scheme universes is
imposed. The main statement has no let-bindings or hidden `show ... from` casts.

Searches actually run:

- `msearch.py ... leanfinder "two point curve constituent purity"`: 8 unrelated
  Weierstrass-curve hits; no statement match.
- `msearch.py ... loogle "Constituent, purity, curve, l-adic"`: no hits, unknown
  identifier Constituent; this is not evidence of completeness by itself.
- `msearch.py ... grep "constituent|purity" Mathlib`: 0 hits (the subdirectory query
  was too narrow, so followed by the unrestricted query below).
- `msearch.py ... leansearch "geometrically irreducible lisse constituents of a real
  Weil sheaf are pure by two point curves"`: 8 hits about geometric reducedness,
  integral schemes, quadratic irreducibility, and irreducible components; none match.
- `msearch.py ... grep "IsIrreducible|Simple" CategoryTheory`: 25 generic category
  hits, including CategoryTheory.Simple. Full constructible-heart simplicity is the
  wrong condition; the statement instead quantifies only over lisse subobjects.
- `msearch.py ... grep "IsPunctuallyPureOfWeight|WeilSheaf|SfIsReal"`: 0 Mathlib hits.
- `rg` over lean/WeilConjectures and lean/Sheaf for purity, constituents, real mixedness,
  curve testing, common-stage lissity and irreducibility found the interfaces imported
  above. Upstream `IsIrreducibleAdicLocalSystem` is on AdicSheaf, not this common-stage
  heart. Its exact nonzero/lisse-subobject criterion is expanded for this clause.
- Exact names and item-id searches over both source roots and dag/lean_names_upstream.json
  returned no hits for the newly introduced declarations or this node.
- DAG concept searches found lem-zl-curve-testing-irreducibility,
  lem-zl-common-irreducibility-detecting-cover and the parent constituent theorem;
  none already states the simultaneous purity and local-power conclusion.
- `blueprint_refs.py search 'geometrically irreducible'`: 10 blueprint-node matches,
  including lem-zl-geometric-constituents-any-base, but not a duplicate definition of
  these curve-clause records. `ancestor` returns thm-zl-real-mixed-by-curves.

No new DAG nodes or dependency modules: the auxiliary declarations package the clauses
of this one statement, as allowed for helpers of an owning node. There is no independent
new mathematical construction requiring a new definition node. No STATEMENT-DISPUTED flag.

Validation: prescribed scompile.py only; the draft compiled both as a sandbox and under
its library module name. Final dry run and delivery are recorded below when completed.

## Second reading by Q22

This is a second pass by the same worker. The dispatcher explicitly prohibits starting
other agents; independent review is the maintainer's review of this delivery.
I reopened the node and the final file together and matched the clauses listed above.
The initial draft needed IsSeparated for the characteristic-factor API; the source's
affine situation already implies this property. The first draft also expressed uniqueness
only inside each selected testing curve. I added the universal qualifying-curve clause
so that the node's assertion about every such curve weight is explicit. The final pass
checks the geometric (not Weil) subobject condition, the actual cokernels, the two arbitrary
residue embeddings, positive residue degrees, multiset rather than set power equality,
the anchor formula and its nonzero proviso, and the empty-family case. The source and
node statements are unchanged. All definitions use the recorded underlying categories
and normalized functors, and the only theorem body is sorry.

## Repair of return L (immutable head ad402953821d)

H2: replaced `lem-zl-constant-extension-weil-heart-equivalence` in stmt_deps with
`def-dl-a1-constant-extension-data` and
`def-zl-constant-extension-restriction-local-data`. Both are already-landed
existing:true definition records for the exact declarations used by this statement.
The theorem remains in proof_deps. Updated the dependency table accordingly.
The Lean file and mathematical statement are unchanged, as requested by the reviewer.
The saved-packet dry run passed before this repair (commit db429f326ba); it did not
check the semantic dependency distinction identified by the independent review.
Compared the saved node with current shared sources: before repair only lean and
stmt_deps differed; both replacement definition records and their recorded
ConstantExtensionWeilHeartEquivalence source declarations were read again.

Self-check: datum/model/projection/fibre-isomorphism uses are ordinary definitions;
ConstantExtensionRestrictionSpec is the recorded normalized restriction predicate.
There is no .choose from constantExtensionWeilHeartEquivalence. No dependency node
or Lean source was changed by this repair.

Repair validation: prescribed scompile.py passed without errors or warnings for both
the sandbox module (16.1 s) and the library module (23.3 s). The Lean SHA-256 remains
`a9cf06ff0c27483fe02e9bc07c4b24f4647a22ac06501f8e99ceb09354111451`.
The self-check verified the verbatim signature, unchanged proof_deps, both definition
owners in stmt_deps, and absence of the equivalence theorem from stmt_deps.
