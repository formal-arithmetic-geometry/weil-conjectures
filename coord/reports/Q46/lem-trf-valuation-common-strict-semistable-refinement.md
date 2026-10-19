## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement`
states `AlgebraicGeometry.MultipointedCurve.exists_common_strictSemistable_refinement`.
It is a stage-2 theorem with `sorry` as its proof and no new definition data.
The node's valuation hypotheses are rendered by
`K : Type u`, `[Field K]`, `[IsSepClosed K]`, `V : ValuationSubring K`, and
`[Finite (PrimeSpectrum V)]`; `ValuationSubring` supplies the valuation-ring
alternative and its fraction-field instance.  `Spec (.of V)` is the base `S`, and
`Spec.map (CommRingCat.ofHom V.subtype)` is the generic map `eta : Spec K -> S`.

The source pair `(C,D)` is `C : MultipointedCurve (Spec (.of V))`.  The smooth
generic-curve and etale generic-marking clauses are respectively `hsmooth` and
`hetale`, each using the pullback projection along the displayed generic map.
The two arbitrary input modifications are `X₁`, `X₂`, their compatible pair maps
`f₁ : X₁.Hom C`, `f₂ : X₂.Hom C`, and the hypotheses `hf₁`, `hf₂` that each is
`MultipointedCurve.Hom.IsEtaModification` for the same generic map.  This
predicate supplies proper curve and marking maps, schematically dense
isomorphism opens on both parts, and isomorphisms after generic base change; no
semistability, stability, separatedness, or properness of `X₁` or `X₂` is added.

The conclusion supplies a multipointed curve `W` and compatible maps
`q₁ : W.Hom X₁`, `q₂ : W.Hom X₂`.  Its strict semistable-pair clause is rendered
by `IsStrictlySemistableCurve W.x ∧ W.IsSemistable`: the first is the existing
strict affine-line/nodal etale-chart predicate, and the second supplies the
marking etaleness, placement in the relative smooth locus, and ordinary-double-
point geometric fibres.  The two `qᵢ.IsEtaModification` clauses give the required
proper, schematically dense, generic-fibre-isomorphic pair maps.  The final two
component equalities,
`q₁.curve ≫ f₁.curve = q₂.curve ≫ f₂.curve` and
`q₁.marking ≫ f₁.marking = q₂.marking ≫ f₂.marking`, render the equality
`f₁q₁ = f₂q₂` of compatible pair maps.  `D` and `E` may be empty because the
multipointed-curve structure permits empty marking schemes.  The finite-chain
instance and all scheme/ring universes are explicit; no characteristic,
separatedness, or properness assumption is introduced.

Dependency declarations read and used:

- `Sheaf.TraceFormula.MultipointedCurve` supplies
  `AlgebraicGeometry.MultipointedCurve`, whose fields are the two structure maps,
  marking compatibility, flat locally finitely presented quasi-compact and
  quasi-separated maps, fibrewise pure dimensions, and the closed immersion.
- `Sheaf.AlgebraicGeometry.MultipointedCurveModification` supplies
  `MultipointedCurve.Hom`, `MultipointedCurve.IsSemistable`,
  `MultipointedCurve.Hom.IsEtaModification`, and the canonical base-change maps.
  Their full signatures and docstrings were read; the eta predicate is the exact
  pair-modification notion needed here.
- `Sheaf.AlgebraicGeometry.StrictlySemistableCurve` supplies
  `AlgebraicGeometry.IsStrictlySemistableCurve`, whose full definition is the
  existing flat, locally finitely presented, pure-dimension-one curve condition
  with local etale polynomial or nodal charts.  The theorem combines it with the
  recorded semistable marked-pair predicate rather than defining a second chart
  notion.
- Mathlib `FieldTheory.IsSepClosed` supplies `IsSepClosed`; Mathlib's
  `ValuationSubring` supplies the valuation ring, `V.subtype`, `CommRing V`,
  `IsDomain V`, and `IsFractionRing V K`; `AlgebraicGeometry.Spec`, `pullback`,
  `Smooth`, `Etale`, `Finite`, and `PrimeSpectrum` are used at their recorded
  signatures.  The dependency leaves `def-weil-field`,
  `def-kun-separably-closed`, `def-weil-affine-spectrum`,
  `def-weil-flat-morphism`, `def-sbc-locally-finite-presentation`,
  `def-weil-closed-immersion`, `def-weil-etale-morphism`,
  `def-weil-geometric-fibre`, `def-weil-proper-morphism`,
  `def-kun-topological-krull-dimension`, `def-weil-pbc-adic-completion`, and
  `def-weil-pbc-multivariate-power-series` are all represented by the imported
  Mathlib or project declarations above and are used in the recorded predicates.

Searches made before writing:

- `msearch.py Q46 lem-trf-valuation-common-strict-semistable-refinement leanfinder
  "A common strictly semistable refinement of two proper modifications of a smooth
  generic multipointed curve over a finite-height valuation ring"`: eight hits,
  principally valuative-criterion and Weierstrass-minimality declarations; none
  states a common marked strict-semistable refinement.
- `msearch.py Q46 lem-trf-valuation-common-strict-semistable-refinement loogle
  "AlgebraicGeometry.MultipointedCurve.Hom.IsEtaModification,
  AlgebraicGeometry.IsStrictlySemistableCurve"`: zero hits; the service reported
  the first project identifier as unknown, so the project source was checked
  directly.
- `msearch.py Q46 lem-trf-valuation-common-strict-semistable-refinement grep
  "MultipointedCurve|IsStrictlySemistableCurve|strictSemistable" AlgebraicGeometry`:
  no Mathlib hits.
- Direct `rg` over `WeilConjectures/` and `lean/Sheaf/` found no declaration of
  this item or theorem name; it found only the existing multipointed, pair
  modification, and strict-curve infrastructure cited above.  The DAG search
  found no separate common-refinement statement.

Edge cases checked are the empty marking, empty curve/fibres, identity
modifications, valuation ring equal to the field, height zero (the finite prime
spectrum may be a singleton), nodal special fibres, and arbitrary characteristic.
The conjunction does not require a nonempty marking or any projectivity, and
`Finite (PrimeSpectrum V)` does not force a discrete valuation ring.

The file compiled cleanly with `scompile.py Q46
lem-trf-valuation-common-strict-semistable-refinement`; the only accepted
stage-2 proof placeholder is the theorem `sorry`.

## Second reading by Q46

I reread the item node, its 13 recorded statement dependencies, the complete
signatures/docstrings of the project declarations, and the source theorem
(Proposition 4.5.1 together with Remark 4.5.2).  Every hypothesis is present:
separably closed field, valuation ring with finite prime chain, base and generic
maps, smooth generic curve, etale generic marking, two compatible eta-modifications,
and no semistability or stability assumption on their sources.  Every conclusion
clause is present: a common multipointed source, strict curve charts together with
semistable marking/fibres, eta-modifications on both curve and marking, and both
component equations expressing the common factorization.  Empty and height-zero
cases remain admitted.  The module has explicit universes, `autoImplicit false`,
no private notation or duplicate definitions, and only the theorem proof is
`sorry`.
