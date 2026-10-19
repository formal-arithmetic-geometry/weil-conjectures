## Worker report

The module `Sheaf.TraceFormula.ValuationModificationProperCompletion` states
`AlgebraicGeometry.Temkin.valuation_modification_proper_completion`, with one `sorry`.
Its three helpers construct the actual localization map, the actual generic point of
that localization, and the induced geometric centre by a pullback section. None chooses
an object from an unproved existence assertion. The existing relative-curve notion receives its own definition-node record in this repair;
no duplicate Lean definition or dependency module is needed.
The node's mathematical statement and proof are unchanged.

Source checked: the author PDF at
https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf, downloaded and read with
`pdftotext`, Lemma 4.4.1(i),(ii) and the proof of Lemma 4.4.2, printed pp. 30--31,
through the normalization giving geometrically reduced fibres. In particular, the source
localizes R, makes the modification locus have only one closed point, compactifies the
normal affine target, extends by the identity, and normalizes without changing the
semistable neighbourhood. The theorem docstring includes all ten DAG proof steps.

Hypotheses, individually:

- The specified field and separable closedness are `(K : Type u) [Field K] [IsSepClosed K]`.
- `V : ValuationSubring K` is literally a subring of K with the element-or-inverse condition.
  Mathlib supplies K as its fraction field. Its primes form a chain because it is a
  valuation ring; `[Finite (PrimeSpectrum V)]` is precisely finiteness of that chain.
- The two structure maps are `c` and `f ≫ c`. Using the composite for Y introduces no
  condition beyond saying that f is a morphism over T.
- `hC : RelativeCurve c` and `hY : RelativeCurve (f ≫ c)` give flatness, locally finite
  presentation, quasi-compactness, quasi-separatedness, and pure dimension one of every
  fibre. Thus they express finite presentation, not only its local version. Pure dimension
  is the recorded `Scheme.IsPureDimension`; it is vacuous for empty fibres.
- `[IsReduced Y]` is the reduced-source hypothesis.
- `hCgeneric` and `hYgeneric` give smoothness of both generic fibres over the specified K.
- `hf : EtaModification ... f c` includes properness, isomorphism between schematically
  dense opens, and invertibility of the actual induced generic-fibre morphism. Schematic
  density uses `SchematicallyDenseOpen`, injectivity of restriction on every ambient open.
- `x : C`, `hx` and `hpositive` give the smooth point (a smooth open neighbourhood) and
  `0 < topologicalKrullDim (f.fiber x)`.
- `hnodal` asserts existence of an open N containing every point of the entire fibre Y_x.
  For each base point t it tests the chosen algebraic-closure geometric fibre at every
  point whose image belongs to N. Each such point is smooth on an open neighbourhood or
  satisfies the existing scalar-compatible `Orgogozo.IsOrdinaryDoublePoint`, whose
  completion is exactly `Omega[[u,v]]/(uv)`. It imposes neither connectedness nor nodality
  outside N, and it does not replace the hypothesis by tests over larger fields.

Conclusion, individually:

- `valuationCompletionBaseMap V (c x)` is `Spec(V_p) → Spec V`, for p = c(x).
  `j₀ : U → pullback c ...`, `IsOpenImmersion j₀`, and `IsAffine U` express the affine
  open neighbourhood in the localized target. The point u and its image equality say
  that it contains the original x. Localization is a monomorphism, so this is the
  unique point over x, not an unrelated choice of a point of the base change.
- `Cbar`, `Ybar`, `cbar`, and `fbar` are the auxiliary S-curves and S-morphism. Both
  `IsIntegral` clauses, both proper structure-map clauses and both `RelativeCurve`
  clauses express integral proper flat finitely presented curves of pure dimension one.
- `IsOpenImmersion j` and `j ≫ cbar = j₀ ≫ pullback.snd ...` put U openly into Cbar
  over precisely the localized base.
- The stalkwise `IsDomain` and `IsIntegrallyClosed` conjunction is exactly normality
  as stated for Cbar; no normality of Ybar is added to the conclusion.
- Both `GeometricallyReduced` clauses express geometrically reduced fibres. Mathlib
  tests all field-valued base changes. This is equivalent to the stated algebraically
  closed tests by faithfully flat descent of reducedness, as in the recorded
  algebraic-closure-test proof dependency.
- Both `GeometricallyIntegral (pullback.snd ... valuationCompletionGenericMap ...)`
  clauses mean that both generic fibres are reduced and irreducible after every field
  extension of K. The helper map is built by `IsLocalization.lift`, with invertible
  denominators supplied by `IsLocalization.map_units` in the fraction field.
- `EtaModification ... fbar cbar` includes properness of fbar, its actual generic-fibre
  isomorphism, and its isomorphism between schematically dense opens.
- `IsPullback i (pullback.snd f (j₀ ≫ pullback.fst ...)) fbar j` identifies its entire
  inverse image over U with `Y ×_C U → U`, as a morphism to U. In particular i is open
  because it is the base change of j. This retains the ambient neighbourhood, not only
  an abstract exceptional-fibre isomorphism.
- `cbar (j u) = IsLocalRing.closedPoint ...` puts x on the closed fibre of S.
  `IsClosed {cbar.asFiber (j u)}` says precisely that x is closed in that fibre.
- The final quantifiers allow every algebraically closed Omega in the scheme universe
  and every geometric point a of U over u, with no algebraicity requirement. Every
  geometric point over x lifts uniquely to U because U is its open neighbourhood
  in C_S, and a field-valued point over p factors uniquely through V_p.
- The singleton equality says that the entire inverse image of x in Cbar_Omega is
  the one induced point, `valuationCompletionGeometricCentre cbar j a`. This helper
  evaluates the canonical pullback section of a, rather than selecting a point.
- The smooth-open clause makes this point smooth on Cbar_Omega. The final universal
  open-restriction clause says that fbar_Omega is an isomorphism away from this point.
  Its source is the iterated pullback, canonically Ybar_Omega. Opens omitting the centre
  cover its complement, so this is exactly the isomorphism away from the point.
- Base change of the displayed cartesian square along a identifies the original
  geometric fibre over x and its full ambient open neighbourhood. This last sentence
  of the node is the direct universal-property consequence of that square, with no
  additional existential identification required.
- No separatedness or properness of C/T or Y/T is assumed. Quasi-separatedness in
  `RelativeCurve` is part of finite presentation, and does not assert separatedness.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (also read the recorded companion
  `IsSepClosure`, which is not needed by this item).
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`, `IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.lift`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, through the existing node
  predicate; `MvPowerSeries` in `Mathlib.RingTheory.MvPowerSeries.Basic` likewise.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Sheaf.TraceFormula.Modification`: `EtaModification`, `SchemeModification`; its
  `SchematicallyDenseOpen` dependency was also read in full.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Sheaf.Paper.OrgogozoInductionData`: `Orgogozo.geometricPoint`,
  `Orgogozo.IsOrdinaryDoublePoint`, `Orgogozo.nodeRing`, `Orgogozo.localScalar`.
- `Sheaf.TraceFormula.ValuationHorizontalCurveModels`: `RelativeCurve`; also inspected
  `HorizontalValuationBase`, but did not create a second valuation-base definition.

The pure-dimension, modification and ordinary-double-point owning nodes already have
usable published Lean records. They are added as statement dependencies under the standing
rule permitting landed nodes to be cited. The plain `RelativeCurve` structure is now cited
through its new owning definition node `def-trf-relative-curve`, rather than through the
horizontal-model theorem node; see the repair and new-node sections below.
All proof-dependency modules with recorded Lean are imported as proof imports. The
unstated `lem-trf-sepclosed-valuation-geometric-components` has no import; its mathematical
step is retained verbatim in the proof plan. Mathlib permanence modules are also available
through the explicit proof imports and the public relative-curve interface.

Searches (2026-10-18 UTC):

- `msearch.py leanfinder "A proper modification of curves over a separably closed valued
  field admits a proper completion preserving a nodal neighbourhood"`: eight hits, all
  Weierstrass reduction/coordinate-change results; none concern general relative curves
  or preservation of a given neighbourhood.
- `msearch.py loogle '"compactification", "IsProper"'`: OK, zero hits.
- `msearch.py grep 'SchematicallyDense|Nodal|PureRelative|semistable' AlgebraicGeometry`:
  OK, zero hits in Mathlib.
- `msearch.py leansearch "proper completion modification valuation relative curves nodal
  neighbourhood"`: eight valuation-completion hits (`Valued.extension`,
  `Valued.extensionValuation`, `Valuation.Completion`, etc.); these complete fields,
  not curves or modifications.
- `rg` in `WeilConjectures/` for the item id: no hits. Searches for nodal, schematic
  density, relative dimension and proper completion give no matching completion theorem.
- `rg` in `lean/Sheaf/` finds the existing preparation, relative-curve, modification,
  schematic-density and ordinary-double-point interfaces used here. The preparation
  theorem does not have this item's hypotheses/conclusions: it requires normal curves
  first and does not supply this whole smooth-centre geometric completion statement.
- Searched `dag/lean_names_upstream.json` and both source trees for the new full names:
  no declaration collision. No duplicate nodal predicate, schematic-density predicate,
  normalization or relative-curve notion is introduced.

Edge cases checked: height-zero valuation base (positive-dimensional f-fibre is impossible
because f is generically an isomorphism); identity modification (same incompatibility);
empty schemes (x and positivity exclude only the relevant empty case); empty other fibres
(allowed by `IsPureDimension`); disconnected original generic fibre (the conclusion chooses
its component near x, with no connectedness hypothesis); higher finite rank; imperfect
separably closed residue fields (no perfectness assumption); arbitrary characteristic;
all geometric points over x including transcendental algebraically closed extensions.
One universe u is used for schemes and test fields, as in Mathlib's geometric properties;
there is no smaller independent test-field universe.

Validation: `scompile.py NC lem-trf-valuation-modification-proper-completion <module>`
compiled both the sandbox and named library forms cleanly (3.5 and 3.8 seconds).
The first compile exposed a scheme-carrier inference error in the geometric-centre
helper; its return type now explicitly uses `↥(pullback (C := Scheme.{u}) ...)`.
No other error or warning remained. The one postponed theorem is intentional stage 2.
No statement dispute or source-based correction was needed.

## Second reading by NC

Author self-check, as required for direct dispatcher deliveries; the maintainer provides
the independent reading. I reopened the full node and the delivered Lean signature.
The valuation ring is a genuine subring of the specified fraction field; the finite chain
is not replaced by rank one. Both finite-presentation clauses include qc and qs. The
source is reduced, and both generic fibres are smooth. The proper generic isomorphism
is the actual induced map, with schematic (not topological) density on both sides.
The local nodal hypothesis is tested only on the given open around the whole Y_x and on
algebraic-closure fibres; connectedness and global nodality are absent.

For the conclusion I checked the open immersion into C ×_T S, its point over x, both
integral proper flat finitely presented curves, the open immersion into Cbar, the
base-map equality, stalkwise normality only of Cbar, both geometric-reducedness clauses,
both geometrically integral generic fibres, the generic isomorphism and schematic-dense
modification, the cartesian preservation square, the closed-fibre and closed-point
clauses, the induced unique geometric point, smoothness there, and the isomorphism on
all opens away from it. The cartesian square retains the full neighbourhood and its
base changes. No original properness or separatedness assumption has appeared.
The geometric fields in the conclusion have no algebraicity restriction.

I specifically compared with `HasNodalGeometricFibres`: that predicate also requires
connected nonempty fibres and is therefore not used. I compared with the projective
preparation theorem: it is only the proof input, not an existing declaration of this
node. The only change during reading was the explicit scheme-carrier annotation needed
by the compiler, plus explicit Noetherian and upstream properness proof imports. No
mathematical clause was changed. Every helper has real constructed data, a source
place and this item's blueprint tag. Only `lean` and the authorized statement-dependency additions change in the item copy.
The repair replaces the previously added horizontal-model theorem dependency with the
new relative-curve definition dependency; it does not alter any dependency on the base.


## New nodes

`def-trf-relative-curve` owns the plain relative-curve predicate of Temkin, *Stable
modification of relative curves*, §1.2, printed p. 2. I downloaded the author PDF again
on 2026-10-19 and read the opening of §1.2: the curve morphism is flat and finitely
presented, of pure relative dimension one, and need not be separated or proper.
The node records `existing: true`, `branch: newtargets-dag`, module
`Sheaf.TraceFormula.ValuationHorizontalCurveModels`, declaration
`AlgebraicGeometry.RelativeCurve`; its verbatim signature is
`structure RelativeCurve {T Y : Scheme.{u}} (y : Y ⟶ T) : Prop`.
The live source was independently fetched using `scompile.py --source` and agrees
with the read-only checkout at lines 70--79. There is no new Lean declaration.

Each part is represented directly: `flat : Flat y`; finite presentation is
`finitelyPresented : LocallyOfFinitePresentation y`, `quasiCompact : QuasiCompact y`
and `quasiSeparated : QuasiSeparated y`; fibrewise pure dimension one is
`pure : ∀ t : T, (y.fiber t).IsPureDimension 1`. The schemes and map are the explicitly
bound `T`, `Y` and `y`, with explicit universe `u`. The five definition dependencies
are `def-pc-scheme`, `def-weil-flat-morphism`, `def-sbc-locally-finite-presentation`,
`def-pc-scheme-fibre`, and `def-weil-pure-dimension`; their recorded declarations are
respectively `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Flat`,
`AlgebraicGeometry.LocallyOfFinitePresentation`, `AlgebraicGeometry.Scheme.Hom.fiber`
and `AlgebraicGeometry.Scheme.IsPureDimension`. I read those records, signatures
and docstrings. Empty fibres satisfy the pure-dimension field vacuously; no
nonemptiness, connectedness, separatedness or properness is imposed.

Searches on 2026-10-19: `msearch.py leansearch` with the new node's full plain-language
statement returned eight flatness/smoothness declarations, no relative-curve predicate;
`msearch.py loogle RelativeCurve` returned zero hits (unknown identifier);
`msearch.py grep 'RelativeCurve|relative.?curve' AlgebraicGeometry` returned zero hits.
`rg` in the upstream algebraic-geometry tree found only comments about smooth relative
curves, not a definition. `rg` in `lean/Sheaf` found exactly the published structure
and consumers. The DAG definition-record search found multipointed curves (a pair
with a marking) and strict semistable curves (extra local charts), neither the plain
predicate; `blueprint_refs.py search 'relative curve'` found zero blueprint nodes.
All three search records are in the new node. The structure already exists, so it
is reused; the missing object was its owning definition node, as the return required.

## Repair of immutable head 209330a802ca

The single return point, H2/C5, is repaired by the new owning definition node above
and by replacing the delivery-added `lem-trf-valuation-horizontal-curve-models` in
`stmt_deps` with `def-trf-relative-curve`. The existing import stays because it is
where the exact reused structure is published. The theorem itself is neither a
statement dependency nor a construction needed to supply `RelativeCurve`.
The horizontal-model lemma remains a genuine proof input through the existing
proof plan; its proof is not used to define this plain predicate. This is a full
stage-2 packet through `deliver2.py`, not a stage-2 FIX. No existing node except the
item is modified, and the item's TeX statement, proof and proof dependencies are
unchanged. The saved Lean module, its helpers and its reviewed signature are retained.

Author self-check by NC (no second agent was started): I reopened the new node and
the full existing structure, matched all five fields as above, and checked that
this record requires no hypothesis or theorem proof to introduce the notion.
I then reopened the completion signature: both original-curve assumptions and
both completed-curve conclusions use that very same `RelativeCurve`. Every
hypothesis and conclusion remains as individually checked in the earlier reading.
The new node's signature is verbatim, all variables and universes are bound, its
statement cites exactly its five definition dependencies, and its blueprint ancestor
and via chain are copied from the item with the item prepended. The ownership error
is the only semantic change in this repair; there is no statement correction.
