## Worker report

The module `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` states
`WeilConjectures.IntegralSystemRealization.systemPrimitiveComparisonShift`, with its proof
postponed by `sorry`. All helper definitions have actual data. The item node changes only in
`lean`; there are no new nodes, dependency repairs, or statement corrections.

Hypothesis and clause correspondence:

- The fixed geometric field is `D : FiniteFieldDatum.{u}` (a specified algebraic closure of a
  finite field). The prime is `l` with `[Fact l.Prime]`, and `_hl : l ≠ D.p` excludes the
  characteristic. The field extension is `E` with `Field`, `Algebra ℚ_[l] E`, and
  `FiniteDimensional ℚ_[l] E`. The imported coefficient sequence uses the valuation ring,
  uniformizer and `Padic.coefficientExtensionRing l E (n+1)`; no zero-index quotient is added.
- `PrimitiveSystemScheme D` is the full subcategory of `Over (Spec (.of D.k))` on objects
  with `LocallyOfFiniteType W.hom ∧ QuasiCompact W.hom`, exactly finite type over k.
  `PrimitiveSystemArrow f` expands separated finite type into `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact` on the underlying arrow.
- `System l E W` is the existing ordinary unbounded derived category of module sheaves on
  the simultaneous ringed coefficient sequence site; its objects retain strict semilinear
  quotient transitions. There is no diagram of derived categories substituted for it.
- `o : Operations l E`, `c : Compositors l E o` and `a : OpenComparisons l E o c` are the
  published canonical simultaneous operations and their normalization interfaces. These
  are not unnormalized maps: c has ordinary section and derived representative equations;
  a has open-unit transpose and clopen transpose equations. Their existence is provided by
  the realization dependency. Quantification makes the assertion independent of that
  canonical presentation. No shift-compatibility hypothesis is assumed.
- `PrimitiveSystemComparison` indexes only the stated primitive families by their actual
  formulas. `pullComp` uses `c.pullComp`; `square` uses `c.square` and the equality of scheme
  composites. The arrow conditions are recorded separately for all four square edges.
- `tensorPullLeft` and `tensorPullRight` use `pullbackTensorSystemComparison`, with its two
  input occurrences selected separately. `assocFirst`, `assocMiddle`, `assocLast` use the
  published monoidal associator, selecting each of its three occurrences. `leftUnitor`
  and `rightUnitor` use the published monoidal unitors, with their fixed tensor unit.
- `primitiveTensorModel` restricts the published system K-flat comparison along the
  flat-term resolving inclusion; it does not choose a second tensor. `primitiveSystemSymmetry`
  applies the dependency's `derivedTensorSymmetry` to this presentation; its uniqueness
  characterization is the signed swap on total K-flat complexes. `symmetryLeft` and
  `symmetryRight` follow the selected input into the opposite tensor position.
- `openComp` uses `c.openComp`, with both opens quasi-compact (and the derived composite
  quasi-compactness witness). `restriction` treats arbitrary opens s, b, k with s ≫ b = k;
  `primitiveSystemRestriction` is the inverse open compositor, the canonical equality
  transport, and inverse open unit, exactly the identification P_b J_k ≅ J_s.
- `clopen` uses `a.clopen` with `IsClosedImmersion s.left`; its properness witness is the
  property of the same clopen immersion required by the already published push context.
  `projection` uses `primitiveSystemProjection`: the actual direct-image unit followed by
  P_s of the inverse canonical J_s-to-S_s map. This is the intrinsic component projection
  normalization of the semilinear proper/open dependency, in the realization presentation.
- The final theorem takes every such family τ, every system M, and every integer r. Its
  equality is `τ (M⟦r⟧) ≫ χ_t = χ_e ≫ (τ M)⟦r⟧'`, which is the node's displayed square in
  Lean composition order. Both χ are the existing `Expression.SlotContext.shift` with
  `systemShifts l E o`. At tensor vertices these use `tensorShifts.systemLeft` and
  `systemRight`, characterized on actual generators by 1 and (-1)^(ri), respectively.
  Thus they are precisely the single-input instances of the specified t_(a,b).
- The equation is in the derived strict-system category itself, before total limit,
  finite evaluation or scalar restriction. No admissibility/boundedness hypothesis is
  added: this node concerns ambient primitive maps. There is no constructor for integral
  realization, arbitrary comparison, proper/open mate, exchange or projection formula.
  Slot contexts serve only to define the displayed primitive endpoints and their fixed
  shifts; their arbitrary closure is not an assertion of the theorem.

Dependency declarations read and used:

- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`:
  `integralCompactificationSystemRealization` and its `Realizations` record; its imported
  `IntegralSystemOperations` gives `System`, `Operations`, `Compositors.pullComp`,
  `Compositors.square`, `Compositors.openComp`, `OpenComparisons.clopen` and `.unit`.
- `Sheaf.SixFunctors.IntegralBasicOperationShift`: `integralBasicOperationShift`, and the
  imported `IntegralOperationShiftData` declarations `systemShifts`, `tensorShifts`,
  `systemPullShift`, `systemPushShift`, `systemOpenShift`, `Expression.SlotContext.shift`.
- `Sheaf.Paper.ShiftedTensorMorphismCalculus`: `shiftedTensorMorphismCalculus`,
  `shiftedTensorResolving`, `ShiftedTensorModel`, `derivedTensorSymmetry`, and its
  `IsCanonicalDerivedTensorSymmetry`/`IsSignedComplexSwap` representative characterization.
- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`:
  `semilinearProperOpenMatePasting`, `openToS`, `pi`, `pi_components`; the realization
  interfaces express their normalization in the fixed coefficient-sequence presentation.
- Proof dependency `Sheaf.SixFunctors.OpenTensorNormalization` is imported privately;
  `openTensorNormalization` supplies the normalized termwise open comparisons.

Edge cases read against the formulas: r=0, negative r, zero input objects, equal values in
independently selected tensor occurrences, identity scheme maps, identity opens, empty opens,
empty schemes, and a clopen immersion that is empty or an isomorphism. None is excluded by
nonemptiness or boundedness assumptions. In the empty clopen case the projection is zero;
for the identity clopen case it is the identity. All three associator input slots and both
symmetry slots are present. Two shifted slots follow by successive individual squares, with
the graded tensor sign; the theorem's square itself shifts one designated occurrence.

Searches (2026-10-18 UTC):

- `msearch.py ... leanfinder "Canonical pullback tensor associator symmetry extension by
  zero comparisons commute with integer shifts in derived strict semilinear module systems"`:
  eight generic results, principally CommShift₂Setup and cochain unitors; no exact match.
- `msearch.py ... loogle "CategoryTheory.NatTrans.CommShift"`: twelve generic compatibility
  and transfer results; none establishes the canonical primitive system comparisons.
- `msearch.py ... leansearch "Canonical derived tensor and pullback structural comparisons
  commute with cochain shifts"`: eight results about exact-functor shifts, tensor-complex
  shift formulas and mapping cones; no complete system primitive statement.
- `msearch.py ... grep "CommShift|commShift" CategoryTheory/Monoidal`: zero matches.
- `rg` in Mathlib's CategoryTheory/Shift, the upstream declaration index, upstream
  WeilConjectures and lean/Sheaf for primitive comparison/shift names: no existing declaration
  with this statement. Upstream item-id grep: zero matches. Existing integral-realization
  shift coherence is about integral realizations and different hypotheses, not this result.
- Read the blueprint's entire fix-prop-coherence proof and Stacks more-algebra sign-rules
  (including shifted tensor, unsigned associator and signed flip), and sites-cohomology
  symmetric-monoidal-derived. Read the full dependency signatures and normalization
  docstrings. The signed calculus's source was also confirmed with scompile.py --source.

Validation: `scompile.py Q03 lem-pur-system-primitive-comparison-shift <module>` compiled the
sandbox and library-form module cleanly (6.2 s and 6.1 s before the explicit redundant
statement/proof dependency import completion). The final import-complete file is checked
again by delivery preflight. No proof other than the item's named theorem is postponed.
No STATEMENT-DISPUTED or node fault was found.

## Second reading by Q03

Author's separate rereading of the node, source, module and every constructor; independent
review is performed by the maintainer under the dispatched-worker brief. The field, prime,
finite coefficient extension and positive quotient indices agree. The scheme full subcategory
and the three-part arrow predicate express exactly the finite-type and separated conditions.
All seven classes of primitives are accounted for by the constructors listed above, including
all input slots. The restriction constructor is general in b and s and does not require a
proper/open square, so it does not silently specialize that clause to a squareLift. The
clopen projection uses the direct-image unit (not the open counit) and the inverse clopen
comparison, giving the required direction 1 → J_s P_s. The symmetry contexts switch left
and right and therefore follow the same occurrence. The tensor shifts come from the existing
signed normalization, without an arbitrary CommShift hypothesis. The equality has the right
composition orientation. No arbitrary expression-context closure is in the finite primitive
predicate. During construction, the resolving inclusion's morphisms were corrected to use
the full-subcategory hom wrapper, and the coefficient/site/localization universes were made
explicit; these are interface fixes, with no mathematical change. No node text changed.
