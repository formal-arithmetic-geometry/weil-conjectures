## Worker report

The module `Sheaf.AlgebraicGeometry.NagataAffineFpDescent` defines the structure
`AlgebraicGeometry.NagataAffineFpDescent`.  It records the finite-stage model data in the
node: a nonempty directed preorder and commutative-ring diagram, a fixed base index, a finite
list of polynomial relations over the colimit ring, a chosen later stage, transported stage
relations, their compatibility with the colimit map, the stage algebra and its finite
presentation, the colimit algebra and its presentation, the comparison algebra map, and the
base-changed scheme objects (including the limit term).  The stage, relation lifts, and all
resulting fields are explicit, so the dependence on the selected coefficient lifts and on the
chosen presentation is retained.

The hypotheses render as `[Preorder I]`, `[Nonempty I]`, `[IsDirected I (· ≤ ·)]`, and
`F : I ⥤ CommRingCat`; the fixed stage is `lambda0 : I`, and the finite presentation is
represented by `n m : ℕ` and `relations : Fin m → MvPolynomial (Fin n) (↑(colimit F))`.
The clause `lambda0 ≤ stage` is `stage_ge`; transported relations are `relationMap` and
`relationMap_colimit`; the stage and colimit quotient presentations are `stagePresentation`
and `presentation`; `beta` is the comparison map; `baseChanged` and `baseChangedLimit` encode
the base-changed system and its limit term.  The structure has no proved theorem: all data
fields are required explicitly and no field is populated by `sorry`.

Dependencies used: `Sheaf.Order.DirectedFiniteUpperBound` (`directedFiniteUpperBound` and
`le_directedFiniteUpperBound`), `Sheaf.RingTheory.FilteredColimitFiniteData`
(`CommRingCat.exists_finite_data_stage`), and the existing source construction
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`
(`AlgebraicGeometry.baseChangeDiagram`, `AlgebraicGeometry.baseChangeCone`) corresponding to
`def-nagata-basechanged-system`.  The latter is represented by explicit scheme fields in this
structure because the recorded declaration is a diagram constructor rather than the full
bookkeeping record.

Edge cases checked: `m = 0` gives an empty relation family and `n = 0` gives a polynomial ring
on no variables; the index is only required to be nonempty and directed, and the selected stage
is allowed to equal the base stage.  No canonicity of lifts or independence of presentation is
asserted.

Searches recorded on the node were reviewed: Lean Finder found only generic finite-presentation
declarations; Loogle returned no match; grep over Mathlib algebraic geometry returned no exact
descent definition; LeanSearch was unavailable.  Project searches found no existing declaration
for this node.  The dependency declarations above were opened and checked against their recorded
signatures.

## Earlier second reading (a previous round; superseded)

I reread the node statement and the module after compilation.  The directed-system hypotheses,
base index, finite presentation parameters, chosen stage, transported relations, quotient
presentations, comparison map, and base-changed scheme/limit fields all occur explicitly in the
same order.  The empty-index and zero-variable cases remain admitted.  I also checked each
recorded dependency declaration and retained the dependency modules as imports; no statement
was weakened by adding a canonicity or nonemptiness condition beyond the node's assumptions.

## Second reading by Q1

I independently opened the node, all four dependency nodes, their recorded source
modules, and the delivered module. The earlier second-reading paragraph above is
superseded: its assertion that the unconstrained fields encoded the construction
was incorrect. The worker report describes the original version; the repairs and
final interpretation are recorded here.

Source reading: the item's source is a blueprint definition, not a Stacks tag.
The literature files are absent from this machine's read-only clone. I read the
actual source document on the server over ssh at
`literature/blueprint/master/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-approximation/def-nagata-affine-fp-descent.md`,
node order 351. It selects coefficient lifts, takes their selected upper bound,
forms the quotient by the lifted relations, and defines the presentation-induced
tensor comparison. The current DAG expands this with the fixed base stage and the
base-changed system. There is no ambient field, characteristic, Noetherian,
separatedness, injectivity, or nonzero-ring hypothesis. The source's bypassed-route
note does not supply an existing declaration for this particular construction.
There is no `statement_change` in the delivered node; the node's mathematical
statement and dependencies remain unchanged.

Object, hypothesis and clause checklist, in node order:

1. Nonempty directed index and ring system: `{I : Type u} [Preorder I]
   [Nonempty I] [IsDirected I (· ≤ ·)]` and `F : I ⥤ CommRingCat.{u}`.
   Verdict: exact project convention for a directed set; no antisymmetry added.
   Functoriality gives the compatible transition ring maps `F.map (homOfLE h)`.
2. Colimit ring and structure maps: `colimit F`, `colimit.ι F i`. Verdict: exact
   categorical colimit, with no redundant `HasColimit` hypothesis.
3. Inverse spectra and colimit spectrum: `F.op ⋙ Scheme.Spec` and
   `Scheme.Spec.mapCone (colimit.cocone F).op`. Verdict: the diagram has exactly
   the reversed ring transition maps; the cone vertex is `Spec (colimit F)` and
   projections are the spectra of the colimit maps. Affineness and the limiting
   property follow from the existing Spec construction, not additional inputs.
4. Fixed base index and finite presentation: `lambda0 : I`, `n m : ℕ`, and
   `relations : Fin m → MvPolynomial (Fin n) (↑(colimit F))`; the fields
   `algebra`, its ring/algebra structures, and `presentation` identify B with
   the stated polynomial quotient. Verdict: exact, up to the explicitly recorded
   algebra equivalence; B is not restricted to a field or an integral domain.
5. The finite list of coefficients: `coefficients` with `coefficients_eq`
   specifies exactly the finite union of the images of all polynomial supports
   under the coefficient maps. Verdict: the list is represented by its finite
   set of coefficient values, without arbitrary extraneous coefficients.
6. Chosen representative stages and lifts: `liftStage`, `liftValue`, and
   `liftValue_colimit` retain one pair for each coefficient. Verdict: individual
   choices are now explicit and no uniqueness or choice-independence is imposed.
7. The selected upper bound u(F): `boundBase`, `boundPair`, `boundPair_le`,
   and `boundOrder` are precisely the choices of
   `def-nagata-directed-finite-upper-bound`. `stage_eq` requires `stage` to be
   `directedFiniteUpperBound boundBase boundPair boundOrder` of the insertion
   of lambda0 into the finite image of all representative stages.
   `stage_ge` and `liftStage_le` record the resulting inequalities.
   Verdict: this is the selected bound, rather than an arbitrary later stage;
   the inequalities are exactly consequences of the dependency bound lemma.
8. Transported polynomials: `relationMap_coeff` specifies each supported
   coefficient as the transition image of its chosen lift; the subtype witness
   k is uniquely determined by its coefficient value. `relationMap_coeff_zero`
   forbids introducing new terms outside the original support.
   `relationMap_colimit` records that applying the colimit map gives each
   original relation. Verdict: exact coefficient-by-coefficient transport,
   not merely any polynomial preimage under a possibly noninjective map.
9. Finite-stage quotient algebra: the ring and algebra structures on
   `stageAlgebra` and `stagePresentation` identify it with the quotient by
   `Ideal.span (Set.range relationMap)`. Verdict: exactly the source quotient
   up to an explicit algebra equivalence, hence finitely presented with no
   separate finiteness hypothesis.
10. Tensor comparison: `colimitAlgebra_map` fixes the scalar map to
    `(colimit.ι F stage).hom`. `tensorPresentation` records the tensor quotient
    identification in the displayed equality of the node;
    `tensorPresentation_variable` fixes this identification on every variable.
    `beta` has the actual tensor domain, and `beta_eq` fixes it to
    `presentation.symm.toAlgHom.comp tensorPresentation.toAlgHom`.
    Verdict: the identity on the two polynomial presentations, not an arbitrary
    map. Mathlib uses `A ⊗[A_stage] B_stage` for its standard A-algebra instance;
    the tensor commutation equivalence identifies this with the node's
    `B_stage ⊗[A_stage] A`. This reverses factors only, not their scalar map.
11. Stage spectrum over its base and over the fixed earlier stage:
    `stageMorphism` is `Spec.map` of the stage algebra map;
    `baseMorphism` composes it with `Spec.map (F.map (homOfLE stage_ge))`.
    Verdict: both structure morphisms specified in the node are present.
12. Later base-changed schemes and transition maps: `baseChanged` is the
    recorded dependency `baseChangeDiagram`, applied to `F.op ⋙ Scheme.Spec`
    and `stageMorphism`, indexed by `Over (op stage)`.
    Its objects are `Spec B_stage ×[Spec A_stage] Spec A_j`; the affine
    fibre product is the spectrum of the indicated tensor product.
    Verdict: exactly the cofinal subsystem j >= stage and its transition maps,
    not arbitrary schemes; the recorded construction is reused without copying.
13. Limit term and projections: `baseChangedCone` is the dependency
    `baseChangeCone` applied to the Spec colimit cone, and `baseChangedLimit`
    is its vertex. Verdict: the vertex is exactly
    `Spec B_stage ×[Spec A_stage] Spec A`, i.e. the affine tensor spectrum,
    with the specified compatible projections. No unrelated Scheme field or
    independent limit choice remains. The limiting assertion is a property of
    this standard cone, not a different object or an extra hypothesis.

Dependencies: I read `directedFiniteUpperBound` and
`le_directedFiniteUpperBound` in `Sheaf.Order.DirectedFiniteUpperBound`: the
auxiliary linear order is explicit, unrelated to the preorder; the first folds
selected binary bounds over its sorted finite enumeration. The second gives
exactly the required inequalities from membership. I read
`CommRingCat.exists_finite_data_stage` in
`Sheaf.RingTheory.FilteredColimitFiniteData`: it provides representative lifts
and finite equations, with no injectivity assumption. Individual choices are
recorded here as data; the finite-data existence theorem need not be imported
or invoked to define a record of already chosen lifts, so its unused import was
removed. Finally I read `baseChangeDiagram` and `baseChangeCone` in
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`, lines 2181
and 2196: they contain the actual pullbacks, maps, and compatible projections.
Their recorded dependency was fully usable. There are no new nodes or dependency
modules in this delivery.

Edge cases: the empty index is excluded by the node's own nonemptiness and fixed
stage, not by an additional requirement. The relation family may be empty
(m = 0), giving an empty coefficient set and the selected bound of {lambda0};
n = 0 allows constant relations and no generator equations. The relation 0 has
empty support and its stage lift is forced to be 0; relations that become 0 after
base change may still have nonzero lifted coefficients as allowed by the source.
Zero rings and unit ideals are admitted, so empty spectra are admitted. No
characteristic restriction occurs. All indices, rings and schemes use universe u,
as required by the project for elementwise colimits; u itself is arbitrary and
no test-object quantification in a smaller universe is introduced. A selected
stage can equal lambda0 whenever the specified upper-bound function selects it.

Independent searches (2026-10-11):

- `msearch.py ... leanfinder "descending polynomial quotient along directed ring
  colimit by individual coefficient lifts"`: eight hits, including
  `Ring.DirectLimit.Polynomial.exists_of` and generic ring-colimit constructors;
  none specifies this presentation, its individual lifts, and its selected bound.
- `msearch.py ... loogle "MvPolynomial.map, Ideal.Quotient"`: no hits;
  `Ideal.Quotient` is not recognized by that service, so this alone is not
  evidence of absence.
- `msearch.py ... leansearch "finite stage model of a polynomial quotient with
  coefficient lifts and selected bound"`: service unavailable (Internal Server
  Error), recorded as unavailable with no absence verdict.
- `msearch.py ... grep "hasCoeffsOf|FinitePresentationModel|coefficient.*stage|affine-fp-descent"`:
  no hits. Independent local rg searches over Mathlib RingTheory, the source
  WeilConjectures tree, project lean/Sheaf, and dag/lean_names_upstream.json used
  `hasCoeffs`, `Model`, `coefficientLift`, `relationMap_colimit`,
  `baseChange.*Presentation`, `tensor.*quotient`, and the item id/name.
  I opened Mathlib `Algebra.Presentation.ModelOfHasCoeffs`,
  `relationOfHasCoeffs`, and `tensorModelOfHasCoeffsHom`/`Equiv` in
  RingTheory/Extension/Presentation/Core.lean: these choose arbitrary relation
  preimages from an algebra containing coefficients, not the node's specified
  individual coefficient representatives and selected directed upper bound.
  I also opened `Algebra.Presentation.baseChange` in Presentation/Basic.lean:
  it base-changes an already supplied presentation rather than supplying this
  directed-stage bookkeeping. None is an exact existing declaration for the
  item; the existing geometric construction is reused directly.

Mismatches repaired: (H3/H4) replaced an arbitrary stage with its specified
selected-bound equation and retained all individual coefficient representatives;
(H3) constrained every polynomial coefficient to be its transported chosen lift;
(H3) replaced the quotient-domain arbitrary beta with the tensor-domain
presentation-induced map fixed on generators; (H3/H4) replaced arbitrary scheme
fields with the existing dependency diagram and cone, including maps and
projections; (H8/H9) added the standard header and module blueprint marker,
documented each exposed definition, removed unused imports, and registered the
record's ring/algebra projections as global instances so its data is usable
outside this file. No theorem was proved, no definition contains sorry, and no
mathematical node statement was changed. All variables and universe binders were
checked by eye. Server scompile: clean, 3.0 seconds, no warnings or errors.
