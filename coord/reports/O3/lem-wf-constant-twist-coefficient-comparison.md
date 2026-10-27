## Worker report

Stage 2 only: every postponed assertion is a named theorem with `sorry` and a source,
blueprint-owner tag and natural-language proof. Definitions have real data, or are
selected from an existence-and-uniqueness theorem specifying every underlying map.
The item's statement is unchanged. Five modules supply its statement and the missing
interfaces needed to use the recorded coefficient categories.

Hypotheses and clauses, read against the node:

- The finite-field datum is `D : FiniteFieldDatum`; `c : D.CoefficientDatum` supplies
  the distinct prime and algebraic closure. `X₀ : Over (Spec (.of D.k₀))` with
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` is exactly separated finite type.
  The geometric scheme is `D.geometricFiber X₀`. Finite dimension and invertibility
  in stalks are supplied as instances from consequences of these hypotheses, not
  hypotheses on the item. The Noetherian instance is the published Weil-category one.
- The coefficient comparison is `S : FdCoefficientComparisonSystem` and
  `J : ConstantTwistWeilComparison D c X₀ S`. Its finite functor is the published
  coefficient functor on carriers, composed with the completion-unit-normalized
  Frobenius transport. `constantTwistWeilComparison_exists` supplies the common
  equivalence into the actual `WeilDQbar`, rather than a substitute category.
- `E : Padic.FiniteCoefficientFields c.l c.Qbar` and `b : E.valˣ` express a finite
  field containing the unit. Common descent explicitly includes
  `Units.map E.val.subtype.toMonoidHom bE = b`, so the given algebraic scalar is kept.
- `pbcFiniteConstantWeilLine` is literally finite J applied to
  `sfFiniteConstantTwist` of `constantWeilRationalComplex`; `pbcConstantWeilLine`
  is its specified PBC stage inclusion. `constantTwistLine_commonImage` identifies
  this with J of its SF common-stage image. Rescaling is the existing scalar action
  after the original theta; its inverse uses the inverse unit, without a lattice
  stability assumption.
- `constantTwistIntegralUnit_existsUnique` identifies the actual integral J-image
  with the single complex of the completed coefficient ring. Its chain map sends
  every section by `integralDetailedCoefficientComparison.inv`, retaining
  `fdCoefficientTransportFactors`. Thus this is the stated integral representative,
  not a newly chosen coefficient sheaf. `constantTwistLine_rankOne` says precisely
  that this representative is a degree-zero locally free rank-one module.
- `constantTwistLineScalar_existsUnique` uses the original normalized constant-object
  scalar arrow and the actual finite J scalar comparison. `constantTwistLineScalar_assoc`
  writes both three-stage composites with `weilScalarAssociator`. Composita compare
  unrelated finite fields. These are the canonical independence identifications.
- A constructible common-stage sheaf is exactly `sfCommonStageWeilSheaf`; finite
  representatives in descent are `sfWeilSheaf`. `sfCommonConstantTwist` leaves the
  carrier unchanged and rescales theta using the uniquely lifted coefficient scalar.
  `constantTwistCommonDescent` states its heart membership, the finite-stage
  representative of F and of its scalar twist, the actual ambient completed tensor
  isomorphism, and the identification of its target with common J of that twist.
- `pbcFiniteConstantWeilTensor` uses `wfTensor` and `wfTensorFrobenius`, without an
  assumed constructibility condition. `constantTwistFiniteEta_existsUnique` is an
  isomorphism of those ambient Weil pairs to J of the scalar twist, with underlying
  map HEq to `constantTwistRationalRightUnit`. This entails membership in the image
  of the constructible heart. It is stronger at finite stages only in allowing all
  constructible complexes; descent is explicitly restricted to the requested heart.
- The right-unit helper fixes the ordinary map on all flat K-flat representatives by
  `HomologicalComplex.rightUnitor`. The completed map is the unique reflector extension
  of that ordinary map, using `wfCompletionExtend`, and the rational map is its scalar
  localization on all unchanged integral objects. Thus eta cannot be an arbitrary
  isomorphism with the same source and target.
- `constantTwistFiniteEta_natural` states the completed tensor naturality square on
  every rational Weil arrow, including denominators. `constantTwistEta_scalar` states
  its integral scalar square using the prescribed J scalar map; its tensor-side
  comparison is uniquely determined by that square since the right unit is invertible.
  This is the unit-factor restriction of the canonical scalar/tensor comparison.
  Uniqueness and the recorded scalar associator cocycle give the associator equation;
  rationalization and the unique eta normalization give it for arbitrary b.
- `constantTwistTensor_inverse` explicitly applies `J.common.inverse` to the actual
  tensor's constructible target and identifies it with `sfCommonConstantTwist b F`.
  The source is the completed tensor via the uniquely normalized finite eta.
- `constantTwistLocalConjugacy` states the H0 linear intertwining equations for both
  requested domains: every `D.extensionPoints X₀ n hn`, and every closed point with
  every compatible residue-field embedding into D.k. The operator at extension points
  is the recorded iterate, positive-return comparison and point transport, not an
  arbitrary endomorphism. The stalk functor preserves both inverses, so the equations
  are linear conjugacies. No generic-point local Frobenius is introduced.
- The connected clause uses `ConnectedSpace` of the geometric fibre, precisely the
  consequence of geometric connectedness. `constantTwistLine_etaleWeilRealization`
  supplies a fully faithful realization from the existing etale lisse Weil category
  and identifies its constant lines with these actual PBC lines for every E and b.
  `constantTwistLisseBase` is the concrete coefficient universe lift, not an equality
  imposed on universes. `constantTwistLine_etaleRepresentative` relates its completed
  unit to the PBC degree-zero representative; `constantTwistCompletedLisseUnit` relates
  that completed unit to the actual etale constant system by the recorded normalized
  comparison. The etale theta is uniquely normalized to multiplication by b on all
  constant fibres and all finite-fibre paths.
- `constantTwistLine_representation` states dimension one, trivial geometric action
  and `etaleFundamentalRep ... g = b^((d.deg g).toAdd) • LinearMap.id`. It uses the
  recorded `EtaleWeilDegreeData` with its chosen degree-one lift and path. The general
  degree datum specializes to W(X₀) and its degree map supplied by the recorded Weil
  group. This includes negative degrees. The specified B of the repaired definition
  is `pbcConstantWeilLine` itself, so its identification with the constructed line is
  definitional, and the same eta applies.

Dependency declarations used: `Sheaf.Paper.RationalCoefficientCategoryComparison`
(`rationalCoefficientCategoryComparison`, `FdCoefficientComparisonSystem`);
`Sheaf.Paper.SfWeilSheafComplex` (`sfWeilComplex`, `sfWeilSheaf`, common-stage versions,
`sfWeilStageObject`); `Sheaf.Paper.PbcWeilCategory` (`WeilD`, `WeilDQbar`,
`weilFrobeniusPullback`, `weilScalarSystem`);
`Sheaf.Paper.ConstantWeilStructure` (`constantWeilIntegralObject`,
`constantWeilRationalComplex`, `constantWeilAlgebraicallyClosedComplex`);
`Sheaf.Paper.WeilTensorProduct` (`wfTensor`, `wfTensorFrobenius`,
`wfOrdinaryDerivedTensor`, `wfTensorModel`);
`Sheaf.Paper.ConstantCoefficientScalarNormalization`
(`constantCoefficientRationalScalarIso`);
`Sheaf.Paper.LocalFrobeniusTrace` (point transports, return comparisons, iterates and
closed-point local operator); `Sheaf.Paper.EtaleWeilFundamentalRepresentation`
(`etaleFundamentalRep`, `etaleGeometricRep`, `EtaleWeilDegreeData`);
`Sheaf.Paper.LisseIntegralSmallCoefficients` (the published lisse systems);
`Sheaf.Paper.LisseCompletedSystemData` (`Base`, `completedRing`, `Comparison`, `IsFreeSystem`).
The existence theorem for the completed-system comparison is a proof dependency only;
no theorem node is added to statement dependencies merely for these record types.
The completed tensor reflector, exact pullback transport and PBC finite coefficient
maps are used through those public recorded APIs. The original dependency signatures
and docstrings and the corresponding proof dependencies were read.

Edge cases checked: b need not be integral or valuation zero; b inverse is retained;
E=L is allowed; all three-stage scalar inclusions, unrelated fields via composita;
rational theta need not preserve any integral lattice; arbitrary disconnected X and
empty X occur in all finite tensor, line and descent statements; rank one on the empty
scheme is the local condition, not a nonzero stalk assertion. A base point and connectedness
are used only for the representation clause. Positive extension degrees begin at one;
closed-point embeddings are not suppressed; negative Weil degrees use b inverse.

Searches: msearch LeanFinder for constant-line tensor/J comparison returned only generic
adic-completion/condensed results; Loogle `rightUnitor, smul` gave no exact comparison;
grep `WeilSheaf|WeilD|constantTwist` in Mathlib found no Weil category. Searches in
WeilConjectures and Sheaf found the older upstream `constantTwist`, but it has a different
coefficient model, and no declaration of this item. The helper-node searches are recorded
verbatim with their results in its `mathlib_searches`. DAG text search and
`tools/blueprint_refs.py search 'completed right unit'` found no owning definition node.
The current blueprint under literature/blueprint/latest was read, including the constant
line definition and the first sentence of the constant-twist weight proof. Live missing
source was checked using scompile.py --source. No statement dispute or item correction.

## Dependency modules

`def-wf-constant-weil-twist`: the old upstream declaration builds a line in another
coefficient model. The replacement builds the explicit PBC J-image and its completed
tensor using the node's actual data. It also names the normalized etale presentation
needed to state the representation comparison, without defining a second lisse category.

`lem-weil-constant-weil-structure-stage-independence`: its recorded source was deleted,
as its lean.note states. The replacement retains both original clauses, using the
specified normalized constant-object scalar arrow. The common isomorphism is the
stage inclusion of its inverse followed by the prescribed stage transition. No
separatedness condition is added to this finite-type statement.

## New nodes

`def-wf-weil-coefficient-comparison-interface` owns `PbcWeilCoefficientComparison`.
It defines the normalized transport from the proved coefficient equivalence to the
concrete PBC Weil categories and the common-stage interface. Its `stage_transition`
field requires the SF transition mapped by common J, followed by `stage E`, to equal
`stage L` followed by the inverse normalized finite scalar map and the PBC transition.
This includes equal stages and pins the stage choices through all finite extensions.
The existence theorem is an obligation about this interface, not a replacement for the
proved general coefficient-comparison theorem. The original `lem-fd` node and its
`lean` record are absent from this packet and remain exactly as on current main.
Searches used LeanSearch, LeanFinder, Mathlib/source/Sheaf grep and DAG/blueprint search;
they found only generic base-change and colimit results, recorded in the new node.


`def-wf-completed-constant-right-unit` owns the previously unnamed normalized ordinary,
completed and rational right-unit maps. Its source is the constant-twist comparison's
coefficient multiplication calculation, ultimately the first sentence of the current
blueprint weight proof. LeanSearch, LeanFinder, Mathlib/source/Sheaf grep and DAG/blueprint
searches found ordinary unitors and algebraic completion comparisons but no definition
of this completed PBC map with its specified J integral normalization. It is directly
cited by the item. Existence/uniqueness theorem obligations determine the maps; no data
is selected from a bare existence of an isomorphism.

## Second reading by O3

The dispatcher assigns a single worker and explicitly prohibits other agents; no
independent worker reading is claimed here. The maintainer performs the independent
delivery review specified by the brief. I reread the node and all five modules: the
repairs removed an unwanted separatedness assumption from SF stage transitions and
removed redundant dimension/prime-unit assumptions from the item API. The etale and PBC
coefficient universes are connected by a real coefficient lift, not silently identified.
Every definition was checked for actual data or a unique determining characterization.

## Repair of return on 8da7a3dcd1de

1. H2: replaced the added statement dependency
   `lem-per-lisse-completed-system-comparison` by the landed definition
   `def-per-lisse-completed-system-data`, and replaced its public import by
   `Sheaf.Paper.LisseCompletedSystemData`. The theorem remains in the node's
   original proof dependencies. The definitions used are exactly `Base`,
   `completedRing`, `Comparison` and `IsFreeSystem`.
2. H13/H2: removed the sandbox copy of the proved `lem-fd` node. Its live general
   statement, proved declaration and original `lean.declarations` are preserved.
   The five-module delivery now has a new owning definition node for the supplemental
   Weil interface, cited directly by the item. Every declaration in that module has
   the new owner tag. `ConstantTwistWeilComparison.stage_transition` explicitly
   requires the requested transition square; it is an actual record field, not a
   theorem claiming coherence for arbitrary stage choices. The existence docstring
   explains why representative descent supplies the field. No original lemma is
   overwritten with an X0-specific sorried statement.
3. Rebind audit: see the complete current-main audit below. The old upstream
   constantTwist declaration and modules are not removed or changed. This packet
   changes the definition node's binding to the current explicit PBC construction;
   its mathematical statement is unchanged. Existing upstream callers remain
   source-compatible, and the item supplies the coefficient-model identification.
4. H11 advisory: the independent review was performed by L on the returned immutable
   head, whose return explicitly accepted the item clauses and edge cases. I do not
   claim that my own second reading is independent. The repair changes only the
   required interface coherence, dependency ownership and documentation; L's next
   independent review checks these new changes. The dispatcher prohibits subagents.

## Citer audit for def-wf-constant-weil-twist

I searched every current-main node's `stmt_deps` and `proof_deps` and read each
matching statement and use. There are 17 direct citers including this item, hence
16 other direct citers now (the return counted 10 on its reviewed head). Each is
listed below; none is edited. Text-only mentions outside these dependency fields
are not silently counted as dependencies. In particular the current
`prop-wf-weil-sheaf-representation-equivalence` no longer names the definition in
either dependency field. The fixed `lem-fd` record is not rebound, so all its citers
retain the same proved API.

- `lem-zl-relative-curve-mixedness`: holds true. Normalizing and undoing a constant
  twist still uses a lisse rank-one line with inverse scalar, and compact-support
  projection and weight rescaling have the same meaning.
- `d-real-cohom`: holds true. The Tate convention B_(q^(-n)) uses the same scalar
  character; the Euler-series construction and its local factors are unchanged.
- `lem-wf-constant-twist-weight`: holds true. It already explicitly uses this
  coefficient comparison to identify the completed tensor with scalar theta;
  local eigenvalues are still multiplied by b to the point degree.
- `lem-wf-pure-realizable`: holds true. The second summand's local eigenvalues remain
  c^m times the dual eigenvalues, so the conjugate-spectrum argument is unchanged.
- `lem-wf-constant-twist-cohomology`: holds true. Its constant line in the PBC model
  is exactly the newly bound completed tensor factor, still rank one and finite Tor.
- `lem-wf-l2-purity-rigidity`: holds true. Normalization retains lissity and nonzero
  objects, since the inverse line cancels b, and gives the same weight shift.
- `lem-fd-constituent-nonexceptional-concentration`: holds true. Geometric monodromy
  is unchanged by the twist, while Weil operators are multiplied by nonzero
  b^degree, preserving invariant subspaces, irreducibility and nonexceptionality.
- `def-wf-normalized-real-envelope`: holds true. The displayed tensor, direct sum
  and dual use the same B_b and the same absolute-value normalization.
- `lem-a1-exceptional-constituents`: holds true. A rank-one constant factor on the
  affine line is still this B_b and restriction preserves the explicit line.
- `sk-l-dl-a1-energy`: holds true. The conjugate twist has character b^degree;
  its local spectra and squared-trace calculation are unchanged.
- `thm-a1-line-middle-extension-upper`: holds true. A geometrically constant
  irreducible factor still has rank one and its degree-one scalar identifies
  it with B_b on the connected curve.
- `lem-fd-realified-kernel-real`: holds true. The twisted-dual Frobenius matrix
  remains b^m times inverse transpose, with no semisimplicity assumption.
- `lem-wf-trace-energy-constant-twist`: holds true. The actual completed right-unit
  eta identifies the tensor with b theta without lissity or connectedness;
  the trace-energy scalar is unchanged.
- `def-fd-nonexceptional`: holds true. The definition depends on the geometric
  sheaf, which the explicit constant-line twist leaves isomorphic to itself;
  no new coefficient-model assumption enters its predicate.
- `lem-wf-envelope-real`: holds true. B_b remains lisse of rank one and gives
  unit-modulus normalized eigenvalues, so duality gives the same real envelope.
- `lem-wf-trace-energy-real-envelope-bound`: holds true. Its normalized tensor
  and dual are the same constructions, so the four-times-energy comparison
  uses the same local traces.

The item's own use also holds: the new binding is precisely
`pbcConstantWeilLine`, so the requested comparison with the specified B_b is
literal, and all construction, eta and representation clauses remain as reviewed.
