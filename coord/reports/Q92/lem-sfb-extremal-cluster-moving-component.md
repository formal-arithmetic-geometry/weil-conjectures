## Worker report

The module `Sheaf.AlgebraicGeometry.ExtremalClusterMovingComponent` states
`AlgebraicGeometry.Scheme.Modules.extremal_cluster_moving_component`, with `sorry` as its
entire proof. Its two auxiliary definitions contain real data: `subcanonicalCliffordIndex`
is the displayed integer formula c(T), and `subcanonicalCanonicalSections` is the image
of the recorded ideal-twist inclusion, expressed as the span of its range. The map is
k-linear, so taking its span does not enlarge the image. These are the notation explicitly
introduced by the item's own statement, not new independent geometric notions.

Hypotheses and clauses, in the order of the node:

- Algebraically closed k: `(k : Type u) [Field k] [IsAlgClosed k]`. There is no characteristic
  restriction. The scheme and the field use the existing geometric framework's universe u.
- X over k, nonempty, connected, projective, reduced: `X.Over (Spec (.of k))`, `Nonempty X`,
  `ConnectedSpace X`, `IsHProjective (X ↘ Spec (.of k))`, `IsReduced X`. H-projective is
  exactly the finite-projective-space embedding convention of def-kun-projective.
- Pure dimension one and ordinary nodal singularities: `D.pure_dimension` and `D.nodal` in
  the recorded `SubcanonicalClusterData`. The latter gives the displayed completed-local-ring
  isomorphism and its compatibility with k; it tests precisely singular closed points using
  `smoothLocus`. No smoothness of the entire curve is assumed.
- Two-connectedness: `hTwoConnected` quantifies over reduced, nonempty closed subschemes A,B
  with disjoint component index sets P,Q covering all components and with the specified
  underlying ranges. The lower bound is the k-dimension of degree-zero module cohomology
  of their scheme-theoretic pullback, using its structural morphism to Spec k.
- Module cohomology: every `scalarCohomology f F 0` is the recorded right-derived
  O-module global-sections functor with scalars restricted along f. Actual section vectors
  use the existing `ProjectiveSpace.fieldSections k F`, i.e. Γ(F,top) with k-scalars.
- Arithmetic genus: every occurrence of g is literally `1 - eulerChar k (unit X)`, in Z.
- The zero-dimensional closed cluster S: `S`, `i`, `IsClosedImmersion i`, and
  `D.zero_dimensional`. `hSsub : IsSubcanonicalCluster i D.dualizing` expressly imposes
  subcanonicity, not merely the empty-or-subcanonical convention in D.
- The canonical line: `D.dualizing`, `D.invertible`, `D.duality`, `D.duality_natural` are the
  existing chosen natural Serre-duality representing datum. This fixes omega_X rather than
  replacing it by an arbitrary invertible sheaf or a mere existence choice.
- F_S and V_S: `subcanonicalModule i D.dualizing` and its `fieldSections`. Its inclusion
  into canonical sections is the existing `subcanonicalModuleInclusion`; the real-data
  helper `subcanonicalCanonicalSections` presents its actual k-vector-space image.
- Length is `Module.finrank k (scalarCohomology (i ≫ X ↘ Spec (.of k)) (unit S) 0)`.
  c(S) is `subcanonicalCliffordIndex k i D.dualizing`, exactly 2g-length(S)-2h0(F_S).
- R and the index and sign bounds: `R : ℕ`, `hIndex`, `hClifford` use respectively the
  recorded `subcanonicalSplittingIndex D` and the displayed integer Clifford formula.
- Minimality and maximal length: `hExtremal` quantifies over every closed immersion j of
  every cluster T with `SubcanonicalClusterData E`, fixing `E.dualizing = D.dualizing`.
  For subcanonical T of index at most R it asserts c(S) <= c(T), and if c(T)=c(S),
  length(T) <= length(S). Fixing the same dualizing object only specifies the same omega_X:
  each T has such E by transferring the fixed pure-dimension, nodal and duality fields
  of D and supplying the stated zero-dimensional and subcanonical properties. It adds no
  property of T. In particular the quantifier includes the empty cluster and full canonical
  zero clusters. It is not restricted to the strict-length range imposed only on S.
- The strict length bounds on S are `hLength` (a natural-number positivity test) and
  `hLengthUpper` (the integer inequality length(S)<2g-2).
- Generality: for every n and every `Module.Basis (Fin n) k (fieldSections k F_S)`, the
  conclusion supplies an open U of `PrimeSpectrum (MvPolynomial (Fin n) k)` containing a
  coordinate k-point. Thus U is nonempty, and its inverse image on affine-space k-points
  is Zariski open. Conversely any nonempty open of this finite affine space has a k-point
  over algebraically closed k. The coordinate point is the prime pulled back from the
  closed point of Spec k along evaluation at the basis coordinates `b.repr s`.
- Generically nonzero s: every component generic germ of s in F_S is nonzero. Because
  the ideal is the unit ideal at the component generic points, this is the node's
  generically nonzero condition on its canonical image.
- Residual S*: quantified as an ideal sheaf J whose zero-dimensional subscheme has
  `imageSubobject (subcanonicalModuleInclusion J.subschemeι omega)` equal to the image
  of `subcanonicalEvaluation F_S omega s`. This is precisely the canonical residual
  characterized by the recorded residual-duality theorem, which supplies its existence
  and uniqueness. Universal quantification over all such J avoids a noncanonical choice
  and is equivalent to making the assertion for that unique residual. No reducedness or
  Cartier hypothesis on J or S is added.
- A common irreducible component: universally quantified reduced closed C with
  `Set.range j ∈ irreducibleComponents X`, with its inherited k-structure. Its maps are
  over k. Every irreducible component has this unique reduced closed subscheme structure.
  Universal implications for these presentations are equivalent to the node's existential
  antecedent that some component has both moving images.
- Both restriction dimensions: `restrictedLinearSeriesImage k j D.dualizing` applied
  respectively to `subcanonicalCanonicalSections k i D.dualizing` and to its J analogue,
  each of finrank at least two. This is the existing actual tensor-pullback restriction
  into H0(C,omega|C), not restriction into the potentially different ideal-twist on C.
- Both conclusions are retained: length(J.subscheme)=2 and h0(F_J)=g-1, with the latter
  equality in Z. The same U works for all generically nonzero points and all components.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.SubcanonicalSplittingIndex`:
  `SubcanonicalClusterData`, `subcanonicalModule`, `subcanonicalModuleInclusion`,
  `IsSubcanonicalCluster`, `subcanonicalSplittingIndex`, with their full definitions.
- `Sheaf.AlgebraicGeometry.SubcanonicalResidualDuality`:
  `subcanonicalEvaluation` (the canonical tensor-Hom evaluation) and
  `subcanonical_residual_duality` (its full signature, including uniqueness, involution,
  finite dimensions and the numerical formulas). This module is publicly imported.
- `def-sfb-restricted-linear-series-image` records the existing definition
  `AlgebraicGeometry.Scheme.Modules.restrictedLinearSeriesImage` in
  `Sheaf.AlgebraicGeometry.MovingLinearSeriesZero`, whose module is publicly imported.
  This definition node is in stmt_deps. The theorem `exists_moving_linear_series_zero`
  remains solely a proof dependency through lem-sfb-moving-linear-series-zero. The shared
  module publicly imports `Sheaf.AlgebraicGeometry.ProjectiveSpace.MRegularConsequences`, whose
  `AlgebraicGeometry.ProjectiveSpace.fieldSections` is used without duplication.
- `Sheaf.AlgebraicGeometry.NodalLineSerreRiemannRoch`:
  `AlgebraicGeometry.exists_nodal_line_serre_riemann_roch`, as the underlying duality
  datum; publicly available through the splitting-index module.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective`; `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `Scheme.Modules.eulerChar`; `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `RingedSpace.moduleCohomology`; `WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`:
  `Scheme.Modules.scalarCohomology`. These are publicly exposed through the recorded imports.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- Recorded Mathlib interfaces: `CategoryTheory.Limits.pullback` and `pullback.fst`,
  `AlgebraicGeometry.IsReduced`, `AlgebraicGeometry.Smooth` and its smooth locus,
  `IsAlgClosed`, `ConnectedSpace`, `irreducibleComponents`, `AdicCompletion`, `MvPowerSeries`.
  Their source signatures and docstrings were read. The nodal expressions are used through
  D, and the other conditions appear directly as above.
- The proof-only import `Mathlib.Algebra.MvPolynomial.Funext` supplies the recorded
  `MvPolynomial.funext_set` of lem-trf-infinite-field-top-form-direction.
  The proof prerequisite lem-sfb-extremal-cluster-residual-nesting has no Lean record yet,
  so its absent module is not imported. No new statement dependency is needed from it.

Edge cases checked: empty X is excluded explicitly and by connectedness. S empty and full
canonical length are excluded by the two strict bounds; neither is excluded from hExtremal.
The residual is allowed to be empty, nonreduced, or non-Cartier. R=0 and all characteristics
are allowed. For an irreducible X the decomposition condition is vacuous as intended.
Subcanonicity forces V_S nonzero, and coherent projective cohomology is finite, so the basis
quantifier covers an actual finite basis. The syntax also permits n=0; it does not assume
n>0. Both inequalities concern the same component, with weak boundary 2 included.
The source's literal all-clusters maximality makes the moving antecedent impossible by the
DAG proof; the Lean retains the implication rather than strengthening the conclusion.

Searches:

- msearch.py leanfinder: `extremal subcanonical cluster residual moving component dimension
  two length two`. Returned unrelated finite-dimensional/covering results, no cluster theorem.
- msearch.py loogle: `Module.finrank, LinearMap.range`. Returned general linear-map range
  finrank lemmas; none states the geometric implication.
- msearch.py grep, AlgebraicGeometry: `subcanonical|residual.*cluster|extremal.*cluster`.
  No matching Mathlib cluster theorem; subcanonical site hits are unrelated.
- rg in `lean/WeilConjectures` for `extremal.cluster|subcanonical` and the exact blueprint id:
  only unrelated subcanonical Grothendieck-topology material, no matching statement.
- rg in `lean/Sheaf/AlgebraicGeometry` located the existing splitting-index, residual-duality
  and moving-zero modules above. Exact names `subcanonicalCanonicalSections`,
  `subcanonicalCliffordIndex`, `extremal_cluster_moving_component` were absent from Mathlib,
  WeilConjectures, Sheaf and dag/lean_names_upstream.json.
- The source PDF at https://pagine.dm.unipi.it/franciosi/lavori/clifford.pdf was read at
  Lemma 3.3 and Steps 1--4, printed pp.236--238. The latest blueprint unit and direct-images
  proof were read. The accepted node and its reviewed six-step argument are preserved.

No statement correction, disputed statement, or dependency-module repair is required.
The new definition-node attachment is described below.
The module was checked with scompile.py in sandbox and library-module mode; both passed
cleanly after qualifying the categorical pullback to avoid the module pullback name clash.

## Second reading by Q92

I made a separate second pass with the node and module open. This is a self-check; no
independent agent was launched because the dispatcher expressly prohibits starting agents.
The maintainer's independent reading remains the delivery review.

I matched all curve hypotheses to the typeclass binders and D's fields, checked that
hExtremal does not impose hLength or hLengthUpper on competitors, and checked that the two
Clifford-index terms use the same fixed dualizing line. I unfolded the two helper definitions:
they are precisely the node's c and canonical image, with no postponed data. I checked that
both restricted images use omega|C and the same C, and that the residual uses the evaluation
image as an ideal sheaf, preserving nilpotents. Finally I checked the order of quantifiers:
U precedes s, J and C; the point condition precedes generic nonvanishing; and both numerical
conclusions follow the two rank hypotheses. The only implementation mismatch found during
compilation was the ambiguous unqualified `pullback`, repaired by its full categorical name.


## New nodes

`def-sfb-restricted-linear-series-image` records, with `existing: true`, the exact landed
`AlgebraicGeometry.Scheme.Modules.restrictedLinearSeriesImage` in
`Sheaf.AlgebraicGeometry.MovingLinearSeriesZero`. There is no new Lean module and no second
definition. Its signature permits every k-morphism C → X and every O_X-module L and subspace
V of its global sections. The value is the k-span of the canonical tensor-pullback images
of sections in V; since that map is k-linear, this is its image. It does not require L
invertible or V finite-dimensional. The source is Franciosi--Tenni Section 2.1, p.228
(the notation for restricted section images), and Lemma 3.3; the canonical map is the
section-normalized tensor-pullback adjunction recorded by def-pc-module-pullback.

Each clause of this definition matches its existing Lean: k is `(k : Type u) [Field k]`;
X and C are `Scheme.{u}` with `.Over (Spec (.of k))`; i is a morphism with
`i.IsOver (Spec (.of k))`; L is `X.Modules`; V is
`Submodule k (ProjectiveSpace.fieldSections k L)`; the target is the analogous fieldSections
of `(tensorPullback i).obj L`; its value is `Submodule.span k (Set.range ...)`, where the
range map is `((tensorPullbackSectionAdjunction i).unit.app L).app ⊤`. All data already exist.
Empty C, the zero module, V=0, and V infinite-dimensional are permitted. No component,
projectivity, or closedness hypothesis is built into the definition.

The searches were run with msearch.py LeanSearch, LeanFinder and Mathlib grep, followed by
rg in WeilConjectures, Sheaf and dag/nodes, and `tools/blueprint_refs.py search
restrictedLinearSeriesImage`. The new node's mathlib_searches retains the full outputs.
LeanSearch found generic restriction morphisms and open-immersion section formulas;
LeanFinder found Proj and ideal-image formulas; Mathlib grep found zero matches.
The project grep found only the exact helper in MovingLinearSeriesZero.lean. The DAG grep
found only the theorem node listing that helper; blueprint_refs found zero blueprint nodes.
Thus no definition node carries this notion, and the existing declaration is reused.

## Returned-delivery repair

Return of immutable head 11930b02ba18, H4/H13, point 1: the earlier delivery added
lem-sfb-moving-linear-series-zero to stmt_deps merely to obtain its plain helper definition.
This was the wrong DAG dependency kind. Replaced that added statement dependency with
`def-sfb-restricted-linear-series-image`, a new definition node attached to the exact existing
helper, using the reviewer's expressly allowed `existing: true` option. The theorem remains
in proof_deps; its module still must be imported publicly because it also exposes the
existing helper used in the statement. No theorem conclusion is treated as a definition.
The module documentation now identifies the definition-node ownership explicitly.

Compared the retained sandbox item to the current shared main node before refreshing its
copy: fields outside lean and stmt_deps agree. The item copy was reconstructed from the
current main record with the retained Lean record and the corrected added definition edge.
The theorem signature, helper bodies, mathematical statement and proof plan are unchanged.
The delivery wrapper rebases the repaired sandbox onto current main in its private worktree.

Second reading of the repair: checked that the new node is kind definition with empty proof
and proof_deps, records the exact signature of the landed def, and has no lean.file or new
module because existing is true. Checked that stmt_deps now contains the new definition ID
and no lem-sfb-moving-linear-series-zero, while proof_deps still contains the latter. The
public import is exactly the new node's recorded module. Checked the definition's zero and
infinite-dimensional edge cases and every binder against the source. This addresses the
single return point without altering the theorem's mathematical content.
