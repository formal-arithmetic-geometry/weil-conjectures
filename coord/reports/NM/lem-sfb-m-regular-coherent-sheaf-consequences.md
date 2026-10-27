## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveSpace.MRegularConsequences` states
`AlgebraicGeometry.ProjectiveSpace.mRegular_coherent_consequences`, with its proof
postponed by `sorry`. It constructs the three supporting declarations `fieldSections`,
`fieldEvaluation`, and `regularityMultiplication` from existing functors and canonical
arrows. These are helpers of this theorem, as authorized by the canonical-map rule;
none chooses an arbitrary map or data from an existence theorem.

Hypothesis and conclusion correspondence:

- The field is `(k : Type u) [Field k]`. The projective dimension is `(n : ℕ)`;
  `ι : Type u`, `[Fintype ι]`, and `hι : Fintype.card ι = n + 1` specify its
  homogeneous coordinates. Thus `ℙ(ι; Spec (.of k))` is exactly projective n-space.
  Every n is covered, for example with `ι = ULift (Fin (n+1))`.
- The coherent module is `F` with
  `hF : RingedSpace.IsCoherent (ℙ(ι; Spec (.of k))).toRingedSpace F`.
  This is the finite-type plus finite-type-kernels definition, not merely a
  finite-presentation or quasi-coherence assumption.
- The integer regularity index is `(a : ℤ)`. The notation F(d) is rendered directly
  as `F ⊗ₘ ProjectiveSpace.twist ι (Spec (.of k)) d`.
- `hregular` quantifies over `j : ℕ` with `1 ≤ j` and `j ≤ n`, and asserts
  `Subsingleton` of `RingedSpace.moduleCohomology` in degree j applied to F(a-j).
  This is exactly the stated a-regularity, using the right derived functors of
  module global sections from the recorded cohomology dependency.
- The first conjunct quantifies over every integer b with `a ≤ b`, and repeats
  precisely the same vanishing conditions with a replaced by b.
- The second conjunct quantifies over every integer d with `a ≤ d` and every
  positive natural cohomological degree j. It asserts vanishing of H^j(F(d)),
  including j>n. No degree bound has been discarded.
- The third conjunct says `Epi (fieldEvaluation k p (F ⊗ twist ... b))` for
  every b≥a, where p is the structure morphism to Spec k. Epimorphisms in this
  category are the surjective sheaf morphisms (stalkwise surjections). The domain
  of `fieldEvaluation` is p* of the sheaf associated to the k-vector space of
  global sections of F(b), i.e. H^0(F(b)) tensor_k O. Evaluation is the counit of `(tilde.adjunction).comp
  (Scheme.Modules.pullbackPushforwardAdjunction p)`, which by definition is
  pullback of `Scheme.Modules.fromTildeΓ` followed by the pullback–pushforward
  counit. This retains the specified domain and canonical evaluation, with no
  replacement by a free sheaf on the underlying set of sections.
- The last conjunct is `Function.Surjective (regularityMultiplication ι k F b)`
  for every b≥a. Its actual source is `fieldSections k F(b) ⊗ fieldSections k O(1)`
  in ModuleCat k, so its tensor product is over k. Its target is
  `fieldSections k F(b+1)`. Degree-zero cohomology is global sections.
  The tensorator of `ModuleCat.restrictScalars` sends pure tensors to pure
  tensors; `Scheme.Modules.tensorSectionsMap` takes their tensor section;
  the associator followed by `F ◁ (twistTensorIso ... b 1).hom` gives the
  canonical product in F(b+1). The existing `twistTensorIso` is normalized by
  sending the standard local twist bases to their product basis.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, extending CommRing and DivisionRing.
- `pqf-def-coherent`: its coherent clause (Stacks 01BV) is rendered by the
  existing `AlgebraicGeometry.RingedSpace.IsCoherent`, publicly imported from
  `WeilConjectures.AlgebraicGeometry.Coherent`. Its landed Q25 record remains
  untouched. The item's `lean.note` explains this rendering and the difference
  from Q25's `IsQuasiCoherentFiniteType`; see Return repair below.
- `def-pc-projective-space-twist`:
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`,
  `AlgebraicGeometry.ProjectiveSpace.twist`, the actual pullback of the
  integral-model twist, not a private copy.
- `pqf-def-cohomology`: `WeilConjectures.AlgebraicGeometry.PQFCohomology`,
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`; its recorded
  degree functors are `RingedSpace.moduleCohomology` from
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`.
- The basis-normalized `twistTensorIso` comes from
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistTensor`.
- The proof imports are `Cohomology.EulerChar` (flat base change),
  `Cohomology.Serre` (cohomology bound and quotient by twists),
  `Mathlib.RingTheory.FiniteType` (Noetherian finite-type algebras),
  `Mathlib.AlgebraicGeometry.Modules.Tilde` and
  `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde` (pullback
  quasi-coherence), `WeilConjectures.AlgebraicGeometry.ModulePullbackTensor`,
  and `WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`.
  The unstated proof dependency `lem-sfb-coherent-hyperplane-restriction-sequence`
  has no module to import. No missing notion is needed to state this item.

Edge cases checked against the source and the formulas:

- n=0: the regularity hypothesis and first conclusion have empty degree ranges;
  all twists on P^0=Spec k are trivial, positive cohomology vanishes,
  evaluation is the usual identity after scalar extension, and multiplication
  with H^0(O(1))=k is surjective.
- The zero sheaf: every vanishing holds and both maps have zero target.
- Negative a and b are allowed; b=a and d=a are included; no natural-number
  subtraction is used in twist indices (`j` is cast to ℤ before subtraction).
- The range j>n is retained explicitly. No infinite-field, algebraic-closure,
  characteristic-zero or nonzero-sheaf condition is imposed.
- Coordinate index types and fields have arbitrary universe u. The cardinal
  condition supplies exactly n+1 coordinates; it does not exclude any field
  universe or dimension. Projective space over a field in dimension n≥0 is
  nonempty, so the empty scheme is not an additional case of this statement.

Searches for existing statements:

- `msearch.py ... leanfinder` query: "Castelnuovo Mumford regular coherent sheaf
  projective space global generation multiplication global sections". Eight
  results concerned Proj multiplication and unrelated structure-sheaf maps;
  none states regularity consequences.
- `msearch.py ... loogle` query: "IsCoherent, ProjectiveSpace.twist". Zero
  hits, unknown identifier IsCoherent in the service's Mathlib index.
- `msearch.py ... grep` query:
  `mRegular|MRegular|Castelnuovo|Mumford|regular.*twist|twist.*regular` in
  AlgebraicGeometry. Zero Mathlib hits.
- `rg` with `mRegular|MRegular|Castelnuovo|Mumford|` followed by the item id
  in `lean/WeilConjectures` and `lean/Sheaf`: no theorem of this statement.
  ProjectiveSpace.Resolution has a P^1 specialization only, so is insufficient
  for arbitrary n. The item id has no existing declaration.
- Focused `rg` searches for evaluation, global sections and multiplication in
  the projective-space, module, and Mathlib module-sheaf sources found
  `twistTensorIso`, `tensorSectionsMap`, `fromTildeΓ`, and
  `pullbackPushforwardAdjunction`; these are reused. Searches for scalar
  tensor comparison found Mathlib's lax monoidal `restrictScalars`, reused
  directly rather than constructing a second tensor theory.

Sources read: Stacks `varieties.tex`, definition-regularity and
lemma-m-regular-up/multiply/globally-generated (Tags 08A3, 08A6–08A8),
including the hyperplane induction preceding them. The docstring contains
all nine proof steps of the live node, with their prerequisite node names.
No statement correction or STATEMENT-DISPUTED flag is needed.

## Return repair

The return of immutable head `289c855f62db` identified H13/H2: the packet
rebound the landed Q25 record of `pqf-def-coherent`. As explicitly requested,
`dag/nodes/sec-abelian-varieties/pqf-def-coherent.json` is removed from this
packet. No dependency module or dependency-record change is delivered.

The Lean module and theorem signature are retained verbatim, including
`hF : RingedSpace.IsCoherent ...` and the public import of
`WeilConjectures.AlgebraicGeometry.Coherent`. The upstream predicate was read
again: it is finite type together with finite-type kernels for every map from
finite free modules on every open, exactly Tag 01BV. The landed Q25 predicate
was also read: it is quasi-coherence conjoined with finite type. The item's
`lean.note` now records why this consumer uses the existing 01BV predicate;
it does not rebind the Q25 record. The discrepancy in that dependency record
remains a maintainer decision, as the return directs.

The maintainer's independent reading accepted every item hypothesis and
clause, canonical evaluation and multiplication, the nine-step proof docstring,
and the edge cases. No statement correction is made. The advisory about
`twistTensorIso` is recorded: it is an existing upstream construction in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistTensor`, reused here;
this metadata repair does not assign it a new owner.

Elaboration uses the upstream scoped `⊗ₘ` (`Scheme.Modules.tensorObj`) to
retain the scheme in instance search. This is existing public notation,
not a file-local notation or a new tensor definition.

## Validation

The prescribed `scompile.py` compiled the final module successfully as both
sandbox `Sheaf.Stage2.Sandbox0` (8.5 seconds) and library
`Sheaf.AlgebraicGeometry.ProjectiveSpace.MRegularConsequences` (10.3 seconds),
with no errors or warnings. All variables and universes are explicit, with
`autoImplicit false`. No local instances, private declarations, diagnostic
commands, custom notation or theorem proofs other than `sorry` are present.
Every module line is at most 100 characters. The repaired packet retains that same published coherence interface.
The initial saved-packet dry run passed at `7be2f68fe53`, but still included
the dependency rebind rejected by the maintainer; it is therefore not the
repaired delivery. Fresh compile and dry-run results are recorded below.

Repair validation (2026-10-22): `scompile.py` completed without errors or warnings
for the retained module, sandbox name (8.5 s) and library name (10.3 s).
The final self-check confirms the signature is verbatim in `lean.statement`,
the public coherence import and hF are retained, the packet contains only the
item node and its one module, and only the item's `lean` field differs from
the refreshed base. The wrapper refreshed `lean_audit`; the sandbox copy now
retains that current base metadata. No Lean declaration was changed in this repair.

The repaired `deliver2.py --no-push` passed preflight and compilation at
`ed4d263a293`. Its exact staged set is the item node, its unchanged Lean
module, and this report; the rejected coherent dependency record is absent.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
