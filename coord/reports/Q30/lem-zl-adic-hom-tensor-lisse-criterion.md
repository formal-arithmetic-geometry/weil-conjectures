## Worker report

The module `Sheaf.Paper.AdicHomTensorLisseCriterion` states the criterion twice:
`WeilConjectures.rationalAdicHomTensor_lisse_cohomology` for a finite coefficient
field and `WeilConjectures.commonAdicHomTensor_lisse_cohomology` for the fixed
algebraic closure. Both theorem proofs are `sorry`, as required in stage 2.
The two comparison definitions contain actual data, with no new choice or sorry.

Clause-by-clause correspondence:

- The geometric finite field and its algebraic closure are `D : FiniteFieldDatum`:
  `D.k₀` has cardinality `D.q = D.p ^ D.a`, and `D.k` is its algebraic closure.
- The coefficient prime is `l : ℕ` with `[Fact l.Prime]`; `hl : l ≠ D.p` is the
  characteristic exclusion. The existing `LisseRealization.baseInvertible`
  derives coefficient invertibility on all residue fields from these data.
- `X : LisseRealization.Base D l hl` contains the scheme, its map to `Spec D.k`,
  `LocallyOfFiniteType` and `QuasiCompact`. The explicit section hypothesis
  `[hsep : IsSeparated (X.scheme ↘ Spec (.of D.k))]` is retained by `include hsep`
  in both theorems. Thus finite type and separatedness are both present.
- The finite coefficient extension is `E : Type u` with `[Field E]`,
  `[Algebra ℚ_[l] E]` and `[FiniteDimensional ℚ_[l] E]`. Its embedding into a
  fixed algebraic closure is immaterial to the finite-stage category/operations;
  every such finite extension admits that embedding. The common-stage theorem
  has `Ω : Type v`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]` and `[IsAlgClosure ℚ_[l] Ω]`.
- `K : sfRationalConstructibleCategory l E X.scheme` is exactly the raw scalar
  localization of the integral constructible category, without Karoubi completion.
  In the other theorem `generalAlgebraicallyClosedConstructibleCategory l Ω X.scheme`
  is the literal carrier of `intrinsicPbcQbarCategory`. Its noetherian,
  finite-dimensional, prime-invertibility domain conditions follow from the finite-type
  geometric base; its transparent abbreviation introduces no further objects.
- The coefficient units are `pullbackTensorRationalUnit` and
  `pullbackTensorCommonUnit`. The dual is literally
  `(rationalDerivedInternalHom ...).obj ⟨(op K, unit), hdual⟩`, respectively its
  common-stage counterpart. No arbitrary object supplied as a possible dual is used.
- `hdual` states the recorded permitted-Hom-pair property for `(K, unit)`.
  This is exactly the dependency definition's qualification that the specified
  internal Hom belongs to the constructible category.
- `hcomparison : ∀ N, ∃ hN, IsIso (...)` quantifies over EVERY object N of the
  selected category. `hN` types RHom(K,N) on the permitted full subcategory of
  `def-weil-derived-pullback-tensor-hom`; it is a proposition, not additional map
  data. The premise that the comparison is an isomorphism in this category already
  requires its target to be an object of the category. No assertion of unrestricted
  integral internal-Hom closure has been made.
- `rationalAdicHomTensorComparison` and `commonAdicHomTensorComparison` implement
  the exact canonical map. Write D for RHom(K,unit) and T for the recorded tensor.
  The underlying arrow is
  `T(T(D,N),K) → T(D,T(N,K)) → T(D,T(K,N)) → T(T(D,K),N) → T(unit,N) → N`.
  These arrows are the prescribed associator, tensor of the Koszul symmetry,
  inverse associator, tensor of evaluation and identity, and left unitor.
  Applying the recorded closed transpose yields `T(D,N) → RHom(K,N)`.
  Common-stage maps are the already normalized representative classes, including
  scalar comparisons, rather than a new operation on chosen representatives.
- The conclusion quantifies over `∀ j : ℤ`. Its argument is
  `constructibleTruncationCohomology (sfRationalStandardTStructure ... D hl) j`,
  or the same functor for `sfCommonStageStandardTStructure`. It is precisely
  `(τ≤j ⋙ τ≥j) ⋙ [j]`, so the object is standard cohomology in degree zero.
- `IsRationalLisse` and `IsCommonStageLisse` say pro-etale locally a finite direct
  sum of coefficient units. Each chart has its own natural-number rank, including
  zero. Since the argument is standard cohomology it already belongs to the heart;
  no separate hypothesis or conclusion about an arbitrary heart is substituted.
- There is no global integral lisse lattice assumption. The local integral free
  models in the EXISTING lisse definitions are chosen separately on each chart,
  with rationalized isomorphisms, exactly as required by the node.

Dependency declarations read and used:

- `Sheaf.Paper.SfRationalizationKaroubi`:
  `WeilConjectures.sfRationalConstructibleCategory` and its induced category/shift.
- `Sheaf.Paper.IntrinsicQbarCategory`:
  `WeilConjectures.intrinsicPbcQbarCategory`, a transparent alias of the existing
  `generalAlgebraicallyClosedConstructibleCategory` used by all common-stage operations.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedTensor`,
  `rationalDerivedInternalHom`, `constructibleRationalHomPairs`,
  `commonStageDerivedTensor`, `commonStageDerivedInternalHom`, `commonStageHomPairs`.
- `Sheaf.Paper.LisseRationalRealization` and its public dependency modules:
  `LisseRealization.Base`, `LisseRealization.baseInvertible`, `IsRationalLisse`
  (`Sheaf.Paper.RationalLocallyFree`) and `IsCommonStageLisse`
  (`Sheaf.Paper.CommonStageLocallyFree`). The primary realization theorem and its
  normalization statement were also read; they supply the last step of the proof plan.
- `Sheaf.Paper.DerivedAutomorphismHomEvaluation`: `podRationalClosed`,
  `podCommonClosed`, `PodPartialClosed.transpose`, `PodPartialClosed.evaluation`;
  their uniqueness normalizations fix the integral/rational/common-stage maps.
- `Sheaf.Paper.DerivedPullbackTensorIso` (publicly available through realization):
  the rational and common-stage unit, associator, braiding and left unitor.
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalStandardTStructure` and
  `sfCommonStageStandardTStructure`; `Sheaf.Paper.ConstructibleTruncations`:
  `constructibleTruncationCohomology`.

The six added statement dependencies identify these shared interfaces (five
existing landed nodes and the new definition-node record): `lem-pod-derived-automorphism-hom-evaluation`,
`lem-pur-derived-pullback-tensor-iso`, `def-zl-constructible-cohomology-functor`,
`def-real-rational-lisse-heart`, `def-real-common-stage-lisse`, and
`def-weil-constructible-heart`. The cohomology definition node is new in the H2 repair; no dependency module is needed.
All recorded, stated proof-dependency modules are imported, using the Mathlib module
`Mathlib.Topology.NoetherianSpace` for the noetherian irreducible-component leaf.

Source reading: the local Hemo--Richarz--Scholbach PDF, Definition 3.3, Theorem
6.2(2), Corollaries 6.3 and 6.11, and Lemma 7.9. They give dualizability, stability
under the ambient t-structure and locally finitely presented coefficient modules in
the heart. Over a coefficient field these modules are finite free. The current
blueprint smooth-proper relative-purity proof was also opened. The item's own
source explicitly identifies the criterion as an agent formulation of the cited
consequence. No statement correction or mathematical dispute was found.

Edge cases checked before writing and on the final source:

- The zero complex and cohomology in every degree outside its bounded support are
  covered by rank zero in the existing lisse predicates.
- The empty scheme has its empty covering sieve; the predicates impose no nonempty
  cover/index set condition and finite type and separatedness allow this case.
- Disconnected schemes and differing local ranks are allowed: no global rank is
  quantified before the cover members.
- No normality, smoothness, connectedness, or integral lisse lattice condition is added.
- The common-stage closure universe `v` is independent of the scheme universe `u`;
  the existing small finite coefficient models handle this size difference.
- The dual is the internal Hom against the unit, and N ranges over all objects,
  including K, the unit, and zero. An arbitrary comparison or supplied dual pair
  is never a hypothesis.

Searches (all via the prescribed wrapper, except the project rg searches):

- LeanFinder: `A rational adic constructible complex whose canonical internal Hom
  tensor comparison is invertible has lisse finite rank cohomology`.
  Eight hits about internally projective light condensed modules and discrete
  condensed modules; none states this adic criterion.
- Loogle: `CategoryTheory.MonoidalClosed, CategoryTheory.HasRightDual`.
  Zero hits.
- Mathlib grep: `dualizab.*lisse|lisse.*dualizab|adic.*hom.*tensor`.
  Zero hits.
- LeanSearch: `Dualizable rational adic constructible complexes have locally constant
  finite rank cohomology`. Eight results about locally constant module rank and
  discrete condensed modules, no matching theorem.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for the node id, for
  `dualizab.*lisse|lisse.*dualizab`, and for the proposed declaration names.
  No node-id or proposed-name match. Related upstream results concern finite
  coefficients or other perfect/lisse criteria, not this raw-rational comparison
  criterion. Existing exact notion matches are reused as listed above.

Validation: scompile.py checked this module in sandbox and library modes in about
7 seconds each, with no diagnostics. The initial mistaken guess at the module for
the noetherian component leaf was replaced by its actual recorded Mathlib match.
A source review caught the need to explicitly include the section's separatedness
instance; `include hsep` is now present and the file compiled cleanly again.
The final delivery dry run passed: deliver2.py --no-push reported OK, with server
preflight and both per-file compilation modes clean (dry-run commit 4972530d926).

## Second reading by Q30

No independent worker was started: the dispatch brief forbids starting other agents
and delegates independent review to the maintainer. A final self-reading checked
every premise, the two canonical composites, both cohomology conclusions, rank-zero
and varying-rank cases, and explicit retention of separatedness. It found no
remaining mismatch. This is a self-check, not a claim of independent review.

## New nodes

`def-zl-constructible-cohomology-functor` records the existing plain definition
`WeilConjectures.constructibleTruncationCohomology` in
`Sheaf.Paper.ConstructibleTruncations`, line 56, with `existing: true`.
Its source is the cohomology display of the current blueprint's
`prop-constructible-truncations`. The node introduces a preadditive category with
zero object, additive integer shifts, a pretriangulated structure, a t-structure
and an integer i, exactly the generic declaration's binders. The displayed
object formula and the action on arrows are the functor composite
`(t.truncLE i ⋙ t.truncGE i) ⋙ shiftFunctor C i`. The object and morphism universes
are independent. Applying it to the existing standard rational/common-stage
t-structures gives exactly the two conclusion objects in this item. The formula
allows every integer, including negative degrees and degree zero, and the zero
object. It neither asserts boundedness nor adds geometric hypotheses.

Fresh LeanSearch and LeanFinder searches for this composite returned the
individual Mathlib truncation and triangle functors, not an exact composite.
The prescribed Mathlib grep for
`constructibleTruncationCohomology|truncLE.*truncGE.*shiftFunctor` returned no hits
in both Algebra/Homology and CategoryTheory/Triangulated. Project rg found the
exact definition at ConstructibleTruncations.lean:56 and its consumers, with no
WeilConjectures match. DAG rg found only the owning theorem's helper list and two
theorem consumers, not a definition node. Blueprint search found no exact-name
match; its broader cohomology-functor search located the source display and
unrelated ordinary cohomology notions. Full queries and returned names are
recorded in the new node's mathlib_searches. We reuse the declaration without
writing or copying any Lean definition.

## Returned-delivery repair

The independent return at immutable head ac3123a55964 identified one H2 fault:
`prop-constructible-truncations` was added to statement dependencies solely to
obtain the plain cohomology composite. It is replaced there by
`def-zl-constructible-cohomology-functor`. The theorem remains unchanged in
proof_deps and in the proof plan, where its scalar/truncation compatibility is
needed. The comparison and closed-calculus theorem dependencies remain because
their uniquely specified chosen data genuinely enter the canonical maps.

Compared the retained packet with current main: prior differences were only
stmt_deps and lean. The repair preserves every original node field outside those
two fields, and preserves the Lean module byte for byte. It changes neither the
mathematical statement nor any proof or proof dependency. No statement_change is
needed. The initial saved-packet dry run passed at 64a5760f5c2; the reviewer fault
is semantic and was repaired despite that mechanical pass.

Final self-reading by Q30: opened the existing definition and its complete
signature, the new definition node, the criterion node and the full criterion
module. Both conclusions use exactly this plain composite on the recorded
standard t-structures; the generic new node excludes no degree, zero-rank case,
empty scheme or universe. The theorem still supplies only proof-level scalar
compatibility. No new Lean declaration, sorry or arbitrary choice was added.

Repair validation: scompile.py checked the unchanged criterion module in sandbox
and library modes (9.7 s and 7.1 s), with no diagnostics. JSON self-check confirmed
that the original item differs from current main only in lean and stmt_deps, the
new node has exactly the required fields, and the truncation theorem is absent
from stmt_deps while retained in proof_deps.
