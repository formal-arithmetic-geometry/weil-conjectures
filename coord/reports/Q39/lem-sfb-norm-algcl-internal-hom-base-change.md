## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CondensedRing.normAlgClInternalHomBaseChange`
in `Sheaf.Paper.NormAlgClInternalHomBaseChange`. Its only postponed theorem is the item
itself. The auxiliary declarations give transparent abbreviations for existing categories
and functors, definitions of the actual derived scalar functor and counit,
the normalization of the specified reassociation,
and the evaluation-transpose comparison. They introduce no alternative tensor product,
internal Hom, constructibility predicate, or derived category.

The source read is the current main-20261015 blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), together with the item's agent-supplied nineteen-step proof. The module's
theorem docstring carries all nineteen steps. This node is an agent coefficient-topology
obligation; the source record explicitly says its exact literature proof is wanted.
No new literature-proof claim is made here.

Clause audit:

- A prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. Positive characteristic different from ell is
  `(p : ℕ) [Fact p.Prime] (_hpℓ : p ≠ ℓ)`, with `[Field k] [CharP k p]`.
- A separated finite-type k-scheme is `X : Scheme.{u}`, `[X.Over (Spec (.of k))]`,
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]`, `[QuasiCompact ...]`, and `[IsSeparated ...]`.
  The first two morphism predicates are the project's finite-type convention.
- The algebraic closure with its extended norm topology is `Ω : Type u`, `[NormedField Ω]`,
  `[NormedAlgebra ℚ_[ℓ] Ω]`, and `[IsAlgClosure ℚ_[ℓ] Ω]`. There is no completeness instance.
  Omega and k live in the scheme universe, avoiding a Type-0 coefficient restriction.
- The finite intermediate field is `E : IntermediateField ℚ_[ℓ] Ω` with
  `[FiniteDimensional ℚ_[ℓ] E]`; the subtype topology and norm are inherited from Omega.
- A and B are `condensedRingObj (Profinite.continuousMapRingObjOfUniverse E) X` and
  `condensedRingObj (Profinite.continuousMapRingObjOfUniverse Ω) X`, respectively.
  Their profinite sections are all continuous maps, with the existing canonical universe
  lift, pointwise operations, and precomposition restrictions. These are actual p_X^*
  pulled-back internal ring objects. The map is postcomposition by E.val.toRingHom.
- C, c, and C_X in the introductory coefficient convention do not occur in the comparison
  or in its hypotheses. Their finite-subextension-valued construction remains publicly
  imported from EllAdic; no identification of C with B is used or asserted.
- The ambient categories are `DerivedCategory (Mod ... (condensedRingObj ... X))`, through
  the transparent `normHomModules` abbreviation. These are internal module objects and
  ordinary unbounded derived categories. The existing `derivedHom` is used on both sides.
- `normHomScalar` is exactly `Mod.extendScalars (coefficientMap a X)` and
  `normHomDerivedScalar` is its existing total `leftDerivedFunctor`, so S_B is the actual
  derived relative scalar tensor, with no flat coefficient hypothesis.
- Bounded constructible K and N use the recorded `constantModelBoundedConstructible`,
  separately for each input. This is the finite constant scalar model convention, not
  arbitrary locally finitely presented coefficient-function matrices.
- `NormHomScalarReassociation` is the type of natural derived scalar tensor
  reassociations. The existential conclusion supplies `d` together with
  `NormHomScalarNormalized d`. This predicate existentially supplies an ordinary natural
  comparison fixed on 1 tensor (x tensor y), using the actual scalar-adjunction unit;
  a cochain comparison fixed on every signed totalization summand; and its compatibility
  with d on K-flat representatives through the actual derived cochain counits and Q's
  tensor comparisons. These equations specify the balanced reassociation without an
  arbitrary coefficient twist. The witnesses are conclusions, not extra hypotheses.
- `normHomComparison d K N` is the actual `derivedTensorHomAdjunction` transpose of
  inverse reassociation followed by scalar extension of evaluation. It uses Mathlib's
  left evaluation. Symmetry of the specified balanced reassociation identifies it with
  the displayed right-evaluation transpose in the node.
- After normalization, the next conjunct asserts `IsIso` of that specified map for every
  bounded constructible K,N. `NormHomComparisonNatural` spells out contravariant K and
  covariant N naturality with f : K' → K and g : N → N'. This formal equation holds on
  all ambient objects; invertibility is asserted under both constructibility hypotheses.
- No global cohomological dimension, global-section comparison, full faithfulness,
  C-to-B flatness, A-to-B flatness, or completeness hypothesis or conclusion is present.

Dependency interfaces read and reused:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `compactificationOverField` and its setting convention (no compactification is needed
  for this local comparison).
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `padicAlgClRingObj`, and their section formulas.
- `Sheaf.Topology.ContinuousMapCondensedRing` and `...ContinuousMapCondensedRingMap`:
  `continuousMapRingObjOfUniverse`, its canonical monoid and commutativity witnesses,
  `continuousMapRingObjMapOfUniverse`, and its `IsMonHom` witness.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, the general ring-object
  convention, with the existing continuous and adic constructors publicly reexported.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`; `...ChangeOfCoefficients`: `coefficientMap`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `Mod`, its action, morphisms and regular-module
  conventions; `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`:
  `Mod.extendScalars`, `Mod.extendRestrictAdjunction`, and the existing total left derivation.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` and Mathlib's
  `DerivedCategory`: the recorded ordinary unbounded derived convention.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  `derivedHom`, `derivedTensorHomAdjunction`, the existing relative K-flat tensor and Q.
- `Sheaf.Paper.CondensedConstantConstructibility`: `constantModelBoundedConstructible`.
- `Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares`:
  `CategoryTheory.derivedCochainCounit`, owned by `def-derived-cochain-counit`. It is
  applied to the actual `normHomScalar`, its actual `leftDerivedFunctor`, and its
  actual `leftDerivedFunctorCounit`, and evaluated at P. No free counit is introduced.
- `Sheaf.Paper.SectionModuleOperationsData`:
  `AlgebraicGeometry.ProEtale.ModuleRingedComparison.internalPureTensor`, owned by
  `def-pd-section-module-operations-data`. This transparent alias is exactly
  `comparison_internalTmul` at the required pro-etale site and coefficient universes.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`:
  `CategoryTheory.Mod.extendRestrictAdjunction`, owned by
  `def-sfb-modobj-extend-restrict-adjunction`; its actual unit fixes insertion of one.
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`,
  `...InternalSectionScalarAdjunction` and `...DerivedTensorRightExact` are comparison
  theorem interfaces retained as proof dependencies only.

All already-recorded proof-dependency modules are imported privately, except where their
interfaces also occur in the statement and hence are public. The added statement
prerequisites are existing landed nodes supplying the coefficient map, ordinary scalar
extension, the definition-owned pure-tensor interface, the scalar adjunction unit, and the
cochain counit used to specify the reassociation. There are no new nodes or
dependency-record repairs: the needed definition nodes have already landed.

Edge cases checked before writing: K=0 and N=0 give zero comparisons; finite local rank zero
is admitted; empty profinite test sets have their unique empty continuous map; the empty
scheme is admitted by the scheme binders; E=Q_ell is admitted by the bottom intermediate
field; positive prime characteristic includes p=2 whenever ell differs; Omega is allowed to
be incomplete. The cochain totalization uses every integer p,q,n with p+q=n, with no bounded
representative assumption. No test-algebra or indexing universe can make a hypothesis
vacuous. The normalization is meaningful for arbitrary ambient derived objects, so it also
specifies the map when scalar extension has unbounded cohomology.

Searches actually run:

- msearch leanfinder: "Extension of scalars of constructible derived internal Hom over
  finite extension of Q_l to the norm algebraic closure". Eight results concerned light
  condensed internal Hom or finite-dimensional module categories; none states this result.
- msearch leansearch: "Derived internal Hom commutes with extension of scalars for bounded
  constructible sheaves". Eight ordinary ModuleCat change-of-rings results; no exact match.
- msearch loogle: "MonoidalClosed.internalHom, Functor.Closed". The service reported the
  first identifier unknown and zero hits; this is not recorded as evidence of absence.
- msearch grep in Mathlib/CategoryTheory:
  `internalHom.*[Bb]ase[Cc]hange|[Ss]calar.*internalHom`: zero hits.
- Direct rg over WeilConjectures and Sheaf for scalar/internal-Hom comparisons found the
  general section-ring scalar-Hom adjunction and tensor comparison, not this constructible
  all-continuous Omega coefficient-change theorem. `normAlgClInternalHomBaseChange` had no
  match. The exact node-id grep over WeilConjectures had no match. The Sheaf node-id search
  found only the downstream topology-defect docstring referring to the needed assertion.

## Return repairs

R1 (returned immutable head 35a4402870a2): the earlier packet put three theorem
nodes in stmt_deps although their theorem conclusions were not used by the
signature. The repair uses already landed definition interfaces, after reading
their nodes and complete declarations:

- Replace both occurrences of `comparison_internalTmul` by the transparent
  `ModuleRingedComparison.internalPureTensor` from
  `def-pd-section-module-operations-data`. Its body is precisely the former
  construction with universes (u+1,u+1,u), not a fresh tensor definition.
- Replace the unowned `rightExact_cochainCounit` helper by the component of
  `derivedCochainCounit` from `def-derived-cochain-counit`, using the actual
  `leftDerivedFunctorCounit`. Both formulas conjugate that counit by the
  quotient-to-homotopy localization comparisons; the latter also spells out
  the mapped-homotopy factorization and associators. A separate module-mode
  scratch probe proved equality of these formulas for arbitrary C,D,F,P
  using their definitions and the mapped identity law. The probe is not
  part of the statement delivery.
- Cite `def-sfb-modobj-extend-restrict-adjunction` for the unit, rather than
  the scalar-section comparison theorem. Import its recorded upstream module
  publicly. Keep the three comparison theorem nodes in proof_deps only.

No new definition node is appropriate: the DAG search found these existing
definition owners. No original definition is copied or moved, and the theorem
signature, natural-language statement, and nineteen-step proof are unchanged.
The item copy was compared with the current main node: only lean, stmt_deps,
and the authorized addition of the two comparison proof dependencies differ.
The original base stmt_deps and proof_deps are all retained.

Additional searches during repair: `rg -l` for `comparison_internalTmul` and
`rightExact_cochainCounit` over dag/nodes found the former in the section-module
operations definition node and the latter in the tensor-comparison theorem node.
Searching definition nodes for cochain counits found `def-derived-cochain-counit`
and its complete canonical transport formula. `blueprint_refs.py search` for
"pure tensor" returned five unrelated blueprint entries; "cochain counit"
returned none. The actual existing project declarations and their owning node
records, rather than a new notion, resolve R1.

## Second reading by Q39

Independent reading by the fresh replacement dispatcher worker on 2026-10-22.
This worker did not author the retained Lean module or the prior repair. No
sub-agent was started. I independently opened the full node statement, the
complete Lean module, the current blueprint paragraph (3), the three
definition-owner nodes, and the full relevant signatures and bodies in
SectionModuleOperationsData, ExactEquivalenceDerivedSquares, ExtendScalars,
InternalSectionTensorComparison and DerivedTensorRightExact. I also reopened
the coefficient-object, coefficient-map, constructibility and derived-Hom
interfaces used by the statement. This reading is distinct from the earlier
packet author's self-audit, which this section replaces.

The current base and sandbox node were compared field by field: the mathematical
statement and proof are unchanged; the only differences are lean, the five
existing definition-owner additions to stmt_deps, and the two return-required
comparison additions to proof_deps. The current base already places
lem-sfb-internal-section-scalar-adjunction in proof_deps, not stmt_deps.
The retained repair preserves that placement.

- The source's prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. Its positive
  characteristic p distinct from ell is `(p : ℕ) [Fact p.Prime]`,
  `_hpℓ : p ≠ ℓ`, `[Field k] [CharP k p]`. Prime characteristic adds no
  restriction for a field of positive characteristic.
- The separated finite-type scheme uses `X.Over (Spec (.of k))`,
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` for the structural
  morphism. The finite-type pair has the required meaning; no properness
  or smoothness hypothesis appears.
- The algebraic closure is `[IsAlgClosure ℚ_[ℓ] Ω]` with `[NormedField Ω]`
  and `[NormedAlgebra ℚ_[ℓ] Ω]`. There is no `CompleteSpace Ω`. Finite E is
  `IntermediateField ℚ_[ℓ] Ω` with `FiniteDimensional ℚ_[ℓ] E`; its subtype
  norm/topology are the required restricted norm/topology.
- `continuousMapRingObjOfUniverse E` and the same construction for Ω have
  ALL continuous functions as sections. `condensedRingObj` is the specified
  coefficient pullback. `normAlgClHomCoefficientMap` postcomposes with
  `E.val.toRingHom`; the coefficient map is the pulled-back ring-object map.
  These are A and B_X. The introductory C and c do not enter the comparison
  or any extra premise; no C-to-B identification is asserted.
- `normHomModules` unfolds to the existing internal `Mod` category. Its
  `DerivedCategory` is unbounded. `normHomScalar` is `Mod.extendScalars`,
  and `normHomDerivedScalar` is its actual total `leftDerivedFunctor`.
  Thus S_B is the required derived relative extension, with no flatness
  premise inserted to use an exact-extension API.
- Each of K and N has its own `constantModelBoundedConstructible` premise.
  Its definition is boundedness intersected with constructibility of every
  cohomology sheaf in the finite constant local-model convention. Neither
  premise was replaced by the more general local-presentation predicate.
- The conclusion first supplies the natural tensor reassociation d and
  `NormHomScalarNormalized d`. In the latter the ordinary comparison is
  fixed on the actual scalar-adjunction units and internal pure tensors;
  the cochain comparison is fixed on every p+q=n totalization summand;
  the derived square uses both K-flat premises, the actual cochain counit,
  and the recorded localization tensorators. All these witnesses are in
  the conclusion. They are not additional assumptions or arbitrary maps.
- The repaired pure-tensor alias has exactly the old body. The repaired
  counit instantiates the generic transport with the actual derived
  counit; its LF and epsilon arguments are specified by definitions.
  Neither replacement invokes a comparison theorem's existential result.
- `normHomComparison` applies `derivedTensorHomAdjunction.homEquiv` to
  `d.inv.app (K, RHom_A(K,N))` followed by scalar extension of the actual
  evaluation counit. Mathlib uses left tensor evaluation; the symmetry
  of the fixed balanced reassociation gives the node's right-evaluation
  display. This defines the required morphism, not an arbitrary iso.
- The next conjunct asserts `IsIso` for that very morphism under both
  constructibility premises. `NormHomComparisonNatural` has f : K' → K
  and g : N → N', so it has the required contravariance and covariance.
- Edge cases remain admitted: K=0, N=0, finite rank zero, the empty
  scheme, the empty profinite set, E=Q_ell, and incomplete Ω. All integer
  totalization indices occur; no bounded representative hypothesis was
  silently introduced. Scheme and coefficient carriers use Type u, with
  the small pro-etale site and coefficient sections in the existing u+1
  convention, including its different object and morphism universes.
- No coefficient flatness, completeness, global cohomological dimension,
  global-section comparison, or full faithfulness appears. Exactly one
  sorry remains, in the named item theorem with all nineteen proof steps
  in its docstring. Every definition has concrete data, autoImplicit is
  false, and the recorded theorem signature is verbatim.

Findings of this independent reading: the retained R1 changes use genuine
existing definition owners. internalPureTensor is transparently the old
comparison_internalTmul at the exact site/coefficient universes. The generic
derivedCochainCounit is instantiated with the actual left-derived counit,
not an unconstrained natural transformation; its component formula reduces
to the old rightExact_cochainCounit using the quotient comparisons and mapped
identity laws. The adjunction unit is owned by the newly cited
`def-sfb-modobj-extend-restrict-adjunction`.
The two comparison theorem nodes occur only in proof_deps. I found no further
mathematical mismatch and made no change to the Lean module or its signature.
The report's previous claim that the author's self-audit repaired R2 was the
remaining documentation defect; it has been replaced by this independent
replacement-worker reading and the checks above.

Validation in this replacement session: the prescribed scompile.py accepted
the retained module under both sandbox and final library module names
(60.0 s and 55.1 s reported), with no errors or unexpected warnings. Exactly
one named theorem has a sorry, and its nineteen-step docstring is unchanged.

## Delivery gate failure

The replacement session first ran the required saved-packet dry run. Compilation
succeeded, but deliver2.py --no-push failed server preflight with:

> (b) statement correction: the item changed in proof_deps without a statement correction (proof and proof_deps change only as far as a correction of the statement forces it)
> (e) the item's statement is corrected but the report has no non-empty section '## Statement corrected' (old statement, what was wrong, the source place, one line per citer)

The current base and sandbox mathematical statements are byte-identical and
neither carries statement_change. The only proof_deps difference is the addition
of lem-pe-internal-section-tensor-comparison and
lem-derived-right-exact-tensor-comparison required by R1. The read-only inspection
of deliver2.py lines 133-140 confirms its explicit authorization for these
return-required dependency-only additions. Its server preflight contradicts
that supported operation. Removing the additions would undo R1; inventing a
mathematical correction would misrepresent the checked statement. No launcher
or project tool was edited or bypassed. The repaired packet is retained.

## Saved-packet retry, 2026-10-22 05:34 UTC

The next replacement worker inspected the retained report and ran the prescribed
saved-packet deliver2.py --no-push before making any changes. Its per-file server
compile passed with no unexpected warnings. Server preflight again returned
exactly the same two errors quoted above. Nothing was pushed.

A fresh field-by-field comparison with the current read-only main node confirms
that statement and proof remain unchanged, and neither node has statement_change.
Only lean, five added existing definition owners in stmt_deps, and the two
R1-required additions in proof_deps differ; no dependency was removed.
Read-only inspection confirms deliver2.py explicitly permits these additive
return repairs, while tools/stage2_delivery.py classifies any proof_deps change
as a statement correction and tools/node_fields.py rejects it when the statement
is unchanged. This is a reproducible conflict in the delivery tools, not a Lean
error or an unrepaired mathematical statement. The existing independent second
reading and complete R1 repair are retained. The tools were neither edited nor
bypassed; the packet is preserved for delivery after the gate is repaired.

## Saved-packet retry, 2026-10-22 05:37 UTC

This replacement worker inspected the saved report and ran the prescribed
deliver2.py --no-push on the retained packet before changing it. The server
compile passed; preflight again rejected the same two R1-required proof_deps
additions as a statement correction, and consequently demanded a Statement
corrected section. Nothing was pushed.

A fresh field-by-field comparison with the read-only main node confirms that
only lean, five additive stmt_deps and two additive proof_deps differ. The
mathematical statement and proof are unchanged, and there is no statement_change.
Read-only inspection of deliver2.py confirms that its dependency-only return
repair path expressly permits additive proof_deps. The project preflight still
classifies that operation as a correction. Removing those dependencies would
undo R1, and inventing a statement correction would be inaccurate. The existing
repair and independent reading are retained. No tool was edited or bypassed.

## Saved-packet retry, 2026-10-22 05:40 UTC

This replacement worker inspected report.md and ran the required saved-packet
dry run before changing anything. The per-file server compile passed. The
server preflight again failed with both concrete diagnostics:

> (b) statement correction: the item changed in proof_deps without a statement correction (proof and proof_deps change only as far as a correction of the statement forces it)
> (e) the item's statement is corrected but the report has no non-empty section '## Statement corrected' (old statement, what was wrong, the source place, one line per citer)

The fresh base-to-sandbox JSON comparison again found only lean, five additive
stmt_deps and the two return-required additive proof_deps. No mathematical
statement or proof changed, and no dependency was removed. Read-only inspection
of deliver2.py confirms its explicit additive proof-dependency return-repair
authorization, while stage2_delivery.py and node_fields.py classify and reject
the same operation as a statement correction. This is the same reproducible
tool conflict; no substantive packet defect is reported by this dry run.
The retained R1 repair and independent second reading remain intact. No tool
was patched or bypassed, and nothing was pushed.

## Saved-packet retry, 2026-10-22 05:42 UTC

The replacement worker inspected the retained report and ran the prescribed
saved-packet deliver2.py --no-push before changing anything. Server compilation
passed, but server preflight returned the same two errors: proof_deps changed
without a statement correction, and no Statement corrected report section.
Nothing was pushed.

A fresh parsed comparison against the read-only current main node found only
lean, five added stmt_deps, and the two R1-required added proof_deps; no
dependency was removed, and statement and proof are unchanged. Neither version
has statement_change. Read-only inspection confirmed deliver2.py explicitly
permits additive proof-dependency return repairs, whereas node_fields.py rejects
them and stage2_delivery.py consequently requests a correction section.
Removing the dependencies would undo R1; inventing a mathematical statement
correction would be inaccurate. The repaired Lean packet and independent
replacement-worker second reading are retained. No tool was edited or bypassed.

## Saved-packet retry, 2026-10-22 05:46 UTC

Ran the prescribed saved-packet dry run before changing the packet. It again
failed only (b), rejecting the two R1-required proof_deps additions without a
statement correction, and (e), demanding a Statement corrected section.
A fresh parsed comparison confirms statement and proof are identical to the
read-only base; only lean, five additive stmt_deps and the two additive
proof_deps differ. Read-only inspection again confirms the conflict between
deliver2.py's additive return-repair authorization and the server preflight's
correction classification. No tool was modified or bypassed. The repaired
packet and its existing independent second reading remain retained; nothing
was pushed.

## Saved-packet retry, 2026-10-22 05:52 UTC

Inspected the saved report and ran the prescribed deliver2.py --no-push before
changing the packet. Server compilation passed. Current server preflight again
rejected only (b), the two R1-required proof_deps additions without a statement
correction, and (e), the resulting demand for a Statement corrected section.
A fresh parsed comparison with current main confirms unchanged statement and
proof, five additive stmt_deps, and two additive proof_deps; neither node has
statement_change. Read-only inspection confirms deliver2.py expressly permits
these additive return repairs, but node_fields.py rejects them and
stage2_delivery.py requires the correction section. The existing R1 repair and
independent replacement-worker reading are retained. No tool was edited or
bypassed, no mathematical correction was invented, and nothing was pushed.

## Saved-packet retry, 2026-10-22 06:18 UTC

Inspected the retained report and ran the prescribed saved-packet dry run
before changing the packet. Server compilation passed. Preflight checked
against base b5fca40fc and again failed only (b), proof_deps changed without
a statement correction, and (e), the resulting demand for a Statement
corrected section. Nothing was pushed.

A fresh parsed comparison with the read-only main node confirms unchanged
statement and proof, five additive stmt_deps and the two R1-required additive
proof_deps, with no removals or statement_change. Read-only inspection of
deliver2.py confirms its explicit additive proof-dependency return-repair
authorization; node_fields.py and stage2_delivery.py instead classify and
reject those additions as a statement correction. Removing the additions
would undo R1; a fictitious mathematical correction would be inaccurate.
The existing repaired module and independent second reading are retained.
No tool was edited or bypassed.

## Saved-packet retry, 2026-10-22 06:46 UTC

Inspected the retained report and ran the prescribed saved-packet
`deliver2.py Q39 lem-sfb-norm-algcl-internal-hom-base-change --no-push`
before changing anything. The wrapper completed its server compile phase and
reached server preflight, which checked base d1b772572 and rejected exactly:

> (b) statement correction: the item changed in proof_deps without a statement correction (proof and proof_deps change only as far as a correction of the statement forces it)
> (e) the item's statement is corrected but the report has no non-empty section '## Statement corrected' (old statement, what was wrong, the source place, one line per citer)

A fresh parsed comparison against the read-only current node confirms unchanged
statement and proof, five additive stmt_deps, and the two R1-required additive
proof_deps; no dependency was removed and neither node has statement_change.
Read-only inspection of deliver2.py confirms its explicit additive
proof-dependency return-repair authorization. The preflight's node_fields.py
instead rejects those additions with an unchanged statement. This remains an
actual conflict between the authorized wrapper operation and its server gate.
The existing R1 repair and independent replacement-worker reading are retained.
No tool was edited or bypassed; no fictitious statement correction was added;
nothing was pushed.

## Saved-packet retry, 2026-10-22 07:13 UTC

Inspected the retained packet and ran the prescribed deliver2.py --no-push
before making changes. Per-file compilation completed, but server preflight
again failed with (b), proof_deps changed without a statement correction, and
(e), the resulting demand for a Statement corrected section. Nothing was pushed.

A fresh parsed comparison against the read-only current node found only lean,
five added stmt_deps and the two R1-required added proof_deps. Statement and
proof are unchanged; no dependency was removed. Read-only inspection of
deliver2.py confirms its explicit additive proof-dependency return-repair
authorization. tools/node_fields.py still rejects precisely that change, and
tools/stage2_delivery.py labels it a correction. Removing those dependencies
would undo R1; recording a mathematical correction would be inaccurate. This
is a delivery-tool refusal, not a compiler failure. The saved repair and
independent reading remain intact. No tool was edited or bypassed.

## Saved-packet retry, 2026-10-22 07:27 UTC

Inspected the retained report and ran the prescribed saved-packet dry run.
Compilation passed. Server preflight again rejected (b), the R1-required
proof_deps additions without a statement correction, and (e), the resulting
demand for a Statement corrected section. A fresh parsed comparison confirms
that statement and proof are unchanged; only lean, five additive stmt_deps
and two additive proof_deps differ from the read-only current node.
Read-only inspection confirms deliver2.py authorizes these additive return
repairs, while node_fields.py rejects them and stage2_delivery.py classifies
them as a statement correction. The retained R1 repair and independent
second reading remain intact. No tool was edited or bypassed; nothing was pushed.

## Saved-packet retry, 2026-10-22 08:27 UTC

Inspected the retained report and ran the prescribed saved-packet dry run before
changing anything. Server compilation passed. Preflight against base 41fc3b8a1
again rejected (b), the two R1-required proof_deps additions without a statement
correction, and (e), the resulting demand for a Statement corrected section.
A fresh parsed comparison with the read-only current node confirms unchanged
statement and proof, five additive stmt_deps and two additive proof_deps, with
no removals or statement_change. Read-only inspection confirms deliver2.py
explicitly permits additive proof-dependency return repairs, but node_fields.py
rejects them and stage2_delivery.py classifies them as a statement correction.
The repaired packet and existing independent second reading are retained.
No tool was edited or bypassed, and nothing was pushed.

## Successful saved-packet validation, 2026-10-22 08:36 UTC

The prescribed first saved-packet dry run now passes: commit 3608b7c8ae2
passed server preflight and per-file compilation. The earlier gate-failure
entries above are historical and are superseded by this successful run.
Current main already includes both return-required comparison proof
dependencies and their proof-step citations. The sandbox proof field was
refreshed from current main; the delivery preserves that upstream proof.

The final self-check reopened the full node statement, the full Lean module,
and the three definition-owner records and their definitions. The signature
is verbatim, autoImplicit is false, and exactly one sorry remains, in the
named theorem with its nineteen-step proof docstring. All three comparison
theorem nodes are proof dependencies only. internalPureTensor,
derivedCochainCounit, and Mod.extendRestrictAdjunction are supplied by their
cited definition owners. The retained independent replacement-worker second
reading above addresses R2. No mathematical statement or Lean declaration
was changed in this retry.
