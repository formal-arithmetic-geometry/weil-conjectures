## What changed

Repaired the returned delivery's duplicate declarations. The owned theorem
ModuleCat.raw_transport_counit_equation is now generalized in place to additive
functors between abelian categories, transported through additive equivalences.
It constructs an isomorphism satisfying the counit equation. This is strictly more
general than the existing ring-specific ModuleCat.raw_compatibility declaration.
The latter keeps its exact signature and specializes the generic theorem.

Removed the duplicate private declarations kan_precomp_full,
kan_postcomp_equivalence and derived_equivalence. Their existing proofs in
DerivedExtensionRingEquivRawTransportIso are reused through Lean's supported
proof-only import all. That module is unchanged. The remaining two private helpers
retain specified counits; the existing helpers instead return mere existence, so
these are different, stronger statements required for the normalization calculation.
The change record is coord/changes/raw-transport-counit-equation-repair.md.

The previously completed second reading below is preserved verbatim as historical
evidence for the returned version. It predates this repair and does not certify
the generic signature or import-all reuse. The fresh independent reading of this repair is recorded at the end of this report.

## Proved and sorry left

The corrected and generalized ModuleCat.raw_transport_counit_equation is proved.
The caller ModuleCat.raw_compatibility is proved from it without changing its type.
Every delivered proof is complete: no sorry remains or is added, and none is split off.
The old false universal hole is retired by a recorded interface repair, not proved
as written. Thus zero unchanged original holed statements are proved, one false hole
is retired, and its corrected generalized statement is proved. The caller originally
had no syntactic hole; its new proof has a closure using only the permitted axioms.

## No longer needed

Removed the owned module's direct proof imports
Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor and
Mathlib.CategoryTheory.Localization.Equivalence: their APIs are already available
through the reused helper module. Removed the caller's redundant proof-only
RawTransportIso import and its direct proof dependency on
lem-pc-derived-extension-ring-equiv-raw-transport-iso. The helper module and node
remain transitively needed by the owned generic proof, so they are NOT globally pruned.
Removed the three duplicate private helper proofs and the old sign-obstruction helpers.
No blueprint unit statement or realized step is bypassed: sk-thm-picard-semicon has
empty realized statement/step lists. No additional node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The original arbitrary-isomorphism equation is false: negating an isomorphism preserves
invertibility but reverses the left side alone. With identity ring changes over the
integers, degree-zero cohomology distinguishes the signs. This repair instead constructs
a normalized comparison from universal counits and their lift factorization equation.

The returned version copied three existing private helpers, and its corrected public
statement was identical to its existing caller. Privacy is handled by import all,
without copying or changing the helper module. The public theorem is generalized
mathematically in place, as requested by the return. Its proof requires only additive
functors and additive equivalences; neither rings nor their square hypothesis are used
once the termwise comparison t has been supplied. Edge cases include zero categories
and identity equivalences: no nonzero or scalar-division assumption is introduced.

## Forced adaptations

Sheaf.Algebra.Homology.DerivedExtensionRingEquivRawCompatibility is unclaimed.
The original final application supplies a chosen comparison to an arbitrary-isomorphism
equation. The new theorem instead takes general functors and category equivalences
and produces its normalized comparison. The original application is ill-typed.
Its final three proof lines are replaced with the specialization of the generic theorem,
and its now-redundant proof import is removed. have _ := hRB prevents an unused-variable
warning arising from that specialization. All existing signatures, universes, docstrings
and visibility in this adapted module remain identical. The delivery dry run supplies
the exact original compiler error against the changed dependency.

## Earlier second reading (a previous round; superseded)

Independent second reader, 2026-10-14 (did not write the delivered proof).

1. Compared both delivered modules with the repository using diff. PASS with the
   declared interface repair: the only public signature change is the recorded
   replacement of universal arbitrary-a compatibility by existence of compatible a.
   The entire raw_compatibility signature is byte-identical. No definitions, target
   statements, universes or public imports change. The sign-change counterexample
   explains why the original assertion cannot be proved. The sole textual caller is
   adapted exactly as the change record requires; other import dependents do not
   mention the changed theorem in their statements or definitions.
2. Compiled both modules through lcompile.py --all, with no errors or warnings.
   Temporarily appended #print axioms for both public theorems and all five private
   helpers, recompiled, and restored the files. PASS: each uses exactly propext,
   Classical.choice and Quot.sound, with no sorryAx. Direct source scan found no
   sorry, axiom, unsafe, opaque, implemented_by or extern. No new definition or
   arbitrary data selected from an unproved existence theorem occurs.
3. PASS: no statements are split off and no new holes or nodes are added. Read the
   five fully proved private universal-property helpers and their applications.
   The construction works also for zero categories/rings; it uses no nonzero counit
   or division by a scalar. For identity scalar changes it selects the normalized
   comparison rather than claiming compatibility for its negative. Independently
   searched Mathlib and lean/ using precomposition, postcomposition, equivalence and
   right Kan uniqueness terminology; msearch grep 'IsRightKanExtension postcompose₂'
   returned no exact replacement. Existing RawTransportIso private helpers are
   inaccessible and its public theorem forgets the necessary counit equation.
4. PASS: the proof uses Mathlib rightKanExtensionUniqueOfIso and its defining lift
   factorization, with explicit transport of both universal counits. Import review
   confirms BaseDerivedTensorCohomologyModel supports the signature, ExactFunctor
   supplies mapDerivedCategory, and Localization.Equivalence supplies the derived
   equivalence proof; the latter two are correctly proof-only imports. The caller's
   unused RawTransportIso import and node are fully listed above. The item's old
   proof_deps are both retained; the caller drops precisely raw-transport-iso.
   sk-thm-picard-semicon has empty realized statement and step lists, so this repair
   bypasses no realized unit step.
5. PASS: compared each node against its baseline and its Lean module. Only allowed
   proof/interface-record fields change. The changed statement and lean.statement
   match the corrected signature, and the statement_change records the old false
   assertion and the sole caller. Both proof_deps lists are exactly the unions of
   their proof steps' uses. The four constructive proof steps describe the code's
   universal-property transport, comparison and counit calculation.

Changes by this reader: added this independent review and the explicit accounting
below; no Lean proof repair was necessary.


## Second reading by Y2

Independent second reader, 2026-10-14; I did not write this repaired proof.

1. Compared both complete delivered modules with the repository using diff. PASS
   under the declared interface repair. raw_compatibility has a byte-identical
   signature, universes and visibility. The owned theorem changes exactly as the
   change record says: the false arbitrary-comparison equation is replaced by a
   constructed compatible comparison, for general additive functors and additive
   equivalences. No target or definition changes. The only textual external user
   is the caller, whose proof must specialize the new interface. The counterexample
   is valid: with identity scalar changes over integers, the identity-derived
   comparison and its negative cannot both commute with the nonzero counit on Z[0].
2. Compiled both delivered modules through lcompile.py --all. PASS without errors
   or warnings. Compiled scratch copies with #print axioms for the two public
   theorems and both newly proved private helpers: only propext, Classical.choice
   and Quot.sound occur. Scanned the delivered Lean for forbidden constructs and
   sorry: none occur. Read the imported kan_precomp_full,
   kan_postcomp_equivalence and derived_equivalence proofs. They construct and
   transport universal objects; no arbitrary witness of an unproved existence
   statement supplies data. Removed the scratch probe sources afterwards.
3. PASS: no split-off statement or new node is added. The two local helper
   statements preserve explicit counits, whereas the similarly named upstream
   helpers only assert existence of some counit. They are therefore needed
   refinements, not duplicates. Checked the general theorem on identity
   equivalences and zero abelian categories: no nonzero hypothesis or scalar
   division is needed. The supplied t already expresses the functor square,
   explaining why the caller's hRB is not used in the specialization. Independently
   searched lean/ and ran msearch grep with rightKanExtensionUniqueOfIso,
   isRightKanExtension_iff_precomp and postcompose₂ObjMkIso terminology. Read
   Mathlib CategoryTheory/Functor/KanExtension/Basic.lean, including the canonical
   comparison definition and its lift factorization. No existing assembled
   counit-compatible transport theorem replaces this calculation.
4. PASS: reviewed from the target downward. complex_universal precomposes the
   given counit by the full faithful homotopy quotient; kan_change_iso preserves
   its exact components. Source equivalence transports the first extension;
   localization full faithfulness descends q and makes E an equivalence, so
   postcomposition preserves the second universal extension. The ordinary
   comparison uses t followed by q inverse. The canonical Kan comparison's lift
   factorization, precomposed with inverse source comparisons and postcomposed
   with q.hom, is exactly the final equation; inverse cancellation directions
   agree with the displayed composite. All remaining imports support the
   signature or these proofs; import all is proof-only and reuses three helpers.
   No old owned proof dependency is removed; the caller drops precisely the
   transport-iso direct dependency, which remains transitively used. No module
   is globally pruned. Read sk-thm-picard-semicon.json: its realized statement
   list and its sole realized step list are empty, so no realized route is bypassed.
5. PASS: compared both node JSON files field by field with the repository.
   The caller changes only proof, proof_deps and proof_origin. The owned node
   additionally records the declared statement/interface change. Both
   lean.statement fields match their Lean signatures, and both proof_deps lists
   equal the unions of the proof steps' uses. The owned proof records the reused
   transport helpers and the explicit counit calculation. Read Stacks Tag 06Y6
   (https://stacks.math.columbia.edu/tag/06Y6): it is the derived change-of-rings
   context, not a verbatim source of this generalized categorical theorem; the
   argument is the right Kan extension universal property, as the module says.

Changes by this reader: added this fresh review and replaced the pending-review
sentence. No Lean or node repair was needed. Accounting: zero unchanged original
holed statements proved; one false original hole retired by the recorded repair;
ModuleCat.raw_transport_counit_equation in its corrected generalized form proved;
ModuleCat.raw_compatibility reproved with its exact original statement and with
no sorryAx in its closure. Holes added: none. Split off: none.

Forced-adaptation verification by this reader: compiled a scratch copy of the
repository's original raw_compatibility against the sandbox's changed dependency.
It fails at the final application (line 58): epsilon-zero is a natural
transformation but the generalized theorem expects a derived-category functor
there; elaboration also requests Abelian (DerivedCategory (ModuleCat R0)).
The delivered specialization compiles. Thus the proof edit is forced; the removed
proof-only import is redundant because this caller no longer uses its theorem.
Removed this scratch source afterwards.

## Forced adaptations

### Sheaf.Algebra.Homology.DerivedExtensionRingEquivRawCompatibility
Original against changed dependencies failed:
```
/tmp/forced-adaptation-rsz4_971/lean/Sheaf/Algebra/Homology/DerivedExtensionRingEquivRawCompatibility.lean:58:43: error: Application type mismatch: The argument
  ε₀
has type
  DerivedCategory.Qh ⋙ L₀ ⟶
    (extendScalars (algebraMap R₀ B₀)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
but is expected to have type
  DerivedCategory (DerivedCategory (ModuleCat R₀)) ⥤ DerivedCategory (DerivedCategory (ModuleCat B₀))
in the application
  raw_transport_counit_equation L₀ ?m.640 ε₀
/tmp/forced-adaptation-rsz4_971/lean/Sheaf/Algebra/Homology/DerivedExtensionRingEquivRawCompatibility.lean:58:8: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Abelian (DerivedCategory (ModuleCat R₀))

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.

(with the modules compiled into /tmp/forced-adaptation-rsz4_971/.lbuild) [2.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
