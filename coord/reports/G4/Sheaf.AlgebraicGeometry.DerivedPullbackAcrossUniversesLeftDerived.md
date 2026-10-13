## What changed

Proved `AlgebraicGeometry.exists_derivedPullbackAcrossUniverses_leftDerived`
with its existing signature unchanged. Two proved private helpers first identify
P with `Scheme.Modules.tensorPullback` using both object and morphism formulas,
and then transport the standard derived comparison through the localization
equivalences. Added the plain proof import
`Mathlib.CategoryTheory.Adjunction.Limits` for preservation of terminal objects
by equivalences. No definitions or public signatures changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.exists_derivedPullbackAcrossUniverses_leftDerived`
(node `lem-sc-derived-pullback-across-universes-left-derived`).
The private helpers `exists_derivedPullback_standard_leftDerived` and
`transport_derivedPullback_leftDerived` are proved. Proved 1 of 1 original holes;
0 split off, 0 holes added. No sorry remains in the delivered module.
The independent axiom check reports only `propext`, `Classical.choice`,
and `Quot.sound`, including transitive dependencies.

## No longer needed

None. The unchanged public imports supply the statement's transported functor
and explicit tensor-pullback ring map. All three old proof dependencies remain
used: `def-pc-derived-pullback`, `def-pc-derived-pullback-across-universes`,
and `def-pc-module-pullback`. No module or node is pruned.

## Where the brief, the DAG or earlier work was wrong

Earlier attempts were blocked by a long-line warning in the delivery tool's
appended axiom probe, despite the submitted source compiling warning-free.
The launcher now filters diagnostics located beyond the submitted source;
no tool edit or linter override was made by this worker.

Current retry (2026-10-13): mechanically checked that the existing theorem
signature is byte-for-byte unchanged and every source line is at most 100
characters. Re-read both proved private helpers, the three dependency nodes,
the derived-pullback construction, and the unit realization record. The saved
proof follows the existing node's route, so no node update is required.

The required `deliver3.py --no-push` printed OK, with review class AUTO,
compilation and preflight passing. The generated axiom probe found no forbidden
axioms. Nothing was pushed. The second-reading notes below are retained as
historical checks; their former dry-run blocker is resolved by this retry.

## Earlier second reading (a previous round; superseded)

1. Compared the entire module against the repository version and mechanically
   checked the existing theorem signature byte for byte. X and Y remain arbitrary
   schemes in universe u, the two derived localization universes remain independent,
   and P retains exactly the additive, object-formula, and map-formula hypotheses.
   The comparison and left-derived conclusion are unchanged. Verdict: pass.
2. Compiled the actual module via lcompile.py: exit 0, no warnings, 15.9 seconds.
   Independently compiled a scratch copy with #print axioms on the target:
   exit 0, 23.0 seconds, only propext, Classical.choice, Quot.sound.
   Read both private helper proofs and scanned the delivered source: no sorry,
   axiom, unsafe, opaque, implemented_by, extern, or definition was added.
   choose_spec extracts the property of the existing derivedPullback choice;
   it does not introduce an arbitrary witness in a new data definition.
   Verdict: pass.
3. No split-off statements or new nodes exist. Functor.ext uses both formulas
   to identify E and P with tensorPullback; it does not infer functor equality
   from object equality alone. The second helper assumes exactly the standard
   universal property and proves its transported version. Empty schemes,
   zero complexes, and identity morphisms introduce no additional requirements:
   the argument uses only functor equality and equivalences. Verdict: pass.
4. Read Mathlib's isRightKanExtension_iff_postcomp₁, postcompose₂ObjMkIso,
   isRightKanExtension_iff_of_iso₂, and the definition of IsLeftDerivedFunctor.
   Postcomposition by EX.inverse gives an equivalence of right-extension
   categories, so preservation of terminal objects proves hα. compUniqInverse
   adjusts its target; compUniqFunctor and postcomp₁ adjust its source. The
   final functor is definitionally derivedPullbackAcrossUniverses.
   Searched the library and Mathlib's derived and Kan-extension modules by
   transport, equivalence, postcomposition, and preservation; no existing
   complete across-universe theorem replaces this argument. The preservation
   interfaces do not eliminate the proof that this equivalence preserves the
   extension. Both public imports occur in the unchanged signature and the
   added plain import supplies isEquivalencePreservesLimits. The unit record
   sk-thm-picard-duality has empty realized statement/step arrays; no recorded
   realization is bypassed. Verdict: pass.
5. Read the target node, its three dependency modules, and its unit record.
   The existing node's proof explicitly identifies tensor pullback in the
   standard localization and transports its universal property. Its uses,
   proof_deps, and proof_origin agree with this proof; no node edit is needed.
   Verdict: pass.

Changed during second reading: removed the forbidden generated-probe linter
workaround and its change record; corrected the report's contradictory retry
history. The mathematical proof was retained unchanged.

Required dry run, current second reading (2026-10-13):
`python3 /home/ubuntu/weil-launcher/deliver3.py G4
Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniversesLeftDerived --no-push`
exited 1 after the 14.3-second compile. It logged `SHEAF-PROBED 1` with
no axiom violations, but rejected the generated probe's line 191, column 100,
which exceeds the 100-character limit. The offending `let used` line belongs
to `PROBE` in repository `tools/stage3_delivery.py`, not the submitted source.
The module itself and the independent scratch axiom check compile warning-free.
This is a delivery-tool failure. AGENTS.md sections 3 and 6 forbid repairing
or working around the script here; its maintainer must wrap the probe line.
No push was attempted because the mandatory dry run did not print OK.


## Second reading by G4

Independent current reading, 2026-10-13; the earlier second reading above is
historical, including its resolved generated-probe blocker.

1. Compared the complete delivered module with the repository module using diff.
   Mechanically verified the existing theorem signature is byte-for-byte identical.
   The two localization universes remain independent, and the additive, object-formula
   and morphism-formula assumptions on P and the existential left-derived conclusion
   are unchanged. The original docstring, public imports and visibility are unchanged.
   The only additions are two proved private theorem helpers, a plain proof import,
   and the replacement proof. No data definition or change record is added. Pass.
2. Compiled the submitted module with lcompile.py: exit 0, no warnings, 10.5 seconds.
   Regenerated a scratch copy from the current source with a #print axioms command
   for AlgebraicGeometry.exists_derivedPullbackAcrossUniverses_leftDerived and
   compiled it: exit 0, 13.7 seconds, only propext, Classical.choice, Quot.sound.
   Scanned the source for sorry, axioms, unsafe, opaque, implemented_by, extern and
   skipKernel: none. Read the choose_spec extraction against exists_derivedPullback:
   it retrieves the universal comparison for the existing chosen derivedPullback;
   this delivery creates no chosen data or arbitrary existence-based definition. Pass.
3. No split-off statements, new public statements, new modules or new nodes.
   Both private helpers are proved and strictly isolate parts of the argument.
   Functor.ext uses the morphism formulas as well as object formulas, so identifying
   P with tensorPullback does not assume object equality alone determines a functor.
   The transport uses categorical equivalences without restrictions on objects;
   empty schemes, zero complexes and identity morphisms require no extra hypothesis.
   No new holes to validate or close. Pass.
4. Read Mathlib's IsLeftDerivedFunctor, isRightKanExtension_iff_postcomp₁,
   RightExtension.postcompose₂, postcompose₂ObjMkIso and the preservation interfaces.
   Searched Mathlib by PreservesRightKanExtension, postcomposition and equivalence,
   and the library by transport, derived pullback and left-derived equivalence.
   No already available complete theorem replaces the helper: the preservation
   constructors still require its central preservation argument. Postcomposition
   by EX.inverse is an equivalence of right-extension categories and preserves the
   terminal universal extension. eX changes the comparison target, while eY and
   postcomp₁ change the localization source. The result functor unfolds exactly to
   derivedPullbackAcrossUniverses. The added Adjunction.Limits import is proof-only;
   the public imports supply declarations occurring in the unchanged signature.
   All three original proof dependencies remain used, so No longer needed is complete.
   Read sk-thm-picard-duality.realized (empty statement and step realization lists):
   no recorded unit route is bypassed. Pass.
5. Read the item node and all three proof-dependency nodes, their Lean declarations,
   and the transported functor definition. The existing proof plan identifies the
   concrete tensor functor, extracts the standard universal comparison, and transports
   it through the two localization equivalences, exactly as the submitted proof does.
   proof, proof_deps and proof_origin remain accurate; no node update is needed. Pass.

Changed during this second reading: appended this independent review and regenerated
only the scratch axiom check. Retained the mathematical proof unchanged. Closed hole:
AlgebraicGeometry.exists_derivedPullbackAcrossUniverses_leftDerived; holes added: none.
