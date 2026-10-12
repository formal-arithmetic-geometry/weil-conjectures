## What changed

Reduced `AlgebraicGeometry.RingedSpace.exists_derivedModuleDirectImageComposition` to the
unit isomorphism on direct images of K-injective complexes. Its statement and universe
parameters are unchanged. The new acyclicity module contains the sole new named `sorry`.
The original module proves the categorical combination: the pasted unit is invertible
on K-injectives, the derivability structure gives its right-derived universal property,
and the canonical desc is invertible. Its inverse supplies the desired comparison.
`rightDerived_fac_app` and an explicit quotient-representative calculation prove the
required unit equation. Both private helpers are completely proved.

The public statement import is retained. The proof imports the new acyclicity module and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`. No interface
or definition changes were made. A scoped heartbeat allowance accommodates elaboration
of the concrete sectionwise composition equality; the local compile completes in 43 seconds.

## Proved and sorry left

Proved `AlgebraicGeometry.RingedSpace.exists_derivedModuleDirectImageComposition`
(node `lem-pc-ringed-spaces-derived-direct-image-composition`): one of one original sorries.
The private `derivedCompositionOfAcyclic` and `moduleDirectImage_comp_eq` are proved.

The only new sorry is
`AlgebraicGeometry.RingedSpace.isIso_moduleDirectImage_unit_on_kInjective`, in
`Sheaf.AlgebraicGeometry.RingedSpaceDirectImageKInjectiveAcyclic`, node
`lem-pc-ringed-space-direct-image-kinjective-acyclic`. It asserts the second unit is
invertible only at direct images of K-injective complexes. It does not assert a natural
composition isomorphism, and the construction and unit equation are proved separately
in the original module. Existing sorries in imported modules remain existing obligations.

## No longer needed

Removed the proof imports `Sheaf.AlgebraicGeometry.DerivedPullbackComposition` and
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral` from the original module.
Its direct proof dependencies no longer include
`lem-pc-ringed-spaces-derived-pullback-composition`,
`lem-pc-ringed-spaces-derived-adjoint-general`, or `lem-cat-right-adjoint-composition`.
The scheme-only pullback-composition module and right-adjoint-composition node are not
used by this reduction. The ringed-space derived-adjunction node is still needed by
the natural-language proof of the new acyclicity obligation, so it is not claimed
pruned from the full mathematical closure. K-flat resolution and preservation likewise
remain on the new node's proof plan. No unit's realized statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned pullback-composition Lean declaration is restricted to schemes, whereas
this theorem quantifies over arbitrary ringed spaces with independent derived-category
universes. It cannot be applied here. The new pointwise acyclicity obligation records
the ringed-space K-flat/adjunction argument from the sources and the canonical pasted-unit
compatibility. The generic source-library composition theorem also requires preservation
of K-injectivity, which is not available for arbitrary module direct image; the proved
helper uses only the strictly weaker unit acyclicity condition.

Edge cases: for identity f the new condition is the ordinary unit on K-injectives; for
identity g it is the unit of an exact identity functor. A zero complex satisfies it.
No boundedness or flatness assumption is introduced. The unit record
`sk-thm-picard-duality` has no realized node requiring the original below-unit route.
LeanSearch was unavailable (HTTP 500); LeanFinder, Loogle and source grep were used.

## New nodes

`lem-pc-ringed-space-direct-image-kinjective-acyclic` is the remaining geometric step.
Its separate module states the second right-derived unit isomorphism on direct images
of K-injective complexes. The node has its unchanged ringed-space setting, source,
complete proof in words, three recorded search kinds, and verbatim Lean signature.
The parent node's proof, proof dependencies and proof origin now follow the compiled
universal-property reduction. No change record is needed because existing statements
and definitions are unchanged.


## Second reading by P1

1. **Interface — pass.** Compared the delivered original module against the repository
   with `diff`. Extracted the existing theorem's signature through `:= by` and checked
   byte-for-byte equality. Universe binders, hypotheses, conclusion and unit equation
   are unchanged; no existing definition changed. The public statement import is
   unchanged and both added imports are proof-only. The new module publicly imports
   only the module needed by its signature. No change record is required.
2. **Proof and axioms — pass, with the reported remaining obligation.** Compiled both
   modules through `lcompile.py --all`: 3.1 s and 45.1 s, no errors or warnings.
   Inspected every proof and scanned the delivery for prohibited declarations and
   attributes. The only delivered `sorry` is the named public acyclicity theorem;
   there are no definitions with postponed data. A scratch copy with explicit
   `#print axioms` compiled: both private helpers use only `propext`,
   `Classical.choice`, `Quot.sound`; the original theorem and new acyclicity theorem
   additionally use `sorryAx`, consistently with the reported new and imported
   obligations. Removed the scratch Lean file before delivery. This is a proved
   categorical reduction, not a claim that the full target closure is sorry-free.
3. **Split statement — pass.** Read the new statement and its full docstring proof,
   checked its node and searched independently with LeanFinder, Loogle and source
   grep using homotopically-injective and pushforward/acyclic terminology. Inspected
   the nearby injective-module acyclicity, open-restriction K-injectivity and global
   Hom comparison declarations; none supplies the unbounded ringed-space unit
   assertion. Checked Stacks Tags 0D5S, 079W and 0D5T against the proof plan. The
   necessary compatibility of derived and underived adjunctions is part of the
   remaining mate calculation, not something supplied merely by existence of an
   arbitrary adjunction. The plan explicitly retains that calculation. For f an
   identity the condition is the unit on K-injectives; for g an identity its unit
   is invertible on every complex; zero complexes satisfy it. Non-flat structure
   maps do not make pushforward K-injective, and the statement correctly avoids
   that stronger assertion. The new statement is a pointwise acyclicity part of
   the argument: the original module independently constructs the natural
   comparison and proves its exact unit equation. No short closure of the geometric
   obligation was found.
4. **Route and pruning — pass.** Read the upstream `RightDerivedFunctor.Comp`:
   its composition isomorphism requires preservation of K-injective complexes,
   unavailable here. The private helper reuses its pasted unit and the existing
   derivability/universal-property machinery with the weaker pointwise condition.
   The quotient representative calculation removes the composition comparison
   without changing its orientation. All retained imports are used. Compared the
   old parent `proof_deps`: all three removed dependencies are enumerated in
   `No longer needed`, with derived adjunction correctly retained in the new
   obligation's mathematical closure. The scheme-only pullback-composition theorem
   cannot serve the arbitrary-ringed-space signature. Read
   `dag/units/sk-thm-picard-duality.json`: its realized statement and step arrays
   are empty, so this reduction bypasses no realized unit step. The inherited
   original docstring describes the mathematical adjoint route; the report and
   updated DAG describe the actual Lean reduction.
5. **DAG — pass.** The parent's three proof steps match the underived equality,
   pasted-unit invertibility and universal-property proof; its sole new direct
   dependency is the acyclicity node. The new node records its setting, source,
   complete proof steps, union of dependencies, proof origin, search kinds,
   creation, blueprint ancestry, chapter/unit and Lean declaration/signature.
   Its proof does not invoke the parent composition theorem, avoiding circularity.

Second-reading changes: appended independent search evidence to the new node and
this review to the report. No Lean proof, statement, definition or import was changed.
