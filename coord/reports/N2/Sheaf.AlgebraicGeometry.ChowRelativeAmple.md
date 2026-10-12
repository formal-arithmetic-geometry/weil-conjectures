## What changed

The existing `AlgebraicGeometry.chow_relative_ample` signature and docstring are unchanged.
Its proof combines two strict conjunct theorems in new modules. The second reader proved
`chow_relative_ample_geometric` directly using proper cancellation, the closed-range criterion,
the existing `ProjectiveSpace.isClosedImmersion_liftBaseChange` instance, and the definition
of `IsProjective`. `chow_relative_ample_twist` remains a named, sourced theorem hole.
All new proof-only imports are plain imports. The existing public imports are retained.
The unused-variable linter is disabled only for the existing theorem, whose unchanged
signature contains the unused existential witness name `hL`.

## Proved and sorry left

Closed original hole: `AlgebraicGeometry.chow_relative_ample`, node
`lem-pc-chow-relative-ample`, by reduction to the two strict conjunct theorems.
Closed the submitted lower hole: `AlgebraicGeometry.chow_relative_ample_geometric`, node
`lem-pc-chow-relative-ample-geometric`; its axiom list contains only `propext`,
`Classical.choice`, and `Quot.sound`.
Added hole relative to the repository: `AlgebraicGeometry.chow_relative_ample_twist`, node
`lem-pc-chow-relative-ample-twist`. This is the only delivered `sorry`.
The upper theorem still depends on this hole: this delivery is a decomposition, not a
complete proof of relative ampleness. One original hole closes and one new hole is added;
the net hole reduction relative to the repository is zero. The submitted two-hole split
has been improved to one hole, but this is not claimed as positive ledger progress.
No definitions or arbitrary data witnesses are added.

## No longer needed

No whole module is claimed pruned. Every old parent proof dependency remains needed in
one of the geometric or twisting arguments; changing the parent's direct dependencies
is encapsulation, not elimination. `Sheaf.AlgebraicGeometry.ProjectiveAmpleInvertible`
moves from the parent to a plain proof-dependency import in the twisting module.
The previously submitted removal of two public Mathlib imports was reversed, and its
unnecessary change record removed. The geometric module needs no twist, tensor pullback,
or ampleness imports; the twisting module needs no public projective-morphism import.

## Where the brief, the DAG or earlier work was wrong

The submitted report called the upper conjunction reassociation a proof without clearly
counting its two new holes. It also described encapsulated dependencies as pruning.
The geometric hole could be closed with existing declarations in a short proof.
The new node statements merely said “the corresponding strict conjunct”; these were
replaced with self-contained mathematical statements. The twisting proof description
needed to first obtain the two closed immersions and explain the affine-spectrum transport.
The earlier review asserted that unit realized fields record these new nodes, but
`dag/units/sk-thm-picard-coherence.json` has empty realized fields. This delivery does
not change that pre-existing bookkeeping gap or any unit statement or route.

## New nodes

`lem-pc-chow-relative-ample-geometric` states the four geometric consequences and now has
an actual Lean proof. `lem-pc-chow-relative-ample-twist` states exactly the remaining
isomorphism, invertibility, and two affine-open ampleness consequences. Each has its own
module, self-contained statement, source, search record, and verbatim Lean signature.
No statement or definition changes; no change records remain.

## Second reading by N2

1. Compared the target module by `diff` and explicitly compared the text from the theorem
   name through `:= by`: the existing signature is byte-for-byte unchanged. Its docstring,
   namespace, visibility, and public imports are unchanged. No existing data or definition
   changed. Verdict: pass.
2. Compiled all three modules in import order using `lcompile.py --all`, without errors
   or warnings. Checked scratch copies with `#print axioms` for each declaration.
   The geometric theorem uses only the three permitted axioms; the twisting theorem uses
   `sorryAx`, and the parent uses the three permitted axioms plus `sorryAx` from that hole.
   No forbidden declarations, hidden proof holes, or hollow definitions. Verdict: pass
   as a partial decomposition, not a complete proof.
3. The two new statements are strict, disjoint portions of the original conjunction.
   The geometric statement is now proved. The remaining twisting statement has a complete
   natural-language proof: first obtain closed immersions from the proved geometric
   theorem, identify the twists by composition, trivialize on standard charts, then
   restrict to affine bases and apply the existing affine-base theorem. Checked m = 0,
   the empty scheme, empty affine opens, and g = identity: no added hypotheses or
   false degenerate cases. Searches with different terminology through leanfinder,
   loogle, msearch grep, and rg on both library roots found the geometric ingredients
   and the affine-base ampleness theorem, but no duplicate complete relative-ampleness
   declaration. The missing global statement is strictly stronger than the affine-base
   ingredient because it addresses arbitrary bases and both affine-open families.
   Verdict: pass; one named hole remains with its source and node.
4. Took the short geometric route using existing Mathlib and projective-space declarations.
   Signature imports remain public; proof-only imports remain plain. Restored the
   affine-base theorem dependency in the twisting module. The No longer needed section
   now distinguishes encapsulation from actual pruning and makes no module-pruning
   claim. Read the coherence unit: its source route is preserved, including the
   projective-space input; its pre-existing empty realized fields are recorded above,
   not asserted to have been filled. Verdict: pass, with existing bookkeeping gap noted.
5. Checked all three node records against the Lean signatures and remaining holes.
   Replaced placeholder new statements by self-contained statements, expanded proof
   steps and corrected their dependency lists to reflect the actual geometric proof
   and the remaining twisting argument. Existing parent fields changed only in the
   permitted proof metadata. Verdict: pass.

Second reading changes: proved the geometric split theorem; repaired new node statements
and proof metadata; made the remaining docstring explain the closed-immersion prerequisite
and affine restriction; restored existing public Mathlib imports; removed the needless
import change record; scoped the linter option to the one existing theorem; corrected
hole counts, pruning claims, and the unit realized-field claim. No existing signatures
or definitions changed. Sources checked against Stacks Tags 02O5 and 01PU online because
the cited local coherent.tex is absent on this machine.

The first dry run required a LeanSearch record in addition to Loogle/LeanFinder and
grep. Ran LeanSearch; it returned Internal Server Error, recorded as unavailable
without a no-match claim. Loogle, LeanFinder and local Mathlib searches succeeded.
