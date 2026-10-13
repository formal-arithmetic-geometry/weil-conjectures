## What changed

Repair: the three helper theorem declarations that duplicated statements in `CoherentSupportUnionExactSequence` have been removed. Their proofs now occur as local proof terms inside the target theorem, so no duplicate global declarations are introduced. The existing theorem `AlgebraicGeometry.Scheme.Modules.exists_coherent_submodule_of_reducible_support` keeps its exact signature. Its proof decomposes the closed support into two proper closed subsets, constructs the actual vanishing ideal of the first, chooses an ideal-power exponent, and constructs the multiplication image H and its inclusion f. Existing quasi-coherent tensor/image and coherent-submodule declarations prove coherence; the abelian cokernel sequence is short exact. The existing stalk formula proves the quotient vanishes outside the first closed subset, including exponent zero. Strictness follows by composing the support bounds with the proper closed inclusions.

One new module, `Sheaf.AlgebraicGeometry.CoherentIdealPowerSupportedOnClosed`, states only the unresolved ideal-power concentration step. Its imports are public because its signature uses their notions. All imports added to the existing item are proof-only plain imports. No definition, existing signature, visibility, or target was changed; no change record is needed.

## Proved and sorry left

Closed the existing hole in `AlgebraicGeometry.Scheme.Modules.exists_coherent_submodule_of_reducible_support` (node `lem-pc-s3-coherent-reducible-support-exact-sequence`): 1 of 1 original holes has a reduction proof.

Added one hole, `AlgebraicGeometry.Scheme.Modules.coherent_ideal_power_supported_on_closed` (node `lem-pc-s3-coherent-ideal-power-supported-on-closed`), in its own new module. It asserts existence of an exponent with quasi-coherent ideal power and the support bound for its multiplication image. It asserts no coherent quotient, exact sequence, or strict support. This is a decomposition: one hole closed, one added, net zero. The upper theorem still depends on `sorryAx` through the open lower statement and imported open statements. No complete axiom-free proof is claimed.

Removed the first worker's unpublished duplicate hole `exists_coherent_submodule_of_support_union_for_closed` and its draft node `lem-pc-s3-coherent-support-union-submodule`; these were never baseline holes and are not counted as progress.

## No longer needed

The old proof dependency `lem-weil-pbc-coherent-support-union-exact-sequence`, module `Sheaf.AlgebraicGeometry.CoherentSupportUnionExactSequence`, is no longer needed by this item and has been removed from its node's `proof_deps`. It was not an actual import in the repository version, so no source import was removed. The former global helper declarations `product_quasiCoherent`, `ideal_proper_locus`, and `power_quotient_stalk_zero` are no longer declarations; their local proof terms remain needed by the target proof. Other library consumers still use that module: no whole-module pruning is claimed. No other old proof dependencies existed.

## Where the brief, the DAG or earlier work was wrong

The first worker's split duplicated `exists_coherent_submodule_of_support_union` and lacked a complete docstring proof. The returned delivery also declared three helper theorems word-for-word equal to private helpers in `CoherentSupportUnionExactSequence`; the repair localizes those proofs to avoid duplicate declarations. Its new node and the item's metadata also failed to describe the actual dependency. Importing the existing support-union module is impossible: its path through CoherentSupportPowerIdealKills, CoherentFormalModule, ModuleSupportProperOverBase, ClosedImmersionPushforwardAnnihilated, AffinePushforwardBaseChange, AffineMorphism, FiniteFreeComplex, FinitePresentationIntegralFiltration, and FinitePresentationSupportReductionFiltration returns to this item. An import of HilbertPolynomial for ideal quasi-coherence also cycles through DirectImage and the filtration modules. The repair isolates only the concentration step, while the remaining construction is explicitly proved without either cyclic import. The split's docstring supplies the finite-affine-cover proof of concentration and quasi-coherence of ideal powers. Its DAG plan names the lower existing ingredients; it does not require importing the cyclic full exact-sequence theorem.

## New nodes

`lem-pc-s3-coherent-ideal-power-supported-on-closed` is the only new node. It belongs to the item's chapter and unit and matches the declaration in `CoherentIdealPowerSupportedOnClosed.lean`. Its source is the ideal-power step of [Stacks 01YD](https://stacks.math.columbia.edu/tag/01YD), using [Stacks 01Y9](https://stacks.math.columbia.edu/tag/01Y9). Searches with leanfinder, loogle, and repository grep found the affine radical-power ingredient and related global annihilation/restriction statements, but no matching concentration statement. LeanSearch returned an Internal Server Error, recorded as unavailable rather than a negative result. No change records were added.

## Earlier second reading (a previous round; superseded)

1. Compared every delivered existing module with the repository version using diff and checked the exact target signature byte for byte. The only existing declaration retains its original hypotheses, conclusion and visibility. No definitions are altered. Verdict: pass.
2. Compiled both sandbox modules in import order using lcompile.py with no errors or warnings. Inspected all declarations and definitions: the only textual sorry is the whole proof of the named lower theorem; no forbidden declaration or hollow definition occurs. A scratch copy with `#print axioms` reports only propext, Classical.choice, Quot.sound, and sorryAx for the target and split. The delivery probe additionally checks every file's constants. Verdict: valid reduction with its reported open dependencies, not an axiom-free completion.
3. Read the new statement against Stacks 01YD and 01Y9 and searched using different words from the first worker. Tested its mathematical edge cases: empty X, zero F, C = X, C empty, K the unit ideal, and K the zero ideal. The first three admit exponent zero where appropriate; with C empty the ordinary support-annihilation argument applies; for the unit ideal the hypothesis already confines F to C; for the zero ideal exponent one kills the product. The recursive power construction handles zero correctly. There is no arbitrary choice of data in a definition: n is obtained only inside a theorem proof, and H is an explicit multiplication image. The new statement omits the coherence, quotient, exactness and strictness work carried out by the upper proof and is strictly simpler. Verdict: pass. The duplicate support-union split was removed.
4. Read the reduction from the top down. The topological cover and strictness use existing topology/set lemmas; coherence, cokernel exactness and the quotient support calculation use existing library/Mathlib declarations. Only ideal-power concentration remains open. Added imports are proof-only and used; original public imports are retained for signature notions. The complete old proof dependency list contained only the support-union node, now recorded as no longer needed. The unit sk-thm-picard-coherence has empty realized statement/step lists; none is bypassed or changed, and the argument keeps the documented ideal-power devissage route. Verdict: pass, one-for-one decomposition with no global pruning.
5. Read both delivered node JSON files against the Lean proof. The original node now records the cover, concentration, coherence/exactness, and quotient-stalk steps and precisely their used nodes. The new node has its self-contained statement, source, full proof plan, proof-dependency union, search results, origin, created/blueprint/chapter/unit records and verbatim Lean signature. No existing node's statement or stmt_deps is changed. Verdict: pass.

Changes made by the second reader: removed the duplicate split theorem/node; added the strictly lower concentration theorem in its own module with a complete source-based docstring and node; expanded the original theorem's real construction, coherence/exactness and quotient support proof; added only necessary proof imports; updated the existing node's proof metadata and rewrote this report to count the result as a decomposition.


## Second reading by C2

1. Compared the existing Lean module and node against the read-only repository with
   `diff -u`, and additionally compared the theorem signature as literal text through
   `:= by`. The signature, original docstring, visibility, and all three public imports
   are unchanged. Only six proof imports and the proof body were added. The existing
   node changes only `proof`, `proof_deps`, and `proof_origin`. Verdict: pass; no
   statement or definition change and no forced adaptations.
2. Independently compiled both delivered modules in import order with `lcompile.py`:
   2.3 and 10.7 seconds, no errors or warnings. Inspected every delivered declaration:
   exactly one textual sorry, the whole proof of
   `AlgebraicGeometry.Scheme.Modules.coherent_ideal_power_supported_on_closed`.
   No forbidden declaration, inline proof hole, or hollow definition occurs. A scratch
   copy of the actual upper module with two `#print axioms` commands compiled and
   reported only propext, Classical.choice, Quot.sound, and sorryAx for both the upper
   theorem and the split. The scratch copy was removed. Verdict: pass as a reduction,
   with open dependencies explicitly acknowledged, not a completed axiom-free proof.
3. Read Stacks Tags 01YD, 01Y9, and the reducible paragraph of 01YF directly. The new
   lemma isolates annihilation on X minus C, with an arbitrary quasi-coherent ideal
   represented by IdealSheafData. No equality of the two closed support pieces or
   strictness is needed for this step. The finite-affine-cover/radical-annihilator
   argument in its docstring proves precisely this assertion. Checked empty X,
   F = 0, C = X, C empty, K = 0, and K the unit ideal: exponent zero handles the
   vacuous/zero cases where applicable, exponent one handles K = 0, and the unit
   ideal hypothesis already confines F to C. No problematic arbitrary witness is
   used in a definition: the exponent is eliminated in a proposition proof and H
   and f are explicit multiplication-image constructions. Fresh leanfinder search
   for Noetherian ideal annihilation returned only affine algebra results; Loogle
   confirmed Ideal.exists_pow_le_of_le_radical_of_fg. Fresh msearch grep and rg on
   lean/ found the global annihilation and restriction comparison statements and
   the full support-union theorem, but no duplicate of the new concentration
   statement. Verdict: true, needed, and strictly below the exact-sequence item.
4. Read the argument from its conclusion backwards. The closed-cover decomposition
   and strict inclusion use existing topology/set lemmas. Tensor/image coherence,
   coherent submodules/cokernels, canonical cokernel exactness, and the quotient
   stalk computation use existing declarations; the exponent-zero branch explicitly
   uses the unit's identity inclusion. Each added proof import supplies a declaration
   used in these steps; each public import in the new module supplies a signature
   notion. Verified the support-union module has an import path back to this item,
   through IdealPowerProductRestrictionZero, IdealTimesQuasiCoherentAffineSections,
   CoherentFormalModule, and the filtration modules. The global annihilation module
   also imports CoherentFormalModule, so importing either cannot close the new hole
   without a cycle. No short replacement for concentration was found. The old
   proof_deps consisted solely of the support-union node, already fully listed under
   No longer needed. The unit sk-thm-picard-coherence has empty realized lists and
   is unchanged; the ideal-power devissage route is retained. Verdict: pass;
   decomposition, net zero holes, and no whole-module pruning.
5. Matched both nodes to the Lean declarations and read their dependencies' Lean
   records or Mathlib matches. The upper node describes the actual closed cover,
   concentration, coherence/exactness and quotient-stalk proof. For both nodes the
   union of proof-step uses equals proof_deps. The new node's recorded Lean signature
   matches its source text verbatim; its source, docstring proof, search records,
   created, blueprint, status, chapter, unit and Lean fields are present. Verdict:
   pass; the existing node's statement and statement dependencies are untouched.

Changes made in this reading: appended this independent review and ran fresh
searches and compilation/axiom checks. No Lean or node repair was required. The
prior report's hole accounting remains: one original hole reduced, one strictly
lower hole added, net zero; no axiom-free completion is claimed.
