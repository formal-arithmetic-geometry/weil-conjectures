## What changed

Replaced the single hole in `LocalTensorFiniteFreeZeroModel.lean` with a complete
Lean reduction. The proof extracts the regular sequence, invokes the existing
`ExteriorAlgebra.exists_koszul_projective_resolution`, constructs a locally
augmented carrier using a new component theorem, proves that the given
augmentation remains a K-flat resolution after restriction using
`AlgebraicGeometry.isKFlat_restrict` and exact restriction, obtains a common roof,
and assembles all fields of `HasFiniteFreeZeroModel`.

Two new modules each state one remaining component, with their source and full
construction/comparison proof in words. `LocalKoszulAugmentedCarrier` has no P
or comparison roof: it produces K, an actual augmentation of K restricted to U
to the restricted quotient sheaf, local K-flatness, and the zero-model term data.
`LocalKFlatTensorRoof` has no Koszul, freeness, bounds or zero-differential
hypothesis: for any morphism and two local augmented K-flat resolutions of an
arbitrary common complex it supplies a quasi-isomorphism roof of their tensor
pullbacks. The roof vertex is chosen after both augmentations.

All existing signatures, visibility and public imports are unchanged. The new
carrier publicly imports only `Sheaf.Paper.KoszulComplex`, rather than the unused
regular-sequence predicates. The new roof privately imports Mathlib
`DerivedCategory.Fractions` and names its `right_fac` construction in the proof
docstring. No
existing definition or other module was changed. The original node's proof and
proof_deps now match the compiled argument. Proof-only imports were added for
the two new components, K-flat restriction, and the proved restriction-limit
instance. The affine sheafification proof import was moved to the carrier module.

## Proved and sorry left

Original hole closed by decomposition:
`AlgebraicGeometry.local_tensor_has_finite_free_zero_model`
(node `split-local-tensor-finite-free`). Its proof contains no sorry.

Two holes added, exactly the whole proofs of named public theorems:

- `AlgebraicGeometry.exists_local_koszul_augmented_carrier`, node
  `new-s1-local-koszul-augmented-carrier`.
- `AlgebraicGeometry.exists_local_kflat_tensor_roof`, node
  `new-s1-local-kflat-tensor-roof`.

This is a decomposition, not a sorry-free proof or a net hole reduction:
one original hole removed, two strictly separate component holes added.
Existing imported holes are unchanged. The existing algebraic Koszul resolution
and open K-flat restriction declarations are invoked directly by the main proof.

Validation: the three-module set and main module compiled through lcompile.py.
The delivery dry run is the final verification. No new definitions, axioms or
private admitted declarations were added.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification` from the main
module; it is still needed and imported by `LocalKoszulAugmentedCarrier`.
The old direct proof dependency
`lem-sc-affine-quotient-resolution-sheafification` is removed from the main
node and retained under `new-s1-local-koszul-augmented-carrier`. Thus it is
no longer a direct dependency, but no original module or node is globally pruned.
All original public imports remain because they support the unchanged signature.
`KoszulProjectiveResolution` remains a direct proof import and is used.

The rejected `LocalTensorFiniteFreeZeroModelData` and
`LocalTensorFiniteFreeZeroModelComparison` candidates and their nodes are not
part of this delivery. Their archived scratch files are not compiled or delivered.
No arbitrary-zero-data lemma is used.

## Where the brief, the DAG or earlier work was wrong

The prior candidate comparison was false: it assumed only a quasi-isomorphism
L to an arbitrary E and concluded a quasi-isomorphism from that fixed L to T.
For the identity immersion of a nonempty Spec(k), E=L=0 meets its hypotheses,
while T may have nonzero degree-zero homology. The old data statement allowed
this arbitrary zero choice because it never tied its data to the quotient sheaf.

The new augmentation condition excludes that example. When K=0, its local
augmentation b can be a quasi-isomorphism only if the common restricted target
is acyclic. The roof statement compares two K-flat resolutions of that same
target, and does not insist on the vertex of an unrelated pre-existing roof.

Edge cases checked mathematically against both statements: for the identity
immersion and m=0 the carrier restricts to the unit complex, and its tensor
pullback has nonzero degree-zero homology on nonempty Spec(k). Empty U or W gives
zero modules over the zero ring. A zero quotient makes all pulled-back Koszul
terms zero. For a nonzero regular generator, the model has the degree-zero and
degree-minus-one quotient modules; a zero differential does not make it acyclic.
The generic roof works for P=K and the same augmentation (identity roof), for an
arbitrary morphism, and for unbounded locally K-flat inputs. These checks avoid
the earlier zero-model counterexample.

The original DAG step 2 hid the full local K-flat comparison and the sheafified
zero-differential calculation without naming their interfaces. Those are now
the two explicit component nodes. Neither replaces the original statement under
another name: construction has no arbitrary input resolution or roof, and
comparison has no finite-free zero-model conclusion or Koszul hypotheses.
The unit record has no realized nodes in its statement or sole step; the original
Koszul/sheafification route is preserved.

Searches: leanfinder, loogle and Mathlib grep were run through msearch; repository
searches found the existing restriction and bounded-flat APIs. LeanSearch
returned Internal Server Error, recorded as unavailable. No exact shorter theorem
was found. Stacks Tags 0BQY, 068C, 06YI and 06YJ were read online because the
literature source files are absent on this machine; their URLs are in the nodes.
The blueprint searches found no exact statement for either component.

## New nodes

`new-s1-local-koszul-augmented-carrier` records the sheafification, reindexing and
finite exterior-basis calculation for a supplied algebraic Koszul resolution,
including its indispensable augmentation to the local quotient sheaf.
Module: `Sheaf.AlgebraicGeometry.LocalKoszulAugmentedCarrier`.

`new-s1-local-kflat-tensor-roof` records comparison of two K-flat resolutions of
the same local complex after tensor pullback and over-site restriction.
Module: `Sheaf.AlgebraicGeometry.LocalKFlatTensorRoof`.

No change records are required: no existing statement, definition or public
interface changed, and no forced adaptations were made.

## Second reading by S1

1. **Existing interface: pass.** Diffed the main module against the repository:
   the entire existing theorem signature is byte-for-byte identical, as are
   visibility and all public imports. Only its proof and private imports change.
   There are no changed definitions, other existing modules, or required change
   records. The two other modules are new statements, explicitly reported above.
2. **Kernel proof and holes: pass as decomposition.** Compiled all three modules
   in import order through lcompile.py, without errors or warnings. Scanned every
   delivered Lean file: exactly the two reported public theorem proofs contain
   sorry; no admitted definition, axiom, unsafe, opaque, implemented_by or extern
   is present. A scratch copy with #print axioms for the original and both new
   declarations reports only propext, Classical.choice, Quot.sound and sorryAx.
   The original proof actually extracts the algebraic resolution, restricts its
   supplied augmentation, invokes both distinct components and assembles the roof.
   This closes one original hole and adds two; it is not net proof progress.
3. **Split statements: pass.** Read both signatures and complete docstring proofs,
   and checked them against Stacks Tags 0BQY, 068C, 06YJ and 06YI. The carrier's
   supplied projective resolution guarantees exactness without needing a separate
   regularity hypothesis. Pushforward from the chart supplies a genuine global
   carrier whose restriction is the constructed local Koszul complex. Its local
   augmentation prevents the arbitrary-zero counterexample. The roof compares
   two resolutions of the same F(S), and chooses its vertex after both maps.
   Checked m=0 and m=1, empty opens, the zero quotient, identity immersion, P=K,
   and K=0 with a nonacyclic target (excluded by the augmentation). No data is
   chosen in a new definition from an unproved mere-existence result. Independent
   leanfinder, loogle and grep searches used different terms and found no exact
   duplicate in Mathlib or the sheaf/upstream library. Found and incorporated the
   shorter common-roof step DerivedCategory.right_fac, and the existing exterior
   basis API. Neither closes the remaining local sheaf/base-change arguments in
   a few minutes; no further split statements were introduced.
4. **Route and pruning: pass.** The proof uses the existing Koszul projective
   resolution and K-flat open-restriction declarations directly. It retains the
   original Koszul/sheafification route. Read dag/units/sk-thm-picard-duality.json:
   its realized statement and sole step are empty, and no realized unit node is
   bypassed. Checked all old proof_deps: the Koszul resolution remains direct;
   affine sheafification moves to the carrier, explicitly recorded above. No
   original module is globally pruned. Public imports of the old module are
   signature dependencies; additional imports are private proof dependencies.
5. **DAG: pass after repair.** Verified every Lean record's statement verbatim,
   every node reference exists, and each proof_deps is exactly the union of the
   proof steps' uses. The old node changes only proof, proof_deps and proof_origin;
   its Lean record and all other fields are unchanged. Both new nodes have source,
   full construction/comparison proof, search records, status, created, blueprint,
   chapter, unit and Lean records required by brief-stage3 section 3. Added the
   Mayer--Vietoris node to the roof's restriction step because its proved over-site
   exactness instances are part of that planned argument.

Changes by this second reader: narrowed the new carrier's public Koszul import;
replaced the roof's Basic proof import with Fractions and made its common-roof
construction explicit; completed the roof's over-site dependency metadata;
recorded independent search results; clarified the removed direct dependency and
added this review. Existing signatures, main proof and the two component
statements are unchanged. No additional holes were closed or added.
