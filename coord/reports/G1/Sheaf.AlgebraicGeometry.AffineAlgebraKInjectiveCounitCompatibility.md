## What changed

Corrected AlgebraicGeometry.affine_algebra_kinjective_counit_compatibility in
Sheaf.AlgebraicGeometry.AffineAlgebraKInjectiveCounitCompatibility: the old
arbitrary-isomorphism statement was false. Added the real construction
AlgebraicGeometry.affineAlgebraCounitHomologyComparison and proved the formal
counit factorization from the adjunction bijection. The repaired identity does
not need K-injectivity or quasi-coherence. The affine hypothesis is retained
in the interface of the comparison.

Added Sheaf.AlgebraicGeometry.AffineAlgebraCounitHomologyComparisonIsIso for
invertibility of that fixed morphism under the original geometric assumptions.
Adapted the proof of the existing existential factorization in
Sheaf.AlgebraicGeometry.AffineAlgebraKInjectiveCounitHomologyFactorization,
without changing its signature or visibility. Updated both existing nodes to
match the actual proof, and added a definition node and an invertibility node.
All three modules compile through lcompile.py. The original downstream source
fails against the changed dependency; the adapted source compiles.

## Proved and sorry left

Retired the false original holed statement of
AlgebraicGeometry.affine_algebra_kinjective_counit_compatibility
(new-affine-algebra-kinjective-counit-compatibility); it was not proved unchanged.
The corrected declaration of that name is sorry-free. Its canonical identity uses
only homEquiv_symm_apply, Equiv.symm_apply_apply and cancellation of an isomorphism.
No claim is made to a proof of the original arbitrary-isomorphism assertion.

Added one hole:
AlgebraicGeometry.affineAlgebraCounitHomologyComparison_isIso
(lem-sc-affine-algebra-counit-homology-comparison-isIso). It is exactly IsIso
of the specified canonical morphism, with a source and complete proof in words.
It contains neither a factorization conclusion nor an existential choice of data.
There are no sorries in the item's module or its added definition. The unchanged
existential factorization is proved from this invertibility and the formal
identity. The ledger removes one original hole and adds one new hole, for net zero.
This is a correction and decomposition,
not a claim to have proved the geometric invertibility or an unchanged false
statement. All inherited dependency holes remain outside this delivery.

## No longer needed

Removed Sheaf.AlgebraicGeometry.AffineAlgebraKInjectiveCohomologyComparison
from both the item and the adapted factorization imports, and removed
new-affine-algebra-kinjective-cohomology-comparison from both existing nodes'
proof_deps. Its existence conclusion cannot establish compatibility of a
specified comparison. The item now publicly imports only its statement context
DirectImageAlgebraDerivedCategory and RingedSpaceDerivedDirectImage in its place;
its existing HomotopyCategory.Adjunction import is needed by the definition and
statement. The new IsIso module is imported only for the adapted proof.

The module Sheaf.AlgebraicGeometry.AffineAlgebraKInjectiveCohomologyComparison
is pruned from TargetsCheck's import closure. Comparing source import closures
before and after the complete delivery removes exactly that module and adds
AffineAlgebraCounitHomologyComparisonIsIso; no other module is claimed pruned.
No unit realization is bypassed: sk-thm-picard-duality's realized statement and
step lists are empty, and the affine counit route is preserved.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the old theorem quantified over an arbitrary isomorphism e.
For f=id on Spec(Q), identity P, and rank-one cohomology in degree zero, replacing
e by its negative changes the right side to minus the nonzero identity, while
the left side is the identity counit. The previous cohomology theorem only
asserts existence of an isomorphism, paired with True. Its interface provides
no compatibility, and the old proof plan incorrectly treated any such witness
as canonical. The correction does not weaken the source's conclusion: the
original existential factorization is retained verbatim.

The source's affine cohomology display is canonical; its map must be proved
invertible, rather than selecting an arbitrary witness. Tags 0AVW and 08D4 were
read at https://stacks.math.columbia.edu/tag/0AVW and
https://stacks.math.columbia.edu/tag/08D4 because the local source TeX is absent.
LeanFinder found short-complex homology naturality; Loogle found the adjunction
counit formula used here; grep confirmed the implementation. LeanSearch was
unavailable (HTTP 500), not recorded as a negative search result.

## New nodes

Definition def-sc-affine-algebra-counit-homology-comparison records the explicit
adjoint mate. It is built from actual maps and uses no unproved existence of an
object. Its source is the counit calculation in Tag 0AVW.

Statement lem-sc-affine-algebra-counit-homology-comparison-isIso records
invertibility of that map. Its proof is the affine-basis cohomology calculation
of Tags 0AVW and 08D4, followed by identification of the canonical edge map with
the mate using tensor pullback and uniqueness of adjunction-compatible left
adjoints. For zero complexes, empty schemes, and degrees with zero cohomology,
it compares zero objects; there is no lost boundedness hypothesis. Both nodes
record the actual searches in searches.jsonl and the finite-duality blueprint
ancestor through the existing factorization route. No blueprint node matching
"affine counit" was found by blueprint_refs.py search.

Change record: coord/changes/affine-algebra-counit-canonical-mate.md.

## Forced adaptations

Sheaf.AlgebraicGeometry.AffineAlgebraKInjectiveCounitHomologyFactorization
is unclaimed. Original compiler error against the repaired item, line 67:
Application type mismatch: the argument hI has type forall n, (I.homology n).
IsQuasicoherent of sort Prop but is expected to have type Int.

Only its proof import at line 13 and its last two proof lines (old lines 66-67)
change: the replacement import supplies invertibility of the fixed comparison;
the local IsIso instance allows asIso; the existential witness must now be that
asIso, and the compatibility invocation uses the canonical identity. These
lines are forced by the item's corrected interface. The original fails under
the sandbox overlay and the adapted version compiles. Every existing signature
and visibility is identical. The independent reader should recheck that
counterfactual and the canonical edge-map identification in the new docstring.

## Second reading by G1

1. Compared every existing delivered module with the repository version. The
   only changed existing signature is the compatibility theorem explicitly
   declared in coord/changes/affine-algebra-counit-canonical-mate.md. Confirmed
   the counterexample: on the one-point scheme Spec(Q), the rank-one complex
   concentrated in degree zero is K-injective, and the negative comparison
   negates the nonzero counit. The existential factorization signature and all
   its visibility are byte-for-byte unchanged. No target or existing definition
   changes. Searched all library uses of the changed theorem and removed export;
   only the adapted factorization uses either. Verdict: declared correction,
   no accidental statement change.

2. Compiled all three modules locally. Separate scratch #print axioms probes
   show only propext, Classical.choice and Quot.sound for the constructed map
   and formal compatibility. The IsIso lemma and downstream factorization also
   use sorryAx, exactly as reported. Inspected for forbidden declarations and
   hollow definitions: none. The one new sorry is a named sourced theorem;
   asIso constructs the unique inverse of a fixed morphism. Compiled the original
   factorization against the changed overlay and reproduced the hI/Int type
   mismatch at line 67. The adapted proof compiles. Verdict: kernel-checked
   formal identity and forced adaptation; geometric invertibility stays open.

3. Read Tags 0AVW and 08D4 independently. Affine inverse images give positive
   quasi-coherent cohomology vanishing; sections commute with countable products,
   so the N=1 truncation argument covers unbounded complexes. The cycle-to-class
   map respects scalar action and restrictions. For tensor pullback, its adjoint
   is multiplication on cycle sections; exact homology comparison and uniqueness
   of left adjoints transport that calculation to arbitrary a. This gives the
   specified mate, rather than an arbitrary existential isomorphism. Empty
   schemes, zero complexes and zero cohomology degrees give maps between zero
   objects; the identity/rank-one case gives an invertible canonical comparison.
   Searched LeanFinder with “right adjoint left exact functor cohomology
   comparison morphism K injective affine acyclic”, Loogle for right homology
   comparison, and grep for IsIso/homologyComparison, plus upstream and local
   sources. Found generic homology and injectivity APIs, no theorem proving this
   fixed affine map invertible. The existing existential cohomology comparison
   cannot identify its witness with this map. Verdict: true, strictly separate
   invertibility obligation, with sufficient source proof; no quick closure.

4. The formal identity already uses the adjunction API directly; no shorter
   geometric proof was found. Removed the unused cohomology-comparison re-export
   and supplied the two actual statement-context imports. Verified that exactly
   that module disappears from the targets' source import closure. Checked the
   unit realization and every old proof dependency in both existing nodes.
   Verdict: route retained; pruning report now complete.

5. Compared the nodes' Lean signatures and proof steps with the delivered code.
   The definition is the actual adjoint mate, compatibility uses bijection and
   cancellation, and factorization uses the fixed-map IsIso lemma and the formal
   identity. New nodes have source, searches, creation, blueprint, chapter/unit
   and Lean records. Corrected the new definition node's reversed composition:
   H^n(epsilon) after c inverse agrees with the Lean expression c.inv ≫ H^n(epsilon).
   Verdict: records agree with the construction and proofs; one planned hole.

Second reading changed the unused public import, the definition node's composition
order, the IsIso docstring's countable-product justification, the explicit former
STATEMENT-DISPUTED marker, the change record, and the reporting of original versus
corrected statements and pruning. No Lean proof body needed repair.

## Forced adaptations

### Sheaf.AlgebraicGeometry.AffineAlgebraKInjectiveCounitHomologyFactorization
Original against changed dependencies failed:
```
/tmp/forced-adaptation-de4669_i/lean/Sheaf/AlgebraicGeometry/AffineAlgebraKInjectiveCounitHomologyFactorization.lean:67:67: error: Application type mismatch: The argument
  hI
has type
  ∀ (n : ℤ), (HomologicalComplex.homology I n).IsQuasicoherent
of sort `Prop` but is expected to have type
  ℤ
of sort `Type` in the application
  affine_algebra_kinjective_counit_compatibility f P a I hI

(with the modules compiled into /tmp/forced-adaptation-de4669_i/.lbuild) [5.4 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
