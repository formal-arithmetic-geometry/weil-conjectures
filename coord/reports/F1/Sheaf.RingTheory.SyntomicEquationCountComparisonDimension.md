## What changed

Corrected and proved Algebra.equationCount_comparison_dimension in
Sheaf.RingTheory.SyntomicEquationCountComparisonDimension: replace c≤n by the
actual target-fibre dimension count. The old universal statement was false.
The complete proof shows that the localization comparison identifies local fibre
dimensions, by spectrum embeddings and an open neighbourhood contained in their
image. All five private helpers are proved, with no sorry and no private signature
exposed publicly. Removed the unused public Mathlib.RingTheory.RingHom.Flat import from the
dimension module; Mathlib.Topology.LocalAtTarget is added only for the proof.

Forced adaptation of Sheaf.RingTheory.SyntomicEquationCountComparison preserves
its existing statement and visibility exactly. It obtains counted local kernel
generators from the new module, then constructs π and u using the existing Core
module's private denominator-clearing theorem through a proof-only `import all`.
The returned duplicate helper has been deleted rather than renamed or reproved. It applies the corrected dimension
transport theorem with the known count. Its public imports are unchanged.

Change record: coord/changes/syntomic-equation-count-dimension.md.
The two existing node proof routes and the corrected dimension node signature and
statement are updated. No unit realization is bypassed; sk-thm-p1 is unchanged.

## Proved and sorry left

Closed the one hole of the corrected Algebra.equationCount_comparison_dimension
(node lem-weil-pbc-syntomic-equation-count-comparison-dimension). The old false
statement is corrected, not claimed proved. The corrected theorem and all its
private helpers use only standard axioms (verified by the delivery probe).

Added one hole: Algebra.exists_codimension_local_kernel_generators in
Sheaf.RingTheory.SyntomicCodimensionLocalKernelGenerators, node
lem-weil-pbc-syntomic-codimension-local-kernel-generators. This is the proper
kernel-generator selection/Nakayama subargument, not the comparison theorem
under a new name: it fixes a presentation φ and supplies localized ideal equality
and the count, but constructs neither π nor u nor a localization isomorphism nor
any dimension assertion about the comparison quotient. Its source and full proof
in words are in its docstring and node. Its proof is exactly := by sorry.

Algebra.exists_equationCount_comparison_of_syntomicAtPrime remains a complete
Lean proof of its unchanged statement, now from that kernel-selection step and
the proved transport and denominator-clearing arguments. No other delivery hole
exists. This is a correction plus decomposition, not a net reduction of one
valid original theorem to an axiom-free proof. The closed/additional-hole counts
are 1/1 and the raw net is zero; the one removed hole was in a false intermediate
statement. No data definition uses sorry or selects an arbitrary unproved witness.

All three files compile cleanly using lcompile.py --all; the original caller
compiles against the green baseline and fails against the changed dependency,
where the adapted caller compiles.

## No longer needed

The caller retains Sheaf.RingTheory.SyntomicEquationCountComparisonCore via
proof-only `import all`, to use its existing private
Algebra.exists_multiplier_of_localized_le. The Core module and its transitive
imports are not pruned. The uncounted Core theorem itself is not applied. The old caller proof dependency
lem-weil-pbc-syntomic-equation-count-comparison-core is therefore no longer used
as a theorem and is removed from that node's proof_deps. Its module is retained
for its proved private denominator-clearing helper.
The previous delivery's Core pruning claim is withdrawn.

The dimension theorem does not need its old planned dependency
lem-weil-pbc-polynomial-quotient-dimension-at-point-height-difference
(Sheaf.RingTheory.PolynomialQuotientDimensionAtPointHeightDifference); it now
uses Mathlib spectrum/topology tools alone. This dependency was never imported
by the assigned file; its proof_deps has been pruned to the empty list. The
height-difference theorem remains relevant to the lower conormal rank theory,
and no global deletion or complete project-wide unreachability is claimed.

Removed the dimension module's unused public Mathlib.RingTheory.RingHom.Flat
import. Its sole direct caller publicly imports Flat itself, so its users retain
the same interface. No UNIT's own statement or proof step was pruned.

The new counted-selection module imports its three planned proof dependencies
privately: SyntomicPolynomialFibreComparison, LciConormalFreeRankCodimension,
and SyntomicLocalKernelIntersection. These common lower dependencies remain
on this branch; Core and its uncounted generator dependencies remain imported; no pruning
of those modules is claimed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old statement): a list containing a zero equation has its
cardinality counted as a dimension drop. Explicit counterexample: R=k, n=c=1,
f=0, S=T=k[x], π=id, u=1. The fibre dimension is 1, whereas n-c=0.
Neither hsurj nor hu nor hbij prevents redundant equations. Even adding the
syntomic hypotheses would not exclude this identity presentation.

The one-step DAG plan invoked 00P2 without establishing that c is the difference
of heights. Stacks 00SC defines c by that difference; 00SY chooses a conormal
basis of exactly that size before Nakayama. The source pages were checked
online because literature/stacks-project/algebra.tex is absent locally.

Return repair: the landing checker correctly rejected the copied private
multiplier theorem. The repaired caller imports and uses the existing private
theorem; all three sandbox modules compile after this change. The delivery
tool rebases the dry-run commit onto the freshly fetched origin/sheaf-dag.

The earlier Core/bounded-kernel-generator statements retained only c≤n and
localized ideal equality, losing the required exact dimension count. Their
existing signatures are unchanged here. A new counted selection node records
the missing subargument; the caller's proof is forced to use it.

## New nodes

lem-weil-pbc-syntomic-codimension-local-kernel-generators is the counted
local kernel generator selection under the syntomic prime hypotheses, with one
module and one named sorry. It adds the fibre-dimension equality to the local
Nakayama result. Edge cases: c=0 gives the zero localized kernel; n=0 forces
c=0 and a zero-dimensional nonempty fibre. Redundant zero equations cannot be
selected as an independent conormal basis, so the counterexample does not
satisfy this conclusion with c=1. The specified prime excludes an empty fibre.
Source: Stacks 00SY, 00SC, 00P2. Search kinds include unavailable LeanSearch,
LeanFinder, Loogle and local grep. Change record:
coord/changes/syntomic-equation-count-dimension.md.

## Forced adaptations

Sheaf.RingTheory.SyntomicEquationCountComparison (unclaimed) is the only adapted
module. Original compiler error: its last argument hle has type c≤n, but the
corrected theorem expects the fibre-dimension equality. The entire existing
public signature and public imports remain identical. The Core import becomes
proof-only `import all` to expose its existing private multiplier theorem, and
the counted-generators import supplies the additional dimension information.
No copied private multiplier declaration remains.
The final proof now obtains the finite presentation and counted generators,
constructs the same quotient, π, and u, proves bijectivity by that multiplier,
and supplies hdim instead of hle to dimension transport. Each step is required
because the old Core output cannot establish the missing dimension count.
The exact counterfactual error is recorded in the change record, and deliver3.py
reruns the original/adapted compile comparison before preflight.


## Second reading by F1

1. Compared every existing delivered module with the read-only repository by diff.
   The caller signature and visibility are byte for byte unchanged. The only existing
   signature change is the dimension theorem's declared replacement of c≤n by the
   S-fibre dimension premise, recorded with its old/new signatures and users in
   coord/changes/syntomic-equation-count-dimension.md. The zero-equation affine-line
   counterexample establishes that the old statement is false. No target statement
   or definition changes. Verdict: pass as a recorded intermediate-statement correction,
   not a proof of the old statement.
2. Compiled all three files with lcompile.py --all. Independently compiled scratch
   copies with #print axioms for all eight delivered theorems, including the five
   private helpers. The dimension theorem and helpers use only propext,
   Classical.choice and Quot.sound. The new selection theorem and unchanged caller
   additionally use sorryAx. Exactly one named theorem has sorry, with no forbidden
   declaration or holed definition. The existential witnesses are eliminated inside
   a theorem proof; no data definition chooses an arbitrary unproved witness.
   Verdict: pass, with the one declared open selection subargument.
3. Read the new selection statement, its node, and its three planned dependencies.
   Checked Stacks 00SY, 00SC and 00P2 directly. Tested identity presentations (c=0),
   n=0, redundant zero equations, and a hypersurface fibre (c=1): the selected count
   is conormal rank, not the size of an arbitrary list. Flatness and finite kernel
   generation justify the final Nakayama step over the polynomial local ring.
   Searched with fresh LeanFinder, Loogle and grep queries recorded in searches.jsonl,
   and rg in both source roots. The existing bounded generator results forget the
   dimension equality; standard-smooth and univariate results do not replace this
   lemma. The new lemma fixes φ and handles generator selection/local ideal equality;
   it constructs no quotient comparison, multiplier or localization isomorphism.
   Verdict: true, strictly a part of the argument, with a complete sourced proof plan.
   Closing it requires formalizing the exact conormal rank and fibre-point transport,
   rather than applying the existing bound, and is not a few-minute repair.
4. Read the proof from the public theorem through every private helper, then the
   adapted caller. The embedding with D(u) in its range gives the required local
   dimension equality. No shorter existing dimension-at-point transport theorem
   was found; the related StandardSmoothDimensionAtPoints helper only supplies a
   dimension inequality and does not replace this argument. Proof-only imports
   are private; public imports supply signature data. Core is retained solely for
   its existing proved private helper via import all. Both obsolete theorem
   dependencies are identified under No longer needed. Inspected sk-thm-p1.json:
   neither pruned dependency realizes its statement or any unit step. Verdict: pass;
   no unit route or module is claimed globally pruned.
5. Compared existing node changes and checked the new node's required fields,
   verbatim Lean signature, source, searches, blueprint ancestry and created record.
   proof_deps matches each proof route; the retained Core private helper is explained
   in the caller proof text. Verdict: pass. The split node docstring and proof text
   now explicitly identify the residue vector space and select a basis from the
   spanning images of I, avoiding the misleading suggestion that an arbitrary
   fibre polynomial lifts to I.

Second-reading changes: clarified the selection docstring and matching node proof;
explicitly listed the unused Core theorem node in No longer needed; added this
independent review. No Lean proof or signature was changed in this reading.
The corrected hole is closed and one valid lower hole is added: 1/1 raw net zero,
a correction plus decomposition, not an axiom-free proof of the original item.

## Forced adaptations

### Sheaf.RingTheory.SyntomicEquationCountComparison
Original against changed dependencies failed:
```
/tmp/forced-adaptation-eyzwufsq/lean/Sheaf/RingTheory/SyntomicEquationCountComparison.lean:78:63: error: Application type mismatch: The argument
  hle
has type
  c ≤ n
but is expected to have type
  topologicalKrullDimAt ((PrimeSpectrum.preimageEquivFiber R S (PrimeSpectrum.comap (algebraMap R S) q)) ⟨q, ⋯⟩) =
    ↑(n - c)
in the application
  equationCount_comparison_dimension q π u hsurj hu hbij hle

(with the modules compiled into /tmp/forced-adaptation-eyzwufsq/.lbuild) [2.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
