## What changed

Replaced the sorry of `constructible_hasPrimeFieldFiltration` by strong induction on a
positive identity-annihilator, specialized to the characteristic of the finite coefficient
ring. A prime divisor p of n gives the short exact sequence with kernel of p times the
identity and its coimage; these are killed by p and n/p respectively. The prime case uses
`exists_module_sheaf_of_nsmul_id_eq_zero`, then the new constructibility-transfer lemma.
Added proof imports for the existing cyclic-module lift, kernel/cokernel constructibility,
characteristic lemmas, short-complex exactness and prime divisors. Added the new transfer
module and its node, and updated the item's proof route without changing its statement.

## Proved and sorry left

`AlgebraicGeometry.Scheme.constructible_hasPrimeFieldFiltration` is proved from the
named imported results and the new transfer lemma, with its original signature unchanged.
Both delivery modules compile locally. The required `deliver3.py --no-push` dry run
prints OK: compilation and preflight pass except for the independent second reading,
which is reserved for the next worker. Nothing was pushed. The induction combines the prime case, the
kernel/coimage short exact sequence, and both annihilation calculations in Lean.
The characteristic calculation also covers the zero coefficient ring (characteristic one).

The new statement module compiles. Its sole sorry is
`AlgebraicGeometry.Scheme.isConstructibleSheaf_prime_of_underlyingAbelianIso`, node
`lem-pbc-prime-coefficient-constructibility-transfer`. It leaves only the constructibility
of the prime-field lift; it contains no filtration claim, annihilator induction, kernel or
quotient construction. The zero ring, zero sheaf and empty scheme are included. Existing
imports may have their own sorries, which this delivery neither adds nor changes.

## No longer needed

Removed the redundant direct import `WeilConjectures.ConstructibleSheaf.Defs`; its
definitions remain available through the required imports. No existing named node or
module is pruned from the transitive closure.
The route needs no Chinese remainder decomposition, primary summands, prime-power induction
or finite-direct-sum reassembly: prime-divisor induction replaces all four. The former
direct proof dependency `def-constructible-finite-locally-constant` is used through the
constructibility-transfer step rather than directly by the target proof. The unit's curve
devissage route stays unchanged.

## Where the brief, the DAG or earlier work was wrong

The previous attempts were blocked by the absent compiled `PrimeFieldFiltration`
dependency. On this retry the dependency is available and both delivery modules compile.
The first dry run also detected a changed top-level `open` command. Restored the original
command and qualified the kernel/cokernel identifiers inside the proof instead, so this
introduces no interface change and needs no change record.

The source and DAG signatures of the named kernel/cokernel declarations are usable, and the
finite ring supplies the Noetherian hypothesis needed for kernel constructibility.
The existing `KilledSheafModuleLift` already proves existence of the canonical cyclic
module sheaf; no new existence lemma is needed. The general-scheme abelian-to-Z/n
constructibility node has no Lean declaration, while the stated torsion comparison theorem
requires a curve. The new lemma supplies exactly the missing module-to-prime-module
constructibility transport, for the encoding and general schemes used by this item.

The second reader also found an existing DAG cycle between
`lem-weil-pbc-sheaf-algebraic-structures-objects` and
`lem-weil-pbc-sheaf-algebraic-structures-abelian-component`. It is already reachable
from the repository version of this item, so this delivery did not introduce it.
Reported here for the maintainer; neither unrelated node was edited.

## New nodes

`lem-pbc-prime-coefficient-constructibility-transfer`:
`lean/Sheaf/AlgebraicGeometry/Curve/PrimeCoefficientConstructibilityTransfer.lean`.
It transfers constructibility through an underlying abelian isomorphism to a prime-field
module sheaf, retaining the same finite constructible stratification. Source read: Stacks
03SC second proof paragraph and 03RW (2),(3), together with 03RZ for the target's exact
sequence. LeanFinder and Mathlib grep found no matching transfer result; LeanSearch was
unavailable and this is recorded without a false absence verdict. The whole imported
blueprint and both Lean roots were searched for a matching usable declaration. No change
record is needed: all existing signatures and definitions are unchanged.

## Second reading by D2

1. **Interfaces: pass.** Compared the delivered filtration module with the repository
   using `diff -u`, and compared the text from `theorem` through the type before `:=`:
   the signature is byte-identical. The existing docstring, namespace, universe, `open`
   command and sole public import are unchanged. The transfer module is new. No definition,
   target, existing public signature or change record is altered. Existing node changes are
   confined to `proof`, `proof_deps` and `proof_origin`.
2. **Proof: pass, conditional on the reported open dependencies.** Compiled both modules
   in import order through `lcompile.py --all`. The filtration proof has no sorry; the new
   transfer theorem has exactly its reported named sorry. Scanned both delivery modules for
   prohibited constructs and hollow definitions; none found. A scratch module printed the
   axioms of both declarations: only `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`.
   In particular this is not an unconditional axiom-free proof while imported results remain
   open. Checked the actual induction: positive characteristic annihilates every section;
   n=1 gives zero identity and the prime-2 case; n=p*m gives 0<m<n; the kernel inclusion
   cancels p on K; the coimage projection cancels m on Q. `exact_cokernel` and the mono
   kernel inclusion give precisely the short exact sequence needed by the extension
   constructor. Finite coefficients supply the Noetherian ring assumption for kernels.
3. **Split statement: pass.** Read the actual Stacks source in `etale-cohomology.tex`:
   `theorem-vanishing-affine-curves` (03SC), second proof paragraph;
   `definition-constructible` (03RW), clauses (2),(3); and
   `lemma-constructible-abelian` (03RZ), clause (3). The new theorem is the missing
   coefficient bookkeeping, not a renamed filtration theorem: it assumes an already
   supplied prime-field module sheaf and underlying abelian isomorphism and concludes only
   constructibility. Its proof retains the given global stratification; it does not assume
   that Stacks' affine-local definition supplies a global partition on arbitrary schemes.
   Finite coefficients make all finitely generated constant values finite. Removing empty
   cover members permits the constant-value stalk argument; primality gives the canonical
   scalar action and additive maps preserve it. Tested empty X, zero F, zero Lambda
   (forcing zero F and G), and r=2: no nonemptiness or nonzero-ring hypothesis is needed.
   Searched both Lean roots and the upstream checkout using forgetting/underlying/local
   constancy terminology, and reran LeanFinder and Mathlib grep with different queries.
   No usable duplicate was found. The general-scheme abelian-to-cyclic node has no Lean
   declaration; the existing torsion comparison requires a curve. The existing
   `finite_local_cyclic_module_forget_iff` covers the local cyclic step, not the complete
   transfer statement. Tried closing the transfer from it and inverse-image comparison;
   the attempt cannot compile because `FiniteLocalCyclicModuleForget.olean` is absent
   from the copied green library. Kept that attempt only in the scratchpad, not the delivery.
4. **Route and pruning: pass.** Strong induction is a shorter below-unit route than Chinese
   remainder decomposition and primary-summand reassembly. It retains prime-coefficient
   devissage and short-exact extensions; `dag/units/sk-thm-p1.json` `realized` is unchanged
   and no realized unit step is bypassed. The only removed old direct proof dependency is
   `def-constructible-finite-locally-constant`, already explained under No longer needed;
   this is not a claim that its module leaves the targets' transitive closure. Removed the
   additional redundant proof import `Mathlib.Data.Nat.Prime.Defs`: the characteristic
   imports already expose the arithmetic used. All remaining added imports are private
   proof imports; the transfer's public imports supply its statement's types.
5. **Nodes: repaired, then pass.** Read both node files against the Lean and the statements
   of the cyclic lift, filtration constructors and constructible kernel/cokernel results.
   The existing node accurately records the strong-induction proof and its four direct
   dependencies. The new node has its declaration verbatim, source, full prose proof,
   searches, blueprint ancestry, chapter/unit and creation record. Its second proof step
   had incorrectly marked inverse-image/constant-sheaf compatibility elementary without
   citations. Added the existing `lem-weil-pbc-module-abelian-inverse-image-comparison`
   and `lem-weil-pbc-constant-module-sheaf-underlying` citations and marked it non-elementary.
   Added `lem-weil-pbc-finite-local-cyclic-module-forget` to the local lifting step and
   recomputed `proof_deps` as the union. These statements give exactly the comparisons
   and local finite-value lifting used there. Also marked the failed LeanSearch call
   explicitly `verdict: unavailable`, rather than an absence verdict.

Second-reading changes: removed one redundant arithmetic import; repaired new-node proof
citations and the search availability metadata; added this review. No mathematical statement
or working proof body was changed. One named transfer theorem remains split off.

Additional verification: both edited nodes have `proof_deps` equal to the union of their
steps' `uses`. The cycle reported above predates this delivery, including its reachability
from the item. Local compilation and the server/preflight dry run passed after the review.
