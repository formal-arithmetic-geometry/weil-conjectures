## What changed

Replaced the sole sorry in `Sheaf.RingTheory.TatePurelyInseparableClosureQuotientFinite`
by a complete Lean reduction to `tate_root_closure_quotient_finite`, in the new module
`Sheaf.RingTheory.TateRootClosureQuotientFinite`. The original theorem signature and
all its public imports are unchanged. Only proof imports and private proved helpers
were added to the original module. The second reader removed redundant new imports. Updated the original DAG node to follow the implemented proof.

The proof constructs the extension E=L(z) inside AlgebraicClosure L, where z^(p^e)=x.
Mathlib supplies the common exponent and finite-adjoin theorem. A Frobenius preimage
subfield proves that E has the same exponent. The constructed root is integral.
The new lemma supplies finiteness of T/yT. A proved induction using
Module.Finite.of_exact gives all T/y^nT. A proved saturation calculation reflects
integrality of a/x along the injective field map and gives an injection S/xS -> T/xT.
Noetherian descent and restriction of scalars finish the original statement.
The injection proof also handles a parameter with zero image separately, without division.
No arbitrary data are defined by choosing a witness from a theorem containing sorry:
E and y are constructed before the new lemma is invoked, which only returns finiteness.

## Proved and sorry left

Closed the original hole:
`tate_purely_inseparable_closure_quotient_finite`
(node `lem-weil-pbc-tate-purely-inseparable-closure-quotient-finite`).
Its module has zero remaining sorries. Both private helpers,
`finite_quotient_powers` and `finite_closure_quotient_of_extension`, are proved.

Added exactly one hole:
`tate_root_closure_quotient_finite`
(node `lem-weil-pbc-tate-root-closure-quotient-finite`). Its whole proof is `by sorry`.
It isolates steps 3--7 of the original plan, plus the zero-parameter N-2 transport.
It concludes finiteness modulo the supplied root, before the principal-power filtration
and descent from the enlarged field. Those steps are implemented in Lean in the item;
this is a decomposition (one hole closed, one added), not a complete axiom-free proof.
The remaining lemma has its source and full proof in its docstring and node.

Validation: both sandbox modules compile through lcompile.py; the item compiles
without warnings. Edge cases checked mathematically: x=0 forces y=0 and reduces the
remaining lemma to N-2; e=0 gives q=1 and a trivial field extension; R/xR being a
domain excludes a unit parameter; the finite-filtration induction includes n=0.
The new lemma explicitly explains the universe transport needed because IsN2 with
FractionRing (R/xR) quantifies over fields in the universe of R/xR.

## No longer needed

Removed the direct proof import `Sheaf.RingTheory.DimOneResidueFieldsFinite` from
the item. It remains a planned proof dependency of the new root-quotient lemma,
whose module imports it, so no library module is claimed globally pruned.
No existing public import was removed. No original mathematical dependency is globally
pruned: localization, height, residue-field, and normalization dependencies now
belong to the root-quotient node. The item itself needs no direct localization,
height or residue-field arguments. Its new DAG proof_deps records this distinction.

The second reader removed redundant direct proof imports
`Mathlib.RingTheory.Finiteness.Finsupp` and `Mathlib.RingTheory.Noetherian.Basic`
from the item (available through its remaining imports), and the unnecessary
`public import Mathlib.FieldTheory.PurelyInseparable.Basic` from the new module.
The new statement uses an explicit common-power hypothesis rather than the
`IsPurelyInseparable` class. Existing public imports remain unchanged.

For completeness, the following old `proof_deps` are no longer direct proof
dependencies of the item; all remain dependencies of the new root-quotient node
(the Japanese-domain and normal-domain definitions still occur in its signature):

- `def-weil-pbc-japanese-domain`
- `def-weil-pbc-krull-dimension-ring`
- `def-weil-pbc-localization-at-prime`
- `def-weil-pbc-normal-ring`
- `lem-weil-pbc-dim-one-residue-field-extensions-finite`
- `lem-weil-pbc-finite-module-over-finite-algebra`
- `lem-weil-pbc-integral-closure-finite-extension-normal`
- `lem-weil-pbc-localization-dimension-chains-below-prime`
- `lem-weil-pbc-localization-noetherian`
- `lem-weil-pbc-noetherian-height-quotient-bound`
- `lem-weil-pbc-prime-residue-field-algebra`

## Where the brief, the DAG or earlier work was wrong

The old final DAG step said that step 5 gave T/xT finite; this should have referred
to the filtration step 8. The new DAG proof removes that stale cross-reference.
The original enlargement paragraph first discussed descent of finiteness of the
whole integral closure, whereas this item needs descent only of the quotient;
the Lean proof establishes the precise inverse-image equality for principal ideals.
No mathematical statement or definition was changed. The unit route is retained.

The local literature/stacks-project/algebra.tex file is absent on this machine.
The source proof was read at https://stacks.math.columbia.edu/tag/032P instead.
LeanFinder, Loogle, and Mathlib source searches ran through msearch.py and are
recorded in searches.jsonl. LeanSearch returned Internal Server Error and is
recorded as unavailable, not as an absence result. No matching closed-fibre theorem
was found; the relevant uniform-exponent and finite-adjoin results were reused.
A blueprint search for the root-quotient statement returned no matching blueprint node.

## New nodes

`lem-weil-pbc-tate-root-closure-quotient-finite`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-tate-root-closure-quotient-finite.json`,
states finiteness of S/yS when y^(p^e)=x and every p^e-th power in L lies in K.
It carries the zero case and the prime/localization/residue-field/N-2 argument
from Tag 032P. Its new module is
`lean/Sheaf/RingTheory/TateRootClosureQuotientFinite.lean`.
No change records or forced adaptations are needed.


## Second reading by F3

1. Compared the complete item with its repository version: the existing theorem
   signature and docstring are byte-for-byte unchanged, all existing public
   imports remain, and there are no changed definitions or target statements.
   The only new public theorem belongs to the new module and has its own node.
2. Compiled both delivered files with lcompile.py. Read both private helpers,
   including the zero-image branch of saturation, and the complete root-adjoin
   construction. No forbidden declarations or hollow definitions occur. Scratch
   #print axioms checks show only propext, Classical.choice, Quot.sound for the
   helpers; the item additionally uses sorryAx through the single split lemma.
3. Read the split lemma against Stacks Tag 032P. Its common exponent and supplied
   root are exactly what the residue-field argument needs. Checked x=0 (N-2
   transports via a small isomorphic finite extension), e=0, and the exclusion
   of units by the domain quotient. The finite basis gives the required Small
   instance, as also implemented in N2AscendsFiniteDomainExtension. Its proof
   docstring and node explain the argument. Independent LeanFinder, Loogle,
   grep and library/upstream searches found no existing theorem replacing it;
   Module.Finite.of_exact is already used for the filtration. This is a genuine
   one-for-one decomposition, not an axiom-free proof or a renamed restatement.
4. The implemented root enlargement, power filtration, saturated quotient
   injection and scalar restriction are substantial proved reductions. No
   shorter applicable route was found. Removed redundant added imports and
   enumerated all old proof dependencies transferred to the new lemma above.
   Checked sk-thm-p1.realized: this auxiliary reduction bypasses no unit step.
   No module is globally pruned.
5. Checked both DAG proof plans and proof-dependency unions against Lean; only
   proof, proof_deps and proof_origin change in the existing node. The new node
   has source, full proof steps, searches, provenance and verbatim Lean signature.
   Added the omitted noetherian-ring definition to its stmt_deps.

Second reading changed only redundant new imports, the new node's missing
statement dependency, and this report's complete pruning and review accounting.
The split residue-field theorem is not a few-minute closure: it still requires
prime/localization, height, residue-field and N-2 transport constructions.
