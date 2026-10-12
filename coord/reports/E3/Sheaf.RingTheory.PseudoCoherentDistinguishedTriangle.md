## What changed

Replaced the sole sorry in `Sheaf.RingTheory.PseudoCoherentDistinguishedTriangle` by a
complete Lean combination of a compatible approximation triangle, the homology ladder,
Mathlib's five and four lemmas, and two rotations. The original theorem signature and
public imports are unchanged. Added proof-only imports of the two new modules and
`Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four`.

Added `Sheaf.RingTheory.MPseudoCoherentShift`, with a fully proved shift equivalence.
Its private proofs shift the actual witness complex, transfer termwise finite freeness,
and conjugate the homology maps through the shift isomorphisms. Added
`Sheaf.RingTheory.PseudoCoherentApproximationTriangle`, isolating the construction
before the third component's cohomology is analyzed. Updated the item's proof route
and recorded both new nodes. No target, definition, existing signature, or visibility changed.
The second reading removed redundant homology-sequence imports from both new modules
and added the construction plan’s proof-only `Sheaf.RingTheory.DerivedMapLift` import.

## Proved and sorry left

Closed: `CategoryTheory.isMPseudoCoherent_of_distinguished_triangle`
(node `lem-pc-ring-pseudo-coherent-distinguished-triangle`), one of one original holes.
Added and proved: `DerivedCategory.isMPseudoCoherent_shift_one_iff`
(node `lem-pc-ring-m-pseudo-coherent-shift`), with no sorry in its module.

One new hole remains:
`DerivedCategory.exists_pseudoCoherent_approximation_triangle`
(node `lem-pc-ring-pseudo-coherent-approximation-triangle`). Its module has exactly
one public theorem and its proof is exactly `by sorry`. It constructs the finite-free
third vertex and compatible triangle but asserts no cohomology comparison for that vertex.
The item's private cohomology comparison and rotation proofs are complete Lean proofs.
This delivery is a decomposition: one old hole closed, one new hole added, net zero holes.
The finite-free construction is still required; this is not an axiom-free proof of the target.

All three modules compile with `lcompile.py`. The shift construction covers arbitrary
integer shifts internally, including negative shifts, and transports epimorphisms using
naturality rather than an unjustified preservation assumption on the homology functor.

## No longer needed

Removed the direct proof-only import `Sheaf.RingTheory.DerivedMapLift` from the item.
Its node remains needed in the new approximation-triangle construction's proof plan:
this is a relocation of that dependency, not a globally pruned module. The fully proved
shift theorem handles the previously implicit shift argument. The old direct proof dependency `def-weil-triangulated-category` likewise moves into
the approximation-triangle node (TR3), rather than being globally pruned.
Removed redundant imports of `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
from both new modules: `MPseudoCoherent` already exposes it through `TStructure` and
`Fractions`. The item’s existing public imports are preserved. No original proof-plan
node is globally unnecessary. No module can be claimed pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically correct. The original nearby
`CategoryTheory.isMPseudoCoherent_cone` is not a shortcut: its module imports this item,
so using it would create a cycle. The original second step hid the termwise finite-free
shift witness and the transport of epimorphisms; these are now proved explicitly.
Mathlib's stupid truncation module has a TODO for its inclusion map, so its truncation
object alone does not complete the remaining construction. The remaining node also
needs representing the target B by a complex before applying the stated derived map lift.

The local literature checkout is absent. Read the official source at
https://stacks.math.columbia.edu/tag/064R, including the entire proof of the three clauses.
The construction theorem follows its first half verbatim, and the rest follows its
cohomology comparison and rotation steps. No unit route is bypassed; the unit record
has empty realized lists and no unit statement or step was removed.

Checked edge cases: the new construction still exists when either witness is the zero
complex, when m is negative, and over the zero ring. Brutal truncation only needs epi
at the boundary, not an iso, so it requires no coherence hypothesis on R. No definition
chooses data from an unproved existence theorem: all new declarations are theorems.

## New nodes

`lem-pc-ring-pseudo-coherent-approximation-triangle` records the first half of the
Tag 064R cone proof. It is strictly a part of the argument: its third map has no
cohomological conclusion; the original conclusion is obtained only by the proved
five/four-lemma comparison. Its docstring and node specify truncation, lifting, bounded
finite-free cone terms, and TR3. Module:
`Sheaf.RingTheory.PseudoCoherentApproximationTriangle`.

`lem-pc-ring-m-pseudo-coherent-shift` records the fully proved shift equivalence used
in both rotations. Module: `Sheaf.RingTheory.MPseudoCoherentShift`. Mathlib searches
and whole-library/blueprint searches found no existing statement of either new lemma.
LeanSearch was unavailable; LeanFinder, Loogle and grep supplied the alternative searches.
There are no change records or forced adaptations.

## Second reading by E3

1. Compared the delivered item with the repository using `diff -u`. Its entire
   existing theorem signature, docstring, universes, visibility and public imports
   are byte-for-byte unchanged. Only its proof, private helpers and proof imports
   differ. The two added modules are new; no change record or adaptation is required.
   Verdict: pass.
2. Independently compiled all three modules in import order with `lcompile.py`,
   before and after the import repair. There is exactly one `sorry`, the named
   `DerivedCategory.exists_pseudoCoherent_approximation_triangle`; no forbidden
   declarations or hollow definitions. A scratch probe using `#print axioms` showed
   only `propext`, `Classical.choice`, `Quot.sound` for the shift theorem, and those
   plus `sorryAx` for the construction and original theorem. The private ladder
   constructs its actual morphism from the triangle commutation proofs and connecting
   map naturality; it chooses no arbitrary witness from an unproved existence claim.
   Verdict: pass as a decomposition, not as an axiom-free target proof.
3. Read Stacks [064R](https://stacks.math.columbia.edu/tag/064R) and
   [064E](https://stacks.math.columbia.edu/tag/064E), the definition of
   `IsMPseudoCoherent`, and the derived-map-lift signature. The remaining statement
   contains only the truncation/lifting/cone/TR3 construction, without any condition
   on third-component homology. The original proof actually derives those conditions
   by the five and four lemmas; the hole is strictly a part of the argument.
   In the brutal truncation at `m+1`, boundary homology is `ker d` mapping onto
   `ker d / im d`, so only an epi is needed there. This works for negative m,
   the zero ring and zero witnesses. The construction preserves independent module
   and derived-category universes and adds no coherence hypothesis. The shift proof
   transfers both freeness and finiteness along termwise isomorphisms and conjugates
   homology maps via naturality, including the boundary epi. Repeated LeanFinder,
   Loogle and Mathlib grep searches with different queries, plus repository-wide `rg`;
   no existing theorem closes the construction. Its complete prose proof and matching
   node are present. Verdict: pass; not a short remaining hole to close.
4. Checked the five-term ladder in order A,B,C,A[1],B[1]. At i=m+1 the first
   component is only epi; at i>m+1 it is iso. At i=m the four-lemma segment deletes
   the initial A term and uses epi on B and A[1], mono on B[1]. The second clause
   rotates twice at m-1; the third rotates once at m. The cone wrapper already
   imports this item, so it cannot be a shortcut. The unit `sk-thm-picard-duality`
   has `realized.statement=[]` and `realized.steps=[[]]`; its route and records stay
   intact. The report now identifies both old dependencies relocated into the new
   construction node and the redundant imports removed. No module is globally pruned.
   Verdict: pass.
5. Read all three node files against their Lean declarations and proofs. The item's
   proof-dependency list is the union of its new construction, homology/diagram tools,
   definition and shift dependencies. The new nodes have the source, complete proof
   plan, search records, provenance, chapter/unit and verbatim Lean statements.
   Added second-reader search records. Restored the construction's missing proof-plan
   import of `DerivedMapLift`, which its node already cites. Verdict: pass after repair.

Changes by this reader: removed two redundant homology-sequence imports, restored
one proof-only dependency import, expanded the pruning report and recorded independent
searches. No statement, definition or proof body changed. One original hole is closed,
one construction hole is added, and the shift lemma is fully proved: net zero holes.
