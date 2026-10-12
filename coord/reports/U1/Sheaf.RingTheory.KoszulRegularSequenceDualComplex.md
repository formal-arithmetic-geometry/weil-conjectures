## What changed

In `Sheaf.RingTheory.KoszulRegularSequenceDualComplex`, proved
`ExteriorAlgebra.koszul_conormal_comparison_change_generators` and
`ExteriorAlgebra.koszul_conormal_comparison_cohomology`, with their signatures unchanged.
Added proof-only imports of `Sheaf.RingTheory.KoszulConormalBasis`,
`Mathlib.LinearAlgebra.ExteriorPower.Basis`, `Mathlib.LinearAlgebra.Dual.Basis`,
and `Mathlib.Algebra.Homology.SingleHomology`.

The private helpers prove exterior-dual pairing injectivity from a finite basis,
conormal-vector surjectivity from the generating-ideal equality, and the identity
`c_g ∘ t = c_f` from `g ∘ t = f`. The change-of-generators proof compares the two
normalization equations on lifted conormal wedges. It needs regularity only for f.
The cohomology proof identifies any normalized comparison with the existing
quasi-isomorphism from `exists_unique_koszul_conormal_comparison`; it does not
assume its quasi-isomorphism circularly. The module M is the explicitly constructed
normal determinant over A/I, e is its identity, and iota is the inverse of the
homology comparison. Naturality proves the required equality on cycles.

Added `Sheaf.RingTheory.KoszulConormalBasis` with a single remaining theorem hole.
Its docstring and node give the exact degree-one argument of Stacks 062I.
Updated the original node with the actual additional Lean arguments, keeping
its original four steps for the four remaining declarations.

Validation: both modules compile together through lcompile.py without warnings.
Checked r = 0 (I = 0, zero conormal module), I = A (zero quotient ring), and the
zero ring. Bases over the zero ring are permitted, so none of these requires an
extra nontriviality or proper-ideal assumption. No target, existing signature,
public import, or definition changed. No arbitrary object is selected from a
mere existence theorem: the conormal basis is used only inside theorem proofs.

## Proved and sorry left

Closed two of the six original holes:

- `ExteriorAlgebra.koszul_conormal_comparison_change_generators`.
- `ExteriorAlgebra.koszul_conormal_comparison_cohomology`.

Four original holes remain, all at node
`lem-sc-koszul-regular-sequence-dual-complex`:

- `ExteriorAlgebra.exists_unique_koszul_conormal_comparison`.
- `ExteriorAlgebra.exists_koszul_quotient_augmentation`.
- `ExteriorAlgebra.exists_intrinsic_koszul_ext_determinant`.
- `ExteriorAlgebra.koszul_conormal_comparison_localization`.

Added one smaller hole:
`ExteriorAlgebra.exists_koszul_conormal_basis`, node `lem-sc-koszul-conormal-basis`.
The two closed declarations are reductions through this conormal-basis statement;
the cohomology proof additionally uses the existing comparison-existence hole.
This is a decomposition with two upper holes closed and one new lower hole,
not a claim that the duality computation is now axiom-free.

## No longer needed

Removed the redundant proof import `Sheaf.Paper.KoszulComplex`: its declarations
are already public through KoszulConormalComparison and KoszulRegularSequence.
Its module and node `def-weil-pbc-koszul-complex` remain needed through those
public imports and the four untouched declarations; no transitive pruning claimed.
No original DAG proof dependency can be removed from the whole module yet.
For the two proved clauses, no dual-complex self-duality computation, new Ext
construction, or localization theorem is needed beyond the existing
comparison-existence declaration and the conormal basis.

## Where the brief, the DAG or earlier work was wrong

The planned exterior-pairing leaf gives only the map and determinant evaluation,
not the required injectivity on the conormal determinant. The missing prerequisite
is the conormal basis for a Koszul-regular sequence. Existing
`RingTheory.Sequence.regularSequence_conormal_free` assumes ordinary regularity;
Koszul-regularity cannot be replaced by that stronger hypothesis. Stacks 062I,
first paragraph, supplies precisely the missing basis statement from H1 vanishing.
The new node records this argument rather than duplicating the ordinary-regular
sequence theorem.

Loogle advertised `exteriorPower.bijective_pairingDual`, but the installed Mathlib
source and compiler do not provide it. Instead the private helper proves
injectivity using exterior-power bases and their coordinate pairings.
Mathlib has no Koszul comparison or conormal-basis theorem in the searched
sources. LeanSearch returned HTTP 500 and is recorded as unavailable, not no match.
The proof of change of generators does not use hregg, but its binder is preserved.

The unit `sk-thm-picard-duality` has no realization of this node as a unit statement
or step; this work stays below the unit level and retains the unit route.

## New nodes

`lem-sc-koszul-conormal-basis`, in
`dag/nodes/sec-picard-framework/lem-sc-koszul-conormal-basis.json`, corresponds to
`ExteriorAlgebra.exists_koszul_conormal_basis` in
`lean/Sheaf/RingTheory/KoszulConormalBasis.lean`. It asserts only that the conormal
classes form a basis. It does not assert existence of the normalized comparison,
quasi-isomorphism, cohomology, Ext, generator compatibility, or localization.
Source read: More on Algebra Tags 0CEM and 062I, first paragraph of the proof of
lemma-H1-regular-quasi-regular, in the locally available Stacks source; duality
Tag 0BQZ was also read. Blueprint searches for `conormal Koszul` and `conormal`
found no blueprint declaration of this fact; repository searches found only the
ordinary-regular conormal theorem. Three logged Mathlib search kinds were run:
LeanSearch (unavailable), Loogle (0 hits), grep (25 unrelated hits and TODOs).
No interface change record is required because all existing interfaces are preserved.

## Second reading by U1

1. Compared the delivered item with the repository using diff and checked the
   raw text of all six existing theorem signatures through `:=`: byte-identical.
   No existing public import, definition, visibility, or target statement changes.
   The only new public declaration is the documented conormal-basis theorem.
   Verdict: no accidental interface change and no change record required.
2. Compiled both delivered modules in dependency order through lcompile.py:
   no errors or warnings. Scanned both sources: exactly the four reported original
   theorem holes and the one reported new theorem hole; no forbidden declaration
   or hollow definition. Compiled a scratch copy with `#print axioms` for all six
   original declarations, all three private helpers, and the new theorem.
   Only propext, Classical.choice, Quot.sound, and the expected sorryAx occur;
   the three helpers themselves have no sorryAx. The determinant module used in
   the cohomology proof is explicitly constructed, and its isomorphisms come from
   the actual homology map, rather than an arbitrary unproved existence witness.
   Verdict: valid reductions, with remaining dependencies openly reported.
3. Read the first paragraph of lemma-H1-regular-quasi-regular and
   lemma-koszul-regular-H1-regular in the locally available Stacks source
   /home/ubuntu/c1-stacks-review/more-algebra.tex. The new statement is the
   degree-one consequence: tensoring the right-exact Koszul presentation with
   A/I kills its first arrow and identifies the standard generators with a basis
   of I/I^2. For r = 0 the generated ideal is zero and the conormal module is zero.
   For I = A (including a unit generator) and for the zero ring, both quotient
   modules are zero; a Fin r-indexed basis over the zero ring is valid. For r = 1
   and a proper ideal, H1 vanishing is injectivity of multiplication by f, giving
   the expected one-generator conormal basis. No properness or ordinary
   regularity is silently assumed. Repeated searches using Lean Finder for
   first-homology vanishing and conormal linear independence, Loogle for the
   exterior pairing, and grep for H1Regular/KoszulRegular and pairing injectivity;
   also read the repository's ordinary-regular conormal theorem and searched the
   Koszul modules. No applicable duplicate was found. Loogle advertises a pairing
   bijectivity result absent from the installed Mathlib source; the existing
   basis-coordinate proof is therefore necessary on this version. Formalizing
   the new basis theorem needs the degree-one exactness and tensor-cokernel
   bridge, which is not a repair achievable in a few minutes. Verdict: true,
   strictly smaller prerequisite, with a complete source-backed proof docstring.
4. Read the two reductions from their conclusions downward. Cohomology first
   identifies the given normalized comparison with the known quasi-isomorphism;
   it does not assume that the given map is already a quasi-isomorphism. Change
   of generators uses equality of the conormal maps and the two normalization
   equations. Their exterior-pairing injectivity helper is proved directly from
   Mathlib bases. Every new proof import supports one of these arguments; all
   original public imports support the unchanged signatures. The removed plain
   KoszulComplex import is redundant through the retained public imports.
   The three original proof-dependency nodes remain needed by the module.
   Read dag/units/sk-thm-picard-duality.json: its realized statement and step lists
   do not name this item or the new leaf, and its unit route is preserved.
   Verdict: appropriate downward reductions and complete pruning report;
   no module becomes transitively unnecessary in this delivery.
5. Compared the original and delivered item nodes: only proof, proof_deps,
   and proof_origin change. The original four steps remain for the four holes;
   the added steps describe the actual basis, normalization, homology, and
   generator-change arguments. The new node has its source, complete steps,
   dependency union, three recorded search kinds (including the unavailable
   service), blueprint ancestry, creation metadata, chapter/unit, and the exact
   Lean declaration record. Verdict: nodes agree with Lean and meet the brief.

Second reading changed only this report by adding the independent checks and
verdicts. No proof or statement repair was needed. The delivery closes two
original holes and adds one smaller hole; both closed declarations still depend
on sorryAx, so this is the reported decomposition rather than an axiom-free
completion. No transitive module pruning is claimed.
