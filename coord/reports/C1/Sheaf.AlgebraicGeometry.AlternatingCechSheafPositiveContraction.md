## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.AlternatingCechSheafPositiveContraction`
with a compiling proof from two strictly weaker geometric statements, in the new modules
`Sheaf.AlgebraicGeometry.AlternatingCechSheafLocalExact` and
`Sheaf.AlgebraicGeometry.AlternatingCechSheafDifferentialInnerInverse`.
The original theorem's signature and visibility are unchanged.
The new modules are proof-only imports. Mathlib's ShortComplex.Abelian module is also a
proof-only import for the proved private helper `exact_inner_inverse_on_cycles`.
No existing definition, public import or other module was changed.

The proof chooses an inner inverse s_k of each differential, sets
q_k = s_(k-1) d_(k-1) with the required index transport, and constructs
h_k = s_k (1 - q_k). Exactness and epi cancellation of the kernel lift show
(1 - d_k s_k) q_k = 1 - d_k s_k. Expanding this equation and using d squared = 0
proves the required two-term homotopy identity. All algebra and integer transports
are proved in Lean, including the private kernel-lifting helper.
The choices occur only inside the existential proof, not in definitions.

Sources read: Stacks Project Tag 02FU, `cohomology-lemma-covering-resolution`,
its explicit insertion formula and cancellation calculation; Tag 01FM,
`cohomology-lemma-alternating-cech-complex`, for the increasing-tuple convention.
The independent new statements extract the cocycle and boundary cases of this
calculation. Intersection presheaves are already sheaves (direct images from the
intersection opens), so finite products and their sheafification units identify
these calculations with the specified sheaf complex.

## Proved and sorry left

Closed: `AlgebraicGeometry.alternatingCechSheaf_restrict_positive_contraction`
(node `lem-pc-s3-alternating-cech-sheaf-positive-contraction`).
Its module has no remaining sorry. The private helper is fully proved.

Added, each with proof exactly `by sorry`:

- `AlgebraicGeometry.alternatingCechSheaf_restrict_local_exact`, node
  `lem-pc-s3-alternating-cech-sheaf-local-exact`.
- `AlgebraicGeometry.alternatingCechSheaf_restrict_differential_inner_inverse`, node
  `lem-pc-s3-alternating-cech-sheaf-differential-inner-inverse`.

This is a decomposition: one original hole closed and two strictly smaller holes
added, net -1 hole. It is not a claim that the geometric contraction is now proved
without sorry dependencies. Exactness alone does not split maps in a category of
module sheaves; inner inverses alone do not imply exactness (a complex with zero
differentials and a nonzero middle term is a counterexample). Neither new statement
is a repackaging of the original homotopy conclusion.

Edge cases checked before stating the new theorems: r=0 admits no i; an empty U_i
has only zero sheaves; negative integer differentials are zero; r=1 has zero terms
in positive degrees; above the maximal increasing-tuple length the terms vanish.
An arbitrary finite open family need not cover X: restriction to U_i is enough.
The original conclusion requires no degree-zero equation.

## No longer needed

None. The original module imported only the construction module, which remains
necessary for the statement. No original dependency or unit route was bypassed.
The downstream singleton, insertion-identity and insertion-homotopy modules cannot
be used as premises: their proofs import this item. The generic ordered Čech
local-exactness theorem concerns an all-tuple model with comparison hypotheses,
not the specified increasing-tuple complex, and was not imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The original DAG has one
non-elementary step whose only dependency constructs the complex; it supplies no
Lean declaration for the local insertion maps or their cancellation equation.
The new nodes expose the needed geometric work rather than treating that step
as elementary. Its original blueprint ancestor metadata is preserved; the unit
record has no realized statements or steps bypassed by this reduction.
LeanFinder returned generic Dold-Kan homotopies, not a geometric match. Loogle
found extendXIso and exact_iff_epi_kernel_lift. The grep search found no matching
Čech homotopy. LeanSearch returned Internal Server Error and is recorded as
unavailable, not as evidence that there is no match.

## New nodes

`lem-pc-s3-alternating-cech-sheaf-local-exact` states only positive-degree local
exactness. Its proof uses signed insertion on cocycles and the already-sheaf
intersection terms, with integer extension transports. It makes no splitting
choices and asserts no contraction identity.

`lem-pc-s3-alternating-cech-sheaf-differential-inner-inverse` states only a one-degree
inner-inverse equation d s d = d. Its proof uses signed insertion on boundaries,
without relating adjacent choices or asserting exactness. In negative degrees
s=0 works. Each node has its own new module, source, full proof in words,
recorded searches, and Lean signature.

No change records are needed: all existing public interfaces are preserved.

## Second reading by C1

1. **Interfaces: pass.** Compared the sole existing module with the repository
   using diff, and separately asserted byte-for-byte equality of its theorem
   signature. Its visibility and original public import are unchanged. The
   existing node changes only proof, proof_deps and proof_origin. No existing
   definition or statement changes, so no change record is required.
2. **Proof: pass.** All three modules compile locally with lcompile.py --all.
   The only two sorry occurrences are the named public theorems listed above,
   each exactly by sorry; no forbidden declaration or hollow definition occurs.
   A scratch-copy #print axioms probe shows only propext, Classical.choice
   and Quot.sound for the private helper; the three public theorems additionally
   use sorryAx, as expected from their open dependencies.
   Reviewed the kernel-lift epi cancellation and every integer transport. The
   choices s and h are local witnesses in an existential proposition, not public
   data definitions chosen from an unproved existence theorem.
3. **New statements: pass.** Read both signatures and full proof docstrings.
   Signed insertion on increasing tuples is linear over the local structure
   ring because inserting i leaves the section open unchanged inside U_i.
   Intersection terms are direct-image sheaves, so finite products and their
   sheafification units support the stated transfer. Checked the formulas by
   integer matrices for r=1 through 5, every i, all available degrees and the
   zero tail. Also checked r=0, empty U_i and negative source degrees (including
   k=-1). Exactness concerns only cocycles; inner inverses concern only one
   differential. Neither restates the original contraction theorem. Independent
   searches used LeanFinder on exact complexes with inner inverses, Loogle on
   Exact/split, and Mathlib grep on inner inverses and split exactness. They
   found generic Dold-Kan and short-exact splitting results, requiring different
   hypotheses. Repository and upstream searches found no usable geometric match;
   the existing all-tuple result cech_sheaf_restrict_exact_positive requires
   comparison isomorphisms unavailable for the increasing-tuple model. These
   geometric holes cannot be closed by a short application of those results.
4. **Route and pruning: pass.** The proof uses Mathlib's epi_kernelLift before
   reducing to the two strictly smaller geometric statements. All imports serve
   its signature or proof; all original proof_deps remain used, so No longer
   needed is complete. The singleton and insertion contractions depend on this
   module and cannot be used without an import cycle. Read the unit's realized
   record: no realized statement or step is bypassed or changed.
5. **Nodes: pass.** Verified that each recorded Lean signature occurs verbatim
   in its module, proof_deps equals the union of the proof-step uses, both new
   nodes contain the required source, creation, ancestry, search and Lean fields,
   and the existing node's algebraic route matches the compiled proof.

Second reading changed only this report by adding the independent review and
validation evidence; the Lean proof and nodes needed no repair. This remains a
one-hole-to-two-hole decomposition, net minus one, not a sorry-free proof.
Source checked directly: [Stacks 02FU](https://stacks.math.columbia.edu/tag/02FU)
and [Stacks 01FM](https://stacks.math.columbia.edu/tag/01FM).
