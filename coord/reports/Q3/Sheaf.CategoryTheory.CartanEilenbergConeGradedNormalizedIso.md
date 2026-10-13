## What changed

The existing declaration
`CategoryTheory.Functor.cartanEilenberg_cone_graded_normalized_iso` now has a complete
Lean proof from two strictly smaller ingredients. Its signature, visibility,
normalization predicate and all existing public imports are unchanged. The two new
proof dependencies are imported privately.

Added `Sheaf.CategoryTheory.CartanEilenbergConeGradedHomExt`, with a fully proved
`CategoryTheory.Functor.cartanEilenberg_cone_graded_hom_ext`. It proves that the retained
column generators detect morphisms from the evaluated graded piece. The proof cancels
the epic quotient projection, constructs an equalizer, and uses the stipulated finite
image supremum to make the equalizer inclusion split epic. The K generator and columns
strictly above p factor through the next step and vanish in the quotient; the retained
column is identified by `extendXIso`. Two proved private helpers handle lifting through
an image inclusion and vanishing of a lift through the next step.

Added `Sheaf.CategoryTheory.CartanEilenbergConeGradedSplitInjection`, which states the
remaining normalized inclusion and left-inverse construction. It does not assert
surjectivity or a right inverse. The original module proves surjectivity using the
proved hom-ext theorem, uniqueness of lifts through a monomorphism, and the explicit
normalization equations. A monic and epic morphism in an abelian category is an
isomorphism; its inverse has exactly the unchanged normalization predicate.

The original DAG node's proof, proof dependencies and proof origin now follow this
argument. Both new nodes contain self-contained statements and full proofs in words.
All three modules compile together cleanly through the authorized local compiler.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.Functor.cartanEilenberg_cone_graded_normalized_iso`
(node `lem-sp-cartan-eilenberg-cone-graded-normalized-iso`). There are no sorries in the
item's module.

New fully proved theorem:
`CategoryTheory.Functor.cartanEilenberg_cone_graded_hom_ext`
(node `lem-sp-cartan-eilenberg-cone-graded-hom-ext`). Its private helpers
`lift_of_image_le` and `lift_next_quotient_zero` are also proved.

Exactly one added hole remains:
`CategoryTheory.Functor.cartanEilenberg_cone_graded_split_injection`
(node `lem-sp-cartan-eilenberg-cone-graded-split-injection`). Its proof is exactly
`by sorry`, in its own new module with its source and complete proof in words.

This delivery is a decomposition, not a complete proof of the mathematical comparison:
one original hole is closed and one strictly smaller hole is added, so the net hole
reduction is zero. The entire generating-family/surjectivity half of the original
argument is proved. No postponed data or arbitrary choice from an unproved existence
statement occurs in any definition.

## No longer needed

None. All original public imports supply objects in the unchanged signatures or
normalization predicate. No original proof-dependency module can be removed: the
presentation, total-complex, filtration and subquotient infrastructure still appears
in the new statements and proofs. No unit statement or realized proof step is bypassed.
The natural-indexed `ConeHorizontalGradedIso` and its projection/quotient modules were
considered but not imported: their bicomplex shapes, cone construction and signed
comparison differ from this integer-indexed augmented-cone comparison.

## Where the brief, the DAG or earlier work was wrong

No false statement or required interface change was found. The parent proof plan hid
two separate tasks in one step: constructing a normalized split injection and proving
that its image generates the quotient. They are now separate, with the second proved.
In fact the generating-family result does not need the below-bound zero assumptions
or the column augmentation a; only the displayed image-step formula and p-1<=m matter.
Those assumptions remain unchanged in the existing theorem.

The generic finite-supremum quotient and hom-ext proofs in `DoubleComplexTotal` are
private and specialize to a different first-quadrant filtration. Their equalizer proof
pattern was useful, but their public graded isomorphisms do not apply directly here.

Read the actual Stacks pages for Tags 012X and 0133. The new proofs in words are marked
as agent-written augmented-cone refinements of the parent's retained-column plan,
rather than claims that Stacks explicitly states the Lean normalization equations.
The local clone lacks the fetched Stacks TeX despite the literature inventory, so the
public source pages were used and the Stacks homology TeX was fetched into the
sandbox scratchpad to verify labels `section-double-complex`,
`lemma-ss-double-complex` and `lemma-double-complex-gives-resolution`.
No literature or repository file was edited directly.

Edge cases were checked in the stated argument: m=p-1 retains only the K term; m>=p
retains only the I term; p<b makes both retained terms zero under the existing zero
assumptions. Empty intervals contribute no generators. In hom-ext, every column s>p
and the K term when p<=m explicitly vanish through step p+1. Below-bound assumptions
are unnecessary there because no retained generator is present outside the interval.

## New nodes

`lem-sp-cartan-eilenberg-cone-graded-hom-ext`, in
`dag/nodes/sec-abelian-varieties/lem-sp-cartan-eilenberg-cone-graded-hom-ext.json`,
is the proved generating-family assertion. It is strictly a surjectivity criterion,
independent of constructing or splitting a comparison map. Its Lean module is
`Sheaf.CategoryTheory.CartanEilenbergConeGradedHomExt`.

`lem-sp-cartan-eilenberg-cone-graded-split-injection`, in
`dag/nodes/sec-abelian-varieties/lem-sp-cartan-eilenberg-cone-graded-split-injection.json`,
is the unproved normalized inclusion with a left inverse. It does not assert the
second inverse identity or epimorphy. Its Lean module is
`Sheaf.CategoryTheory.CartanEilenbergConeGradedSplitInjection`.

Ran logged LeanFinder, Loogle, LeanSearch and Mathlib grep searches. LeanSearch returned
an internal server error, recorded as unavailable. LeanFinder found subobject
supremum/factorization infrastructure, but no augmented-cone normalization result.
The whole blueprint search for retained columns found no duplicate. No change record
or forced adaptation is needed: every existing signature and public import remains.

## Second reading by Q3

1. Compared the existing module against the repository with diff. The only edits
   are two plain proof imports and the theorem body. Every existing signature,
   definition, docstring and public import is byte-for-byte unchanged. No change
   record is required. Verdict: pass.
2. Independently compiled all three modules in import order through lcompile.py.
   Scratch copies with #print axioms show only propext, Classical.choice and
   Quot.sound for hom-ext; the parent and split injection additionally have
   sorryAx from the explicitly reported remaining theorem. The sole textual
   sorry is the whole proof of that public theorem; there are no forbidden
   declarations or hollow definitions. Verdict: pass, one open decomposition.
3. Read the split-injection statement and its complete construction in words.
   It asserts a left inverse and the two lift equations, without epimorphy or
   a right inverse. The separately proved hom-ext argument supplies epimorphy,
   so this is a genuine reduction rather than a renamed target. Checked m=p-1
   (only K), m>=p (only the resolution term), p<b (both retained objects zero
   in the split theorem), and empty generating intervals. Independently searched
   LeanFinder for a column split inclusion, Loogle for IsSplitMono, and rg for
   column quotient and graded comparison results. The cone decomposition and
   split-mono lemmas are infrastructure, not this normalization result; the
   existing natural-indexed horizontal cone comparison has different inputs.
   Verdict: true, needed, strictly partial, no duplicate found.
4. Read the equalizer/generating-supremum proof and its private helpers, and
   compared the available finite_sup_hom_ext and finite_sup_cokernel_iso
   constructions in DoubleComplexTotal. Those helpers are private and the
   public comparisons concern other shapes. All public imports provide symbols
   in signatures. The new imports are plain proof imports. The four old
   proof dependencies (presentation, total, subquotients, filtration) remain
   used through both new lemmas; none of their modules is pruned. The unit
   sk-prop-av-pqf-finite has realized statement [] and steps [[]]; no realized
   node or chapter route is bypassed. Verdict: pass.
5. Compared all three nodes with the declarations and proof bodies. The parent
   changes only proof, proof_deps and proof_origin. New nodes have the required
   source, searches, provenance, chapter/unit, blueprint and verbatim Lean
   statements. The parent uses the split injection and hom-ext exactly as its
   node records. Read the Stacks filtration source (Tag 012X); the explicit
   augmented-cone refinements are identified as agent-written. Verdict: pass.

Second reading changed only one inaccurate sentence in the new hom-ext
proof docstring and its node proof: when p<b the index-p generator is absent
from the interval, not assumed zero. The hom-ext theorem deliberately has
no below-bound zero hypothesis. No Lean signature or proof term changed.
All scratch axiom-check files were removed. One original hole is closed,
one lower hole is added, and the net hole reduction remains zero.
