## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_cover_filtration`
with a complete proof assembling the geometric Sylow cover, the existing proved
`Representation.invariants_ne_bot_and_exists_filtration_of_isPGroup`, and exact-functor
transport. The original declaration signature and existing docstring are unchanged.

Added `Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf`, stating only the geometric
cover, its finite ℓ-group representation, and its exact additive associated-sheaf functor.
It does not assert a filtration. Added
`Sheaf.RepresentationTheory.InvariantFlagCategoricalFiltration`, whose public theorem is
fully proved from Mathlib. Its private helper proves that the quotient representation is
the cokernel of an invariant-subspace inclusion. The public proof constructs the truncated
flag, proves its initial and final conditions, computes quotient dimensions, and constructs
the equivariant rank-one isomorphisms. Thus the remaining geometric theorem is a strict part
of the argument, rather than the original conclusion under another name.

The item adds only proof imports of the two new modules, the source-library invariants
module, and Mathlib's preservation-of-cokernels module. Updated the item's DAG proof and
created nodes for the two new modules. All three sandbox modules compile without warnings.

## Proved and sorry left

Proved, from the geometric intermediate theorem:
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_cover_filtration`
(node `split-locally-constant-cover-filtration`). No direct sorry remains in the item.

Fully proved from Mathlib, with no sorry:
`Rep.exists_categorical_filtration_of_invariant_flag`
(node `lem-weil-pbc-invariant-flag-categorical-filtration`), including its private
`Rep.cokernel_inclusion_iso_quotient` helper.

The sole sorry of the delivery is
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_sylow_cover_associated_sheaf`
(node `lem-weil-pbc-sylow-cover-associated-sheaf`). Its complete proof in words states
how to construct the cover and functor, and identifies every supplied witness. This is
still a partial delivery: the original result depends transitively on this sorry.

Checked the edge cases: the categorical flag proof works for the zero representation
(n = 0); the truncated flag is constant after n; P need not be finite in that algebraic
lemma. The geometric lemma permits zero G by taking the trivial image and cover of degree
one. It also permits ℓ = 2 and trivial P. The coefficient change is a ring isomorphism,
not a characteristic assumption on the base scheme. The cover's group can be replaced by
an isomorphic finite group in Type u; arbitrary representation dimensions live in Type
(u + 1).

## No longer needed

The original proof dependency `lem-weil-pbc-inverse-image-stalk-germ` and its module
`Sheaf.Paper.InverseImageStalkGerm` are not needed on this route. That statement is for
abelian-group sheaves, whereas the argument uses the functorial finite-monodromy
correspondence and an exact associated-sheaf functor. It was not imported in the initial
module and was not added.

No existing import was removed: both original public imports supply its unchanged
statement. In the new modules the broad `Mathlib.FieldTheory.Finite.Basic` imports were
replaced by `Mathlib.Algebra.Field.ZMod` and finite-dimensional definitions;
`Mathlib.LinearAlgebra.FiniteDimensional.Lemmas` is now a proof-only import. The other original geometric dependencies remain in the geometric intermediate
node: `cor-galois-lisse-representations`, `thm-galois-fundamental`, `thm-galois-lc-etale`,
`lem-weil-pbc-sylow-subgroup-prime-index`, `def-pc-finite-locally-free`,
`lem-weil-pbc-finite-locally-free-degree-locally-constant`,
`lem-weil-pbc-fibre-degree-base-change`, and `lem-galois-geometric-fibre`.
`def-galois-categories` and `def-weil-connected-scheme` continue to describe notions used
by that construction. The original ℓ-group filtration node remains directly used.
These nodes have been moved below the geometric intermediate, not pruned.

## Where the brief, the DAG or earlier work was wrong

The initial module has no proof-dependency imports, despite the standing brief's description
that such imports are already present. The needed proof imports were added explicitly.
There is no mathematical correction to the item or its unit: the Sylow reduction and
finite ℓ-group filtration required by `sk-thm-p1` are both preserved.

The existing group-filtration theorem gives an invariant submodule flag rather than a
categorical chain with cokernels. The new, fully proved algebraic lemma supplies that glue.
The Galois correspondence statements do not directly give a Sylow cover together with
the exact associated-sheaf functor used here; that geometric step is explicitly left open.
Its functor is defined on all representations so the completed categorical flag can be
mapped without introducing a second full-subcategory implementation. A future proof may
construct it by descent on the finite étale P-torsor; that construction works for arbitrary
modules, not just the finite-dimensional representation used in this item.

The Stacks tex sources are absent on this machine. I read the current statements and proofs
of [Tag 0A3R](https://stacks.math.columbia.edu/tag/0A3R) and
[Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5) online. LeanSearch returned HTTP 500;
its searches are recorded as unavailable, not as absence of a matching theorem. LeanFinder,
Loogle, and local source searches ran and their results are recorded in the new nodes.

## New nodes

`lem-weil-pbc-sylow-cover-associated-sheaf`:
`lean/Sheaf/ConstructibleSheaf/SylowCoverAssociatedSheaf.lean`, declaration
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_sylow_cover_associated_sheaf`.
One sorry, covering the geometric construction and functor, with no filtration conclusion.

`lem-weil-pbc-invariant-flag-categorical-filtration`:
`lean/Sheaf/RepresentationTheory/InvariantFlagCategoricalFiltration.lean`, declaration
`Rep.exists_categorical_filtration_of_invariant_flag`. Fully proved; no sorry.
No existing public signature or definition changed, and no change record is required.

## Second reading by A2

1. Compared every delivered module with the repository. The item is the only existing
   module; its existing signature and docstring are byte-for-byte unchanged. The other
   two modules are new. No existing definition or target statement changed; no change
   record is required. Verdict: pass.
2. Compiled all three modules through lcompile.py without errors or warnings. Searched
   the delivery for forbidden declarations and hollow definitions: none. The sole sorry
   is the named geometric theorem listed above. Explicit axiom checks show only
   propext, Classical.choice, Quot.sound for the categorical theorem; the item and
   geometric theorem also have sorryAx, as expected. The delivery tool additionally
   probes all declarations, including the private quotient helper. Verdict: pass as a
   partial reduction, not an axiom-free completion of the item.
3. Read the two new statements and the geometric docstring proof. Checked the zero
   representation, trivial P, degree-one cover, characteristic two, and indices at and
   beyond the flag length. The group is finite but the functor accepts arbitrary modules:
   finite-torsor descent of constant module sheaves works at that size and exactness is
   checked after local trivialization (or on geometric stalks). The geometric theorem
   asserts no filtration; the proved categorical theorem supplies a separate, substantial
   part of the argument. Searched with new terms for torsor descent/associated sheaves
   (LeanFinder), Rep cokernels (Loogle), and quotient-cokernel matches (Mathlib grep),
   and searched the local Sheaf and source-library declarations. No theorem closing
   the geometric construction or the complete categorical realization was found.
   Checked Stacks 0A3R, 0DV5, and 0DV6 online against the proposed construction.
   The remaining geometry cannot be closed by a short application of existing statements.
   Verdict: pass; one honest geometric obligation remains.
4. Read downward through the Sylow cover, the existing proved p-group flag theorem,
   categorical quotient realization, and exact-functor transport. No unit is bypassed:
   sk-thm-p1 keeps its curve-calculation and locally constant reduction route, and its
   realized fields are unchanged. All original proof dependencies removed from the
   item's direct proof_deps are accounted for: the correspondence, fundamental group,
   locally constant correspondence, Sylow-index and four degree/fibre nodes move below
   the geometric node; def-galois-categories is supplied through the fundamental-group
   dependencies, and def-weil-connected-scheme remains a statement dependency of the
   geometric node. Only lem-weil-pbc-inverse-image-stalk-germ is genuinely pruned.
   Verdict: pass after correcting the proof-only import and narrowing field imports.
5. Compared the node proof steps, their uses/proof_deps unions, and proof_origin with
   the Lean argument. The existing node changes only stage-3-owned fields. New nodes
   have sources, creation/blueprint metadata, matching declarations, and recorded
   searches. Replaced compressed new-node Lean statements with the exact multiline
   signatures from the files, and removed verdicts for unavailable searches.
   Verdict: pass.

Second-reading changes: import visibility and import narrowing in the two new modules;
verbatim new-node signatures; unavailable-search metadata; complete pruning explanation
and this review. The mathematical proof bodies were correct and were retained.
