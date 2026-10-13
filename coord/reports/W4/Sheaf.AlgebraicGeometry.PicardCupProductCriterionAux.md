## What changed

Replaced the remaining sorry in PicardCupProductCriterionAux by a complete proof from
an explicitly constructed cup-product transpose, a commuting base-change square, and
a local equal-rank dual-basis criterion. The original theorem's signature and
visibility, including hD, are unchanged. The already proved dual-direct-image theorem
is unchanged.

PicardCupProductMap constructs the tensor/unit comparisons by uniqueness of left
adjoints, pushes evaluation forward using the adjunction Hom equivalence and inverse
structure-sheaf unit, and curries the resulting pairing. All data are actual
constructions; no morphism or frame is selected from an unproved existence theorem.
Its picardPushforwardPairing_counit theorem is proved: pulling the pairing back
recovers evaluation of the two counits. Its proof uses naturality of the adjunction
unit and cancellation of the two unit isomorphisms.

PicardCupProductBaseChange states a commuting square of actual morphisms under
isomorphisms of their source and target. PicardCupProductLocalCriterion states the
single-base dual-basis calculation using only finite local freeness and equal local
ranks, with no properness, flatness, or universal base-change assumption.

The assembly in the assigned module cancels the source and target isomorphisms,
extracts the required local ranks from hW, transports them through identity-composition
equalities by congruence, and composes the two equivalences. Updated the proof and
proof dependencies of new-picard-cup-product-equivalence accordingly. No unit or
chapter route changes.

Validation: this resumed worker recompiled all four sandbox modules in import order
through lcompile.py (exit code 0). The first dry run found a node-signature mismatch:
the preflight records signatures starting at `def`, excluding the `noncomputable`
modifier. Corrected that record without changing the Lean construction.
The remaining new lemmas were checked mathematically on empty bases, rank zero,
identity base change, and nonreduced test schemes. A split square matrix over a
commutative ring is invertible by its determinant; no reducedness is used.

## Proved and sorry left

Closed the original hole
AlgebraicGeometry.Scheme.picard_cupProductCriterion_of_finiteLocallyFree
(new-picard-cup-product-equivalence). This is a decomposition into two strictly smaller
arguments, not a claim that the whole cup-product theorem is now sorry-free.

Proved the additional evaluation identity
AlgebraicGeometry.Scheme.Modules.picardPushforwardPairing_counit
(def-sc-picard-cup-product-map).

The assigned module has no remaining sorry. Its existing
AlgebraicGeometry.Scheme.picard_dual_directImage_isFiniteLocallyFree remains proved.
Added exactly two holes, each a public theorem with proof exactly `:= by sorry`,
a complete proof in words, and its own module and DAG node:

- AlgebraicGeometry.Scheme.picardCupProduct_isIso_iff_counit_of_local_ranks
  (lem-sc-picard-cup-product-local-dual-bases), in PicardCupProductLocalCriterion.
- AlgebraicGeometry.Scheme.picardCupProduct_baseChange_square
  (lem-sc-picard-cup-product-base-change-square), in PicardCupProductBaseChange.

Neither lower statement is the original existential, universally base-changed
criterion under another name. The first concerns only one explicitly given morphism
on one base and uses just local ranks. The second asserts equality of two morphisms
under source/target comparisons and contains no evaluation-counit isomorphism
criterion. Both are needed in the Lean assembly. Holes closed: 1; holes added: 2;
net holes closed: -1, a decomposition.

## No longer needed

Second reading removed the redundant direct public import of
WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree from the new
PicardCupProductLocalCriterion module. PicardCupProductMap publicly imports Dual,
which already publicly imports LocallyFree. This removes no module from the closure.

No existing import, node, or module is pruned: the original imports are still used by
the unchanged finite-local-freeness proof and the statement. The original remaining
node had no proof dependencies to remove. Its informal one-step plan is now replaced
by the explicit construction, base-change square, and local dual-basis calculation.

The local criterion does not need the dual direct image's rank condition,
properness, flatness, or universal rank hypotheses. The main theorem keeps all its
original hypotheses, and uses hW for the primal rank and base-change assertions;
hD is retained unchanged but not mathematically needed by this route.

## Where the brief, the DAG or earlier work was wrong

The remaining node's plan names no proof dependency and says only to use the local
finite-free dual-basis argument. The required actual cup morphism and the compatibility
between its pullback and cup product on a further base were not stated. This delivery
supplies the construction and makes those two separate arguments explicit, following
the final two paragraphs of Stacks Tag 0BDP.

The brief's Mathlib source path is absent on this machine. msearch.py's grep branch
silently reports zero hits for that absent directory. I did not modify the tool;
I independently searched the read-only Mathlib sources at
/home/ubuntu/weil-lean/.lake/packages/mathlib/Mathlib and the repository's two Lean
roots. The nodes record this limitation rather than treating the broken-path search
as evidence. LeanSearch returned Internal Server Error; LeanFinder and Loogle ran,
and no exact theorem was found. Blueprint searches for cup product, dual bases,
and 0BDP found no duplicate of the new degree-zero relative statements. The ancestor
helper returns None for the existing new-picard-cup-product-equivalence; I traced the
existing parent record to thm-sc-theorem-of-cube when recording the new nodes' origin.

## New nodes

- def-sc-picard-cup-product-map: explicit adjunction construction of degree-zero cup
  product and its transpose, with the proved counit identity. Source: Stacks 0BDP,
  final paragraph, and the tensor-pullback adjunction formula in 0095/0096. This node
  contains no sorry and introduces no arbitrary data from a holed existence theorem.
- lem-sc-picard-cup-product-local-dual-bases: the single-base local rank calculation.
  Source: Stacks 0BDP, final paragraph and its two dual bases. The docstring explains
  the construction of a left inverse, the equal-rank determinant argument, the
  converse projection-formula argument, and degenerate cases.
- lem-sc-picard-cup-product-base-change-square: the morphism-level compatibility with
  arbitrary base change. Source: Stacks 0BDP, penultimate and final paragraphs. Its
  proof in words specifies both comparison isomorphisms and the mate/adjunction
  calculation establishing the square, including arbitrary nonflat base changes.

All three nodes have recorded real search queries and outcomes, the original
chapter and unit, the blueprint origin, and the verbatim Lean signature. No
interface change record or forced adaptation is needed.

## Second reading by W4

1. **Interfaces: pass.** Compared every delivered module with the repository. The
   three helper modules are new. The assigned module differs only in its two plain
   proof imports and the body of
   `picard_cupProductCriterion_of_finiteLocallyFree`. Both existing declaration
   signatures, docstrings, visibility, and the already proved finite-local-freeness
   proof remain byte for byte unchanged. No existing definition or statement changes
   and no change record is required.

2. **Proofs and data: pass as a decomposition.** Compiled all four modules through
   lcompile.py in import order, and recompiled the local criterion after import
   cleanup. Searched the delivered Lean for forbidden declarations and holes.
   Exactly the two reported public lower theorems have `:= by sorry`; no definition
   contains a hole. Independently ran `#print axioms` in a scratch module for all ten
   delivered declarations. The five new constructions, the pairing-counit identity,
   and the existing dual-direct-image theorem use only propext, Classical.choice,
   and Quot.sound. The two lower theorems and the assembled criterion additionally
   use sorryAx, as expected. Choosing the canonical tensor-pullback adjunction is
   justified by its unit formula, which determines the adjunction; all cup-product
   data are constructed from it and ordinary pullback. The existential isomorphisms
   of the base-change theorem are eliminated only inside a proof, not used to
   define arbitrary data.

3. **Lower statements: pass.** Read their statements and complete docstring arguments
   against [Stacks Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP) and the
   imported pullback-duality, finite-locally-free-unit, and mate-pasting modules.
   Checked the empty base, rank zero, identity base change, and the square-matrix
   argument over a nonreduced commutative local ring. The rank condition supplies
   both required base-change isomorphisms; no flatness of the new base-change map
   is required. The local lemma concerns one base and removes the global family
   assumptions; the square lemma concerns equality of constructed morphisms and
   contains no counit criterion. Neither restates the original universally quantified
   existential. Fresh LeanFinder queries used “evaluation of global sections” and
   “direct image of evaluation pairing”; fresh Loogle searched adjunction/IsIso.
   Searches returned algebraic duality, vector-bundle trivializations, or generic
   adjunction results, not these assertions. Independent rg searches of both Lean
   roots and the available Mathlib source tree found no replacement. Nearby exterior
   determinant and finite-locally-free dual-pairing results do not prove either
   relative direct-image assertion. No lower hole could be closed by those results
   in a short proof.

4. **Route and pruning: pass with one cleanup.** Read the assembly top downward.
   It constructs the witness, uses the commuting square, cancels its isomorphisms,
   extracts the common local ranks from hW, and applies the single-base criterion.
   The original node had no proof dependencies, so there is no omitted old node to
   list as pruned. The unit sk-prop-av-cube and its realized fields are untouched;
   the general-cube/Picard-locus route is retained. Removed the redundant direct
   public LocallyFree import from the new local module; compilation confirms that
   the public import through PicardCupProductMap and Dual supplies it. The remaining
   plain helper imports in the lower modules support their documented pending
   arguments. No module is pruned from the target closure.

5. **Nodes: pass.** Compared the existing node JSON with the repository: only proof,
   proof_deps, and proof_origin differ. Verified each dependency exists, each
   proof_deps set is exactly the union of step uses, and the three new records
   contain the required source, origin, searches, created, blueprint, chapter, unit,
   and Lean fields. The new Lean signatures match their records and the existing
   signature is unchanged. The construction node also records all six declarations
   of its module.

Changes by this reader: removed one redundant public import and documented this
independent review. No proof, statement, definition, or node was rewritten. The
accounting remains one original hole closed and two lower holes added (net -1);
this delivery is a decomposition, not a sorry-free proof of the cup-product theorem.
