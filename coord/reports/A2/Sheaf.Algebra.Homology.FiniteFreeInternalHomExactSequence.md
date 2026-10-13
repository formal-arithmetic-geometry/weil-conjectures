## What changed

Replaced the sorry in CochainComplex.finiteFree_internalHom_exact_sequence by a
complete Lean argument. Private proved helpers establish preservation of finite
limits via evaluation and coyoneda, and preservation of epimorphisms via finite
local lifting. unitLift is an explicit construction through the proved unit-Hom
bijection; it contains no sorry and chooses no unspecified object. The statement,
universes, visibility and all existing public imports stay identical.

Added the proof-only import Sheaf.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
and Mathlib/source imports for exact functors, abelian sheaves,
local surjectivity, exact forgetting of module structure and free coordinate
projections. Updated the existing node to describe the actual argument.

## Proved and sorry left

Closed: CochainComplex.finiteFree_internalHom_exact_sequence
(lem-sc-finite-free-internal-hom-exact-sequence). No sorry remains in the item.

Added and left: CategoryTheory.hasSheafify_addCommGrp_of_weak
(lem-sc-weak-sheafify-addcommgrp-left-exact), in the new module
Sheaf.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact. Its proof is exactly
`by sorry`; its docstring and node give the full finite-refinement proof.

This is a decomposition: one original hole closed and one infrastructure hole
added, net zero holes. The finite-free calculation itself, including local
preimage assembly and compatibility, is written and compiled. The result still
rests on the new infrastructure hole; it is not an axiom-free completion.

## No longer needed

Removed the redundant added proof import Mathlib.CategoryTheory.Limits.Yoneda;
the original InternalHom import already supplies the coyoneda limit API.
No original imports or proof-dependency nodes are removed. Both original
definition dependencies remain needed. The coincident-universe module
Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact and its upstream
InternalHomFree route are not imported: neither applies to arbitrary universes
or merely middle-exact sequences. They were not dependencies of the original
node, so this is not a claim that they leave the targets' closure. No pruning
of existing modules is claimed.

## Where the brief, the DAG or earlier work was wrong

The original plan assumes the abelian-category and epi/local-surjectivity API
under HasWeakSheafify. Mathlib requires the stronger HasSheafify, namely a left
exact reflector. The new node isolates the finite local-refinement implication
from the exact original hypotheses, rather than strengthening the theorem.

The source checkout's existing homObjUnitIso and homObjFreeIso are restricted
to coincident universes. Instead of changing those interfaces, this proof
constructs local rank-one maps explicitly and uses existing freeπ/ιFree lemmas,
which already allow arbitrary site universes.

The literature source files are not present in this clone. Read the exact
primary-source pages https://stacks.math.columbia.edu/tag/00WJ and
https://stacks.math.columbia.edu/tag/03CN for the residual lemma, and
https://stacks.math.columbia.edu/tag/0GM8 for the parent application.
No existing definitions or statements were changed; no forced adaptations.

## New nodes

lem-sc-weak-sheafify-addcommgrp-left-exact: the left exactness of an already
existing abelian sheafification from weak sheafification and its characterization
by locally bijective morphisms. This is strictly an infrastructure part of the
argument: it contains no finite free P and no exact sequence S. Sources: Stacks
00WJ and 03CN. Searches: LeanSearch unavailable, LeanFinder and source grep gave
no matching arbitrary-universe implication. Edge cases checked: the empty finite
diagram is terminal and already a sheaf; finite intersections remain coverings
including the empty intersection; equalities are refined only finitely many
times. There is no assumption that the site is small in w. The parent unit has
empty realized statement and step lists, so no unit realization was bypassed.

## Second reading by A2

1. Compared the complete module diff with the repository version and checked the
   original theorem signature byte for byte through `:= by`: identical. The
   existing visibility, universes, definitions and four public imports are
   unchanged. There is no statement change or forced adaptation. Restored the
   original docstrings exactly, including their blank lines.
2. Compiled both delivered modules locally in dependency order: no errors or
   warnings. Scanned all delivered Lean text: the sole sorry is the complete
   public proof of CategoryTheory.hasSheafify_addCommGrp_of_weak. No forbidden
   declaration or attribute, and no sorry in data. Scratch-copy `#print axioms`
   checked every new private helper and the original theorem: the restriction,
   limit and unitLift helpers use only propext, Classical.choice and Quot.sound;
   finiteFreeHom_epi and the original theorem additionally use sorryAx. The
   residual theorem also uses only these four. unitLift uses the existing
   unitHomEquiv, a proved bijection, not a witness from an unproved existence
   statement. HasSheafify itself is a Prop certifying left exactness of the
   already specified adjoint; no arbitrary new object is chosen from the hole.
3. Independently read the residual lemma, docstring and node. Verdict: true,
   needed and strictly simpler than the finite-free exactness theorem. Its local
   comparison argument uses finitely many lifts and compatibility equations,
   then local injectivity to establish the equations on a common refinement.
   Finite presheaf limits stay in the given section universe, and the sheaf
   inclusion creates them; no large limit over a covering is asserted. Checked
   empty finite diagrams, the bottom topology (identity reflector), and rank
   zero (empty basis sum and top covering sieve). Read Stacks Tags 00WJ and 03CN
   directly. Independent LeanFinder search for preservation of kernels by a
   weak abelian reflector, Loogle search for HasWeakSheafify/HasSheafify, and
   source grep for weak-to-left-exact implications found no applicable theorem.
   Loogle reported unknown identifier HasWeakSheafify. The upstream concrete
   plus and essentially-small-site results have additional size assumptions.
   This hole is not a restatement of the item and cannot be closed in a few
   minutes with an existing API.
4. Read the proof downward: reflect finite limits through evaluations and
   coyoneda; lift the finitely many basis images of an epi on the intersection
   covering; assemble the local morphism using free projections and the proved
   unit-Hom bijection; use the sum-of-projections identity; then apply Mathlib
   preservation of homology and Exact.map. This proves middle exactness without
   assuming the given short complex is short exact. The coincident-universe
   InternalHomFree route does not supply the arbitrary-universe statement.
   Removed the redundant added Yoneda proof import and recompiled. All original
   proof dependencies remain used; no original node or module is pruned. Read
   sk-thm-picard-duality.json: its realized statement and single step are empty,
   and this argument bypasses no realized unit step.
5. Compared both nodes with the Lean declarations and actual proof. The original
   node's proof, proof_deps and proof_origin accurately record the limit, local
   lifting and homology argument and the new dependency. The new node has its
   full source, natural-language proof, searches, provenance, blueprint ancestry,
   chapter/unit, and verbatim normalized Lean statement. Both original definition
   dependencies are retained. No unauthorized node field or statement change.

Second-reading changes: removed only the redundant added Yoneda import, restored
original docstring whitespace, and added spacing between declarations. No proof
term or signature changed. One original hole is closed and one strictly simpler
infrastructure hole is added: decomposition, net zero, no modules pruned.
