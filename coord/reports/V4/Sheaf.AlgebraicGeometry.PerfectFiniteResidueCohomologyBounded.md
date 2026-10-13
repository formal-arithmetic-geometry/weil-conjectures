## What changed

Proved `AlgebraicGeometry.Scheme.finiteFiberCohomologyBounded` in
`Sheaf.AlgebraicGeometry.PerfectFiniteResidueCohomologyBounded` without changing its
signature or either public import. Added proof imports for the universe-aware
open-restriction comparison, flat-complex derived pullback, tensor-closed sheaves,
categorical flat retracts, and Grothendieck abelian sheaves.
The private proved helper `flat_of_finiteFree_retract` establishes flatness of each
transported model term. The original model bounds give the resulting fibre bounds.

The residue map factors through the chosen open because it is constant at x. The
proof transports the model to that open subscheme, computes derived pullback by the
ordinary additive functor supplied by `flatComplexDerivedPullback`, and reflects
cohomology vanishing through the faithful exact restriction to the whole spectrum.
It then maps zero cohomology through evaluation and scalar restriction to get finrank
zero. Standard localizations on open subschemes avoid any new universe hypotheses.
Updated the item's node proof and proof dependencies to match this argument. No new
nodes, definitions, or interface changes. No other module was edited.

Local compilation passed without warnings. The proof retains exactly the supplied
bounds, with no assumption a ≤ b: a reversed interval forces all terms zero, and the
same argument applies. The zero complex and rank-zero free retracts are included.
Searches were run with LeanFinder, Loogle and Mathlib grep (see searches.jsonl);
no direct scheme residue-fibre boundedness theorem was found. Existing flat-complex
and restriction comparisons supplied the argument. The repository's referenced
Stacks .tex files were absent; the official Stacks pages for 0BCD, 08C4, 06YJ and
08DW were read instead.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.finiteFiberCohomologyBounded`
(node `new-perfect-finite-residue-cohomology-bounded`).
The private helper `flat_of_finiteFree_retract` is also fully proved.
No sorry remains in the item and no holes were added or split off. This is a proof
from existing library declarations, which may still depend on pre-existing open statements; no new holes are introduced.

## No longer needed

No original imports, dependency nodes, or modules were removed: the original
`def-pc-perfect-complex` dependency is used. The explanatory plan's exactness of
evaluation on a one-point spectrum and its explicit vector-space homology comparison
are unnecessary. Vanishing is proved at the level of cohomology sheaves first, and
additivity alone transports it through evaluation and scalar restriction. These
steps had no separate nodes or imports to prune. Finite dimensionality and minimal
free model existence are not imported or used.

## Where the brief, the DAG or earlier work was wrong

The original node had only the definition of strict perfectness as a proof dependency,
although its prose used the flat derived-pullback computation and open-restriction
comparison. The updated node records those existing theorems and the tensor-closed
structure actually used. No statement error was found. The unit record
`sk-prop-av-cube` has no realized nodes at this descendant; its theorem-of-the-cube
route is unchanged. The three generic comparison/structure lemmas from the Picard
framework serve as tools, not as a replacement for the cube unit's route.

## Second reading by V4

1. Compared the sole delivered Lean module and node with their repository versions.
   The existing theorem signature is byte for byte unchanged; both public imports
   and all existing definitions are unchanged. No change record is required.
2. Compiled locally without errors or warnings. There is no sorry or forbidden
   declaration mechanism in the delivered module. Scratch `#print axioms` checks
   show propext, Classical.choice and Quot.sound for the private flatness helper;
   the main theorem additionally uses sorryAx through existing library dependencies.
   No arbitrary witness is installed as a definition: the functor witness is used
   locally inside a proposition proof, and its imported specification pins its maps
   and objects to tensor pullback.
3. No statements were split off and no holes were added. Checked the finite-free
   retract argument, including rank zero, and the zero complex and reversed bounds.
   Searched the library for fibre boundedness and flat retract results. The related
   localizedPullback_perfectModel_iso requires additional localization instances
   on every open of the source; it is not a shorter direct application here.
4. The argument follows restriction, bounded flat pullback, then cohomology vanishing.
   All old proof dependencies remain used. The cube unit has no realized node for
   this descendant, and its route is preserved; the added generic comparison and
   tensor tools do not replace any unit step. Tested removal of the three upstream
   proof imports in scratch copies: flat and Grothendieck-abelian imports are needed;
   the exact-derived-functor import is redundant and was removed. All remaining
   imports supply statement definitions or proof declarations used here.
5. The node's four proof steps and proof_deps agree with the Lean argument;
   proof_origin identifies the bounded-flat/restriction route. No new nodes need
   validation. Node statement and Lean record were preserved.

Changed only the redundant added proof import and the theorem's natural-language
proof docstring, which now follows zero cohomology through faithful exact restriction
and uses additivity of evaluation. The Lean proof itself needed no repair. The removed
import is WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor;
its module remains reachable through existing imports, so no module is pruned.
