## What changed

Repaired reviewer X-34936 point 6: added the eventual-zero node copy with proof steps matching the delivered induction. Its direct proof dependencies are now the degree-zero kernel, corrected lift, and cohomology pullback functoriality; proof_origin records this implementation. No Lean statement or proof changed in this repair.

Added a real induction proof of `etale_limit_affine_eventual_zero`. The successor case uses the corrected-lift subtraction argument and the existing finite-stage class descent theorem. Added intermediate exact-ladder and degree-zero kernel interfaces; the ladder and degree-zero geometric constructions remain named theorem holes.

## Proved and sorry left

Closed the item's one hole by decomposition, adding two lower holes (net holes: -1). This repair adds no further holes. Proved `AlgebraicGeometry.Etale.etale_limit_affine_eventual_zero` and `AlgebraicGeometry.Etale.etale_limit_affine_corrected_lift`. The two added holes remain in `AlgebraicGeometry.Etale.etale_limit_affine_degree_zero_kernel` (node `lem-weil-pbc-etale-limit-affine-degree-zero-kernel`) and `AlgebraicGeometry.Etale.etale_limit_affine_exact_ladder` (node `lem-weil-pbc-etale-limit-affine-exact-ladder`). No sorry remains in the item module or corrected-lift module.

## No longer needed

Removed from this node's direct proof dependencies (they may remain needed inside the intermediate geometric lemmas):

- `lem-weil-pbc-limit-affine-transition`
- `lem-weil-pbc-affine-etale-site-colimit`
- `lem-weil-pbc-colimit-of-sites`
- `lem-weil-pbc-affine-etale-site-topos`
- `def-weil-pbc-direct-image`
- `def-weil-pbc-inverse-image`
- `lem-weil-pbc-inverse-image-composition`
- `lem-weil-pbc-left-adjoint-preserves-colimits`
- `lem-weil-pbc-colimit-sites-eventual-vanishing`
- `def-weil-pbc-cohomology-pullback`
- `def-weil-pbc-etale-cohomology`
- `lem-weil-pbc-colimit-initial-full-subcategory`

Removed proof-only imports from the item module: `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`, `Sheaf.CategoryTheory.CohomologyColimitSitesEventualVanishing`, `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`, `Sheaf.AlgebraicGeometry.LimitAffineTransition`, `Sheaf.CategoryTheory.ColimitSites`, `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, and `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

The original broad imports for affine site construction, full affine topos, limit affine transitions, lower shriek, and generic colimit-site machinery are unnecessary in the target proof body; the proof imports only pullback functoriality, class descent, and the three delivered intermediate modules.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery omitted the eventual-zero node update, leaving the obsolete direct colimit-site proof plan in the DAG. This repair replaces that plan and its dependencies with the actual induction.

The DAG plan omitted the explicit corrected-lift subtraction interface needed to make the induction typecheck. The exact ladder is therefore stated in continuation form and the remaining geometric construction is isolated in one theorem.

## New nodes

`lem-weil-pbc-etale-limit-affine-degree-zero-kernel`, `lem-weil-pbc-etale-limit-affine-exact-ladder`, and `lem-weil-pbc-etale-limit-affine-corrected-lift` are new intermediate theorem nodes.

## Earlier second reading (a previous round; superseded)

The second reader checked the item signature against the target node, verified that the induction preserves every hypothesis and that the successor transition uses the stated composition coherence. The intermediate degree-zero and exact-ladder statements are strictly smaller parts of the Stacks 09YP argument; their remaining holes are explicitly named and documented.

## Earlier second reading (a previous round; superseded)

1. I compared the delivered item module with the repository version. The target declaration has the same signature and hypotheses byte for byte; only its proof and proof-only imports changed. Verdict: pass.
2. I compiled the item and all three supporting modules with `lcompile.py`; they compile without errors. The only remaining `sorry`s are the two explicitly named geometric interface theorems, each documented and represented by a split node. No definitions contain `sorry`, and no forbidden declarations were added. Verdict: pass.
3. The split-off statements are the degree-zero kernel, exact-ladder continuation, and corrected-lift interfaces. They are strict subclaims used by the induction, retain the source hypotheses, and are not duplicate library declarations. Verdict: pass.
4. The eventual-zero proof follows the unit route: degree zero invokes the kernel interface, and successor degree uses corrected lifting followed by induction and composition coherence. The imports removed from the earlier proof are listed above; the remaining imports are used by the proof or by its supporting declarations. Verdict: pass.
5. The DAG nodes and Lean declarations agree on names, signatures, proof dependencies, sources, and split status; the unit's realized route is preserved. Verdict: pass.

I added this second-reading record only; no mathematical statement or proof was changed during the review.

## Earlier second reading (a previous round; superseded)

1. Compared every delivered module with the repository. Only the item module
   exists there; its theorem signature is byte-for-byte identical, including
   all hypotheses, the zero-image assumption, and the eventual-zero conclusion.
   The other three modules introduce new declarations; they alter no existing
   signature or definition. All supporting imports used only by proofs are plain
   imports. Verdict: pass.
2. Compiled all four modules locally with `lcompile.py --all`: all pass without
   errors or warnings. A scratch module printed the axioms of all four public
   theorems: exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The only literal holes are the reported degree-zero kernel and exact ladder.
   No definitions or forbidden declarations were introduced. The item and
   corrected-lift proofs are kernel-checked reductions, not axiom-free completed
   geometric proofs. Verdict: pass as a decomposition.
3. Read both open statements and their complete docstring arguments against
   Stacks 09YP, 09YN, 0EXZ, and 0739. The degree-zero statement is only the base
   case. The ladder supplies exact connecting rows and comparison squares,
   without asserting continuity or eventual zero. Its continuation form is
   existence elimination entirely inside a proof, with no arbitrary data
   defined from an unproved existence theorem. The zero system and empty scheme
   have zero groups; for a singleton system the degree-zero comparison is an
   equivalence and the ladder is ordinary long-exact-sequence exactness. For
   n=0, only H^0 and H^1 occur; no negative degree is used. Corrected lifting
   subtracts a descended E-class from a lifted R-class at a common later stage;
   it uses existence, not detection, in degree n. Searches with different words
   through `msearch.py` (LeanFinder, Loogle, grep), and `rg` in the library and
   upstream checkout found structure-sheaf section lemmas and general Ext
   machinery, not these arbitrary-abelian-etale statements. The generic
   colimit-site kernel and ladder require additional site and map comparisons;
   the existing scheme class-descent connecting ladder supplies a different
   surjective limit connecting map, not the exact kernel row needed here.
   Neither open theorem can be closed by a direct application found in this
   search. Verdict: true, needed, strictly smaller subclaims, still open.
4. Read the induction and corrected-lift subtraction from top downward. The
   composition helper is a direct application of pullback functoriality. All
   remaining imports are needed for signatures or the actual proof. Compared
   the old and new eventual-zero proof dependencies: every removed node is
   listed under `No longer needed`; this is direct pruning, not a claim that
   those modules are globally unreachable. Inspected `sk-thm-p1.json` including
   `realized`: this node is below its realized unit steps and the delivery
   changes none of them. Verdict: pass.
5. The eventual-zero node already matches the induction. The three supporting
   node records were deficient: their natural-language statements merely
   pointed to Lean, their proof plans all described the same degree-zero
   argument, and corrected lift had no dependencies despite applying two
   project theorems. Repaired those new records with self-contained statements,
   separate source-based proof steps and accurate proof origins; corrected lift
   now records exact ladder and class descent as direct proof dependencies.
   Removed inherited review stamps from the new nodes, which did not certify
   this delivery. Lean statements recorded in the nodes are unchanged and match
   their modules. Verdict: pass after repair.

Changes in this reading: corrected the supporting DAG records and the item's
proof docstring, which incorrectly said its proof applied the now-pruned
colimit-site theorem. No Lean signature, definition, proof term, import, or hole
was changed. No additional lower hole was closed. The result remains one upper
hole closed by two lower holes (net -1), rather than a completed proof of the
geometric kernel theorem.

## Second reading by H2

1. Compared the item with the repository using diff and the declaration parser.
   The existing public signature is byte-for-byte identical. The other three
   modules are new; no existing definition or statement changes. Proof-only
   imports are plain imports. Verdict: pass.
2. Compiled all four delivered modules locally with lcompile.py, and compiled a
   scratch audit printing the axioms of all four public theorems. Each uses only
   propext, Classical.choice, Quot.sound and sorryAx. The two literal holes are
   exactly etale_limit_affine_degree_zero_kernel and etale_limit_affine_exact_ladder.
   No definition, forbidden declaration or arbitrary witness definition was added.
   Verdict: pass as a decomposition, not an axiom-free geometric proof.
3. Read the open degree-zero and exact-ladder statements and their docstring
   proofs. Checked Stacks 09YN (sections), 0EXZ (injective systems) and 09YP
   (continuity). Degree zero is a strict base case. The ladder asserts exact
   rows and natural comparison squares, not continuity or eventual vanishing;
   its continuation form eliminates existential data inside a proof. Stage
   injectivity supplies surjectivity of delta, and limit exactness supplies
   ker beta = im alpha_0 without assuming limit injectivity. For n=0 all
   displayed degrees are nonnegative; empty schemes and zero coefficients give
   zero groups; a singleton index is ordinary long-exact-sequence exactness.
   Searched again using LeanFinder, Loogle and grep via msearch.py and rg on
   the library. LeanFinder's finite-stage zero detection applies to structure
   sheaves, not arbitrary abelian etale sheaves. Loogle did not know Sheaf.H;
   no matching result was obtained there. Existing generic site ladders require
   site/comparison data not supplied by this statement. The existing scheme
   class-descent ladder has different exactness data. No direct closure in a
   few minutes was found. Verdict: true, needed, strictly smaller open claims.
4. Read the induction from the target downward and the corrected-lift proof.
   It lifts x, descends its limit correction using degree-n class descent,
   subtracts at a common stage, and then applies lower-degree zero detection.
   Thus it does not circularly invoke this item. Composition functoriality
   identifies the two transitions with the composite. All remaining imports
   serve signatures or proof terms. The report enumerates the removed direct
   proof dependencies and imports; this does not claim global unreachability.
   Inspected sk-thm-p1.json and its realized steps: none is bypassed or changed.
   Verdict: pass.
5. Parsed every new node and compared its recorded Lean statement with the
   corresponding declaration (up to whitespace for the existing compact node).
   All match. Every proof_deps list equals the union of the proof steps' uses.
   The item records induction, corrected lift records exact ladder and class
   descent, and the two open geometric nodes record their construction plans.
   Source, creation, blueprint, unit and chapter fields are present. Verdict: pass.

Changes in this reading: appended this current audit section, resolving the
preflight failure for its missing exact heading. No Lean proof, signature,
definition, import or node was changed. Closed one original hole by adding two
lower holes, with no further holes closed during this reading; net closed minus
added is -1. Corrected lift is proved relative to existing and new open lemmas.
