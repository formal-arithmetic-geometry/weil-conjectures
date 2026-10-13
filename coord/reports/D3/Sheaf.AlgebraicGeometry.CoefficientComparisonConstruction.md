## What changed
Proved `AlgebraicGeometry.Scheme.Modules.coefficientSectionAddMap_linear` in
`Sheaf.AlgebraicGeometry.CoefficientComparisonConstruction`, without changing any signature,
definition, visibility, or import. The proof transports scalars through the restriction
identification, pullback adjunction unit, and presheaf restriction using Mathlib linearity
lemmas. It simplifies the global spectrum scalar convention and identifies the two ring maps
using `Scheme.Hom.appLE_comp_appLE` and the commuting-square hypothesis `w`.

## Proved and sorry left
Closed 1 original hole: `AlgebraicGeometry.Scheme.Modules.coefficientSectionAddMap_linear`
(node `lem-pc-coefficient-section-map-linear`). No sorry remains in the item; no hole was added
or split off. The proof uses Mathlib directly rather than any unproved intermediate theorem.
The explicit additive map and both downstream definitions retain their original bodies.
The module compiles locally without warnings (approximately 13 seconds).

## No longer needed
No imports removed and no modules pruned. The sole public import supplies the statement and
construction infrastructure. No additional proof-dependency imports are necessary: all
linearity and ring-map composition lemmas used here are available from Mathlib through it.
The tilde adjunction node `lem-weil-pbc-affine-tilde-gamma-adjunction` is not needed for the
linearity proof itself; the unchanged coefficient mate definition still uses `tilde.adjunction`,
so its infrastructure remains necessary to the module. The sheaf-of-modules and pullback
notions in the existing node remain used. There are no new nodes.

## Where the brief, the DAG or earlier work was wrong
No mathematical or interface defect found. The second reading corrected the stale tilde-adjunction proof dependency in the node. The existing natural-language proof is implemented
by the direct scalar calculation. Rewrite steps require explicit underlying section types
because restriction and pushforward module structures coincide only after unfolding; the
commuting-square rewrite also requires generalizing and reverting its dependent containment
proof. No changes to definitions or downstream modules were necessary. The proof applies to
empty opens and arbitrary schemes, with exactly the original hypotheses.


## Second reading by D3
1. Compared the entire module with the repository using diff. The only Lean change is
   replacement of the original sorry in coefficientSectionAddMap_linear. Every existing
   signature, definition body, visibility annotation, option and import is byte for byte
   unchanged. No change record is needed. Verdict: pass.
2. Read the scalar calculation from source to target, including the containment hL,
   scalar transport through restriction and the unit, cancellation of GammaSpecIso,
   and the final appLE composition using w. Compiled the delivered file cleanly through
   lcompile.py. A scratch copy with #print axioms reports exactly propext,
   Classical.choice and Quot.sound for coefficientSectionAddMap_linear. No sorry or
   forbidden declaration remains in the module; definitions are concrete constructions.
   Verdict: pass.
3. No statements or holes were split off, so no new statement or duplicate lemma needs
   review. The argument is uniform for zero scalars, zero sections, empty Z or W, and
   arbitrary schemes: it uses ring-map identities and linearity without nonemptiness
   assumptions. Verdict: pass.
4. The proof directly uses Mathlib scalar-transport and appLE composition lemmas; local
   searches found analogous appLE calculations, but no existing exact coefficient-map
   linearity theorem to replace this calculation. The sole public import supplies the
   unchanged construction infrastructure. No imports or modules can be pruned from
   this delivery. Read sk-thm-picard-coherence and its realized record: this calculation
   stays below the unit level and changes none of its routes. Verdict: pass.
5. The original node still listed lem-weil-pbc-affine-tilde-gamma-adjunction as a proof
   dependency of linearity although the proof does not use it. Removed that edge from
   proof[].uses and proof_deps, and described the actual Mathlib calculation in proof
   and proof_origin. The sheaf-of-modules and pullback dependencies remain. Verdict:
   pass after repair.

Second-reading changes: DAG proof metadata and this report only; the Lean proof was
correct and was retained. Closed 1 of 1 original holes, added 0, split off 0.
