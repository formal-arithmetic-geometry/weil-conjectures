## What changed

Proved `AlgebraicGeometry.schemeHigherDirectImage_of_affine` in
`Sheaf.AlgebraicGeometry.AffineDerivedCohomology`, with its signature unchanged.
The proof follows both original DAG steps. For the acyclicity hypothesis it rewrites a
positive integer degree as a natural-number degree, transports the source library's
proved affine vanishing through `homologyRightDerivedFunctorObjSingleFunctorIso`,
then evaluates `qcoh_acyclic_derived_pushforward_cohomology` at `⟨E, hE⟩`.
The second conjunct applies the source library's proved affine pushforward
quasi-coherence theorem to `H^i(E)`, whose quasi-coherence is `hE i`.

Added the proof-only import
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`.
The second reader removed the redundant explicit Mathlib enough-injectives import;
its instance is already available through the retained imports.
The local Grothendieck instance comes from the proved
`Scheme.Modules.isGrothendieckAbelian X`. The DAG proof now records these generic
compatibility and enough-injectives tools. No definition, statement, public import,
unit statement, or unit proof step changed.

Search: LeanFinder for affine derived pushforward cohomology returned ordinary
pushforward declarations only; Loogle for
`Functor.homologyRightDerivedFunctorObjSingleFunctorIso` had no indexed result;
`msearch grep` found no exact result. Direct `rg` searches of both library roots
located the source affine vanishing, quasi-coherence, and single-object comparison
used here. No shorter exact theorem was found.

## Proved and sorry left

Proved the sole original sorry:
`AlgebraicGeometry.schemeHigherDirectImage_of_affine`
(node `lem-sc-affine-derived-cohomology`). No sorry remains in the delivered module;
no new statement or sorry was added. This is a complete Lean reduction to the existing
comparison theorem `AlgebraicGeometry.qcoh_acyclic_derived_pushforward_cohomology`
(node `lem-sc-qcoh-acyclic-derived-pushforward-cohomology`), whose sorry remains in its
existing module outside this delivery. The module compiled cleanly with `lcompile.py`.

## No longer needed

Removed the redundant proof-only import
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives` added by the
first worker. Its instance remains used transitively, so its DAG dependency remains.
Both original proof dependencies and the derived-direct-image construction are used.
No original dependency node or module is pruned, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original plan omitted the Lean bridge between
natural-number classical higher direct images and integer-degree cohomology of the
unbounded derived direct image on a degree-zero module. The existing proved source
comparison supplies it, so no new intermediate theorem is needed.
The two added generic tool nodes are `src-right-derived-functor-plus-compatibility`
and the Mathlib leaf `lem-sp-grothendieck-enough-injectives`; they implement this
bridge and the required injective resolutions, preserving the unit route.


## Second reading by A3

1. PASS: compared the delivered module and node against the repository with `diff`.
   The existing theorem signature, docstring, definitions, and public imports are
   byte-for-byte unchanged. No change record is required. Only its proof, a proof-only
   import, and the allowed DAG proof fields change.
2. PASS: compiled the module locally without errors or warnings. No `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, or `extern` occurs in the delivered module.
   A scratch copy with `#print axioms` shows only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx` for the theorem, consistent with the existing open
   cohomology-comparison dependency. The single-object comparison, affine vanishing,
   and affine pushforward quasi-coherence declarations have only the three standard
   axioms. The proof does not assume termwise quasi-coherence or boundedness of E.
3. PASS: no split-off statement or new node exists, and no restatement was introduced.
   Read the existing acyclic comparison and the proved source inputs. The positive
   integer-to-natural conversion uses positivity, including p = 1; it makes no
   assertion for p = 0 or negative p. The final comparison permits every integer i
   and every unbounded E with quasi-coherent cohomology, as required.
4. PASS after import repair: the proof preserves both original steps and all original
   proof dependencies. Independent `rg` searches for derived affine homology and
   scheme higher direct images, and `msearch grep` for
   `rightDerivedFunctor cohomology quasicoherent affine`, found no shorter exact
   theorem. The source affine module comparison supplies the necessary degree-zero
   bridge. The unit `sk-thm-picard-duality` has empty `realized` lists; no realized
   unit node or step is bypassed or changed. Removing the explicit enough-injectives
   import still compiles; removing PlusCompatibility makes the single-object bridge
   unknown, so that import stays. No old proof dependency is unused.
5. PASS: the node's two proof steps match the Lean proof. Its `proof_deps` is exactly
   the union of their `uses`, including the existing compatibility node and the
   Mathlib enough-injectives leaf. Both added nodes already exist; the compatibility
   used directly is a proved corollary in that node's module. The recorded agent
   implementation and source references in `proof_origin` match the delivered route.

Changed only the redundant explicit Mathlib enough-injectives proof import and the
report's description of it. No mathematical proof repair was needed.
