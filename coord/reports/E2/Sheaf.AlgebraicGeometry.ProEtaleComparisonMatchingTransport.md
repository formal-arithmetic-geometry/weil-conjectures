## What changed

Proved `AlgebraicGeometry.proEtaleComparisonMatchingTransport` without changing its statement.
The proof normalizes terminal transport, proves naturality of terminal restriction in the
coefficient sheaf, and derives a triangle square from the existing inverse-image associativity
law. It then constructs the scheme overlap as a weakly etale object of the pro-etale site,
evaluates the two triangle squares, applies the matching-family equality, and identifies the
remaining dependent cast with the stated `Eq.mp`. All auxiliary definitions construct their
data explicitly from the existing canonical maps; every private helper theorem is fully proved.

Updated `lem-cbc-comparison-matching-transport` to record this calculation and its actual
proof dependencies. The unit route is preserved; there are no realized unit steps to bypass.
Only the item module and its node are changed. No statement, public definition, or target changed.

## Proved and sorry left

Closed the one existing hole in `AlgebraicGeometry.proEtaleComparisonMatchingTransport`
(node `lem-cbc-comparison-matching-transport`). Added zero holes and left zero holes in the
item or elsewhere in this delivery. Single-file compilation passed without errors or warnings
(12.6 seconds after second-reading repair). This is a proof, not a decomposition. It uses the existing
proved `etaleSetInverseImageCompositionUnits`; it adds no unproved intermediate theorem.

The construction works for an empty index type: after constructing the dependent family,
the compatibility proof introduces two indices and therefore requires no nonemptiness.
It also imposes no covering hypothesis and makes no assumption that section types are inhabited.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` and removed
`def-weil-pbc-proetale-site` from this node's direct proof dependencies. The proof uses the
small pro-etale category already available from the existing public Proetale import and does
not use any derived category. The statement dependency on the pro-etale site remains intact.

Removed the redundant direct import
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`: the retained public import
`Sheaf.AlgebraicGeometry.EtaleSetTerminalTransport` already reexports it. Its composition
coherence theorem and DAG node remain essential to the proof.

No other planned node or module is discarded. `EtaleSetTerminalCone` and
`EtaleSetSectionComparison` were read for the coherence pattern but are not imported or used;
the normalized calculation is proved directly. No global unreachability claim is made for
any of these modules.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The import of a derived-category module
was unnecessary for this degree-zero matching-family calculation. The existing node's three
steps suffice when their terminal maps, naturality squares and equality casts are made explicit.

## Second reading by E2

1. **Statements and visibility — pass.** Compared the complete delivered module with
   the repository version, including a byte-for-byte extraction from `theorem
   proEtaleComparisonMatchingTransport` through its type before `:= by`. The signature
   is identical. There is no existing public definition to change. Added declarations
   are private calculation helpers; neither public import changed. Only the item module,
   its existing node's proof fields, and this report are delivered; no change record is
   needed.

2. **Proof and axioms — pass after repair.** Read every helper and the main proof.
   The terminal lift is an explicit pullback lift; `res` is the unit followed by
   restriction; `tr` is equality transport followed by the existing composition
   isomorphism. The chosen composition family comes from a fully proved theorem whose
   fixed-sheaf uniqueness clause determines every component. Thus there is no arbitrary
   witness from an unproved existence theorem. The initial compile failed in
   `transport_triangle`; its inverse-cancellation simplification was in the wrong
   position. Moved that simplification after the naturality/associativity rewrites and
   the other inverse cancellation. The repaired file compiles without errors or
   warnings. A scratch copy with `#print axioms` shows exactly `propext`,
   `Classical.choice`, and `Quot.sound` for both the main theorem and
   `etaleSetInverseImageCompositionUnits`. Source scan finds no `sorry`, custom axiom,
   unsafe/opaque declaration, foreign implementation, or skipped kernel check.

3. **Split statements and small cases — pass.** There are no split-off statements,
   new nodes, or remaining holes. The matching equality is applied to the explicit
   weakly etale overlap object `W` and its projections `a` and `d`; `had` is exactly
   their equality over `Y`. The weakly etale cancellation assumptions are supplied
   by the objects' structure maps. Empty index types require no construction of an
   index, and empty schemes or identity arrows require no extra assumptions. The
   family `t` uses the supplied `s i`, so no inhabitance or covering assumption is
   hidden. The final `tr_eq` eliminates an equality and therefore checks the direction
   of the displayed `Eq.mp`, including coincident arrows.

4. **Route, searches and pruning — pass.** Read the retained composition-unit theorem
   and terminal-transport definition, together with `EtaleSetTerminalCone` and
   `EtaleSetSectionComparison`. The latter cone theorem concerns an etale object and
   does not directly supply this arbitrary weakly etale matching-family equation;
   its similar triangle calculation is private. Searched `lean/Sheaf`, the upstream
   algebraic-geometry source, and LeanFinder through `msearch.py` using
   “naturality of inverse image restriction on terminal sections and composition
   associativity”. The Mathlib global-section restriction results returned concern
   restriction within one site, not this inverse-image triangle; the direct
   naturality calculation here is appropriate. Checked the first proof paragraph of
   [Stacks Tag 0GLZ](https://stacks.math.columbia.edu/tag/0GLZ): this is the overlap
   identification used before fpqc descent, with no descent theorem needed here.
   Both removed imports are accounted for under `No longer needed`: the composition
   module remains publicly reexported by terminal transport; the derived-category
   module is unused. The sole removed old proof dependency is
   `def-weil-pbc-proetale-site`; it remains a statement dependency, with its category
   available through the retained public Proetale import. Read
   `dag/units/sk-prop-sf-comparison.json`: both `realized` lists are empty, and this
   calculation changes no unit statement or route.

5. **DAG agreement — pass.** Parsed both versions of the node: only `proof`,
   `proof_deps`, and `proof_origin` differ. Step 1 matches terminal-lift cancellation
   and the construction of `t`; step 2 matches unit/presheaf naturality and the
   terminal evaluation of the composition associativity clause; step 3 matches the
   explicit overlap and the application of `hs`, followed by equality elimination.
   The two recorded proof dependencies are exactly the retained terminal transport
   and composition coherence inputs. The statement, Lean statement record, source,
   unit and chapter are unchanged.

Second reading changed only the position of the final isomorphism-cancellation
simplification in `transport_triangle` and corrected the compilation evidence in this
report. Closed one original hole, added zero holes, and split off zero statements.
