## What changed

Proved `AlgebraicGeometry.Etale.etale_limit_open_cohomology_cocone_degree` by constructing
K from its actual stage cohomology groups and canonical maps, and its natural transformation
from the canonical legs. Every object identification is the identity isomorphism.
The original signatures and definition bodies are unchanged.

Added `Sheaf.AlgebraicGeometry.TailOpenCohomologyArrowLaws` and
`Sheaf.AlgebraicGeometry.TailOpenCohomologyLegNaturality`, one coherence theorem each.
Their canonical formula definitions duplicate the already specified arrow/leg formulas to
avoid an import cycle with the parent; no data is chosen from existence statements.
The parent proves the formula identifications by reflexivity.

All three modules are checked in import order by the final deliver3.py dry run.
The first dry run passed compilation and preflight except for the second reading,
which the independent reader supplies. Redundant public imports of TopologicalInvariance
and Mathlib.AlgebraicGeometry.Restrict were removed from the new modules; they are already
publicly supplied by EtaleLimitOpenCohomologyCocone.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.etale_limit_open_cohomology_cocone_degree`
(node `lem-weil-pbc-etale-limit-open-cohomology-cocone-degree`).

Added two strictly partial coherence holes:
- `AlgebraicGeometry.Etale.tailOpenCohomologyArrow_laws`
  (`lem-weil-pbc-tail-open-cohomology-arrow-laws`): identity/composition only, no G or cocone.
- `AlgebraicGeometry.Etale.tailOpenCohomologyCoconeLeg_naturality`
  (`lem-weil-pbc-tail-open-cohomology-leg-naturality`): leg compatibility only, no functor
  construction, and no coefficient identity/composition hypotheses.

This is a decomposition, not a net sorry reduction: one closed, two added.
No sorry remains in the parent module or in a definition.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.EtaleLimitCanonicalCohomologyDiagram`.
The parent no longer uses `lem-weil-pbc-etale-limit-canonical-cohomology-diagram`,
`lem-weil-pbc-cohomology-pullback-functorial`, or
`lem-weil-pbc-inverse-image-composition` directly. The last two remain in the new coherence
nodes' proof plans. The existing public import of
`Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone` remains necessary for the definitions
of restricted schemes and coefficient squares; the old proof dependency
`lem-weil-pbc-etale-limit-open-cohomology-cocone` is retained only for those definitions,
not its degree-zero existence theorem. Thus all four old proof dependencies are accounted for.
No unit realization or unit step is bypassed. The two new modules also omit redundant
imports of WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance and
Mathlib.AlgebraicGeometry.Restrict; both remain available through their statement imports.

## Where the brief, the DAG or earlier work was wrong

The second reader corrected both new node statements: their copied parent setup mentioned
unused cone/cocone data or coefficient laws omitted from their actual Lean hypotheses.
The new statements now state precisely the hypotheses of their Lean declarations.
No mathematical error in the Lean statements was found. The continuation also inspected
Sheaf.AlgebraicGeometry.EtaleLimitOpenRestrictedSystem and tried its existing
tailOpenRestrictedSystem_coherence together with the general canonical diagram theorem.
Its first three conclusions provide restricted coefficient laws, but its leg formula is
only in degree zero. We tried to identify the degree-n leg by expanding tailOpenLimitIso,
and again with a separately proved generic coefficient-identity helper. These concrete
applications exceeded the 60-second single-file limit; they are not delivered. The final
proof does not import this alternative module or change its definitions. The planned full restricted coefficient diagram is unnecessary
for assembly: explicit identity/composition and naturality equations suffice. Attempts to
apply generic proved coefficient/cohomology coherence helpers triggered large definitional
unification of the concrete inverse-image expressions and exceeded the single-file limit.
The delivered main proof assembles the data directly from the two specialized laws and
compiles in about 33 seconds. Source tags 01F7 and 09YQ were read on the Stacks website;
local literature copies were unavailable. LeanSearch was unavailable; LeanFinder, Loogle,
Mathlib/project grep and blueprint searches found no existing specialized law.

## New nodes

`lem-weil-pbc-tail-open-cohomology-arrow-laws` packages the identity/composition portion
of the canonical restricted cohomology construction. Its proof plan restricts coherent
coefficient transitions, applies inverse-image square pasting, then cohomology functoriality.

`lem-weil-pbc-tail-open-cohomology-leg-naturality` packages the independent cocone compatibility
portion. Its proof plan starts from L.w and hG, restricts the projection squares, then applies
cohomology pullback composition and naturality. Both nodes keep the parent's source and unit,
include edge-case checks and complete proof docstrings, and record all three search kinds.



## Second reading by E2

1. **Interface: pass.** Compared the complete parent module with the repository by `diff -u`.
   The only changes are its plain proof import and the body of
   `etale_limit_open_cohomology_cocone_degree`. Both existing canonical formula definitions,
   all three existing signatures, visibility, and existing docstrings are byte-for-byte
   unchanged. No target or definition used by a target changes; no change record is required.

2. **Proof and data: pass as decomposition.** Independently compiled all three modules in
   import order (12.0, 15.2, 26.4 seconds). The parent builds K.obj from actual cohomology,
   K.map from the explicit canonical arrow, and the natural transformation from the explicit
   canonical leg; the two holes supply only propositional structure laws. No arbitrary
   existence witness supplies data. The `rfl` proofs compare the two formula definitions
   directly. Scanned delivered Lean for forbidden declarations and every sorry: exactly the
   two reported named coherence theorems remain, none in definitions. A scratch copy prints
   axioms for the parent theorem, both coherence theorems and both new formula definitions;
   the final delivery also runs the all-declarations axiom probe. The scratch result was
   propext, Classical.choice, Quot.sound for the formula definitions, and those three plus
   sorryAx for the parent and both coherence theorems. The parent remains
   dependent on sorryAx through the two new laws and is not an axiom-clean completed proof.

3. **Split statements: pass after metadata repair.** Arrow laws require only the diagram,
   coefficient identity/composition equations and open data; they do not assert existence
   of K or any cocone. Leg naturality requires hG and L.w, but does not assume coefficient
   identity/composition equations or construct K. It follows by precomposing L.w with
   eG.inv, cancelling eG.inv/eG.hom, restricting the resulting coefficient equality and
   applying pullback composition/naturality. Identity singleton diagrams give restriction
   maps; empty W and zero coefficients give the same equations for zero groups. These checks
   reveal no missing limit, qcqs, affine-transition, colimit or torsion hypothesis.
   Read Stacks [01F7](https://stacks.math.columbia.edu/tag/01F7), in particular
   cohomology-equation-functorial, and [09YQ](https://stacks.math.columbia.edu/tag/09YQ),
   theorem-colimit. The new laws are the formal functoriality prerequisite, not the continuity
   theorem of 09YQ, so its limit and finiteness assumptions are not needed here.
   Independent LeanFinder search used “inverse image restriction square pasting cohomology
   functor identities cocone compatibility”: eight unrelated hits. Loogle `cohomologyMap`
   reports an unknown identifier, not evidence of absence. msearch grep and targeted project
   searches found the general diagram theorem, degree-zero cocone, and
   tailOpenRestrictedSystem_coherence, but no duplicate specialized degree-n law. Read the
   upperStarComp unit/associativity laws in upstream Coherence.lean: they supply the square
   pasting calculation described in the new docstrings. The generic restricted-system lemma
   is still sorry and includes degree-zero leg identification; it does not close either new
   theorem in a few minutes. Kept the valid Lean decomposition without rewriting it.

4. **Route and pruning: pass.** Read the proved canonical diagram theorem and the existing
   restricted-system coherence statement. The main construction uses the two exact structure
   equations rather than an equivalent existential restatement. The four old proof
   dependencies are accounted for under No longer needed: three removed as direct uses,
   and the open-cocone module retained for definitions only. The canonical diagram also stays
   indirectly imported by that definition module; removing the direct import does not claim
   it leaves the target import closure. Read sk-thm-p1.json, including realized statement and
   all four realized step lists: none of the replaced helper nodes realizes a unit step.
   The unit route is unchanged. This delivery closes one upper hole and adds two lower
   holes, net minus one; no claim of net proof progress or whole-module pruning is made.

5. **DAG agreement: pass after repair.** The parent proof has exactly two steps, matching
   construction of K from arrow laws and construction of the natural transformation from
   leg naturality, with their union as proof_deps. Both new nodes have source, created,
   blueprint ancestry, chapter/unit, searches and Lean records. Corrected their natural
   language statements to remove the copied parent's unused hypotheses and unused objects,
   rewrote them in TeX, and replaced the flattened lean.statement fields with verbatim
   multiline declaration signatures. Corrected their source records to locate 01F7 in
   cohomology.tex and distinguish 09YQ's application from the functoriality assertion.

Changed only the two new node records and this report during the second reading. No Lean
proof or existing interface needed repair. Verdict: deliver the reported decomposition.
