## What changed

Proved `AlgebraicGeometry.derived_open_unit_cone_properties` in
`Sheaf.AlgebraicGeometry.DerivedOpenUnitCone` without changing its signature or visibility.
Added the proved private helper `AlgebraicGeometry.open_right_adjoint`.
It constructs the derived open adjunction, cancels the derived over equivalence,
and uses uniqueness of right adjoints to identify the supplied R. Underived open
pushforward is fully faithful and preserves K-injective complexes, so its derived
functor is fully faithful. Restriction followed by qcqs direct image gives
quasi-coherence of R(F(E)).

The final proof specializes `supported_qcoh_isTriangulated` to the whole scheme,
uses cone closure for quasi-coherence, then the adjunction triangle identity and
Mathlib's zero-cone criterion for vanishing on U. The standard localization used
on U is a concrete library construction, not a witness chosen from an unproved
existence assertion. Updated the node's proof and proof dependencies accordingly.

Added proof-only imports for RightDerivedFunctor.Adjunction,
RightDerivedFunctor.FullyFaithful, DerivedCategory.ExactFunctor, and
SupportedQCohTriangulated. Retained DerivedDirectImagePreservesQCoh and
DerivedOpenRestrictionQCoh. No definition, public import, target, or existing
statement changed. No adapted modules or change records are needed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.derived_open_unit_cone_properties`
(node `lem-pc-derived-open-unit-cone`). The private helper
`AlgebraicGeometry.open_right_adjoint` is also completely proved.
No sorry remains in the delivered module; no holes or new statements were split off.
This closes one module-local hole and adds zero. Existing imported dependencies
retain their own proof obligations; this does not claim that the entire targets'
import closure is axiom-free.

Local single-file compilation passed without warnings. Delivery dry run also
checks the permitted axioms and direct sorry usage.

## No longer needed

Removed `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction` and the proof
dependency `lem-pc-restrict-derived-direct-image-open`. Generic preservation of
full faithfulness under right derivation gives the invertible counit directly,
so the general four-scheme open-restriction comparison is unnecessary here.
Removed the definition-only `def-pc-derived-category` from proof_deps; it stays
in stmt_deps and its module remains publicly imported for the statement.
No other original imports or proof nodes are pruned. This is local pruning;
other callers may still require the removed module.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The planned sectionwise counit
computation can be replaced by the library's proved fully-faithful-derived-functor
result. The triangulated closure step already exists in
`lem-pc-supported-qcoh-triangulated`, specialized to Set.univ; no new glue lemma
is necessary. This preserves the unit route and does not bypass any realized step.
The node and Lean statements are unchanged, including the empty open, entire
spectrum, unbounded complexes, and supplied arbitrary adjunction.

Searches: LeanFinder returned general sheaf-adjunction results only; Loogle
rejected the unqualified IsIso query; msearch grep found no direct derived-fullness
match. Local rg located RightDerivedFunctor.FullyFaithful and Adjunction,
ExactFunctor's derived over equivalence, SupportedQCohTriangulated, and Mathlib's
Triangle.isZero₃_of_isIso₁. The local literature checkout lacks perfect.tex and
the unit source markdown. The unit JSON and dependency nodes were read; source
statements were checked at https://stacks.math.columbia.edu/tag/09IR and
https://stacks.math.columbia.edu/tag/08D5.

## Second reading by W3

1. **Interface unchanged:** compared the delivered module and node with the
   repository versions. The target theorem signature and all existing declaration
   statements are byte-for-byte unchanged; verdict: pass.
2. **Proof validity:** compiled the module with `lcompile.py`; the file contains no
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof
   uses only permitted declarations and preserves the supplied adjunction; verdict:
   pass.
3. **Statements and duplication:** no new public statement was split off. The
   private helper is fully proved, and local searches found no duplicate theorem;
   verdict: pass.
4. **Shortest route and pruning:** the proof uses existing derived adjunction,
   fully-faithful, quasi-coherence, triangulated-closure, and zero-cone results.
   The obsolete comparison and unused definition-only dependency were removed;
   verdict: pass.
5. **DAG and unit agreement:** the node proof, `proof_deps`, and `proof_origin`
   match the Lean proof, and the realized unit route remains intact; verdict: pass.

Changed only proof imports, the proof body, and corresponding node proof metadata;
no interface or definition was changed.
