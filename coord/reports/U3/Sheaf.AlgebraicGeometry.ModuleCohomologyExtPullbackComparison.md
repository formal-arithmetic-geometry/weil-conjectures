## What changed

Replaced the sole sorry of ModuleCohomologyExtPullbackComparison by a reduction to
coherent direct-image edge comparison. The original theorem signature, hypotheses,
universes and public imports remain verbatim.

Added the edge comparison module and two proved coefficient-factorization modules and their proved transport lemma.
The module factorization specializes the existing h-map source naturality to an
identity coefficient map. The Ext factorization specializes coeff_naturality and
sheafComparison_naturality to the identity target module morphism. The main proof
combines these factorizations with source coefficient naturality and the edge
comparison. These modules are imported only for the proof.

The proved factorization modules use the comparison library's shared sheafification
and Ext instances locally. Each new statement has its own module, as required by the brief; the transport
lemma packages the four coefficient equalities for the concrete specialization.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Scheme.Modules.exists_moduleCohomology_ext_pullback_comparison
(node new-module-cohomology-ext-pullback-comparison).

Proved three new helper declarations without sorry:
AlgebraicGeometry.Scheme.Modules.moduleCohomology_coefficient_factor
(node new-module-cohomology-coefficient-factor), and
AlgebraicGeometry.Scheme.Modules.moduleCohomology_ext_coefficient_factor
(node new-module-cohomology-ext-coefficient-factor), and
AlgebraicGeometry.Scheme.Modules.moduleCohomology_transport_coefficient
(node new-module-cohomology-coefficient-transport).

Added one hole:
AlgebraicGeometry.Scheme.Modules.exists_moduleCohomology_ext_edge_comparison
(node new-module-cohomology-ext-edge-comparison).

This is a decomposition: one original hole closed, one hole added, net zero.
The edge theorem is the only sorry in this delivery. Its docstring gives its source
and complete resolution argument. No data is chosen from an unproved existence
statement to define an object.

## No longer needed

No original parent import was removed and no global pruning is claimed.
Second reading removed the unused FlatCohomologyComparison public import and its
unneeded local instance attributes from ModuleCohomologyCoefficientFactor, and the
unused ModuleCohomologyFMap public import from ModuleCohomologyExtCoefficientFactor.
Both files compile with those imports absent.

The following old parent proof dependencies are replaced as direct dependencies:
- def-weil-pbc-module-cohomology-fmap;
- lem-sc-injective-module-abelian-acyclic-zariski;
- lem-sc-module-abelian-zariski-cohomology;
- lem-sc-module-cohomology-source-comparison;
- lem-sc-site-cohomology-right-derived-sections;
- lem-weil-pbc-derived-functor-map-via-lift;
- lem-weil-pbc-homotopic-maps-equal-cohomology;
- lem-weil-pbc-module-cohomology-fmap-functorial.

These are retained below the edge-comparison or coefficient-factorization nodes,
including the module/abelian comparison used by the source-comparison theorem.
The parent retains def-pc-flat-cohomology-comparison directly. None of the old
modules is claimed globally pruned. The parent now
uses the identity edge comparison, the two proved coefficient factorizations and
the definition of the linear base-change map. Its original acyclicity,
derived-section comparison, source comparison and homotopy dependencies remain
needed in the edge argument. The functorial h-map module is imported in the module
factorization proof rather than directly by the parent.

## Where the brief, the DAG or earlier work was wrong

The existing source comparison supplies naturality within one scheme, without
cross-scheme normalization. Arbitrarily chosen natural comparison families do not
suffice: negating one family preserves coefficient naturality but can destroy
cross-scheme compatibility. The new edge theorem chooses coherent families.

The inherited report claimed completion although its main proof ended in a
diagnostic fail. This repair completes the combining proof and checks compilation
and the delivery dry run.

The edge specialization also covers degree zero, zero coefficients, empty schemes,
zero rings and nonflat extensions. It uses exact abelian inverse image, without
assuming exact module pullback, vanishing higher direct images, quasi-coherence or
qcqs. Its coefficient is f_*F; compatibility with an arbitrary coefficient morphism
and with the base-change unit is derived by the two proved factorizations.

## New nodes

new-module-cohomology-ext-edge-comparison, in
Sheaf.AlgebraicGeometry.ModuleCohomologyExtEdgeComparison, isolates the common
resolution diagram for the identity coefficient map of a direct image. Its source
is Stacks 03FD, 01FB and 01F7. It is the sole new unproved statement.

new-module-cohomology-coefficient-factor, in
Sheaf.AlgebraicGeometry.ModuleCohomologyCoefficientFactor, is proved from the existing
module h-map source naturality (01FB), by evaluating it and removing composition
with the identity.

new-module-cohomology-ext-coefficient-factor, in
Sheaf.AlgebraicGeometry.ModuleCohomologyExtCoefficientFactor, is proved from the
existing coefficient square and exact-functor Ext naturality (01F7), by removing
the identity target coefficient map.

new-module-cohomology-coefficient-transport, in
Sheaf.AlgebraicGeometry.ModuleCohomologyCoefficientTransport, combines the two
proved factorizations with the given source naturality and edge compatibility.
It works for arbitrary schemes and coefficient maps, and for functions that need
not be equivalences. It is fully proved; the main item specializes it to the unit.

No existing definition or statement changed; no change record or forced adaptation
is needed. The parent node's proof route and dependencies follow the Lean proof.


## Second reading by U3

1. Compared every delivered module with the read-only repository. Only the parent
   existed there; its complete theorem signature and docstring are byte for byte
   unchanged. Its two original public imports remain. All four helpers are new;
   no existing definition, statement, visibility or target changed. No change
   record or forced adaptation is required. Verdict: pass.
2. Compiled all five modules in import order with lcompile.py: no errors or
   warnings, each under 60 seconds. Scanned all delivered Lean sources: one sorry,
   solely in exists_moduleCohomology_ext_edge_comparison; no forbidden declarations
   and no definitions in the new modules. A scratch #print axioms check of all five
   declarations found only propext, Classical.choice and Quot.sound in the three
   proved helpers. The parent and edge theorem additionally use sorryAx, as
   explicitly reported above. No arbitrary existence witness defines data.
   Verdict: a checked decomposition, not a completed proof of the import closure.
3. Read Stacks [03FD](https://stacks.math.columbia.edu/tag/03FD),
   [01FB](https://stacks.math.columbia.edu/tag/01FB) and
   [01F7](https://stacks.math.columbia.edu/tag/01F7), and the existing source
   comparison and h-map functoriality modules. The residual edge theorem isolates
   the identity coefficient diagram; the three proved helpers remove coefficient
   naturality and the base-change unit calculation from that obligation. It is
   not the original unit equality renamed. Its node and docstring specify the
   forgotten-resolution construction and why independent arbitrary equivalences
   cannot be used. Degree zero reduces to the counit on sections; zero coefficients
   and empty schemes give zero groups. No exact module pullback, flatness, or
   acyclicity of f_*F is used. Repeated leanfinder, loogle and grep searches with
   counit/underlying-sheaf terminology, and rg in both library roots. The hits give
   adjunction and within-scheme naturality, not this cross-scheme comparison.
   ScalarCohomologyExtCoefficientNaturality concerns a field and a different Ext
   source, so does not apply. No short closure of the residual diagram was found.
   Verdict: true sourced residual statement, with one reported hole.
4. Read the proof from the parent down through transport and both factorizations.
   The parent specializes the identity edge map using source naturality at the
   base-change unit and unfolds H.baseChangeLinear. Factorization uses the existing
   module h-map source naturality, and Ext factorization uses coeff_naturality and
   sheafComparison_naturality; no new hole is hidden in these reductions. All
   remaining imports supply signature data or a cited proof declaration. Read
   dag/units/sk-thm-p1.json: none of the delivery nodes is a realized statement or
   step, and the unit route and realized entries remain unchanged. Expanded the
   dependency accounting above; no global pruning is asserted. Verdict: pass.
5. Checked all five node records against their Lean signatures and proof bodies:
   verbatim signatures, proof steps, proof_deps unions, sources, origins, creation
   metadata, chapter, unit and blueprint links agree. The parent now records the
   edge and transport reduction; the edge retains the original resolution inputs.
   The three helper nodes record their actual proved reductions. Verdict: pass.

Changed only two unused helper imports (and the unused associated local instance
attributes), the report's dependency accounting and module explanation, and this
second-reading record. Added the independent search results to the residual node.
The holes closed and added remain one each; no additional hole was closed.
