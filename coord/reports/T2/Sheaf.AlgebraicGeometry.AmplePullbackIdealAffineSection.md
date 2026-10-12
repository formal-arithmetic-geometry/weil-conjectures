## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.Modules.exists_ample_pullback_ideal_affine_section`
with the planned construction. The target's signature, public imports and docstring are unchanged.
The proof takes an ideal-supported section and an affine section from ampleness, constructs their
product using the associator and `tensorPowAddIso`, applies `affine_cap_section_open`, and transports
through the pullback tensor-power comparison.

Five proved private helpers provide the tensor-product locus formula, ideal-support avoidance,
two image-map naturality formulas, and ideal-section transport. Isomorphism invariance reuses
the existing private `nonvanishingLocus_iso` theorem through `import all AmpleIso`. Local free generators and `Scheme.basicOpen_mul` replace the
planned residue-fibre argument. The ideal-support argument does not require J to be invertible.
Added private proof imports of `NonvanishingGeneratingLocus` and `TensorPullbackAdjunction`.
Updated the item's node proof and proof dependency list to match.
Removed both unaccepted draft modules and their draft nodes from the earlier attempt.

Returned-delivery repair: removed the duplicate private `tensorPow_iso` declaration and added
`import all Sheaf.AlgebraicGeometry.AmpleIso`. The unchanged call in `pullback_ideal_section`
now uses the existing private theorem from that module. A normal import does not expose this
private theorem; `import all` is needed and is already used for `AmpleIso` elsewhere in the library.
No visibility or signature of `AmpleIso` is changed. Added `lem-sc-ample-iso` to the node's
transport-step uses and proof dependencies. The repaired module compiles without warnings.

## Proved and sorry left

Closed 1 original hole: `AlgebraicGeometry.Scheme.Modules.exists_ample_pullback_ideal_affine_section`
(node `lem-sc-ample-pullback-ideal-affine-section`). Added 0 holes; split off 0 statements.
There are no sorry tokens in the delivered module, and every private helper has a complete proof.

The local compile passes without warnings. The target signature was mechanically compared with
its original signature and is identical. The axiom check for the target still includes the
existing transitive holes reached through `affine_cap_section_open`; this is a proof of this
stage-3 item from existing declarations, not a claim that the entire target closure is closed.
The axiom checks for `exists_section_of_ample_ideal`, `exists_tensorPullbackAdjunction`,
`nonempty_pullback_tensorPow_iso`, and `mem_nonvanishingLocus_iff_generatesAt` each report only
`propext`, `Classical.choice`, and `Quot.sound` in the compiled snapshot.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor` and the
corresponding proof dependency `lem-weil-pbc-invertible-pullback-tensor`. The proof uses local
coefficients instead of its rank and residue-fibre clauses, and the proved source monoidal
pullback comparison instead of its bundled comparison clauses. This module and its dependency
subtree are unnecessary for this item's proof; other targets may still reach them independently.

Removed the redundant direct proof import `WeilConjectures.AlgebraicGeometry.Modules.Invertible`;
its definitions remain available through the public `Ample` import, so its module is not pruned
from the import closure.

The unaccepted `GenericAmpleIdealAffine` and `PullbackTensorPowIdealSection` modules, and
`lem-sc-generic-ample-ideal-affine` and
`lem-sc-pullback-tensor-pow-ideal-section-transport` draft nodes, are discarded. Neither their
sorry-backed statements nor their imports are used. They were never landed, so their removal
is not counted as closure progress.

The second reading also removed the redundant direct proof import
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`. Its proved pullback tensor-power
comparison and invertibility instances remain available through the retained imports; the source
module remains in the import closure. A scratch copy without this import compiled cleanly.

Removed the duplicate private helper `AlgebraicGeometry.Scheme.Modules.tensorPow_iso`:
the existing theorem in `Sheaf.AlgebraicGeometry.AmpleIso` supplies it through `import all`.
The module `AmpleIso` is now needed; no additional module is pruned by this repair.

## Where the brief, the DAG or earlier work was wrong

The earlier generic existence split relocated nearly the whole original argument. This delivery
instead writes and proves the construction, including its product, support and transport glue.
No new statement or interface change is needed.

The tensor-power mismatch identified by the earlier attempt is real, but its transport can be
proved: uniqueness of left adjoints compares tensorPullback with the source pullback, whose
monoidal tensor-power comparison is already proved. The positive exponents from ampleness
supply p+q>0; the transport proof itself also handles exponent zero. For J=0 the original
outside-support hypothesis has no point to which it applies, and for J=top the support-avoidance
conclusion is vacuous. No extra hypotheses are introduced in either case. The blueprint unit's
route is retained.

The returned delivery duplicated the private tensor-power isomorphism theorem in `AmpleIso`.
The earlier review's statement that private helpers were unavailable overlooked `import all`.
The repair uses that existing theorem rather than reproving it. The second-reading text below
records the previous delivery, before this repair, and requires a fresh second reading.

## Earlier second reading (a previous round; superseded)

1. **Interfaces — pass.** Read the whole delivered module and its diff against the repository.
   The existing declaration `exists_ample_pullback_ideal_affine_section` has a byte-identical
   signature and docstring, and all public imports are identical. The only new declarations
   are seven private proved helpers. No definition, hypothesis, conclusion or target changed;
   no change record or forced adaptation is required.
2. **Proof and axioms — pass.** Compiled the delivered module through `lcompile.py` with no
   errors or warnings. Scanned it for sorry and forbidden declarations/options: none occur.
   A scratch copy with `#print axioms` for the target and all seven private helpers compiled.
   Every helper uses only `propext`, `Classical.choice`, `Quot.sound`. The target additionally
   uses the existing `sorryAx` dependency through `affine_cap_section_open`; its ideal-section,
   adjunction, pullback tensor-power and nonvanishing-generation dependencies use only the
   three standard axioms. No data definition or arbitrary existence-backed object was added.
3. **Split statements and small cases — pass.** There are no split-off statements or new holes.
   Read each helper: isomorphisms preserve local generators, local product coefficients give
   D(ab)=D(a) intersect D(b), and the ideal-image coefficient lies in the affine ideal, so its
   nonvanishing excludes support. Tensor-power transport uses uniqueness of left adjoints
   and a proved source comparison, not the discarded generic existence restatement.
   For J=0 the outside-support point hypothesis is impossible; for J=top support is empty.
   Empty schemes have no point y; zero sections have empty loci. The transport induction
   handles n=0 with the unit isomorphism; the final exponent p+q is positive by hp.
4. **Route and pruning — pass after one import correction.** Read the existing ample ideal
   section, affine-cap, nonvanishing-generation and pullback adjunction modules, and the source
   `nonempty_pullback_tensorPow_iso`. An independent LeanFinder query for line-bundle product
   nonvanishing and isomorphism invariance found `Scheme.basicOpen_mul`, already used here,
   but no shorter scheme-level result. Searched the upstream and Sheaf modules for tensor and
   isomorphism locus lemmas: analogous helpers in `AmpleIso` are private and unavailable.
   Removing each of the four retained proof imports individually loses the declaration it
   supplies. Removing the direct `ProjectionFormula` import compiles cleanly, so removed it.
   Public imports supply the statement's notions and are preserved. The old proof dependency
   removed is exactly `lem-weil-pbc-invertible-pullback-tensor`, reported under No longer needed.
   Read `dag/units/sk-thm-curveestimate.json`: this helper is not a realized unit statement or
   step; the existing realized statement and all higher routes remain unchanged. The proof
   retains the ideal-section/product/affine-intersection route of the node.
5. **DAG agreement — pass.** Read the original and delivered node. Only `proof`, `proof_deps`
   and `proof_origin` differ. The uses union equals proof_deps, and every step corresponds to
   the Lean construction: ample choices, affine cap and product, local coefficient locus,
   ideal support exclusion, and pullback transport. The source comparison is proved upstream
   and explicitly named in the transport step. The node statement and Lean record are unchanged;
   there are no new nodes to audit. All old dependencies omitted by the proof are reported.

Second-reading changes: removed the redundant private `ProjectionFormula` import, corrected
What changed and No longer needed accordingly, and added this review. Kept the working proofs
and node records. Closed 1 original hole, added 0 holes, split off 0 statements; the upstream
holes used by the affine-cap theorem remain open outside this delivery.


## Second reading by T2

1. **Interfaces — pass.** Read the entire repaired module and its diff against the repository's
   original module. Mechanically compared the existing theorem's signature and docstring:
   byte-identical. Its scheme universes, both invertibility assumptions, ampleness, ideal,
   outside-support point, positive exponent, ideal-tensor section, affine open, exact locus
   equality and disjointness conclusion are unchanged. Public imports are identical; all added
   imports are private proof imports. No definitions, change records or adaptations are added.
2. **Proof and axioms — pass.** Compiled the repaired proof, then a fresh scratch copy of the
   final proof with `#print axioms` for all five local helpers, the target and its key imports.
   No errors or warnings. The helpers and the reused `AmpleIso.tensorPow_iso` and
   `AmpleIso.nonvanishingLocus_iso` use only `propext`, `Classical.choice`, `Quot.sound`.
   So do `exists_section_of_ample_ideal`, `exists_tensorPullbackAdjunction`,
   `nonempty_pullback_tensorPow_iso`, and `mem_nonvanishingLocus_iff_generatesAt`.
   The target additionally has `sorryAx`, traced to the existing `affine_cap_section_open`
   dependency. Scanned delivered Lean for sorry, axioms, unsafe, opaque, extern,
   implemented_by and skipped kernel checking: none. Adjunction choice is from a proved
   theorem with a pinned canonical unit; the isomorphisms are proved to exist and used only
   within proposition proofs. No arbitrary data is defined from an unproved existence.
3. **New statements and edge cases — pass.** There are no split statements, new nodes or
   added holes. Read the five proved private helper signatures and bodies. Simultaneous local
   bases give product coefficient ab, hence D(ab)=D(a) intersect D(b); the ideal-image
   coefficient belongs to J.ideal, so support membership contradicts its basic-open condition.
   Neither argument assumes J invertible. The two image identities are associator, whisker
   and unitor naturality. The transport composes the correctly oriented adjunction comparison,
   upstream tensor-power comparison and existing power isomorphism. For n=0 the power
   comparison is the unit isomorphism; zero sections have empty loci. For J=0 the outside-support
   hypothesis cannot hold, while for J=top the support is empty. Empty schemes have no chosen y.
4. **Shortest route and pruning — pass after repair.** Read `AmpleIso`, `AmpleIdealSection`,
   `AffineCapSectionOpen`, `NonvanishingGeneratingLocus`, `TensorPullbackAdjunction` and the
   upstream `ProjectionFormula.nonempty_pullback_tensorPow_iso`. A fresh LeanFinder query
   about the nonzero locus of tensor products of line-bundle sections returned
   `Scheme.basicOpen_mul`, already used here; repository and source searches found no shorter
   product-locus result. They did find the existing `AmpleIso.nonvanishingLocus_iso`, now
   accessible via the newly retained `import all`, so removed its duplicate local
   `nonvanishing_iso` proof and replaced both calls. Fresh scratch compilations removing each
   of the five retained proof imports separately failed with missing declarations, confirming
   they are needed. The only omitted old proof dependency is
   `lem-weil-pbc-invertible-pullback-tensor`, correctly listed under No longer needed; removed
   direct source imports remain transitively reached. Read the unit's `realized`: its statement
   is `thm-sc-proper-cohomology` and its steps are empty; this helper is not a realized unit
   statement or step. The ideal section, product, affine intersection and transport route stays.
5. **DAG — pass after repair.** Compared original and delivered node: only `proof`,
   `proof_deps`, `proof_origin` differ. The statement and Lean record are unchanged. Checked
   that the uses union equals proof_deps. Each step matches the Lean construction, including
   the two ample choices, affine-cap application, product coefficients, ideal support exclusion
   and left-adjoint transport. Added `lem-sc-ample-iso` to the locus step's uses and explained
   reuse of its existing theorem; it was already in proof_deps for tensor-power transport.
   No new nodes require source, search or schema checks.

Second-reading changes: removed the remaining duplicate private `nonvanishing_iso` theorem,
reused `AmpleIso.nonvanishingLocus_iso` twice, updated the node's locus step and proof origin,
and corrected the helper count in this report. No public interface changed. Closed 1 original
hole (`AlgebraicGeometry.Scheme.Modules.exists_ample_pullback_ideal_affine_section`), added 0,
split off 0. Existing affine-cap dependencies remain open outside this delivery.
