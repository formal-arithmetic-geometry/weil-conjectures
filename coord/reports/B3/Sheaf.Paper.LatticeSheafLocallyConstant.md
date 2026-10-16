## What changed

The original one-hole theorem is proved, with its exact original public signature,
from two strictly smaller geometric statements: exact descent of lattice classes and
the continuous matrix calculation on one specified finite integral basis chart.
This is a decomposition; the closure ledger measures the pruning separately. The concrete comparison between the
constant coset sheaf and the presented class sheaf is fully implemented.

The already proved foundational definitions and theorems move to
`Sheaf.Paper.LatticeSheafBasic`, publicly reexported by the original module, so proof
modules can import them without a cycle. All 26 original public signatures were
compared and are identical; original public definition bodies are identical.
The two existing coefficient ring homomorphisms are exposed, and coset detection is
generalized to any nonempty slice object. All these additions are proved.
The second reading enables type transparency in the existing proof sections and
gives the private local-basis coordinate equivalence its expected type immediately,
avoiding repeated inference through localized coefficient sheaves. These are
elaboration and private-proof changes; public signatures and definition bodies stay
identical.

New proved modules construct the constant-coset map and its normalization, handle
larger-universe sheafification, prove openness of the integer ring and constant-coset
neighborhoods, lift pointwise integral continuous matrices, produce the finite-basis
cover, and prove local surjectivity. Both the empty-object and rank-zero cases are
included: empty objects use the empty covering, and all finite sums/matrices also
apply to Fin 0. No data is chosen from an unproved mere existence theorem.

The current seven downstream lattice coefficient, normalization, coefficient transport,
presentation transport, slice transport, class sheaf and etale-local modules compile
unchanged against this overlay. No existing consumer is adapted. Single-file
compilation has been used throughout. Change record:
`coord/changes/lattice-coset-comparison.md`.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.ProEtale.integralLatticeSheaf_locallyConstant` (1 of 1).
Added two direct holes, so the direct count of this decomposition is net -1:

- `AlgebraicGeometry.ProEtale.exists_latticeClassPresentation`, node
  `lem-weil-pbc-lattice-class-descent`: exact global descent and presentation only;
  it asserts no coset classification or local constancy.
- `AlgebraicGeometry.ProEtale.integralLatticePair_matrixAtBasis`, node
  `lem-weil-pbc-lattice-pair-matrix-at-basis`: the matrix calculation on one supplied
  basis chart only; it constructs neither a covering nor a class sheaf.

These are the only two direct sorries in the delivered Lean files. Each is a named
public theorem in its own module, with exactly `:= by sorry`, a matching node, source,
and complete proof in words. The original theorem therefore still depends on sorry;
it is not claimed to have only the three permitted final axioms.

In addition to the original theorem, the following new theorems are proved:
`CategoryTheory.largeSetSheafification_locallyBijective`;
`AlgebraicGeometry.ProEtale.integralMatrixSubgroup_mem_iff`,
`matrixLatticeImage_coset_eq_of_eq_at`, `matrixLatticePair_image`,
`matrixLatticePair_class_eq_iff`, `matrixLatticePair_class_eq`,
`latticeCosetMap_normalization`, `latticeCosetMap_eq_restrict_iff`,
`latticeCosetMap_injective_at`, `latticeCosetMap_locallyInjective`,
`latticeCosetSheafMap_unit`, `latticeCosetSheafMap_normalization`,
`latticeCosetSheafMap_isIso`, `isOpen_latticeCoefficientIntegers`,
`continuousMatrixCoset_neighborhood`, `sectionMatrixLatticeImage_integral_mul`,
`sectionMatrixLatticeImage_constant`, `coefficientMatrix_integral_of_pointwise`,
`sectionMatrixLatticeImage_eq_of_pointwise_coset`,
`integralLatticePair_localMatrix`, and `latticeCosetMap_locallySurjective`.
The cover and local-surjectivity lemmas were first isolated and then proved in this
session, rather than handed on as further holes.

## No longer needed

The proof bypasses these planned nodes:
`lem-pod-lattice-stabilizer-open`, `lem-weil-pbc-open-immersion-etale`,
`def-weil-pbc-etale-site`, `def-weil-pbc-site-comparison-morphism`,
`lem-weil-pbc-site-sheafification-sections-local`, and
`lem-galois-set-sheaf-local-bijection-isomorphism`.
The three obsolete top-level tool_uses approvals for the stabilizer, Galois local
bijection, and specialized local sheafification nodes are also removed.
The integer-ball and entrywise argument avoids the compact-open linear-map topology.
The existing ProEt.mem_topology_of_openImmersion supplies the cover directly.
The general Mathlib criterion and proved larger-universe unit argument replace the
specialized sheafification-section and Galois local-bijection lemmas.

The following remaining old direct `proof_deps` are no longer direct dependencies
of the final assembly; they remain in the helper proofs or the descent plan and are
not claimed pruned from the transitive argument:
`def-pur-localized-ringed-site`, `def-pur-sheaf-tensor-product`,
`def-weil-pbc-constant-sheaf`, `def-weil-pbc-sheafification`,
`def-weil-pbc-sites-and-cohomology`, `def-weil-sheaf-of-modules-category`,
`lem-weil-pbc-constant-matrix-lattice-pair`,
`lem-weil-pbc-lattice-free-scalar-extension`,
`lem-weil-pbc-lattice-pair-image-classification`,
`lem-weil-pbc-matrix-lattice-coset-invariance`, and
`lem-weil-pbc-site-module-sheaf-gluing`.

Removed proof imports from the old foundational file:
`Sheaf.NumberTheory.Padics.LatticeStabilizerOpen`,
`Sheaf.Paper.SiteSheafificationSectionsLocal`,
`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`,
`Mathlib.AlgebraicGeometry.Sites.Etale`,
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`,
`Sheaf.CategoryTheory.RingedSiteModules`, and
`Sheaf.CategoryTheory.SiteCoveringAxioms`.
The second reading also removes the unused proof import
`Mathlib.Topology.Instances.Matrix` from `LatticeMatrixNeighborhoods`: its continuity
argument uses only individual entries and finite sums, without a topology on matrices.
These imports are not added to the proof modules. Existing transitive dependencies
of the unchanged foundations are not claimed removed from the entire target closure.
`Sheaf.CategoryTheory.SiteModuleSheafGluing` is also removed as an unused proof
import; its node remains in the descent proof plan for the next worker. `Mathlib.CategoryTheory.Sites.LocallyBijective` moves to the new proof API and
remains needed. Original public imports remain through Basic. No existing Lean module
is withdrawn. Pruning here concerns this proof's route, not other parents' uses.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or unit-route change was found. The old proof plan was usable,
but several detours were unnecessary as listed above. Mathlib's automatic
WEqualsLocallyBijective instance for sets is restricted to the site-size universe;
the class sheaf here has values in Type (u + 2). A real proof for larger universes
was needed, and is supplied without a new hypothesis. Foundational code had to be
extracted to avoid circular proof imports; this does not change mathematical data.

The remaining basis calculation needs compatibility of localized sheafification with
scalar extension, invariant basis number, and the naturality of basis coordinates.
Scratch experiments prove the empty-chart case, finite-free restriction, the generic
finite-free scalar extension before sheafification, and its comparison on a basis
chart. They are not delivered as unused auxiliary modules.

For continuation of the basis proof, first restrict the change-of-rings presheaf to
Over W and identify it with the rational free presheaf using the supplied integral
basis, TensorProduct.piRight and AlgebraTensorModule.rid. The compatibility
Over.forget.toSheafify_pullbackSheafificationCompatibility, with pointwise right Kan
extensions supplied by limits in AddCommGrpCat, then makes the original
sheafification unit an isomorphism at W. Express the rationalization and rational
frame as a natural map between coordinate presheaves T ↦ (I → coefficientRing T).
Evaluation at a point gives a nontrivial coefficient ring, so invariant basis number
identifies the finite integral rank with n. A natural coordinate automorphism is
multiplication by its matrix at the identity; naturality gives every restriction.
The remaining assembly identifies the image of each pure tensor 1 ⊗ m with the
corresponding integral linear combination of matrix columns. This component
calculation needs an explicit API for the composed frame isomorphism to avoid
expensive unfolding. The experimental assembly is outside the delivered Lean tree.

## New nodes

`lem-weil-pbc-large-set-sheafification`: proved larger-universe local-bijection
criterion from plus refinements and the subsheaf generated by the unit's image.

`lem-weil-pbc-lattice-matrix-neighborhoods`: proved integer-ring openness and open
neighborhoods of constant right coset, by finitely many entrywise integrality conditions.

`lem-weil-pbc-lattice-section-matrix`: proved continuous integral lifting of a matrix
and its inverse, integral right-multiplication invariance, and the pointwise-coset
criterion for equality of lattice images.

`lem-weil-pbc-lattice-coset-map`: actual constant-matrix lattice pairs define a natural
map, locally injective even on empty objects, with normalization and an isomorphism
criterion after sheafification.

`lem-weil-pbc-lattice-pair-matrix-at-basis`: remaining hole. It needs the localized
finite-free tensor/sheafification comparison, equality of ranks on nonempty charts,
and the restriction formula for the coordinate matrix. Its precise basis and
factorization are supplied as hypotheses, not hidden in a new existence condition.

`lem-weil-pbc-lattice-pair-local-matrix`: proved covering reduction from finite locally
free generators to the preceding calculation on one specified chart.

`lem-weil-pbc-lattice-coset-local-surjectivity`: proved from that covering reduction,
the entrywise open neighborhoods, continuous integral lifting, and the exact
presentation restriction criterion. All covering and slice-associativity glue is proved.

`lem-weil-pbc-lattice-class-descent`: remaining hole. Restrict and quotient pairs,
use uniqueness of intertwining isomorphisms to obtain cocycles, apply the existing
module-sheaf gluing theorem, glue embeddings and inverse rationalizations, and prove
unique amalgamation. This is the global descent part of original steps 2–3 only.
The proof does not assume local constancy of L and has no coset conclusion.

The four existing auxiliary nodes now point to Basic. The original node's proof and
dependencies follow the actual compiled combination. Every new node records actual
Mathlib searches; blueprint and local-module searches found no duplicate. Change
record: `coord/changes/lattice-coset-comparison.md`.

## Second reading by B3

1. **Interface preservation — pass.** Read the original module and the complete
   delivery, including the diff against Basic. Compared all 26 original public
   signatures byte for byte and all original public definition bodies; they are
   unchanged after the second-reading edits. The foundational move and the two
   private-to-public ring homomorphisms are declared in the change record. No
   consumer is adapted and no target statement changes.

2. **Proof and data — pass as a decomposition.** All ten delivered modules compile
   individually, in dependency order, without errors or warnings. Basic takes
   55.6 seconds in this check. A scratch import module runs `#print axioms` on all
   33 public theorems: only `propext`, `Classical.choice`, and `Quot.sound` occur,
   with `sorryAx` precisely in the two named open theorems and the three proved
   theorems depending on the basis calculation or descent. The two reported holes
   are the only direct sorries. There is no forbidden declaration or hollow
   definition. The chosen matrix pair comes from the proved, explicit
   `exists_matrixIntegralLatticePair`; the descent witness is used only inside a
   theorem proof, never as a definition of data.
   Also independently recompiled the seven unchanged lattice coefficient and
   transport/class/etale-local consumers against the final overlay; all pass.

3. **Split statements — pass.** Descent asserts only the exact class presentation,
   without any coset comparison. The basis calculation works on one supplied
   finite basis chart and supplies neither descent nor a cover. Both are true,
   needed, strictly smaller parts of the original argument; each has its own
   module, sourced proof docstring, and matching node. Checked zero rank, empty
   charts, and arbitrary subrings in the basis calculation; no nonempty chart or
   positive rank is silently assumed. New LeanFinder searches for submodule
   descent and global coordinate matrices, Loogle for free scalar extension, and
   local/upstream searches found generic APIs already used here, not duplicates
   that close either remaining hole in a few minutes.

4. **Reduction and pruning — pass after reporting repair.** The final theorem
   actually combines descent, the constructed normalized coset map, local
   injectivity, the finite-basis covering reduction, open neighborhoods, integral
   matrix lifting, and large-universe sheafification. It is not an application of
   a renamed copy of itself. Checked the unchanged `realized` record of
   `sk-thm-properbasechange`; no unit step is bypassed. Public imports support
   statements or data, and proof-only dependencies remain plain imports. Removed
   the unused matrix-topology import. Completed `No longer needed` with all old
   direct proof dependencies, explicitly distinguishing the eleven still used
   indirectly from the six bypassed nodes. No whole-library pruning count is
   claimed here.

5. **DAG agreement — pass.** Checked each delivered node's module and declaration
   names against Lean and each `proof_deps` against the union of its proof steps'
   `uses`. The four existing foundational nodes point to Basic; the main node
   records the actual three-part assembly. All eight new nodes carry their
   provenance, source, searches, creation data, and Lean record. The two open
   nodes' plans agree with their docstring proofs.

Changes made in this reading: repaired the compilation timeout by respecting type
transparency in Basic's proof sections and supplying the private basis equivalence's
expected type immediately; removed `Mathlib.Topology.Instances.Matrix`; completed
the dependency-pruning inventory; and updated the report and change record. No
hole, statement, or mathematical definition was added or weakened.
