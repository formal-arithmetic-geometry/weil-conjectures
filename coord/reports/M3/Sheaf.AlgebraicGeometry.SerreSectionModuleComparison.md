## What changed

Replaced the whole proof of `AlgebraicGeometry.serreSectionModuleComparison` without
changing its signature or existing docstrings. The proof works on each arbitrary positive-degree
homogeneous standard open, using `L = O(d)` and its section `f`. Mathlib's proper polynomial Proj
structure morphism supplies compactness and quasi-separatedness. The degree-zero ring is
isomorphic to the field, giving local Noetherianity; coherence then gives quasi-coherence.

Surjectivity uses `exists_tensorPowSection_eq_restrict_qcqs`, then transports the numerator
through the twist tensor-power isomorphism. Injectivity uses `section_restriction_s_torsion`
on the twisted module, then transports the zero tensor section through the associator and
multiplication isomorphism. `Modules.ProjectionFormula` supplies proved invertible tensor-power
and quasi-coherence transport results. Explicit `(X := P)` arguments avoid expensive scheme
inference; no time or heartbeat limits were increased.

Added `Sheaf.AlgebraicGeometry.ProjHomogeneousSectionTensorPowers`, containing the compatibility
part of the argument, and updated the item's DAG proof to match the Lean reduction.

## Proved and sorry left

Closed: `AlgebraicGeometry.serreSectionModuleComparison`
(lem-sc-p1-serre-section-module-comparison), the item's only original hole.
There is no `sorry` left in the item's module.

Added: `AlgebraicGeometry.proj_homogeneous_section_tensor_powers`
(lem-sc-p1-homogeneous-section-tensor-powers), exactly one whole-proof `sorry` in its own module.
This is a decomposition: one upper hole closed and one lower hole added, net zero.
The lower statement concerns only twists and their section multiplication, independently of
`G`, coherence, extension or torsion; it is strictly a part of the argument, not a restatement.

Existing imported holes are not modified: the clearing-denominators and torsion theorems
remain separate downstream items. Both delivered modules compile without warnings. The new
compatibility statement was checked mathematically for `f=0`, exponent zero, negative initial
twist `m`, and positive arbitrary degree `d` using the local basis `x_i^m`. The existential
isomorphisms are used only inside the proof, never to define data from an arbitrary witness.

## No longer needed

Removed direct imports:
- `Sheaf.AlgebraicGeometry.InvertibleSectionLocalization`:
  lem-sc-p1-invertible-section-localization is replaced by its two existing constituent claims.
- `Sheaf.AlgebraicGeometry.ProjectiveLineTwistMultiplication`:
  lem-sc-p1-twist-multiplication is needed only below the new compatibility node; the new
  module keeps this import, so it is not claimed as globally pruned.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`:
  def-sc-p1-standard's TwistData record is not used in the section-level proof.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules`:
  def-weil-pbc-proj-twisting-sheaf remains needed in statements through the public Twist import;
  the redundant direct import is removed.

Removed the item's proof dependency lem-weil-pbc-quasi-separated-affine-cover-criterion:
Mathlib's proper Proj structure morphism provides quasi-separatedness directly. No explicit
cover, nonnegative-truncation construction, fraction-presentation quotient, or gluing step is
needed for the already-stated section-level conjunction. No UNIT statement or realized step
is bypassed: sk-thm-picard-duality has no realized nodes in this subtree, and the Serre section
comparison is still used by the graded-resolution route.

`Sheaf.AlgebraicGeometry.InvertibleTensorQcoherent` was considered but not added: the source
library's proved `isQuasicoherent_tensorObj` suffices.

## Where the brief, the DAG or earlier work was wrong

The original plan and docstring work with degree-one coordinates; the Lean conclusion asks
for every homogeneous positive-degree polynomial. The existing twist-multiplication theorem
states only coordinate degree-one compatibility, so it does not directly supply the required
arbitrary `f` tensor-power identities. The new node records exactly that missing compatibility.
The final section-level statement needs neither an associated-sheaf construction nor gluing;
its two clauses can be combined directly from the existing localization constituents.

The literature TeX sources are absent in this clone (they are intentionally not committed).
Read the cited Stacks tags online and downloaded constructions.tex into the sandbox scratchpad,
then read lemma-when-invertible and lemma-principal-open. LeanSearch returned HTTP 500;
this is recorded as unavailable, with Loogle, LeanFinder and source grep also performed.

## New nodes

`lem-sc-p1-homogeneous-section-tensor-powers` in
`dag/nodes/sec-picard-framework/lem-sc-p1-homogeneous-section-tensor-powers.json` states
invertibility, the locus equality, and coherent tensor-power multiplication identities for
`O(d)` and arbitrary homogeneous `f`. Source: Stacks Constructions 01MS, 01MU, 01MV, 01NG.
Its full chart proof is in the docstring and DAG. The lower plan retains the existing
polynomial-chart and twist-multiplication nodes. No definitions or existing statements changed,
so there is no change record.

## Second reading by M3

1. PASS: compared the complete target module with the repository using `diff -u`.
   Only proof-only imports and the theorem body changed. The existing declaration signature
   and docstrings are byte for byte unchanged; there are no changed definitions, no new
   hypotheses, and no change record is needed. The existing node differs only in `proof`,
   `proof_deps`, and `proof_origin`.
2. PASS: compiled both modules together with `lcompile.py --all`, without errors or warnings
   (2.9 seconds and 7.3 seconds). There is no forbidden declaration or attribute, and the
   only delivered hole is the named whole-proof theorem
   `AlgebraicGeometry.proj_homogeneous_section_tensor_powers`. Neither file constructs data
   using an unproved existence theorem: the existential isomorphisms are eliminated within
   the target proof. A scratch-copy `#print axioms` check and the delivery axiom probe check
   the resulting dependencies; `sorryAx` is expected from the explicitly listed open claims.
3. PASS: read the new theorem and its full chart proof, matching node, and sources.
   For n=0 its maps are the structure-sheaf and right-unit identifications; for f=0 the locus
   is empty and positive section powers vanish; arbitrary negative m uses the invertible
   chart coordinate and presents no extra positivity requirement. The isomorphisms can be
   chosen by multiplication of homogeneous fractions independently of f. This lemma concerns
   twists alone, so is strictly smaller than the coherent-section extension/torsion target.
   Independent searches: Loogle `"unitToTwist"` returned no hits; LeanFinder searched
   isomorphisms of tensor products of twists compatible with homogeneous sections and returned
   only graded-ring tensor products and a Proj pullback lemma. Source `rg` found
   `Proj.nonempty_tensorObj_twist_iso` and `Proj.isInvertible_twist_homogeneousSubmodule`;
   these prove the isomorphism/invertibility parts but omit both displayed section identities
   and the locus statement, so do not duplicate the new theorem. The coordinate-only theorem
   supplies fraction multiplication but does not already state this arbitrary-f conjunction.
4. PASS: read the localization constituent claims, chart theorem, twist multiplication,
   source twist API and ProjectionFormula. The target combines extension and torsion by
   naturality, rather than restating either conclusion as a new hole. All added imports in
   the target are plain proof imports; the new module's public imports are required by its
   signature. The two plain imports there carry its stated lower proof dependencies. The
   unit `sk-thm-picard-duality` has empty realized statement/step lists; no realized node is
   bypassed. The section comparison remains in the graded-resolution route. In addition to
   the individually listed pruned dependencies above, `def-sc-p1-standard` and
   `def-weil-pbc-proj-twisting-sheaf` cease to be direct target proof dependencies: they remain
   statement dependencies and are used below the new compatibility node. No claim is made
   that these modules, or twist multiplication, leave the global target import closure.
5. PASS: checked both JSON nodes against the Lean. The target proof steps record precisely
   its four direct Sheaf proof dependencies; the new node has the required source, statement,
   proof, dependency union, searches, origin, creation, blueprint, unit/chapter and Lean
   records. Its docstring and node explain the same local multiplication and locus argument.

Changes by second reader: completed the pruning account for the two former definition-node
proof dependencies and appended this independent review. The Lean proofs and new statement
needed no repair. This remains a decomposition: one original hole closed, one lower hole
added, net zero; existing imported holes remain open.
