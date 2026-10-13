## What changed

Proved `AlgebraicGeometry.Scheme.exists_perfect_supported_extension` with its signature and
visibility unchanged. Its proof follows Tag 08EK: extend F plus its shift, construct an
actual finite scalar cone chain, apply the existing iterated-cone theorem, lift the
projector, and take a supported perfect cone. The private cone-chain proof uses natural-number
recursion and Mathlib's proved existence of distinguished cone triangles.

Added two fully proved helper modules, one public theorem each:
`Sheaf.AlgebraicGeometry.AffineSupportPoweredGenerators` and
`Sheaf.AlgebraicGeometry.AffineBinomialProjectorCone`. The first obtains a finite
principal-open cover, applies the existing power-annihilation theorem to id_F, and
increases the exponents to positive ones. The second takes the product of cone triangles
of zero on one chosen summand and identity on all others, proves the other cones zero,
and transports the resulting cone isomorphism through restriction.

The existing proof dependencies for affine extension, scalar cones, and map lifting remain
used. Added proof imports for the two helpers, perfect implies quasi-coherent,
perfect two-out-of-three, and supported quasi-coherent triangulated closure.

Read the downloaded Stacks `perfect.tex`, labels
`lemma-lift-perfect-complex-plus-shift-support` (08EK),
`lemma-perfect-into-support-on-T` (08EJ), and
`lemma-lift-perfect-complex-plus-shift` (08EI). Read the pinned Mathlib declarations
`productTriangle_distinguished`, `exists_iso_binaryBiproduct_of_distTriang`, and
`isoTriangleOfIso₁₂`. Searches are recorded in `searches.jsonl`; LeanSearch returned
Internal Server Error, while LeanFinder, Loogle, and source grep supplied component lemmas.
The blueprint searches for powered generators and projector found no exact existing node.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.exists_perfect_supported_extension`
(node `lem-sc-affine-perfect-support-extension`).

Also proved the new declarations
`AlgebraicGeometry.Scheme.exists_affine_support_powered_generators`
(node `lem-sc-affine-support-powered-generators`) and
`AlgebraicGeometry.Scheme.exists_binomial_projector_cone_restrict`
(node `lem-sc-affine-binomial-projector-cone`).

No sorry remains in any delivered module; no new holes were added or split off.
The proof still depends on the existing declared results for extension, scalar power
annihilation, iterated cones, and map lifting, which are downstream items of this stage.
Every delivered file compiles through lcompile.py without errors or warnings.

## No longer needed

Removed the direct proof import of
`Sheaf.AlgebraicGeometry.PerfectIntoSupportPowerTorsion` from the original module:
it is now imported and used by `AffineSupportPoweredGenerators`. Its theorem and DAG node
remain necessary transitively, so this is no module pruning. The projector helper imports
`DerivedCategory` rather than the larger `PerfectComplex`, since its statement and proof
need no perfectness hypothesis. No planned dependency node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No statement or definition required correction. The finite cone chain, quasi-coherence of
the perfect map-lifting target, and cone-support closure needed explicit Lean glue.
The original binomial multiplicity uses s+1 as required by the initial F plus F[1]; this
was retained. The empty-generator case T=X, the empty-open case U=empty, zero F, and
s=0 were checked in the constructions: Fin 0 causes no cone steps; positive powers
preserve the principal-open cover; the projector index (0,0) always exists because
choose(s+1,0)=1. No arbitrary data was defined using an unproved existence theorem:
global section families are explicit restrictions, and all existential cone choices
occur in proofs using Mathlib's proved cone-existence theorem.

## New nodes

`lem-sc-affine-support-powered-generators` records the finite powered-generator
preparation at the beginning of 08EK. Its proof is complete, using the existing
perfectness-to-quasi-coherence and power-annihilation declarations and Mathlib's
finite-subcover and principal-open lemmas. It adds no outstanding proof item.

`lem-sc-affine-binomial-projector-cone` records the final cone cancellation. It has no
affineness, support, or perfectness assumption: it is a restriction and distinguished
triangle calculation. Its proof is complete using products of distinguished triangles,
zero cones of identities, the split zero-map cone, and triangle isomorphisms.

No statement/definition change record or forced adaptation is required.

## Second reading by G1

1. PASS: compared the main module with the repository using diff. The existing theorem's
   signature and docstring are byte-for-byte unchanged; changes are its proof, private
   proof helper, and proof-only imports. Both added public theorems live in new modules.
   There is no statement/definition change or forced adaptation.
2. PASS: independently compiled all three delivered modules with lcompile.py, without
   errors or warnings. Independently ran #print axioms in scratch copies: the projector
   theorem uses only propext, Classical.choice, Quot.sound; the powered-generator and
   main theorems additionally use sorryAx from existing open dependencies. No delivered
   module contains sorry, axiom, unsafe, opaque, implemented_by or extern. The global
   section family is explicitly constructed; the recursive cone choices use Mathlib's
   proved distinguished_cocone_triangle inside a proof, not an unproved existence axiom.
3. PASS: no statement is split off with sorry. Read both new helper statements and
   proofs: they are strictly smaller preparation and cancellation results, not renamed
   copies of the item. Checked T=X (empty family), T empty, U empty, F zero, and s=0.
   Positive powers preserve the principal opens and still annihilate F; the chosen
   binomial index exists even at s=0. Read the source's full 08EK proof locally.
   Independently searched the library for finite principal covers, projector/cone and
   summand arguments, ran LeanFinder with a differently worded diagonal-cone query and
   Loogle for basicOpen_pow. Only component lemmas appeared, already used here.
4. PASS: the proof uses the existing affine extension, power-annihilation, iterated-cone
   and map-lifting declarations. The supported target for map lifting is quasi-coherent
   by perfectness, and both terms of the final cone are supported on T. The triangle
   isomorphism transports the lifted first arrow with the correct composition order.
   The imports provide statement notions or explicitly used proof declarations. The
   old power-torsion dependency is absent from the main node's direct proof_deps but
   remains used through the powered-generator helper; no old dependency is genuinely
   obsolete or pruned. Read sk-thm-picard-duality's realized record: it is unchanged
   (statement and step lists empty); this delivery does not bypass a unit's route.
5. PASS: checked all three node records against the Lean declarations, proof steps and
   dependency unions. The new nodes have sources, complete proofs, recorded searches,
   creation/provenance and verbatim normalized Lean signatures. The main node retains
   its original statement and updates only its stage-3 proof metadata.

Second reading changed only this review report; no Lean or node repair was needed.
One original hole closed, zero holes added, zero split off; existing dependency holes
remain open, so this is a proved reduction of the item, not an axiom-free target closure.
