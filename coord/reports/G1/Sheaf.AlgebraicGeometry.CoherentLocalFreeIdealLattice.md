## What changed

Proved `AlgebraicGeometry.Scheme.Modules.coherent_local_free_ideal_lattice` without
changing its signature or existing docstring. Constructed the lattice ideal explicitly
as `(K ^ (n + m)).comap i`, where K is the vanishing ideal of the closed complement.
Used the existing tensor extension and image lift, proved coherence from the source
Noetherian kernel theorem, and proved invertibility on U using restriction of the
multiplication image. The final morphism is the comparison followed by the image lift
and the tensor extension; its agreement equation is proved by functoriality.

Added the proved module `Sheaf.AlgebraicGeometry.ClosedFreeIdealProductIso`.
Its theorem assembles the existing rank-one normalized closed structure comparison
using finite coproduct preservation by pushforward and tensorLeft, then identifies
the resulting epi-mono factorization with the ambient multiplication image.
Both modules preserve the module-system layout; all added proof imports are non-public.
Updated the original node proof route and added a node for the proved comparison.
The unit's realized lists are empty; no unit statement or step was bypassed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.coherent_local_free_ideal_lattice`
(node `lem-pc-c3-coherent-local-free-ideal-lattice`).

Also proved `AlgebraicGeometry.Scheme.Modules.closed_free_ideal_product_iso`
(node `lem-pc-g1-closed-free-ideal-product-iso`).
No sorry remains in either delivered module. Holes added: zero. Split off: zero.
This is a proof from existing project declarations:
`closed_structure_ideal_product_iso`, `coherent_open_map_tensor_extension`, and
`ideal_power_tensor_image_lift`. All three now have proofs in the repository sources,
but the compiled dependency closure still contributes `sorryAx`; no pre-existing
dependency holes are claimed closed by this delivery.
No data definition was added, and no arbitrary existential witness was used in a definition.
The comparison proof handles r = 0, zero/unit ideals and empty schemes; the original
argument also covers empty U, U = X and zero local maps without integrality assumptions.

## No longer needed

No original import was removed: the four public imports provide the existing interface.
The second reader removed the redundant explicit
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` import from the new comparison
module; its public Functorial import already provides it. This removes no module
from the import closure.
The direct original planned proof dependencies
`lem-weil-pbc-reduced-induced-closed-subscheme`
(`Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`),
`lem-weil-pbc-coherent-homs-over-open`
(`Sheaf.AlgebraicGeometry.CoherentHomsOverOpen`), and
`lem-weil-pbc-coherent-kernel-cokernel-locnoeth`
(`Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`)
are not needed directly by this proof and are omitted from the updated proof_deps.
The first is replaced by the proved vanishing-ideal support formula, the second by
the existing tensor extension and image lift, and the third by the proved source
Noetherian kernel theorem. This does not claim those modules are globally unreached:
other imports or targets may still need them.
The original quasi-coherent pushforward and coherence-criterion nodes remain needed.
No integral generic-lattice extension or local rank-one map extension is imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The original module lacked its planned
proof imports, and its plan did not record the normalized finite-sum comparison.
The latter is now a proved node, reducing to the existing rank-one comparison.
`WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial` contains convenient
ideal coherence and tensor restriction lemmas but already reaches the assigned module;
its import would close a cycle. The delivered proof instead uses lower source modules.
LeanSearch returned Internal Server Error; this is recorded as unavailable rather
than treated as evidence that no theorem exists. LeanFinder, Loogle and grep ran.

## New nodes

`lem-pc-g1-closed-free-ideal-product-iso` records the proved finite-rank extension of
`lem-pc-closed-structure-ideal-product-iso`, with no Noetherianity, open, target module,
or supplied local map. It is strictly the ideal-product identification step, and
introduces no new hole. No change records or forced adaptations are needed.

## Second reading by G1

1. Compared the original module with the repository using diff and compared its
   theorem signature as literal bytes. The sole existing theorem has exactly the
   same hypotheses, universes, conclusion, visibility and docstring. Restored one
   extra space before its proof delimiter. No definition or target changed, and
   there are no forced adaptations or statement change records. The comparison
   module is new and contains one theorem, no data definition.

2. Both delivered modules compiled cleanly in import order using lcompile.py.
   Scratch copies with `#print axioms` for both public theorems showed precisely
   propext, Classical.choice, Quot.sound and sorryAx. The latter comes from the
   existing compiled import closure, not a direct hole in these two files. Text
   inspection found no sorry, axiom, unsafe, opaque, implemented_by, extern or
   kernel-check bypass. The ideal I is explicitly `(K ^ (n + m)).comap i`;
   existential morphisms and isomorphisms are used inside theorem proofs only.

3. No statement was split off with sorry. Read the new comparison and its node:
   for a closed immersion A -> B=A/L its two sources are (image(J -> B))^r,
   and its equation identifies the actual coordinate inclusions. The proof uses
   the normalized rank-one theorem to obtain c, finite coproduct preservation
   to obtain the epi q, and image.isoStrongEpiMono with the monic coordinate map
   j. The coordinate naturality calculation proves q followed by j is exactly
   multiplication. Checked r=0 (empty coproduct), J=0, J=A, empty Z and empty X;
   all are included, with no Noetherianity or integrality needed. Independently
   ran LeanFinder for tensor images and finite biproducts, Loogle for image
   uniqueness, and grep for direct-sum images, and searched both library roots
   and the upstream checkout for ideal/free/coproduct comparisons. Mathlib gives
   the assembly APIs, not this normalized geometric theorem. The private
   ideal_power_finite_free_lattice in CoherentIntegralGenericLatticeExtension
   treats an unpushed free source and does not supply this inclusion equation;
   it is not a substitute. Read the source pages [01QY](https://stacks.math.columbia.edu/tag/01QY),
   [01YB](https://stacks.math.columbia.edu/tag/01YB), and
   [01YE](https://stacks.math.columbia.edu/tag/01YE): this is the quotient-algebra
   calculation of 01QY applied coordinatewise, and the extension proof follows
   the tensor-to-image passage of 01YB. The generic injectivity conclusion of
   01YE is neither assumed nor asserted by this item.

4. Read the proof from its conclusion back to its inputs. The last equation uses
   precisely hbeta, ha and he; the invertibility argument uses restriction of
   multiplication, epi_of_epi_fac and preservation of monomorphisms. Coherence
   uses finite pushforward and the Noetherian kernel theorem, with their stated
   hypotheses supplied. The three abandoned old proof dependencies are all
   listed under No longer needed; the quasi-coherent pushforward and coherence
   criterion remain used. Each added proof import supplies declarations or
   instances used by the proof. Removed the redundant ClosedImmersion import
   from the new module (provided publicly by Functorial). The original public
   interface is preserved. The unit sk-thm-picard-coherence has realized.statement
   [] and realized.steps [[]]; this below-unit construction does not replace
   any of its recorded statement or proof-step realizations.

5. Compared both node files with the Lean. The existing node changes only lean,
   proof, proof_deps and proof_origin (the lean statement is semantically and
   textually unchanged after JSON decoding). Its four steps record finite-source
   coherence, tensor extension/image lift, ideal coherence/comparison, and
   restriction invertibility/agreement; every cited dependency provides the
   stated result. The new node's only geometric proof dependency is the existing
   rank-one comparison; the rest is proved categorical assembly. Its Lean
   signature, source, creation record, chapter/unit and blueprint placement all
   match the delivered theorem. No new hole or relabelled version of the item
   is introduced. Added the new node's blueprint tag to its module docstring.

Changes made: signature-delimiter whitespace repair; redundant import removal
and module-docstring blueprint tag in the new comparison; correction of the
report's stale claim that the three directly used project theorems still have
sorry bodies. The mathematical proof bodies required no repair.
