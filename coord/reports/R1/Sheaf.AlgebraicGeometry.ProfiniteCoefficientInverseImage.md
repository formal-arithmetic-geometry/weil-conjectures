## What changed

Proved both holes of `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
without changing any existing signature or definition. Naturality follows through
sheafification and inverse-image adjunctions. Constant comparison is an isomorphism
by uniqueness of left adjoints to terminal evaluation. The profinite comparison is
the composite of the preserved-limit comparison and the limit of the constant
comparison. Projection equations, uniqueness, tower naturality, identity and
composition coherence are proved explicitly.

Added four proved helper modules:

- `Sheaf.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable`: finite constant
  set sheaves are represented by coproducts of copies of the base, naturally in the
  finite set. The proof includes the empty finite set and the empty scheme.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTowerRepresentation`: shrink finite ring
  carriers into the site universe, take their profinite limit, and use the existing
  profinite test-object functor. Its representing cone and its base change are
  limiting, with no surjectivity assumption on tower transitions.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTowerLimit`: transfer these geometric
  limits through lifted Yoneda and inverse image, then reflect through forgetting
  ring-sheaf structure.

The fourth helper module,
`Sheaf.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction`, proves
`AlgebraicGeometry.ProEtale.profiniteToCommRingCatOp_isRightAdjoint` by importing
the existing private Hom equivalence and naturality lemma from
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` with Lean's `import all`.
The source module stays unchanged. The tower representation installs the proved
adjunction theorem locally to preserve its countable limit.

Repair of returned head `530cb96ce`: removed both flagged duplicate lemmas,
`profinite_localization_map_eq_eval` and
`profiniteLocallyConstantHomEquiv_naturality`, and the copied private definitions
`profiniteSpectrumProjection` and `profiniteLocallyConstantHomEquiv` from the
helper. It now contains only the public adjunction theorem, assembled directly
from the source module's original equivalence and naturality lemma. No proof is
repeated and no new global instance or source-module API is introduced.

Updated the original node's proof route and added four nodes for the proved API.
The adjunction node now records reuse of the private declarations through
`import all`. New imports needed only by proofs are private imports.

## Proved and sorry left

Closed 2 of 2 original holes:

- `AlgebraicGeometry.Scheme.proEtaleConstantInverseImageMap_naturality`.
- `AlgebraicGeometry.Scheme.proEtale_profinite_coefficient_inverse_image`.

Added holes: zero. Remaining holes in the item and all delivered files: zero.
All four new node statements and all helper declarations are proved. No obligation
was split off with `sorry`. These proofs use existing library declarations as
stage 3 permits; this report makes no claim that their transitive axioms have all
already been eliminated.

Validation: the delivery compiles all five modules and checks their declarations,
axioms and DAG records. The repaired adjunction theorem reuses the source proof;
no theorem remains with `sorry` in any delivered module.

## No longer needed

Removed these six direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.LimitAffineTransition`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`.
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`.
- `Sheaf.RingTheory.IndEtaleStability`.
- `Sheaf.RingTheory.IndPrincipalZariski`.

The new route does not rebuild affine-transition limits or descend ring operations
using a separate algebraic-structure argument: the test-object functor supplies the
geometric limit, and ring forgetting reflects limits. The following original direct
proof dependencies are removed from the item's node (some foundational notions
remain used transitively by the library, so this is not a claim that every listed
module leaves the targets' entire import closure):

- `def-weil-pbc-proetale-site`.
- `lem-weil-pbc-fpqc-representable-descent`.
- `lem-weil-pbc-scheme-coproduct-family`.
- `def-weil-pbc-proetale-covering`.
- `def-weil-weakly-etale-morphism`.
- `lem-weil-pbc-limit-affine-transition`.
- `def-weil-pbc-ind-etale-algebra`.
- `lem-weil-pbc-ind-etale-stability`.
- `def-weil-etale-morphism`.
- `lem-weil-pbc-sheaf-algebraic-structures-objects`.
- `lem-galois-yoneda-hom-bijection`.
- `lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection`.
- `def-pc-fibre-product`.
- `lem-weil-pbc-presheaf-pullback-sets-left-exact`.
- `lem-weil-pbc-sheafification-sets-exact`.

Removed these obsolete top-level `tool_uses` approvals, retaining the remaining
entries in their original order:

- `def-weil-pbc-proetale-site`.
- `lem-weil-pbc-fpqc-representable-descent`.
- `lem-weil-pbc-scheme-coproduct-family`.
- `def-weil-pbc-proetale-covering`.
- `def-weil-weakly-etale-morphism`.
- `lem-weil-pbc-limit-affine-transition`.
- `def-weil-etale-morphism`.
- `lem-weil-pbc-sheaf-algebraic-structures-objects`.
- `lem-galois-yoneda-hom-bijection`.
- `lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection`.
- `def-pc-fibre-product`.
- `lem-weil-pbc-presheaf-pullback-sets-left-exact`.
- `lem-weil-pbc-sheafification-sets-exact`.

Removed the two unnecessary proof imports from the adjunction helper:

- `WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant`.
- `WeilConjectures.Topology.SpectralSpace.ConnectedComponent`.

The helper also drops all four copied private declarations listed above. It needs
only the existing equivalence and naturality lemma, reused through `import all`.
No module is withdrawn. No unit statement or realized unit proof step is bypassed;
this is a new internal proof of the same coefficient-identification node.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The earlier plan's reconstruction of affine limits is
unnecessary given the already implemented profinite test-object functor.
The returned delivery incorrectly copied the source module's private adjunction
argument. Lean's `import all`, already used in this project and Mathlib, makes
those existing private declarations available to the proof directly. Finite
limits alone would not justify the countable coefficient tower.

## New nodes

`lem-weil-pbc-profinite-locally-constant-right-adjoint`: the proved theorem in
`Sheaf.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction`, using the source
module's original private Hom equivalence and naturality lemma via `import all`,
without copying either one.

`lem-weil-pbc-proetale-finite-constant-representable`: the proved finite constant
representation and its naturality. Clopen coproduct fibres give the local inverse;
the comparison is explicitly induced by constant sections.

`lem-weil-pbc-proetale-finite-tower-representation`: the proved geometric
representation of finite ring towers, with limiting cones before and after base
change and an explicit isomorphism to the underlying constant sheaf diagram.

`lem-weil-pbc-proetale-finite-tower-limit`: the proved preservation theorem needed
by the original coefficient comparison. It combines the preceding representation,
representable inverse image, and ring-forgetting preservation and reflection.

No existing definition, statement, visibility or public import changes; no
consumer adaptation or change record is required. The source library is unchanged.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
