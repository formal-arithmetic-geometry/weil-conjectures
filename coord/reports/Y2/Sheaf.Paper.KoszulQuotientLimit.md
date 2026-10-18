## What changed

Replaced the `sorry` in `AlgebraicGeometry.Scheme.koszulQuotientLimit` by a proof from
strict tensor augmentations and invertibility of their explicit product-cocone comparison.
The existing theorem statement and its public imports are unchanged.

The proof constructs the comparison with `mappingCocone.lift`, proves its differential
condition from the strict transition squares, proves both coordinate formulas, and obtains
the derived isomorphism with `asIso`. It proves the unit equation by checking both cocone
coordinates, then localizing. It proves the last naturality clause by checking both
coordinates of the two composite chain maps, using the assumed formulas for `a` and `b`.
Private helpers prove the cocone differential identity, coordinate extensionality, the
coordinate formulas of the lift and the Koszul unit, and the product transition square.
The proof also establishes that the constant rank-one module unit is invertible using
the sheafification adjunction, hence that the exterior degree-zero Koszul unit is
invertible. Naturality of tensor units and the total-tensor coproduct injections then
derive levelwise augmentation naturality from the unit and zero-summand formulas.
Naturality is not assumed in the new augmentation statement.

Validation: `lcompile.py --all` compiled all three delivered modules without errors or
warnings (5.6 s, 5.1 s and 28.4 s respectively). The two new node signatures were checked
against their source text; all proof-dependency lists equal the unions of their steps.
The original target theorem signature was compared byte-for-byte with the shared source.

Two new public statements isolate the unfinished tensor construction and the pro-zero
invertibility argument. These are parts of the original argument, not restatements of
its existential conclusion: neither one constructs a completion isomorphism satisfying
its unit and naturality conclusions. The unit's route is preserved.

## Proved and sorry left

This is a decomposition, not a completed mathematical proof of the original theorem.
The original module has zero remaining `sorry`s. Its former hole,
`AlgebraicGeometry.Scheme.koszulQuotientLimit`, is reduced by a complete Lean proof to
the following two newly added holes:

- `AlgebraicGeometry.Scheme.koszulQuotientTensorAugmentation`
  (`new-s3-koszul-quotient-tensor-augmentation`): construct the balanced augmentation
  from the explicit constant sheafified exterior Koszul total tensor to the actual
  changed-ring quotient complex, and prove its levelwise formulas and transition squares.
- `AlgebraicGeometry.Scheme.koszulQuotientCone_isIso`
  (`new-s3-koszul-quotient-cone-is-iso`): transport the existing coefficient pro-zero
  cone theorem through constant module sheafification and K-flat total tensor, then
  identify the explicit termwise product-cocone map with the strict derived-limit map.
  Exact pro-etale countable products justify this last identification.

Holes removed in the item: 1. Holes added: 2. Net in the delivered statements: -1.
This is not a claim about the target-closure ledger, which also measures import changes.
No definition, private declaration or proof fragment contains a `sorry`.

## No longer needed

The following original direct proof imports are removed from the item:

- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`.
- `Sheaf.Algebra.Homology.KFlatResolutionGeneral`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
- `Mathlib.CategoryTheory.Sites.Sheafification`.
- `Sheaf.RingTheory.NoetherianKoszulAugmentationProZero`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`.
- `Sheaf.Algebra.Homology.DerivedTensor`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`.

The Noetherian augmentation, exact sheafification, and strict derived-limit ingredients
remain needed inside the cone-invertibility intermediate theorem; they are relocated,
not globally pruned. The explicit tensor and K-flatness definitions remain available
through the unchanged public definition modules.

The parent proof no longer calls `lem-pc-kflat-resolution`: an `AdicKFlatModel` is already
an argument of the theorem. It also does not call
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: the actual final naturality clause is
for specified strict maps of models and their cone coordinates, and the coordinate proof
establishes it directly. The corresponding general tensor-pullback and resolution modules
are unnecessary for this proof route. This makes no claim that they are unreachable from
other targets. There are no withdrawn modules.

## Where the brief, the DAG or earlier work was wrong

No false statement was found, and no target, existing definition or theorem signature
was changed. The original plan's instruction to choose a K-flat resolution is redundant
for this Lean statement, which supplies one. Its general derived tensor-pullback argument
is stronger than the strict-map naturality equation required by the signature.

The given Noetherian coefficient augmentation and strict derived-limit statements were
read and retained. Applying them does require explicit comparisons of the concrete
sheafification, scalar-extension and product-cocone models; their interfaces do not state
these comparisons. These are the unfinished content of the two intermediate theorems.

The coefficient-universe-generalized strict tower module named by the latest DAG Lean
record was absent in the shared checkout at the time of reading. The existing original
`RingedStrictTowerHomotopyLimit` module is available and has the required universe for
this pro-etale site. No replacement of that declaration was added.

## New nodes

`new-s3-koszul-quotient-tensor-augmentation`, module
`Sheaf.Paper.KoszulQuotientTensorAugmentation`, states the strict levelwise tensor
augmentation part of blueprint order 1259. Its docstring gives the degree-zero quotient,
vanishing of the differential, balanced sheaf map, total tensor construction and strict
transition arguments. The parent proves its naturality from its defining formulas.
Edge cases checked: with zero generators the ideal is zero and the coefficient
augmentation is the degree-zero identification; over the zero ring every module is zero.
At n=0 the exponent is one, and all nonzero Koszul degrees are sent to zero. A unit ideal
gives a zero quotient and the zero augmentation. It needs no inverse-limit construction.

`new-s3-koszul-quotient-cone-is-iso`, module `Sheaf.Paper.KoszulQuotientConeIsIso`, states
only invertibility of an already supplied explicit comparison. Its proof in words gives
the coefficient pro-zero input, exact constant sheafification, the signed tensor-cone
identification, the K-flat derived passage, and the exact-product Roos comparison. The
last comparison is natural: the strict Roos
functor preserves quasi-isomorphisms, and its inverse-limit unit is a quasi-isomorphism
on resolutions with injective tower terms. The right-derived universal property then
identifies its action on maps with the strict total derived inverse-limit functor. The
unit and zero-summand conditions determine the level map; the two cocone coordinates
determine the cone map. This avoids an arbitrary choice of a triangle filler.

Both nodes record the local-source citations, searches, blueprint provenance, exact Lean
statements and dependencies. The original node's proof and proof dependencies now match
the Lean assembly. Existing statements, definitions, visibility and public imports are unchanged.
The static preflight also flags the new `open` and section-variable commands.
`coord/changes/Y2-koszul-quotient-proof-commands.md` documents them, the unchanged
signature and its downstream consumer. No consumer adaptation is required.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
