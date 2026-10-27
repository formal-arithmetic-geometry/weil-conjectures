## What changed

Filled `AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenRestrictionSuccessive`
in `Sheaf.Paper.DerivedOpenRestrictionSuccessive`, preserving its complete signature.
All helpers are proved and private in that module. Flexible module composition
comparisons incorporate equality transport. Their existing associativity lifts through
exact derivation by the source-library composition/whiskering laws. Three applications
of this associativity give square pasting. The helpers identify these comparisons with
the prescribed canonical maps; `mateEquiv_vcomp` and mate whiskering then give the
assigned equation componentwise.

Added proof-only imports of module pullback coherence, source-library mate whiskering,
and exact-derived mate coherence.
The existing public import is retained. Local irreducibility prevents unfolding the large
functor constructions during the coherence calculations; it exports no attributes.
Updated this item's DAG proof and proof dependencies to the actual mate argument.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenRestrictionSuccessive`
(node `lem-sfb-derived-open-restriction-successive`).
Added zero holes. No `sorry` remains in the delivered module; this is a proof, not a
decomposition. No definitions or public signatures changed.

The complete proof compiled through `lcompile.py` in 18.5 seconds with no warnings.
The delivery runs the final compile, axiom probe and repository preflight.

## No longer needed

The direct mate argument does not use these former proof dependencies:

- `lem-sfb-kinjective-direct-image-open-word-model`, module
  `Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel`: no resolution-word
  descent is needed for a formal mate-pasting identity.
- `lem-sfb-module-direct-image-open-pasting`, module
  `Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting`: no sectionwise comparison
  is needed, since the canonical derived transformations are defined as mates.
- `lem-weil-pbc-derived-exchange-module-termwise`, module
  `Sheaf.AlgebraicGeometry.DerivedExchangeModuleTermwise`: no representative-level
  normalization is needed for this coherence equality.

Those modules were not imported by the original item; they remain unimported by this
proof. No module is withdrawn, and no source-library declaration is removed. There is
no realized unit statement or proof step attached to this auxiliary node in
`dag/units/sk-cor-affine-space-rational.json`, so this replacement bypasses no unit step.

## Where the brief, the DAG or earlier work was wrong

The old DAG and declaration docstring gave a longer plan through common K-injective
models. The equality follows directly from the existing mate calculus and exact-derived
pullback coherence. Both the docstring and DAG now give the implemented direct proof. The hypotheses are sufficient: the argument works even
for arbitrary commutative squares, but the assigned theorem keeps all pullback and
open-immersion binders unchanged. Identity morphisms and empty opens are included.

No shared-module repair, forced adaptation, new node, or arbitrary witness choice is used.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
