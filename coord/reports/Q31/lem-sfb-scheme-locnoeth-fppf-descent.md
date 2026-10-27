## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyNoetherianFppfDescent` states
`AlgebraicGeometry.isLocallyNoetherian_of_fppf`, with proof `by sorry`.
It introduces no definitions and changes the item's node only in `lean`.
The source is Stacks Project, descent.tex, Tag 034C,
`lemma-Noetherian-local-fppf`, read at lines 4761–4784. Its locality assertion
includes the descent implication for the singleton covering in this node.

Hypothesis and conclusion correspondence:

- Schemes and size convention: `universe u` and `{X Y : Scheme.{u}}`.
  The theorem is polymorphic in `u`, with no bound on the chosen universe.
- A scheme morphism: `(f : X ⟶ Y)`.
- Flatness: `[Flat f]`. `Flat.iff_flat_stalkMap` identifies this class with
  the stalkwise flatness of the recorded dependency.
- Locally of finite presentation: `[LocallyOfFinitePresentation f]`.
  This is the recorded dependency's affine-local predicate, not finite
  presentation of the entire morphism.
- Surjectivity on underlying topological spaces: `[Surjective f]`.
  Its `surj` field is `Function.Surjective f` on points.
- Locally Noetherian source: `[IsLocallyNoetherian X]`.
- Locally Noetherian target: conclusion `IsLocallyNoetherian Y`.
  The class uses all affine opens; the recorded
  `isLocallyNoetherian_of_affine_cover` proves equivalence with the node's
  affine-cover definition.
- No quasi-compactness, separatedness, reducedness or common-base assumption
  appears in the binders or conclusion. There is no common base parameter.

Statement dependency declarations, with full signatures and docstrings read:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-size-convention`: recorded as a metatheoretic convention with
  no declaration or module; rendered by the explicit universe binder.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- `def-sbc-locally-finite-presentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective`,
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `Mathlib.AlgebraicGeometry.Noetherian`, including its affine-cover equivalences
  and the open-subscheme and locally-finite-type permanence declarations.

All stated proof dependencies have imports. `Sites.Fpqc` supplies
`Scheme.fppfPrecoverage`, `fppfTopology`, `fpqcPrecoverage` and
`fppfPrecoverage_le_fpqcPrecoverage`; `Scheme` supplies `Spec` and `Spec.map`;
`RingTheory.Noetherian.Defs` supplies `IsNoetherianRing`;
`Flat.FaithfullyFlat.Basic` supplies
`Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat`;
`Flat.Basic` and `Algebra.DirectSum.Module` supply `Module.Flat.directSum`,
`Module.Flat.of_linearEquiv` and `DirectSum.linearEquivFunOnFintype`;
`Morphisms.Flat` supplies `flat_iff`; `Flat.FaithfullyFlat.Algebra` supplies
`Module.FaithfullyFlat.of_comap_surjective`; `Noetherian` supplies
`IsLocallyNoetherian.component_noetherian` and the affine-cover criterion.
These imports are public exactly when needed for the statement; the rest are
ordinary imports for the recorded six-step proof plan. The docstring retains
each of those six steps, including the finite-product ideal argument.

Edge cases checked before writing: the empty source with a surjective map
forces an empty target, which is locally Noetherian. An empty affine target
open permits an empty family and the zero product ring. A nonempty affine
target open requires a nonempty covering refinement. Identity morphisms give
the unchanged local Noetherianity hypothesis. Arbitrary non-quasi-compact
schemes and non-quasi-compact morphisms are included; finite refinements are
chosen separately over each affine target open. No nonemptiness, finiteness,
base scheme, reducedness or separation restriction was introduced.

Searches on 2026-10-23 using the prescribed `msearch.py` wrapper:

- LeanFinder: `Local Noetherianity descends along flat surjective locally
  finitely presented scheme morphisms`. Eight hits: locally-finite-type
  ascent, open-immersion ascent, flat-lfp universal openness, and generic
  morphism-property descent. No exact match.
- LeanSearch: `A scheme is locally Noetherian if it admits a flat surjective
  locally finitely presented morphism from a locally Noetherian scheme`.
  Eight hits: the class and constructors, affine-cover criterion, global
  Noetherianity and Artinian ascent. No exact match.
- Loogle: `AlgebraicGeometry.IsLocallyNoetherian, AlgebraicGeometry.Flat`.
  Six hits concern geometric reducedness or integrality over a locally
  Noetherian base; none gives this descent statement.
- Mathlib grep in `AlgebraicGeometry`:
  `([Nn]oetherian.*[Dd]escen|[Dd]escen.*[Nn]oetherian|isLocallyNoetherian_of.*[Ff]lat)`.
  Zero hits.
- `rg` of the same expression in the project's `lean/WeilConjectures` and
  `lean/Sheaf`, plus the exact blueprint id: found Noetherian approximation
  results, the parent stack descent's citation, and
  `Sheaf.AlgebraicGeometry.EtaleLocalNoetherianDescent`. The latter was read:
  its theorem assumes etale morphisms and is a narrower result, so cannot
  replace the present fppf theorem.
- Exact-name search for `isLocallyNoetherian_of_fppf`,
  `isLocallyNoetherian_of_flat` and `schemeLocallyNoetherianFppfDescent` in
  both Lean trees and `dag/lean_names_upstream.json`: no collision.

No statement correction, missing notion, unusable dependency or disputed
statement was found. The inherited unchanged-node failure belonged to the
earlier split delivery. The current item is stage-2 queued with no Lean
record; the stage-handoff paragraph of `coord/brief-stage2.md` explicitly
authorizes preserving its reviewed split and supplying the Lean attachment.

## Second reading by Q31

Sequential worker re-reading: the node and Lean signature were opened together.
`{X Y : Scheme.{u}}`, `(f : X ⟶ Y)`, `[Flat f]`,
`[LocallyOfFinitePresentation f]`, `[Surjective f]` and
`[IsLocallyNoetherian X]` account for every object and assumption, and the
conclusion is exactly `IsLocallyNoetherian Y`. In particular the statement
does not require `[QuasiCompact f]` or a locally Noetherian base. The empty
case and the unrestricted universe binder are retained. No mismatch or
correction was needed. This is a self-check, not an independent second
worker review: the dispatcher forbids starting other agents and assigns
the independent reading to the maintainer.
