## What changed

Repaired the quarantine return at `3714d173785`. Read the rework row and the archived
`quarantine/Sheaf/AlgebraicGeometry/CoefficientSectionsLocalization.lean`; the existing
claim is held by X2. During this repair the shared branch restored that same archived
one-hole source under `lean/`. This packet replaces its hole with the retained complete
proof. It preserves the module path, every original declaration and theorem signature,
and the node's Lean attachment. Nothing is withdrawn and there is no `deleted.txt`.
Rebased the node on its current metadata, retaining the newer independent reviews and
split history, and updated the theorem docstring to describe the actual proof.

Proved
`AlgebraicGeometry.ProEtale.sfbCoefficientSectionsLocalization` with its statement unchanged.
The proof constructs the slice equivalence, proves invertibility and the unit/product
identities for the actual coefficient section map, proves its naturality along every
morphism of test objects, and constructs multiplication endomorphisms with the normalized
regular-module pullback isomorphism.

Added concrete generic definitions `sfbSectionMapOfHom`, `sfbSheafSectionOne` and
`sfbSheafSectionMul`, together with the canonical coefficient unit and multiplication
morphisms `sfbCoefficientUnit` and `sfbCoefficientMul`. The four existing coefficient
operations/maps specialize these constructions with their signatures and formulas
unchanged by definitional equality. Proved formula lemmas provide an explicit rewrite API,
avoiding costly kernel conversion between generic evaluations and coefficient wrappers.
The remaining helpers are private and proved. The new public data definitions are attached
to the existing item's Lean record; no new mathematical assertion or unfinished module
is introduced.

The proof uses the existing internal/sectionwise module equivalence and the existing
extension-restriction adjunction. It does not construct arbitrary objects from unproved
existence statements. No source-library file was changed. The DAG proof and its dependency
list now describe this route. Definition and consumer checks are recorded in
`coord/changes/X2-coefficient-sections-graph-map-api.md`.

## Proved and sorry left

Proved `AlgebraicGeometry.ProEtale.sfbCoefficientSectionsLocalization`
(node `lem-sfb-coefficient-sections-localization`): **1 of 1 original holes closed**.
There are **zero holes left, zero holes added, and zero statements split off**.
All new data definitions are concrete; all private proof helpers are proved.

The complete module compiled cleanly on the project server in **13.5 seconds**, with no
warnings and normal resource settings. Its theorem statement matches the current restored
source verbatim, all Lean lines are at most 100 characters, and the four refactored
coefficient definitions retain their original signatures and formulas by definitional
equality. The quarantined source has one hole; the delivered module has zero. Consumer
searches found no external direct use of those four definitions.

The final source and its three unchanged direct consumers compiled together in import
order on the server, using the repaired module as an overlay: the item (16.3 seconds),
`LocalModelCohomologyDescent` (4.9 seconds), `AdmissibleScalarRealizationExact`
(6.8 seconds), and `IdentityOpenDerivedRestriction` (8.0 seconds). All passed without
warnings. The consumer copies are validation artifacts under `scratchpad/` and are not
part of the delivery. The two other downstream modules are transitive consumers and
have no direct use of the refactored definitions.

## No longer needed

Removed the proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`;
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`;
- `Sheaf.CategoryTheory.SheafTensor`;
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`;
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` (already a public dependency);
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
  (already available through the retained public dependencies).

Also removed the public imports `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`
and `Sheaf.AlgebraicGeometry.ProEtalePointPullback`: the definitions and proof do not use
them. The continuous-coefficient consumers independently import that API through their
finite-constant model dependencies; the internal-Hom consumer imports the point-pullback
API itself. The identity-open consumers use the published condensed-module framework.

Removed the corresponding unnecessary planned proof dependencies:

- `lem-sfb-proetale-object-inverse-image-restriction` and
  `def-weil-proetale-inverse-image`: uniqueness of the already canonical left adjoints
  gives the restriction comparison directly, including the precise mate formula;
- `def-pur-localized-ringed-site`: ring operations are obtained from the existing
  section-ring functor and the lax monoidal direct-image identities;
- `sk-def-sfb-sheaf-tensor`: the existing scalar-extension adjunction and its regular-module
  API replace the separate pure-tensor/sheafification calculation.

The current DAG additionally proposes these three intermediate results. None is needed
by this complete proof, so their modules are not imported:

- `lem-sfb-localized-ring-mate-graph-evaluation`
  (`Sheaf.AlgebraicGeometry.ProEtaleLocalizedRingMateGraphEvaluation`): the direct
  factorization through the existing restriction adjunction proves invertibility;
  the unit and product laws are evaluated directly for the actual internal ring map.
- `lem-sfb-coefficient-mate-diagonal-graph`
  (`Sheaf.AlgebraicGeometry.CoefficientMateDiagonalGraph`): the private generic graph
  composition calculation and existing coefficient-mate composition law prove naturality.
- `lem-sfb-regular-scalar-extension-multiplication`
  (`Sheaf.CategoryTheory.RegularScalarExtensionMultiplication`): the coefficient map
  here is invertible, so the existing extension/restriction adjunction suffices; the
  more general result for arbitrary coefficient maps is unnecessary.

Withdrew only the obsolete inverse-image-restriction entry of `tool_uses`, preserving
all remaining approvals in order. No module or declaration is withdrawn, and no assertion
is made that these modules are unused by other parts of the project. The unit's own route
is preserved; its `realized` lists impose no additional step on this auxiliary node.

## Where the brief, the DAG or earlier work was wrong

The original statement needs no correction. The proof plan is longer than necessary:
the canonical restriction adjunction and existing scalar-extension API avoid reconstructing
Kan comparison maps and balanced tensor inverses. The explicit diagonal and graph remain
essential; the proof does not replace a general pro-etale object by a monomorphism or
replace arbitrary sections by constant sections.

The restored source and its Lean attachment are preserved. The definition
refactor avoids costly concrete normalization without changing coefficient objects,
operations, assumptions, conclusions or any Challenge declaration. The argument works for
empty test objects, the zero coefficient ring, identity arrows, and non-monomorphic objects.
The return concerned a post-base quarantine, rather than a mathematical defect. The
archived source is preserved, and the current branch's restoration is the baseline for
this proof delivery. The newer DAG decomposition was checked against the already complete
argument; its three general intermediate declarations are stronger than this proof needs.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
