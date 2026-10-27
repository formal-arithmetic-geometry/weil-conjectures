## What changed

Proved `WeilConjectures.RationalOperations.rationalHom_identifications` without
changing its statement or its public import. Its proof now constructs both full
Hom identifications: integral closure supplies permitted pairs, a proved adjunction
construction supplies the normalized counits, and equality on objects and pure
maps identifies internal Hom into omega with each supplied Verdier duality.
Tensor induction proves the functor equality; heterogeneous transport and the
integral evaluation equations prove the evaluation fields.

Added the proved module `Sheaf.SixFunctors.RationalHomAdjunction`. It restricts the
supplied ordinary adjunction along the fully faithful constructible inclusion and
its invertible completion comparison, proves linearity, extends its linear Hom
bijection to raw scalar localization, identifies the prescribed rational functors
by their object/pure-map equations, and computes the actual counit. All private
helpers and definitions are complete. Keeping the chosen rational Hom functor
abstract avoids expensive unfolding; no shared definition was changed.

Added `Sheaf.SixFunctors.RationalHomScalarEvaluation` for only the remaining finite
coefficient evaluation square. The item imports these two proof modules and the
existing integral-Hom constructibility and completeness-comparison modules with
private imports. Updated its DAG proof route and added the two matching nodes.
No target, existing public signature, source-library file or public import changed.

## Proved and sorry left

Original holes closed: 1 of 1,
`WeilConjectures.RationalOperations.rationalHom_identifications`
(`lem-sf-rational-hom-identifications`).

Additional theorem proved without any new assumption:
`WeilConjectures.RationalOperations.rationalHom_adjunction`
(`lem-sf-rational-hom-adjunction`), including restriction, scalar extension,
functor identification and counit normalization.

New holes added: 1,
`WeilConjectures.RationalOperations.rationalHom_scalar_evaluation`
(`lem-sf-rational-hom-scalar-evaluation`). Its proof is exactly `by sorry`.
It assumes already constructed full Hom identifications and asserts only their
finite-scalar evaluation square. It asserts no closure, adjunction existence,
duality identification or existence of the final witnesses. The item combines
this square with records constructed by complete proofs; this is not the original
existence theorem renamed or made into a hypothesis.

The item and adjunction module contain zero holes; the scalar module contains one.
This is a decomposition overall: one original hole closed and one strictly smaller
hole added, net zero new proof holes. It is not claimed as a proof free of remaining
assumptions. The scalar statement was checked against zero and torsion objects,
identity embeddings and ramified finite extensions; its normalization is the
actual coefficient-passage comparison, not an arbitrary isomorphism.

Validation: the final `lcompile.py --all` compiled the complete module set in
import order with no errors or warnings: adjunction 28.3 seconds, scalar statement
7.1 seconds, item 14.4 seconds. All files remain below the 60-second limit.
The node dependency IDs, proof dependency unions, exact Lean statements, module
headers and 100-character line limit were also checked locally.

## No longer needed

No existing import was removed: the original public import of
`Sheaf.SixFunctors.RationalOperationsData` is retained. No module is withdrawn.
The following original proof dependencies are unnecessary for the new argument
as separate lemmas: the given completion datum already supplies the isomorphism
needed to restrict the ordinary adjunction. Their modules may remain necessary
for other declarations or for constructing the supplied data.

- `def-coef-normalized-dvr-tower` — `Sheaf.Paper.NormalizedDVRTower`.
- `def-pc-kflat-complex` — `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.
- `def-pc-tensor-complex-sheaves` — `Mathlib.Algebra.Homology.BifunctorShift`.
- `def-weil-abstract-derived-category` — `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-weil-derived-complete` — `Sheaf.Paper.DerivedCompleteOnSlices`.
- `def-weil-derived-complete-integral-detailed` — `Sheaf.Paper.SfIntegralConstructible`.
- `def-weil-proetale-tor-amplitude` — `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`.
- `lem-coef-integral-finite-extension` — `Sheaf.SixFunctors.CoefIntegralFiniteExtension`.
- `lem-coef-integral-residue-tor` — `Sheaf.Paper.IntegralResidueTor`.
- `lem-coef-normalized-dvr-effectivity` — `Sheaf.Paper.NormalizedDVREffectivity`.
- `lem-pc-kflat-resolution` — `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `lem-pur-hom-kflat-into-kinjective` — `Sheaf.Algebra.Homology.KInjectiveHomComplex`.
- `lem-pur-integral-operations-well-defined` — `Sheaf.Paper.IntegralOperationsWellDefined`.
- `lem-pur-kflat-change-of-rings` — `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.
- `lem-pur-rhom-global-sections` — `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`.
- `lem-pur-rhom-well-defined` — `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`.
- `lem-sc-derived-hom-tensor-total` — `WeilConjectures.Algebra.Homology.HomTensorTotal`.
- `lem-sf-derived-homology-long-exact` — `Mathlib/structural leaf`.
- `lem-sf-tensor-ctf` — `Sheaf.Paper.FiniteCoefficientTensorCtf`.
- `lem-weil-derived-scalar-extension-restriction-adjunction` — `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`.
- `lem-weil-l-adic-extension-integers-dvr` — `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `lem-weil-pbc-constant-completion-equivalence` — `Sheaf.Paper.ConstantCompletionCore`.
- `lem-weil-pbc-hom-into-triangle-exact` — `Mathlib/structural leaf`.
- `lem-weil-pbc-hom-out-of-triangle-exact` — `Mathlib/structural leaf`.
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit` — `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `lem-weil-proetale-countable-products-exact` — `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `prop-pur-kinjective-resolutions-exist` — `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsMixedUniverses`.
- `thm-coef-integral-verdier` — `Sheaf.SixFunctors.IntegralVerdier`.
- `thm-coef-rational-verdier` — `Sheaf.SixFunctors.RationalVerdier`.

The rational-transport, finite-free scalar, scalar-comparison and rationalization
nodes retained by the two new nodes remain dependencies; they are not claimed as
pruned merely because they moved below the proved helper or the remaining square.
The integral and rational Verdier theorem statements are not applied by the new
proof: the data records already give precisely the object, pure-map and evaluation
equations it needs. Public re-exports through the unchanged data module remain.

## Where the brief, the DAG or earlier work was wrong

The original DAG rebuilt completion and ambient currying even though the theorem
already receives an ordinary tensor-Hom adjunction and a completion transformation
invertible at every constructible pair. Restricting that supplied adjunction is a
shorter route. No statement or definition repair is needed.

The current server queue assigns a proof-route item. The earlier quarantine/build
record reported an unavailable dependency import; the restored original source
compiled against the published build, and this delivery supplies a substantive
proof rather than treating that compilation as completion of the assignment.

Mathlib's categorical localization adjunction does not directly apply to the raw
scalar-localization category without extra universal-property instances. The
proved helper instead extends the actual linear Hom equivalence. The related
`scalarHom_presentation_evaluation` declaration supplies selected ordinary
presentations; it does not directly resolve the square for the arbitrary normalized
presentations in the two supplied records. That comparison is the one remaining
named obligation.

The unit record has no realized statement or proof-step attachments. The unit's
statement and route are unchanged. No forced adaptation or change record is needed.

## New nodes

`lem-sf-rational-hom-adjunction` is the proved restriction-and-rationalization step
of the original proof (steps 6–7). Its conclusion is only the adjunction with its
specified integral counit. It is implemented by
`Sheaf.SixFunctors.RationalHomAdjunction` and introduces zero holes.

`lem-sf-rational-hom-scalar-evaluation` is the original proof's finite-extension
square and its localization (steps 9–10). It requires the two full identifications
and proves only their coefficient compatibility. It is implemented by
`Sheaf.SixFunctors.RationalHomScalarEvaluation` and is the sole remaining hole.
Both nodes have current-source references, complete proof plans, Lean signatures
and three kinds of Mathlib search. No change records were added.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 1 OK, 1 SLOW.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalHomAdjunction": "4387bdd6689d18fec3408609c9f2d63b036069cf", "Sheaf.SixFunctors.RationalHomIdentifications": "c302253e6a3a8f461a26d57e626d003eea7a7805", "Sheaf.SixFunctors.RationalHomScalarEvaluation": "fb9cbdeb29ee247c9b3a2f454697378b5e21edbf"}, "results": {"Sheaf.SixFunctors.CoefQbarVerdierCore": {"hash": "c95bcfeb86963608cbf18ce68781bdce0824eed1", "status": "SLOW"}, "Sheaf.SixFunctors.RationalOperations": {"hash": "4e2dd58b9d060b7498c0e0a39f8083bc1e768c81", "status": "OK"}}, "seconds": 203, "time": "2026-10-28T01:03:23+0800", "transitive": 0, "version": 1}
```

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
