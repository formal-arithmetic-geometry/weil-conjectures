## What changed

Restored the assigned module from the current `coord/rework.tsv` quarantine path and
preserved its Lean attachment, theorem signature and public API. Moved the definitions
unchanged to the publicly re-exported `FiniteDiscreteOrdinaryEncoding`, so the separate
comparison modules can state their results without a cycle. No source-library or target
statement changes.

Proved `encoding_exists`: constant functions are locally bijective by their finite clopen
fibres; sheafification and monoidal inverse image give the normalized coefficient-ring
isomorphism. Transport the section-action equivalence through it, then use the proved
constant-ring module equivalence to obtain precisely the specified additive forward
functors. The fibre cover is indexed by `Fin (Fintype.card A)`, so `A : Type u` is supported.

Proved `canonicalAbelianMap_naturality` using the existing general terminal-unit proof via
`import all Sheaf.Paper.FiniteDiscreteCoefficientTerminal` and naturality along the unique
terminal arrow. This has no finite, discrete, nonzero or nonempty hypotheses.

The main theorem has a complete combining proof from three strict source components.
It derives finite Tor from ordered intervals by widening `[a,b]` to `[min a b,b]`, combines
the generating predicates, proves invariance under isomorphism on the same covers and
strata, and proves both directions of localizing-closure transport by inverse images of
replete triangulated coproduct-closed properties. Shifts, triangles and coproducts use
the actual termwise derived equivalence and its inverse.

Validation: all six delivered Lean modules compile without warnings. A textual check
confirms every moved public definition body and the original theorem signature are
verbatim unchanged, apart from the definitions' documentation attachment IDs.

## Proved and sorry left

Original holes: one, in
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.moduleObject_ordinary_coefficient_equivalence`.
It now has a complete proof from the three components below. This is a decomposition,
not a net proof closure: one upper hole closed, three lower holes added, net -2.

New proved public results, in the namespace
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary`:

- `encoding_exists` (`lem-sf-finite-discrete-normalized-encoding`).
- `canonicalAbelianMap_naturality` (`lem-sf-finite-discrete-encoding-naturality`).

Every hole left, each exactly `:= by sorry` in its own new module, in the same namespace:

- `encoding_tensor_tor` (`lem-sf-finite-discrete-encoding-tensor-tor`): original steps 5--7.
- `encoding_constructibility` (`lem-sf-finite-discrete-encoding-constructibility`): 8--9,
  with the Tor condition handled separately in the main proof.
- `encoding_compactification` (`lem-sf-finite-discrete-encoding-compactification`): 11--12.

Each is strictly a proper part of the source argument and has its source and complete
proof in words. There are no holes in definitions or private declarations. The family's
encodings are chosen from the proved construction, never from a new unproved existence
of arbitrary data.

## No longer needed

The old point and scheme finite-ring theorem nodes
`lem-weil-pbc-finite-discrete-condensed-ring-constant` and
`lem-weil-pbc-finite-discrete-scheme-ring-constant` are not used as black boxes: the
universe-general canonical isomorphism is constructed directly. The scheme module stays
because its general `constantSchemeIso` and monoidal API are needed. Scalar naturality
uses the general terminal-unit proof and does not require the public Type-0 theorem
`lem-weil-pbc-finite-discrete-coefficient-sections`.

The other original tensor, geometric and derived-operation dependencies remain needed
below the three comparison nodes; they are redistributed, not claimed as mathematical
pruning. All original public imports remain available through the encoding module.
No adopted source declaration or quarantined module is withdrawn.

Old proof-only imports absent from the entire packet:

- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso`
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.Paper.CondensedModuleDerivedPushpull`
- `Sheaf.Paper.FiniteDiscreteCoefficientSections`
- `Sheaf.Paper.FiniteDiscreteCondensedRing`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`

## Where the brief, the DAG or earlier work was wrong

The preflight consumer scan also reports three lexical candidates: IntegralDirectImageTower
uses an unrelated `.coefficient` projection; CoefTowerTraceRectification and WeilConjectures
import unrelated modules ending in `Ordinary` or `Internal`. These are recorded in the
change record without source edits.

The item is quarantined, not withdrawn. Its current archive and attachment are restored.
The public finite-ring and coefficient-sections interfaces take `B : Type`, whereas the
item takes `A : Type u`; the old DAG's suggested applications are not literal Lean
applications at the required universes. The finite-fibre construction and the general
terminal-unit proof resolve this without weakening the statement. The old list also
omitted the proved `lem-cbc-constant-ring-module-sheaves`, which supplies exactly the
required fixedRestriction functor.

An initial naturality proof exceeded the compile limit through terminal-scheme unfolding.
A named terminal-arrow existence theorem stopped that reduction; the combined proof then
compiled in 35 seconds. The independent naturality result was subsequently given its own
module and node, as required for separate source results. This was not a file split to
get an unresolved slow proof under the limit.

## New nodes

`lem-sf-finite-discrete-normalized-encoding` owns the unchanged API and the proved encoding.
`lem-sf-finite-discrete-encoding-naturality` is the proved scalar identity needed by the
geometric comparisons. The tensor/Tor, constructibility and compactification nodes named
above are the three independent remaining components. Every node records its source,
proof, dependencies, Mathlib searches and exact Lean attachment. The unit's route stays.

Change record: `coord/changes/finite-discrete-ordinary-encoding-modules.md`.

New remaining comparison node IDs in full:

- `lem-sf-finite-discrete-encoding-tensor-tor`.
- `lem-sf-finite-discrete-encoding-constructibility`.
- `lem-sf-finite-discrete-encoding-compactification`.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
