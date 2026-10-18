## What changed

Repaired the returned duplicate-declaration finding: removed
`AlgebraicGeometry.ringComplex_point_eq` from `RingComplexSemilinearExtension` and its
node attachment. The extensionality proof now imports and uses the existing private
`CategoryTheory.point_eq` from `Sheaf.Algebra.Homology.RingHomExtensionTransport`
via a proof-only `import all`. The public `ringComplexPointLift` definition uses
`Subsingleton.elim` directly, so its body contains no private imported helper.
No existing library module is edited by this repair. The repaired module compiled
on its own, all eight delivery modules compiled together, and the repaired delivery
passed its dry run and axiom preflight. The overlay DAG has 499 reachable nodes and
no dependency cycle.

Kept the complete signature of `AlgebraicGeometry.exists_functorial_ringComplex` unchanged.
Its proof now assembles a concrete Godement mapping fibre, strict functorial maps,
augmented ordered localization models, and a normalized scalar-extension map.
The upper assembly compiles. The three remaining mathematical obligations are separate,
strictly smaller public theorems, each in its own module with its source and full proof
in words.

`RingComplexGodementConstruction` constructs the open complement, the restriction map
from the ring into Godement sections, its mapping fibre, and its augmentation. There is
no `sorry` in these definitions. The chosen Godement model is obtained from
`moduleCup_godement_models_exist`, which specifies its actual terms, cofaces,
codegeneracies, and germ augmentation. These determine the extended cochain complex
and the augmentation up to the equality used downstream; no arbitrary witness of a
mere existence assertion supplies the data.

`RingComplexSemilinearExtension` constructs the actual tensor-presheaf/sheafification
functor. It proves additivity, its section isomorphism on the bottom site, extension of
semilinear maps, the chain equation, and normalization on `1 tensor x`. In particular,
`E` in the upper theorem has exactly the stipulated `changeOfRings` terms and
`changeOfRingsHom` differential, and `chi` is the induced map specified by the theorem.

`RingComplexCechData` only packages the existing clauses as predicates. Its proved
`ringComplexHasCechModel_of_quasiIso` transports an augmented model backwards across a
quasi-isomorphism by composing with the inverse of its derived image. This is used in
the upper proof for the arbitrary supplied K-flat resolution.

All eight delivery modules compiled cleanly together with `lcompile.py --all`.
The subsequently extended cochain-map API in `RingComplexGodementModelMaps`
also compiled cleanly on its own (17 seconds).
The new local base-change formulation, augmented model transport, and pure-tensor
normalization were included in that compile. Both delivery dry runs passed
compilation and preflight, including the final K-flat preservation and resolution
imports and their updated proof plan. All Lean lines have at most 100 characters.
The delivery checks verify that the revised dependency graph is acyclic. No existing definition, public import, consumer signature,
or target statement changes, so no consumer adaptation or change record is required.

## Proved and sorry left

One original hole is removed from `AlgebraicGeometry.exists_functorial_ringComplex`.
Three holes are added below it. This is a decomposition, not an independently proved
original obligation: original holes fully discharged without new obligations: 0 of 1;
holes closed 1, holes added 3, net -2 before any closure pruning.

The repair adds zero holes and closes zero further holes; the retained decomposition
still has exactly three holes. Every remaining hole in the delivery is exactly one of
these standalone theorem bodies:

- `AlgebraicGeometry.ringComplex_godement_functorial`, node
  `lem-weil-pbc-ring-complex-godement-functorial`.
- `AlgebraicGeometry.ringComplex_godement_cech`, node
  `lem-weil-pbc-ring-complex-godement-cech`.
- `AlgebraicGeometry.ringComplex_cech_baseChange_quasiIso`, node
  `lem-weil-pbc-ring-complex-cech-base-change`.

`AlgebraicGeometry.ringComplex_godement_model_maps` is proved: the chosen cosimplicial
model maps and extended cochain maps satisfy strict identity, composition, and
actual germ-augmentation equations. Its
proof reuses the existing coordinate stalk/product constructions, proves their strict
equations on germs and by iteration, and cancels the model transports. It has no holes.

The concrete mapping fibre and augmentation, the scalar-extension functor and complex,
`ringComplexSemilinearLift_one_tmul`, `ringComplexExtension_hom_ext`,
`ringComplexExtension_map_one_tmul`, `ringComplexExtendMap`,
`ringComplexExtendAlong`, `ringComplexExtendAlong_one_tmul`, and
`ringComplexHasCechModel_of_quasiIso` contain no holes. The upper theorem's combination
of these constructions and the three stated obligations contains no holes.

## No longer needed

Removed the duplicate `AlgebraicGeometry.ringComplex_point_eq`; its existing library
counterpart is reused instead. No module is withdrawn for this repair.

Removed the following direct proof imports from `RingComplexFunctorial`:

- `Sheaf.Algebra.Homology.KFlatResolution`
- `Sheaf.Paper.ModuleCupGodementModel`
- `Sheaf.Paper.ModuleCupGodementModelsExist`
- `Sheaf.Paper.ModuleCupGodementModelQuasiIso`
- `Sheaf.Paper.ModuleCupGodementObjectFlasque`
- `Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing`
- `Sheaf.Paper.ModuleCupFlasqueAcyclicity`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology`
- `Sheaf.Topology.RingedSpaceModuleEnoughInjectives`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Mathlib.AlgebraicGeometry.Modules.Tilde`
- `Mathlib.AlgebraicGeometry.Scheme`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Mathlib.RingTheory.Flat.Localization`
- `Sheaf.Paper.FiniteOrderedFlasqueCechComparison`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives`

The upper proof now imports only the three new obligation modules as proof imports.
The original Godement model/existence declarations are used by the concrete construction;
Godement exactness, flasqueness, affine vanishing, acyclic-resolution comparison, and
finite ordered flasque-Cech comparison remain inputs to the Cech obligation. Localization
flatness, bounded-flat K-flatness, localization base change, and the tensor/K-flat notions
remain inputs to the base-change obligation. It also imports the proved generic
`changeOfRings_kFlat_quasiIso` and `exists_isKFlatResolutionIndependentCoefficients`: a common
derived roof can be replaced by a K-flat one, and actual scalar extension preserves
its two quasi-isomorphism legs. Their nodes have moved below the appropriate
new nodes; they have not been declared globally unnecessary. All 18 original
proof dependencies remain reachable in the revised node graph.

`KFlatResolution`, `KFlatIndependentCoefficients`, and the separate stage-2
`Sheaf.Topology.RingedSpaceModuleEnoughInjectives` wrapper are not used in the upper
assembly: it accepts the supplied resolution and derived-category instances, and its
geometric comparison uses the existing ringed-space module input. This does not assert
that these modules disappear from every target's import closure. No entire module or
unit is withdrawn, and no global module pruning is claimed. The proper-base-change
unit's realized statements and proof steps remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the private one-point equality lemma in
`RingHomExtensionTransport`. The two statements are identical, with no difference
in implicit binders or namespaces. This repair removes the duplicate and reuses
the existing lemma. Its node now records that proof dependency.

No statement correction is made. The original proof plan did not provide Lean declarations
for strict Godement functoriality on this particular mapping fibre, its augmented
localization comparison, or the final normalized base-change argument. Those are the
three new obligations; the existing finite ordered comparison alone does not directly
state any of them.

The base-change obligation is local to two augmented complexes, rather than a hypothesis
repackaging of the full functorial-family conclusion. Its augmentation compatibility
identifies the actual induced map using the local-cohomology coreflection, following
Stacks `dualizing.tex`, Tags 0A6R and 0ALZ. This replaces the need for a separately chosen
natural Cech roof for every ring map. The upper proof formally verifies the required
augmentation equation from the functoriality equation and pure-tensor normalization.

Edge cases checked in the statements and proof in words: an empty generating list,
the zero ideal, the unit ideal, the zero ring, repeated generators, zero generators,
and a denominator whose image becomes zero. Finite generation is retained explicitly:
without it, an assertion quantified only over finite generating lists could be vacuous,
so it would not justify the local base-change statement. K-flatness is retained because
ordinary scalar extension of an arbitrary acyclic summand need not remain acyclic.

## New nodes

`def-weil-pbc-ring-complex-cech-data` records the predicates encoding augmented families,
strict semilinear functoriality, and the exact ordered localization coordinates. It also
attaches the proved augmented-model transport lemma. Module:
`Sheaf.Paper.RingComplexCechData`; no holes.

`def-weil-pbc-ring-complex-semilinear-extension` records the explicit scalar-extension
functor and the proved semilinear lifting API. Module:
`Sheaf.Paper.RingComplexSemilinearExtension`; no holes.

`def-weil-pbc-ring-complex-godement-construction` records the actual open-complement
Godement mapping fibre and its augmentation. Module:
`Sheaf.Paper.RingComplexGodementConstruction`; no holes.

`lem-weil-pbc-ring-complex-godement-functorial` isolates the coordinate-induced strict
functoriality. It now uses the proved `ringComplex_godement_model_maps` for its strict cosimplicial
and cochain maps, including their actual germ-augmentation squares. What remains
is semilinear transport to sections on the open complements and the
mapping-fibre square with preservation of the strict equations.

`lem-weil-pbc-ring-complex-godement-cech` isolates the augmented comparison for one ring.
It still needs to apply the existing Godement exactness/flasqueness and affine section
acyclicity declarations, instantiate `finiteOrderedFlasqueCechComparison` on the principal
cover, pass to mapping fibres, and identify all localization coordinates and signs.

`lem-weil-pbc-ring-complex-cech-base-change` isolates a local augmentation-compatible
base-change statement for two complexes. It still needs the bounded-flat Cech model,
the existing termwise localization/tensor isomorphisms, the K-flat-roof comparison
using the two existing generic theorems just named, and the support/coreflection Hom
calculation identifying the stipulated map as an isomorphism. The proof in words gives
the fraction inverse, contraction, and finite-triangle argument explicitly.

`lem-weil-pbc-ring-complex-godement-model-maps` is a proved dependency of the
functoriality obligation. Its module `Sheaf.Paper.RingComplexGodementModelMaps` supplies
the strict cosimplicial and extended cochain map families for every scheme morphism
and structure-module coefficient map, with identity, composition and augmentation
equations in every integer degree. It imports the
existing Godement f-map module only as a proof tool and reuses its private constructions
inside proved theorem bodies; no public definition or signature contains a private helper.
No hole is added.

All seven new nodes inherit the item's chapter, unit, and complete blueprint ancestry. Each
records LeanSearch, LeanFinder, and a Mathlib source search. No change record is added.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
