## What changed

The original target signature and docstring are unchanged. Its proof now chooses the uniquely
characterized isomorphism for each model pair and applies separate comparison and naturality
results. New proof imports are SecondLocalizationIso, SecondLocalizationComparison,
SecondLocalizationNaturality and Mathlib.RingTheory.Flat.Localization.

SecondLocalizationMap constructs exact scalar extension on derived homology, the canonical
left-derived lift of the ordinary associator, and its cohomological adjoint transpose. These
are actual constructions without holes. IsSecondLocalizationMap fixes the resulting D-linear
map on generators, and IsSecondLocalizationMap.ext proves uniqueness. Thus the selected
isomorphism is determined up to equality of its hom, rather than an arbitrary existence witness.

The remaining argument is split into invertibility, comparison compatibility and naturality.
All five modules were recompiled together through lcompile.py during this continuation. Identity localization, zero complexes,
and localization at a monoid containing zero are covered in the intermediate proof docstrings.

## Proved and sorry left

Closed the one original hole:
`RingTensorCohomology.derivedTensor_second_localization_models`.

Added three strictly smaller holes, so this is a decomposition, not a net hole reduction:

- `RingTensorCohomology.exists_secondLocalization_iso`:
  `lem-pc-second-localization-iso`, in SecondLocalizationIso.
- `RingTensorCohomology.secondLocalization_comparison`:
  `lem-pc-second-localization-comparison`, in SecondLocalizationComparison.
- `RingTensorCohomology.secondLocalization_naturality`:
  `lem-pc-second-localization-naturality`, in SecondLocalizationNaturality.

SecondLocalizationMap contains no sorry. Its concrete constructions and generator uniqueness
are proved. There is no sorry in the original item's module.

## No longer needed

No original import was removed and no existing library module is pruned.
The original direct proof dependencies are accounted for as follows:

- `lem-pc-derived-tensor-flat-second-localization` is replaced as a direct dependency
  of the item by `lem-pc-second-localization-iso`; it remains a planned proof dependency
  of that invertibility node and its module is imported there with plain `import`.
- `lem-weil-pbc-localization-flat` remains used through Mathlib's `IsLocalization.flat`.
- `def-pc-base-derived-tensor-cohomology-model` no longer occurs in the item's
  `proof_deps`, because the reduction uses the three intermediate theorem nodes.
  It remains a statement dependency and a public import needed by the unchanged signature.

The unnecessary public import `Mathlib.RingTheory.Localization.Basic` was removed
from SecondLocalizationMap and placed in SecondLocalizationIso, whose statement uses
`IsLocalization`. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt was retained after checking its constructions and reduction.
The comparison and naturality node statements now explicitly name the flatness hypothesis
and the generator characterization already present in their Lean signatures. The old second
reading was removed so the independent reader can review this final version.

The original one-step plan did not supply arbitrary-model transport interfaces. Its existing
flat localization theorem proves resolution-level statements, whereas the target requires
transport through universal counits and both tensor-algebra actions. The new characterization
fixes the coefficient map before splitting these transport obligations. The unit record's
realized statement and step lists are empty; the route is unchanged.

The cited literature source files are not present in this machine's repository. The primary
Stacks pages for [Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6) and
[Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8) were read directly; they state derived associativity and
the affine localization identity used here.

## New nodes

`lem-pc-second-localization-map` records the real canonical coefficient-map construction and
its generator characterization (SecondLocalizationMap). No hole is added by this node.

`lem-pc-second-localization-iso` records pointwise invertibility of that characterized map
for localization, including its tensor-algebra linearity (SecondLocalizationIso).

`lem-pc-second-localization-comparison` records the counit and localized-comparison square
for any characterized isomorphism (SecondLocalizationComparison).

`lem-pc-second-localization-naturality` records naturality under chain maps and
counit-compatible model transformations (SecondLocalizationNaturality).


## Second reading by P1

1. **Interfaces unchanged — pass.** Compared every delivered source with the repository.
   DerivedTensorSecondLocalizationModels is the only existing module; the diff changes
   only its proof and adds four plain proof imports. Its original declaration signature,
   variables, instances, visibility and docstring are byte-for-byte unchanged. The other
   four modules and their nodes are new; no existing definition or target changes.
2. **Proof and constructions — pass, conditional decomposition.** All five modules
   compile through lcompile.py. Inspected all bodies: exactly the three named theorem
   holes listed above remain, with no forbidden declaration or hollow definition.
   The canonical map uses an actual leftDerivedLift, the exact homology isomorphism
   lifted through derived localization, and the extension/restriction adjunction.
   Generator equality and ExtendScalars.hom_ext prove uniqueness of its D-linear
   extension. Thus the existential iso selected in the upper proof is fixed up to
   equality of its hom, and its inverse is then fixed by the iso laws; it is not an
   arbitrary witness of mere existence. Explicit scratch #print axioms checks are
   recorded below. Closing one original hole and adding three is a decomposition
   (net -2 holes), not a completed proof of localization.
3. **Split statements — pass.** Read each signature and docstring against the model's
   universal, cohomologyIso_smul, comparison_eq and localized_eq fields. Invertibility
   supplies only a characterized pointwise iso; comparison and naturality prove separate
   equations for any such iso, including arbitrary flat second-factor maps. None
   restates the full family theorem. The generator predicate makes these equations
   substantive rather than arbitrary compatibility assumptions. Checked zero complex,
   zero D, identity localization, and localization containing zero: tensor extensions
   of zero objects are zero; in the last case Bp and D are zero rings. With identity
   localization but distinct models, universality fixes the counit-compatible transport.
   In the naturality equation the given g and h are fixed by the cohomologyIso equations,
   and zero/identity f obey the same derived square. Read Stacks Tags
   [06Y6](https://stacks.math.columbia.edu/tag/06Y6) and
   [0DJ8](https://stacks.math.columbia.edu/tag/0DJ8): the former supplies derived
   associativity via K-flat resolutions; the latter supplies the affine localization
   identity. The arbitrary-model characterization is the explicit specialization here.
   Repeated searches with different terms: msearch loogle `Functor.leftDerivedLift`
   returned unknown identifier (not evidence of absence); leanfinder `Exact extension
   of scalars commutes with homology of left derived tensor functors naturally`
   returned Ext/Tor exact-functor results, without this arbitrary-complex interface.
   Also searched Mathlib's derived homology/exact-functor sources, upstream Algebra
   and CategoryTheory, and lean/Sheaf homology modules. FirstLocalizationNaturality
   has analogous universal-property reasoning for localization of the first factor,
   but neither its statement nor its coefficient-map construction covers this change
   of output rings. DerivedTensorFlatSecondLocalization covers resolution models.
   No exact existing theorem or quick closing proof was found for the three holes.
4. **Top-down reduction, pruning and unit — pass after bookkeeping repair.** The upper
   proof derives flatness from Mathlib, assembles pointwise characterized isomorphisms
   and applies the separate compatibility results. No unit-level route is replaced:
   sk-thm-picard-semicon has realized.statement = [] and realized.steps = [[]].
   No original import can be removed without changing visibility or signature support.
   The No longer needed section now explicitly accounts for all three old proof_deps,
   including those retained indirectly or as statement dependencies.
5. **DAG agrees — pass after repair.** The item's proof and proof_deps match its flatness,
   pointwise-iso, comparison and naturality applications. The map node records the
   actual constructions and generator uniqueness, not an existence axiom. Each new
   theorem node has its source, complete proof plan, statement dependencies, searches,
   created/blueprint/lean records and the same chapter/unit. The invertibility node's
   planned resolution-level dependency is now a plain import in its module. New
   lean.statement records were expanded to the verbatim multiline signatures.

Changes in this second reading: moved the unnecessary public localization import from
SecondLocalizationMap to SecondLocalizationIso, added the invertibility plan's plain
DerivedTensorFlatSecondLocalization import, made the new node signatures verbatim,
completed the old-dependency accounting, and added this independent reading. Existing
proofs, target statement and the three split statements were retained.

Explicit axiom-check result: flatDerivedHomologyIso, secondLocalizationDerivedMap,
secondLocalizationCohomologyMap, IsSecondLocalizationMap and IsSecondLocalizationMap.ext
use only propext, Classical.choice and Quot.sound. The three split theorems and
derivedTensor_second_localization_models additionally use sorryAx, exactly as expected
from the three remaining named obligations. The scratch copies compiled in import order.
