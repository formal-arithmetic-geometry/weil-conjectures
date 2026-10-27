## What changed

Proved `AlgebraicGeometry.ringComplexGodement_affineSections` with its existing signature,
using only existing declarations and two fully proved private helpers in the item module.
The public import and all existing definitions are unchanged. Added proof imports for
Godement exactness/flasqueness, affine vanishing, the source flasque-module API,
quasi-coherence of the structure module, and finite intersections of affine opens.

`principalIntersection_affine` constructs the ambient finite intersection of basic opens,
proves it lies in the ideal complement using the generator indexed by `t 0`, and applies
open-immersion transport of affineness. The tuple is always nonempty. Thus the argument
includes empty intersections, repeated or zero generators, and the zero ring; when `r=0`
there are no tuples.

`godement_eval_quasiIso` proves the comparison on every affine open of every scheme.
Affine vanishing supplies right-acyclicity of the structure module for the existing
abelian-group-valued open-section functor. The specified Godement model supplies exactly
the augmentation already in the statement and identifies its terms as products of stalk
skyscrapers. The source flasque-module dimension-shifting criterion supplies their
right-acyclicity on the chosen open directly. Extension by zero and the single-complex
API supply the remaining terms. The existing Leray comparison preserves this actual
augmentation; the exact faithful functor forgetting the section-module structure reflects
quasi-isomorphisms and recovers the displayed module-valued map.

Server validation: `lcompile.py` compiled the final file cleanly with no warnings
(21.8 seconds of compiler time). Static comparison confirms the public theorem signature
is unchanged and all Lean lines meet the 100-column limit.

Updated the existing node's proof, proof dependencies and proof origin to follow this
argument. Sources read: `cohomology.tex`, `lemma-godement-resolution` (0FKS),
`lemma-flasque-acyclic` (09SY); `coherent.tex`,
`lemma-quasi-coherent-affine-cohomology-zero` (01XB); `derived.tex`,
`lemma-leray-acyclicity` (015E). The Mathlib/source signatures were read before use.
Mathlib searches used the prescribed msearch LeanFinder, Loogle and grep services;
LeanFinder returned affine-open and injective-resolution results, Loogle did not know the
source `Functor.rightAcyclic` declaration, and grep found the Mathlib flasque API.
Local source searches found the complete existing Leray and flasque-module criteria.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ringComplexGodement_affineSections`
(node `lem-weil-pbc-ring-complex-godement-affine-sections`).

Added holes: 0. Split-off theorems: 0. Sorries left in the delivered module: 0.
Both private helpers are fully proved. No other Lean module is changed.

## No longer needed

No existing public import is removed, and no module is withdrawn.

The updated proof does not need these original direct proof dependencies:

- `lem-weil-pbc-principal-localization-open-immersion`: affineness follows from Mathlib
  basic-open affineness, finite intersection, and the complement's open inclusion;
  an explicit presentation as a localization spectrum is unnecessary.
- `lem-weil-pbc-spec-module-tilde-sections`: no section/localization coordinates are needed
  for the quasi-isomorphism comparison.
- `lem-weil-pbc-spec-tilde-free-module`: the source already proves
  `SheafOfModules.isQuasicoherent_unit` directly.
- `lem-sc-module-cup-flasque-acyclicity` / `Sheaf.Paper.ModuleCupFlasqueAcyclicity`:
  the existing source `Scheme.Modules.rightAcyclic_of_isFlasque` applies directly to
  open sections; no comparison with global module cohomology is required.
- `src-right-derived-functor-plus-acyclic-unit` /
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology`:
  the fully proved `Functor.quasiIso_map_of_rightAcyclic` is the needed form directly.

The latter two modules were never imported by the item and are not newly imported.
The two replacement dependency nodes are existing: the Mathlib leaf
`lem-sc-zariski-flasque-quotient-sections` and the source-proved
`lem-weil-pbc-leray-acyclicity-quasi-iso`. The proper-base-change unit's realized
statement and steps are preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically valid but required more transport than necessary.
The source library already supplies the bounded-below acyclic-complex comparison and a
flasque-module criterion for arbitrary left exact additive functors. Applying them to
open sections avoids restriction-to-open resolutions and total derived categories.
No statement or definition repair was required, and no obligation was split off again.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
