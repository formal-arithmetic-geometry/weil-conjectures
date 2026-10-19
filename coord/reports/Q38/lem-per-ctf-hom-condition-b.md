## Worker report

The delivery states `AlgebraicGeometry.Etale.ctf_hom_condition_b`, with its sole proof
`sorry`, and uses Q59's landed Galois-partition classes from
`Sheaf.Paper.GaloisPartitionModules` (`def-per-galois-partition-modules`).
No statement correction and no disputed statement are required. The original item's
statement and proof are unchanged; its statement dependencies gain the existing
landed definition node. No new node or dependency module is delivered.

The correspondence with every hypothesis and conclusion is as follows.

- The prime and prime field are `(ℓ : ℕ) [Fact ℓ.Prime]` and `ZMod ℓ`.
  `ULift.{u + 1} (ZMod ℓ)` is used for the prime-field sheaf values, as required by
  the existing small-etale coefficient convention. This is the same ring via
  `ULift.ringEquiv`, without an additional hypothesis. The algebra assumption on A
  is the ordinary `[Algebra (ZMod ℓ) A]`.
- The Noetherian scheme is `(X : Scheme.{u}) [IsNoetherian X]`. This is the usual
  quasi-compact locally Noetherian scheme, equivalently the stated finite Noetherian
  affine cover. The coefficient algebra is `(A : Type (u + 1)) [CommRing A]
  [IsNoetherianRing A]`. The zero algebra is included.
- All complexes inhabit `Etale.DerivedCategoryModule R X`, definitionally the ordinary
  derived category of `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)`. There is
  no adic, condensed, pro-etale or bounded localization in place of this category.
- Q belongs to bounded constructible complexes by `_hQ`, using the dependency's
  recorded `DerivedCategory.isBoundedConstructible`. `_hdual` says exactly that
  internal Hom into Q preserves that class and the canonical biduality map is an
  isomorphism for every object of it. `HasConditionBDuality` is a real Prop-valued
  definition: it writes the existing tensor-Hom adjunction transpose of signed
  evaluation. It contains no chosen morphism, opaque data, or postponed proof.
- The first argument P and `_hP : DerivedCategory.boundedConstructibleFiniteTor A X P`
  give bounded constructibility and finite Tor amplitude. The source definition in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` is the intersection of
  `boundedConstructible (ModuleCat A)` and `finiteTorAmplitude (ModuleCat A)`.
  Tor amplitude tests derived tensor against every module sheaf in degree zero.
  Thus no perfectness, finite coefficient ring, or stronger local model is assumed.
- `boundedConstructible (ModuleCat A)` uses finite locally closed scheme strata,
  local constancy and finitely generated geometric stalks. The additional
  constructibility condition on upstream strata is automatic for Noetherian X,
  as documented and implemented by `IsConstructibleSheaf.of_noetherianSpace`.
  Each bounded complex has a common finite stratification by common refinement of
  the finitely many individual cohomology stratifications. No finiteness of the
  underlying set of an A-module is imposed.
- `Scheme.GaloisPartition X` consists of the dependency's finite locally closed
  stratification with connected and reduced strata, finite etale covers, and
  `PreGaloisCategory.IsGalois` on each cover. `FiniteEtale.isGalois_iff` identifies
  this with the simply transitive automorphism action on geometric fibres; the
  Galois predicate includes connectedness of the cover. Scheme connectedness and
  categorical connectedness agree, as in FundamentalGroup.Connected.
- `GaloisPartition.FiniteExtensions` gives a finite chain starting at zero,
  with short exact sequences whose successive quotients are locally constant and
  constant on the cover. The chain has arbitrary finite length, including zero,
  and no finite-generation requirement. `GaloisPartition.modules` uses a filtered
  diagram, a colimit cocone, and an isomorphism from its vertex to the restricted sheaf.
  `IsFiltered` includes nonemptiness. The index universe u+1 is the universe of
  module values and of small diagrams on this site. `boundedDerived` requires
  this property in every cohomological degree and an integer interval outside which
  all cohomology sheaves vanish.
- The outer `∃ r : ℤ, DerivedCategory.IsLE P r ∧ ...` chooses r independently of
  the input partition. Each `∀ partition, ∃ partition' c, ...` then chooses the
  output partition and upper bound independently of N, u and v.
- `∀ (u v : ℤ), u ≤ v → ∀ N, partition.boundedDerived A N →
  homologyConcentratedIn u v N → ...` quantifies over exactly the stated bounded
  partition class and degree interval. The first conjunct puts internal Hom in
  the output partition's bounded derived class. The second gives the exact interval
  `[u-r,v+c]`; the third is the additional constructible-input/constructible-output
  assertion. The same output partition and c work for all of these clauses.
- Every internal Hom is the existing `Etale.derivedHom (ModuleCat A) X`, listed in
  the recorded internal-Hom dependency. No finite-generation condition is imposed
  on N except in the final implication explicitly asking for constructibility.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`;
  `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, `DerivedCategory.boundedConstructibleFiniteTor`;
  `WeilConjectures.CategoryTheory.DerivedCategory.Constructible`:
  `Etale.DerivedCategory.boundedConstructible`, with the local-constant/stalk
  definitions in `WeilConjectures.ConstructibleSheaf.Defs`.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`, the exact finite-field predicate
  of the dependency. Its current source was read with `scompile.py --source`:
  the older local upstream checkout lacks that module. The preferred upstream
  import avoids bringing in the retired duplicate library declaration.
- `Sheaf.Paper.GaloisPartitionModules`: `Scheme.GaloisPartition`,
  `Scheme.GaloisPartition.FiniteExtensions`, `Scheme.GaloisPartition.modules`,
  `Scheme.GaloisPartition.boundedDerived`. These are the recorded declarations of
  `def-per-galois-partition-modules`, read in full including their docstrings.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`, with no constructibility restriction.
- `Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules`:
  `SheafOfModules.IsLocallyConstantFiniteTypeModules`, read and retained as a
  statement-dependency import. The module-valued-etale formulation already available
  upstream gives its locally constant/finitely generated stalk specialization.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses` publicly exposes the
  recorded `Etale.derivedHom` and `Etale.derivedTensorHomAdjunction` from
  `WeilConjectures.SixFunctors.Etale.Derived.Hom`.
  `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry` gives
  `Etale.derivedTensorSymmetry`, the canonical descended signed swap.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic`:
  `Scheme.FiniteEtale`, its GaloisCategory instance, and `FiniteEtale.isGalois_iff`;
  `Mathlib.CategoryTheory.Galois.GaloisObjects`: `PreGaloisCategory.IsGalois`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`;
  `Mathlib.Algebra.Homology.ShortComplex.ShortExact`: `ShortComplex.ShortExact`;
  `Mathlib.CategoryTheory.Filtered.Basic`: `IsFiltered`;
  `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit`, `colimit`.

Proof-only imports retain the stated plan: `Sheaf.Paper.CtfHomLocallyConstant`
(the Step 4 sibling, now using precisely the same partition type),
`Sheaf.Paper.SfHomTriangulated`,
`Sheaf.Paper.CohomologyInWeakSerreSubcategory`,
`Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono`,
`Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`, and Mathlib's
`CochainComplex.isKInjective_of_injective`. HomologySequence and the standard
TStructure are exposed by these imports. The remaining condition-(B) devissage,
flat-model, exact-refinement and inheritance children had no Lean record in the
original packet. Current main has since recorded NoetherianCtfFlatModel and
DualizingLocallyClosedInheritance; their normal proof-import propagation remains
with the maintainer. This repair retains the previously reviewed proof plan.
The theorem's docstring retains all six proof steps and their node names.

Edge cases checked: the empty scheme admits the empty partition (`n=0`), so all
stratum requirements are vacuous; no stratum is required to exist. Connectedness is
imposed on each actual stratum, not on X. P=0 admits r=0 and the zero Hom satisfies
all bounds. N=0, A=0, coincident endpoints u=v, and output intervals with reversed
endpoints are allowed (the last forces the object zero). Negative r, c, u and v are
not excluded. N may have infinite, non-finitely generated stalks. The signed
transpose is oriented M -> Hom(Hom(M,Q),Q): the adjunction for Hom(M,Q) transposes
Hom(M,Q) tensor M -> M tensor Hom(M,Q) -> Q.

Searches: `msearch.py` LeanFinder for uniform derived Hom bounds and Galois
partitions returned generic derived-category/Galois-category infrastructure, no
match. Loogle queries for DerivedCategory/IsLE/IsGE and RHom returned no exact
match; the qualified IsFiltered/IsColimit search returned generic colimit examples.
LeanSearch for finite Galois partitions and filtered finite-extension classes
returned module and sheaf filtered-colimit declarations only. Mathlib grep for
`GaloisPartition|HasConditionBDuality|ctf_hom_condition_b` returned zero.
`rg` with the same names in the upstream WeilConjectures tree and project
lean/Sheaf found only the downstream proof-plan reference to this item.
The original DAG concept searches found statement nodes defining partitions inline,
but no independent definition node. The repair reads Q59's now-landed definition node
and source, replacing that obsolete search conclusion. `tools/blueprint_refs.py search 'Galois partition'`
returned zero blueprint nodes. Exact tool outputs and dates are recorded in the
original search log `searches.jsonl`. The superseded new node is removed.

Validation of the repair: the initial retained packet passed `deliver2.py --no-push`
as commit `cfbc92a338`, but it still had the reviewed duplication. After removing it,
both the prescribed `scompile.py` and `deliver2.py --no-push` stopped with exit 75:
`INFRASTRUCTURE RETRY (stale live olean): the published live build predates (or lacks)
the live module Sheaf.Paper.GaloisPartitionModules`.
The compiler reports that its live `.olean` does not exist. The prescribed
`scompile.py --source Sheaf.Paper.GaloisPartitionModules` succeeds and confirms the
source matches the definition used here. This is an infrastructure publication
failure before statement elaboration; no corrected packet has been pushed.
A further prescribed-wrapper diagnostic supplied the read-only partition source
as an additional compile input without adding it to the delivery. That definition
compiled cleanly (~3.0--3.4 s), then the theorem import failed with the same
infrastructure classification for the missing published
`Sheaf.Paper.CtfHomLocallyConstant.olean`. Thus at least both newly landed shared
modules need their live artifacts published. Full diagnostic: `repair-compile.log`.
All variables and universes are explicit with autoImplicit and relaxedAutoImplicit
both false. Every definition has real data; only the target theorem has `sorry`.

## Return repair

The return on immutable head `bb7823097173` identified H12/H4 and H9: the packet's
new `def-per-galois-partition` duplicated Q59's landed
`def-per-galois-partition-modules`, including the full name `Scheme.GaloisPartition`.
The duplicate node and `Sheaf.AlgebraicGeometry.GaloisPartition` module are removed
from this delivery. The item's `stmt_deps` now cites the landed node, and its module
imports `Sheaf.Paper.GaloisPartitionModules`. The Step 4 sibling
`Sheaf.Paper.CtfHomLocallyConstant` is also imported as a proof dependency, so compilation
will check their simultaneous use of the one shared partition type once the live
artifact is published.
The theorem's signature and the canonical biduality helper are unchanged; the
`lean.statement` is re-extracted verbatim and `lean.declarations` lists only those
two declarations owned by this module. Comparison with current main found only
`lean` and `stmt_deps` changed; all statement/proof/source fields are retained.

## Second reading by Q38

This is the dispatcher's worker self-check, not an independent review. The node,
repaired theorem module and Q59's definition module were reread clause by clause as recorded above; independent review
belongs to the maintainer under this brief. The draft's lifted-prime-field algebra
binder was changed to `[Algebra (ZMod ℓ) A]`, agreeing with the ordinary coefficient
algebra and downstream consumer. The finite-field duality helper uses the exact
canonical transpose formula and is listed in lean.declarations. No extra
hypothesis, finite-generation restriction on N, or stronger geometric assumption
was found. No definition's data and no helper proof is postponed.

Repair self-check: the landed partition still supplies connected reduced strata,
finite etale Galois covers, filtered colimits of finite successive extensions, and
bounded cohomology. Its explicit finite-filtration and colimit-isomorphism formulation
has the same meaning as the removed extension-closure formulation. The theorem still
chooses r before the partition and partition′,c before u,v,N; its three conclusions
are partition membership, the interval [u-r,v+c], and constructibility for constructible
N. The zero-length filtration, empty partition, zero objects and unrestricted stalks
remain allowed. This is the worker's self-check (H11), not an independent review.

## Retained-packet retry

The next dispatched repair retained this packet and first ran the required
`deliver2.py Q38 lem-per-ctf-hom-condition-b --no-push`. It again stopped before
elaboration: the published live artifact
`Sheaf/Paper/GaloisPartitionModules.olean` does not exist. The direct prescribed
`scompile.py` invocation independently returned exit 75 with the same
`INFRASTRUCTURE RETRY (stale live olean)` diagnostic. No delivery was pushed.

The current-main comparison confirms that only `lean` and `stmt_deps` differ:
the only added dependency is `def-per-galois-partition-modules`, and no original
dependency was removed. The duplicate node and module are absent from the packet.
The recorded theorem signature is byte-for-byte the signature in the Lean file;
`lean.declarations` lists exactly the duality helper and target theorem.
I reread Q59's current `GaloisPartitionModules` and `CtfHomLocallyConstant` sources
alongside the retained theorem. Both consumers use the same partition type and
`boundedDerived`; the quantifier order and all three conclusion clauses still
match the item. There is no item repair note in `coord/repair-notes` on this base.
This is an explicit worker self-check, with independent review left to the
maintainer. The remaining failure requires publication of the live artifacts;
changing the statement or restoring a duplicate definition would not repair it.

## Retained-packet retry 3 (2026-10-18 UTC)

As dispatched, this retry first inspected this report and ran
`deliver2.py Q38 lem-per-ctf-hom-condition-b --no-push` on the saved packet.
It failed before elaboration with `INFRASTRUCTURE RETRY (stale live olean)`:
the published `Sheaf/Paper/GaloisPartitionModules.olean` does not exist.
The separate prescribed `scompile.py Q38 lem-per-ctf-hom-condition-b
lean/Sheaf/Paper/CtfHomConditionB.lean` returned exit 75 with the identical
missing-artifact diagnostic. `scompile.py --source
Sheaf.Paper.GaloisPartitionModules` succeeded; the current server source agrees
with the Q59 source reread during this retry.

The retained repair is preserved. Comparing its node with current main shows
only `lean` and `stmt_deps` differ; the sole added dependency is
`def-per-galois-partition-modules`, and none is removed. The duplicate node and
module are absent. The theorem signature matches `lean.statement` verbatim,
`lean.declarations` names exactly the duality helper and target theorem, and all
Lean lines satisfy the 100-character limit. The shared partition and sibling
locally-constant source were reread. The retained worker self-check still applies:
r precedes the partition; partition' and c precede u, v and N; the three output
clauses are bounded partition membership, the exact interval [u-r,v+c], and
constructibility for constructible N. No further source change is indicated by
the concrete diagnostic. No packet was pushed; the prescribed tools require the
published dependency artifact before they can validate or deliver this repair.

## Retained-packet retry 4 (2026-10-18 UTC)

As instructed, this retry inspected the saved report and first ran the prescribed
`deliver2.py Q38 lem-per-ctf-hom-condition-b --no-push` on the retained packet.
It again failed before elaboration because the published
`Sheaf/Paper/GaloisPartitionModules.olean` does not exist, classified as
`INFRASTRUCTURE RETRY (stale live olean)`. The separate prescribed
`scompile.py Q38 lem-per-ctf-hom-condition-b
lean/Sheaf/Paper/CtfHomConditionB.lean` returned exit 75 with the same diagnostic.
No delivery was pushed, and the repaired Lean and node are retained unchanged.

The current shared DAG comparison still finds only `lean` and `stmt_deps`
changed. The sole added dependency is `def-per-galois-partition-modules`; none
was removed. The duplicate definition node and module are absent, and
`lean.statement` exactly matches the theorem signature. `lean.declarations`
contains exactly the canonical duality helper and target theorem. There is no
maintenance repair note for this item on the current base.

Worker self-check: rereading the current shared partition and sibling
locally-constant modules confirms that both consumers use Q59's
`Scheme.GaloisPartition` and its `boundedDerived`. The retained theorem chooses
r before the partition, and the output partition and c before u, v and N.
Its conclusions still give partition membership, the exact interval [u-r,v+c],
and constructibility when N is constructible. Empty partitions, zero-length
filtrations, zero objects, and unrestricted coefficient stalks remain included.
This is a worker self-check, not an independent review. The concrete tool
diagnostic requires publication of the missing live artifact; it identifies no
further packet repair.
