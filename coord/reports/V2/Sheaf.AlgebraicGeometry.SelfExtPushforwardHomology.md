## What changed

Proved `AlgebraicGeometry.nonempty_selfExt_pushforward_homology` with its signature and
existing docstring unchanged. Its proof inverts the two augmentations, applies the fixed
K-flat/K-injective model, takes homology, and composes the localization and ordinary
pushforward homology comparisons.

Added two fully proved modules:
- `Sheaf.AlgebraicGeometry.ClosedModulePushforwardHomology`: ordinary module pushforward
  preserves homology, proved through local lifting of abelian-sheaf epimorphisms and the
  faithful exact forgetful functor. The local lift uses an ambient open whose inverse
  image is the prescribed source open; outside the closed image it uses the empty-cover
  sheaf axiom. This avoids the closed-subset/stalk transport of the former proof plan.
- `Sheaf.AlgebraicGeometry.DerivedHomPushforwardKFlatModel`: a general fixed-representative
  derived Hom comparison, with no closed-immersion assumption. First compute using the
  existing derived adjunction, K-flat pullback, K-injective Hom, and direct-image
  representative theorems. Then transport from standard localizations by computing both
  internal Homs with the identical functorial K-injective replacement and composing the
  explicit localization comparison isomorphisms.

All imports of these two modules in the item are proof-only. Updated the item's DAG
proof and recorded the two proved helper nodes. No existing definition or statement
changed, and no consumer adaptations or change records are required.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.nonempty_selfExt_pushforward_homology`
(node `lem-pc-self-ext-pushforward-homology`).

Also proved `AlgebraicGeometry.closed_modulePushforward_preservesHomology`
(node `lem-pc-closed-module-pushforward-homology`) and
`AlgebraicGeometry.nonempty_derivedHom_pushforward_kFlat_model`
(node `lem-pc-derived-hom-pushforward-kflat-model`). All private helpers are proved.

Holes closed: 1. Holes added: 0. No `sorry` remains in any delivered file.
These proofs use existing stated library dependencies, whose own unresolved holes are
not part of this delivery. This is a proof from those dependencies, not a decomposition
into new holes. All three files compile individually through lcompile.py, within the
60-second per-file limit, with no warnings. Identity maps, empty sources, zero complexes,
and arbitrary integer degrees are included by the functorial comparisons and local
lifting proof; no restriction on the supplied derived universe was introduced.

## No longer needed

Removed the item's direct import of `Sheaf.Topology.ClosedImmersionPushforwardExact`.
This argument no longer needs that module or node
`lem-sc-closed-immersion-pushforward-exact`, nor its subordinate modules
`Sheaf.Topology.ClosedPushforwardAbelianStalks`
(node `lem-sc-closed-pushforward-abelian-stalks`) and
`Sheaf.Topology.AbelianSheafShortExactStalkwise`
(node `lem-sc-abelian-sheaf-short-exact-stalkwise`). The ordinary module argument uses
Mathlib's local-surjectivity criterion instead. This is pruning of this proof route;
other targets may independently use these nodes.

Removed the item's direct import of
`Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackAdjunction`, but that module and node
remain necessary through `DerivedHomPushforwardKFlatModel`; they are not pruned.
The original derived-pullback and derived-internal-Hom steps remain necessary in that
model. No original public import was removed or changed.

## Where the brief, the DAG or earlier work was wrong

The planned mathematical route is valid, and the unit's realized steps are unchanged.
The needed representative comparisons were not exposed as one ready-made public API,
but the specification of `exists_derivedPullback` gives its K-flat counit. Combining
that specification with the existing representative and adjunction theorems completes
the plan without new holes.

The supplied localization on Y must be retained explicitly during universe transport:
installing the standard localization can otherwise cause typeclass inference to select
it for an unannotated comparison. The proof explicitly passes the original `hY` to Q
and to `derivedInternalHom_comparison`, and passes the standard instances only to the
standard computation.

The existing algebra-direct-image homology theorem concerns modules over the
direct-image algebra, a different target category from ordinary O_Y-modules here.
The new ordinary-pushforward theorem therefore has a distinct interface. Both follow
the same closed-embedding local-lifting argument. Searches found no existing declaration
with the new general fixed-representative comparison. LeanSearch returned HTTP 500;
this is recorded as unavailable, not an absence result.

## New nodes

`lem-pc-closed-module-pushforward-homology` records ordinary O_Y-module pushforward
homology preservation, with its complete Lean proof in
`lean/Sheaf/AlgebraicGeometry/ClosedModulePushforwardHomology.lean`.

`lem-pc-derived-hom-pushforward-kflat-model` records the general derived comparison
before the augmentations and degree-k homology are applied. It is fully proved in
`lean/Sheaf/AlgebraicGeometry/DerivedHomPushforwardKFlatModel.lean`, including transport
to the arbitrary supplied localization. Neither node leaves a hole or restates the
item's self-Ext homology conclusion.

## Second reading by V2

1. PASS: Read the complete repository/sandbox diff of the existing module. Its sole
   existing declaration has byte-identical signature, hypotheses, conclusion and
   docstring; only its proof and two proof-only imports changed. The two other
   modules are new. No definition, target statement or public interface of an
   existing module changed; no change record or consumer adaptation is needed.
2. PASS: Compiled all three modules in import order through lcompile.py, without
   errors or warnings (5.7, 24.4 and 12.7 seconds). Scanned all delivered source:
   no sorry, axiom, unsafe, opaque, implemented_by or extern, and no new definition
   or arbitrary witness construction. Scratch-copy #print axioms gives only
   propext, Classical.choice and Quot.sound for closed_modulePushforward_preservesHomology;
   the derived model and the item additionally use sorryAx through existing library
   dependencies. They close their own holes but are not yet axiom-free target proofs.
   The delivery probe checks all declarations, including the private helpers.
3. PASS: No statement is split off with sorry. Both new theorems are proved and
   strictly intermediate: exactness of ordinary direct image, and the fixed
   representative comparison before augmentations or homology. Checked identity
   maps, empty sources, zero complexes and arbitrary integer degrees directly in
   the local-lifting and isomorphism arguments. Checked that the supplied hY is
   explicitly retained in QY and derivedInternalHom_comparison during localization
   transport. Independent msearch queries about exact closed direct image and
   derived representative computation found no matching ready-made theorem;
   qualified Loogle found the Mathlib epis-and-kernels homology criterion already
   used here. An initial unqualified Loogle query failed to resolve its name and
   supplies no absence evidence. Also searched repository declarations using
   preservesCokernel, computed_by_resolution and isLocallySurjective_iff_epi.
4. PASS: Read from the target downward through both new modules and their cited
   representative/adjunction APIs. The existing
   Scheme.Modules.closedImmersion_pushforward_preservesCokernel provides another
   exactness route, but not this homology declaration; its stalk-based dependency
   route would retain work avoided by the elementary local-lifting proof here.
   Retained the correct proof. Removed redundant direct imports
   Mathlib.Algebra.Homology.ShortComplex.PreservesHomology and
   Mathlib.CategoryTheory.Abelian.Exact from the new closed-module helper: the
   former is publicly available through Modules.Sheaf and the latter through
   Topology.Sheaves.Abelian. Preserved all existing public imports. All old proof
   dependencies are accounted for: def-pc-derived-pullback,
   def-pur-derived-internal-hom and lem-pc-derived-internal-hom-pullback-adjunction
   remain through the new derived-model node; only the closed-subset exactness
   route is pruned. Read dag/units/sk-thm-picard-duality.json: its realized record
   is unchanged, and no unit statement or step is bypassed.
5. PASS: Compared the existing node with the repository: only proof, proof_deps
   and proof_origin differ. Read both new nodes against their Lean signatures and
   proofs, including their source, stmt_deps, searches, creation, blueprint and
   lean records. Each proof_deps is the union of its steps' uses. The site-local
   surjectivity dependency is the Mathlib leaf for the exact theorem used by the
   private helper; module forgetful colimit preservation comes from the existing
   source-library instance, and the right-adjoint kernel instance from Mathlib.

Second reading changed only the two redundant imports and this report. No proof
repair or additional hole was necessary. The report's proof count is one original
hole closed out of one, zero new holes; both additional helper theorems are proved.
The removed redundant Mathlib imports prune no additional project nodes.

The local Stacks .tex files are absent on this machine. Independently read the
primary online sources [08KS](https://stacks.math.columbia.edu/tag/08KS),
[0A96](https://stacks.math.columbia.edu/tag/0A96) and
[08I3](https://stacks.math.columbia.edu/tag/08I3): they supply, respectively, closed
module direct-image exactness, K-injectivity of Hom from K-flat into K-injective,
and the derived pullback/internal-Hom comparison used by the cited library API.
