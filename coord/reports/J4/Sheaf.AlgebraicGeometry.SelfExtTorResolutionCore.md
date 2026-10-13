## What changed

Replaced the proof of `AlgebraicGeometry.exists_selfExt_tor_resolution_core` in
`Sheaf.AlgebraicGeometry.SelfExtTorResolutionCore` without changing its signature,
public imports, or existing docstring. The proof chooses P and its augmentation
from `CochainComplex.exists_isKFlatResolution`, and chooses J and its augmentation
from the existing functorial K-injective resolution theorem. It proves the
homology vanishing and degree-zero identification using Mathlib's single-complex
homology and the homology isomorphism induced by the quasi-isomorphism b. It then
constructs both requested isomorphisms by applying tensor pullback to the two
pushforward comparisons and composing with the closed-immersion counit.

Added the proof imports `Mathlib.Algebra.Homology.SingleHomology` and
`Mathlib.CategoryTheory.Adjunction.Additive`, and the two new statement modules
`Sheaf.AlgebraicGeometry.SelfExtPushforwardHomology` and
`Sheaf.AlgebraicGeometry.SelfTorPushforwardHomology`. The existing theorem gets a
scoped unused-variable linter suppression: its existential witnesses hJ, e0, eG
and eQ are intentionally not used by the final `True` in the unchanged signature.
No new definition, axiom, interface change, or forced consumer adaptation is made.

The new comparisons split the existing node's second step. They assert
isomorphisms on Y for arbitrary integer degree and arbitrary supplied resolutions;
they do not choose resolutions or assert their existence, flat terms, the
homology of J, or the final ordinary-pullback isomorphisms on Z. Their proofs in
words follow the existing internal-Hom adjunction and qcqs projection formula,
with exact closed pushforward and localization transport made explicit. These are
strict parts of the argument, rather than a renamed joint existence statement.

All three delivered modules compile together in dependency order, within the
single-file limit. The original unit record has no realized statement or step
node at this core, and the original internal-Hom and projection-formula route is
retained through the new comparisons.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_selfExt_tor_resolution_core`
(node `new-j3-self-ext-tor-core`). There is no textual sorry left in the item.

Added two holes, each as the entire proof of one public theorem in a separate
new module, with a source and a complete proof in words:

- `AlgebraicGeometry.nonempty_selfExt_pushforward_homology`
  (node `lem-pc-self-ext-pushforward-homology`).
- `AlgebraicGeometry.nonempty_selfTor_pushforward_homology`
  (node `lem-pc-self-tor-pushforward-homology`).

This is a decomposition, not an axiom-free proof of the entire core. The
resolution construction, homology of J, and counit compositions are complete
Lean proofs. The two representative comparisons are the remaining items.
The delivery closes one hole and adds two; no positive net-hole claim is made.

## No longer needed

Removed these direct proof imports from the core:

- `Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackAdjunction`
  (`lem-pc-derived-internal-hom-pullback-adjunction`), now a proof dependency of
  `SelfExtPushforwardHomology`.
- `Sheaf.AlgebraicGeometry.QCqsDerivedProjectionIsoUniverses`
  (`lem-pc-qcqs-derived-projection-iso-universes`), now a proof dependency of
  `SelfTorPushforwardHomology`.
- `Sheaf.Topology.ClosedImmersionPushforwardExact`
  (`lem-sc-closed-immersion-pushforward-exact`), now a proof dependency of both
  new comparisons.

These dependencies remain necessary transitively; no original DAG node or
module is globally pruned. The redundant direct public import
`Mathlib.Algebra.Homology.HomotopyCategory.KInjective` was removed from the new
`SelfExtPushforwardHomology` module: its signature already sees this API through
`DerivedInternalHom`. All original core public imports are retained. The core's
proof_deps now list the resolution theorems, closed-immersion counit theorem,
and the two new comparisons.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed statement was found. The original step 2 bundled
representative comparisons, exactness on scheme modules, and transport into an
arbitrary supplied localization. The available adjunction and projection-formula
statements do not directly supply these homology comparisons. Also,
`shortExact_map_pushforward_closedSubset` is formulated for abelian sheaves on a
literal closed subset, so using it for scheme modules needs the closed-image
homeomorphism and forgetful reflection of exactness; this glue is explicitly
recorded in both new proof plans.

LeanSearch was tried for each comparison and returned Internal Server Error;
that failure is recorded without claiming absence. LeanFinder, Loogle, and
repository/Mathlib grep provided no exact existing comparison. Existing
`derivedInternalHom_obj_iso` is the generic internal-Hom representative API and
is retained in the new self-Ext proof plan through its definition node.

Checked the new statements on identity immersions (ordinary internal-Hom
resolution computation and derived tensor unit law), empty schemes and zero
quotients, and all integer degrees. No flatness or regular-immersion assumption
is needed. The augmented resolutions are supplied arguments, so the comparison
statements introduce no arbitrary object chosen from a holed existence theorem.

## New nodes

`lem-pc-self-ext-pushforward-homology`, in
`dag/nodes/sec-picard-framework/lem-pc-self-ext-pushforward-homology.json`, states
G isomorphic to pushforward of Hom(T,J) homology for fixed resolutions. Its new
module is `lean/Sheaf/AlgebraicGeometry/SelfExtPushforwardHomology.lean`.
Sources: Stacks 08DH, 08DJ, 08I3, and 08KS. The proof plan identifies the
representatives, uses the internal-Hom adjunction, takes homology through exact
pushforward, and transports to the supplied localization.

`lem-pc-self-tor-pushforward-homology`, in
`dag/nodes/sec-picard-framework/lem-pc-self-tor-pushforward-homology.json`, states
the tensor-square homology isomorphic to pushforward of H(T) for a fixed K-flat
resolution. Its new module is
`lean/Sheaf/AlgebraicGeometry/SelfTorPushforwardHomology.lean`.
Sources: Stacks 08EU, 068G, and 08KS. The proof plan verifies qcqs and
quasi-coherence, applies the projection formula and derived unit law, uses the
K-flat pullback representative, takes homology through exact pushforward, and
transports to the supplied localization.

Both nodes carry the three requested search kinds and the unchanged core's
chapter and unit. No change record is required because no existing interface
changes.


## Second reading by J4

1. Compared the core module against the repository with `diff -u`. The complete
   existing theorem signature and docstring are byte-for-byte unchanged. Changes
   are its proof, proof imports, and scoped unused-variable lint suppression.
   No definition, target, or existing public import was changed. No change record
   or forced adaptation is needed.
2. Compiled all three modules locally in dependency order. All passed without
   warnings or errors. A scratch copy printed axioms of all three declarations:
   each uses only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   Exactly the two reported new public theorems have whole-proof `sorry`; the core
   has none. There is no forbidden declaration or hollow definition. Resolution
   witnesses are eliminated inside an existential theorem proof, not exported as
   arbitrary data definitions from unproved existence.
3. Read both new comparisons and their full proof docstrings. They are separate
   parts of step 2, strictly smaller than the joint existence theorem. Checked
   identity and empty immersions, degree zero, negative degrees, and the affine
   quotient model A -> A/I: the tensor comparison is Tor_A(A/I,A/I), while the
   Hom comparison is the corresponding derived Hom by restriction of scalars.
   No regularity or flatness hypothesis is missing. Checked Stacks Tags
   [08I3](https://stacks.math.columbia.edu/tag/08I3),
   [08EU](https://stacks.math.columbia.edu/tag/08EU), and
   [08KS](https://stacks.math.columbia.edu/tag/08KS) against the argument.
   Repeated LeanFinder, Loogle, and grep searches with exact-direct-image,
   cohomology, and homology-map terminology. Loogle's first query had an unknown
   identifier, so repeated it successfully with `"homology", "map"`.
   Generic `ShortComplex.mapHomologyIso` handles the exact-functor substep but
   neither search nor repository inspection supplied either full comparison.
   Read the existing `derivedInternalHom_obj_iso` API; the scheme representative
   and pushforward glue remains. Neither remaining theorem can be closed by a
   short application of the available APIs.
4. Read downward from the original theorem and checked each construction and
   counit composition. The old proof dependencies removed from the core are all
   listed under No longer needed; they remain transitively used by the new plans.
   No globally pruned module is claimed. Read the unit's realized record: its
   statement and step arrays are empty, so no realized route is bypassed. The
   internal-Hom adjunction and qcqs projection formula remain in the proof plans.
   Removed the redundant KInjective import from the new self-Ext module and
   recompiled it successfully. The explicit DerivedCategory import is necessary
   for the public signature and was retained.
5. Compared core node JSON with the repository: only `proof`, `proof_deps`, and
   `proof_origin` differ, and they describe the Lean proof accurately. Both new
   nodes have the required source, search, creation, blueprint, chapter/unit,
   statement, and Lean records. Their proof dependencies are the unions of their
   plan steps. No existing statement or statement-dependency record changed.

Second reading removed the redundant direct public KInjective import in the
new self-Ext module, corrected the new self-Tor docstring source for Tag 08EU
from cohomology.tex to Derived Categories of Schemes, and completed this report. Verdict: valid decomposition, one original
hole closed and two named lower holes added; no net proof-progress claim.
