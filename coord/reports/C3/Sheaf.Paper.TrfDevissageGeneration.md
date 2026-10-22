## What changed

Replaced the existential counterexample proof in
`lean/Sheaf/Paper/TrfDevissageGeneration.lean` without changing any existing public
signature, public import, definition, or the already proved generation equality.
The witness is the punctured line in characteristic five, with the actual level-one
Q_3 coefficient datum. The proof constructs that datum, verifies the coefficient
ring is nonzero of characteristic three, and proves finite type and separatedness
of the witness scheme.

The new quadratic Kummer module proves the nonsquare-coordinate argument and constructs
an algebraic-closure automorphism exchanging the roots. `TrfKummerMonodromy` constructs
the finite etale quadratic cover, its fixed geometric point, and its moved lift.
`NilpotentFiberHomology` proves that nilpotence of a natural endomorphism on an exact
fibre functor defines a thick cohomology property. The main proof contains every
step combining this obstruction with the constant-extension and lisse-flat generator
clauses, including homology of a single sheaf and the universal property of thick closure.

One independent geometric result remains: `finite_etale_point_monodromy` connects the
canonical germ-normalized point action to the finite-cover permutation stalk, verifies
local freeness of the cover sheaf, and computes the action on constant stratum extensions.
Its new module has a complete sourced proof in words and a matching node. Its hypotheses
include an actual finite etale cover and a two-cycle, which the Kummer module constructs;
it does not assert the counterexample or any thick-generation conclusion.

The monodromy endomorphism is a real construction from the existing uniquely normalized
stalk reparametrization, with subtraction of identity. No definition chooses a witness
from the new unproved existence theorem. The named proposition
`SeparatingPointMonodromy` records the three clauses with the same F, t and L; this keeps
kernel checking from repeatedly expanding the large canonical stalk term. All five files
compile cleanly through lcompile.py; the last complete run took about 1, 0, 0, 9 and
22 seconds respectively (cached helper files were reused). No wall-clock limit was changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_trf_constant_coefficients_not_generating` (one of one original
holes). Added one hole in
`AlgebraicGeometry.finite_etale_point_monodromy`, node
`lem-trf-finite-etale-point-monodromy`. This is a decomposition: one hole closed,
one hole added, net zero. The item file itself has zero textual sorries; its counterexample
still depends on the named geometric lemma, so this is not an axiom-free proof of the
whole counterexample yet.

New complete proofs:
`CategoryTheory.nilpotentFiberHomology_thick`,
`AlgebraicGeometry.quadratic_kummer_generic_action`, and
`AlgebraicGeometry.exists_trf_kummer_monodromy` (the last uses the named geometric lemma).
The coefficient-convention witness, Laurent finite-type proof, homology transport and
thick-closure contradiction are complete private/main proofs. The existing
`AlgebraicGeometry.trf_devissage_generation` proof is unchanged.

## No longer needed

The rank-two permutation sheaf suffices: on its anti-invariant vector, monodromy minus
identity is multiplication by -2=1 in characteristic three. Thus no sign-line construction,
fundamental-group representation equivalence, field-discrete-module equivalence or
Galois classification of etale field covers is needed. The nilpotent Serre-class argument
also avoids an ambient derived thick-equivalence transport and a full composition-factor
filtration. The flat-model unit and its lisse-flat stratum generators are retained.

Removed these direct proof imports from the item module:

- `WeilConjectures.ConstructibleSheaf.OpenClosed`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.ComparisonTorAmplitude`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`
- `Sheaf.Paper.ProEtaleLisseOrigin`
- `Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.CategoryTheory.Triangulated.AmbientThickClosureEquivalence`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor`
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`
- `Sheaf.Paper.GaloisLisseRepresentations`
- `Mathlib.CategoryTheory.Abelian.Basic`
- `Mathlib.CategoryTheory.ObjectProperty.Kernels`
- `Mathlib.RepresentationTheory.Rep.Basic`
- `Sheaf.Paper.LisseAdicFiberFunctors`
- `Sheaf.Paper.LisseModuleSheaves`
- `Sheaf.Paper.LisseTensorScalarExtension`
- `Sheaf.RepresentationTheory.LAdic`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.FieldDiscreteModules`
- `WeilConjectures.SixFunctors.Finite.Stalk`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`
- `WeilConjectures.FieldTheory.EtaleFieldGaloisClassification`

The updated proof and its new subnodes no longer cite these old proof dependencies:

- `lem-sf-proetale-constructible-origin`
- `lem-sf-comparison-tor-amplitude`
- `lem-sf-comparison-pullback-exact`
- `lem-sf-exact-functor-derived-triangulated`
- `lem-trf-exact-equivalence-inverse`
- `def-weil-closed-immersion`
- `lem-trf-ambient-thick-closure-equivalence`
- `def-sc-gm-ga`
- `thm-galois-fundamental`
- `cor-galois-lisse-representations`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-exc-field-discrete-modules`
- `lem-fin-closed-immersion`
- `lem-exc-etale-field-galois-classification`

These old dependencies moved to the geometric point-monodromy lemma and are **not**
claimed pruned from its mathematical argument:

- `prop-weil-pbc-comparison-direct-image`
- `lem-cbc-proetale-extension-zero-comparison`
- `lem-sf-proetale-locally-constant-origin`
- `lem-cbc-proetale-comparison-stalk`
- `lem-weil-pbc-standard-etale-monic-derivative`
- `lem-sf-derived-homology-long-exact`
- `lemma-weil-pbc-finite-stalk-formula`
- `lem-weil-pbc-extension-by-zero-stalks`
- `lem-weil-pbc-closed-immersion-finite`

Deleted the obsolete top-level tool approvals for `cor-galois-lisse-representations`,
`thm-galois-fundamental`, `lem-exc-field-discrete-modules`, and
`lem-exc-etale-field-galois-classification`. Retained the standard-etale derivative
criterion approval, now used by the explicit quadratic-cover proof. No source-library
module or declaration is withdrawn; the lists above concern this proof's dependencies,
and do not claim these modules are unused elsewhere in the target closure.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The generation equality was already proved and was preserved.
The old plan's sign representation and Galois-module filtration are unnecessary for the
counterexample: a single natural endomorphism and the finite cover's permutation module
give a smaller obstruction. The constant-stratum stalk calculation works at any geometric
point fixed by the field automorphism; genericity and integrality are only used to supply
the moved Kummer lift, not in that calculation. Empty fibres give zero stalks; a closed or
open immersion has at most one lift, so the fixed-lift calculation also covers nonreduced
strata and strata not meeting the point.

The geometric lemma uses the finite-etale local-splitting and pushforward-local-constancy
nodes as tools to verify finite free local models. They are not replacements for the
flat-model unit's route; that unit supplies the generator family. Their statements and
Lean attachments were read. Germ normalization, not bare existence of an isomorphism of
stalks, is necessary for the action calculation and is explicitly part of the lemma's proof.

## New nodes

`lem-trf-nilpotent-fiber-homology`: proved generic Serre-class and derived thick-property
argument, in `Sheaf.CategoryTheory.NilpotentFiberHomology`. Its statement allows arbitrary
abelian categories and imposes no unnecessary boundedness condition.

`lem-trf-quadratic-kummer-action`: proved nonsquare-coordinate, irreducibility and
root-exchanging automorphism argument, in `Sheaf.AlgebraicGeometry.QuadraticKummerAction`.

`lem-trf-finite-etale-point-monodromy`: the remaining geometric lemma, in
`Sheaf.AlgebraicGeometry.FiniteEtalePointMonodromy`. Its statement is a strict part of
Step 3: the cover and two-cycle are hypotheses, and it asserts a stalk action on sheaves,
not failure of thick generation. Constants are killed, whereas a two-cycle in the cover
provides a nonnilpotent action; finite local splitting supplies the flat lisse generator.

`lem-trf-kummer-monodromy`: proved explicit Laurent polynomial cover construction and
application of the point-monodromy lemma, in `Sheaf.Paper.TrfKummerMonodromy`.

All four nodes carry actual Mathlib search records from searches.jsonl, a blueprint
ancestor and exact Step 3 location, complete proof steps and Lean attachments. Whole
blueprint searches for nilpotent monodromy, quadratic Kummer and finite-etale point
monodromy found no duplicate. No existing statement or definition changed, so no consumer
adaptations or change record are required.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
