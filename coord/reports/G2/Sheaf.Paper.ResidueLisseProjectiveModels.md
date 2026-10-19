## What changed

The signature of `WeilConjectures.residue_lisse_projective_models` is unchanged.
Its combining proof obtains a finite disjoint partition, applies the local finite
free model result on each piece, and uses the term isomorphism and its inverse
as the required inclusion and retraction.

The retained local-model reduction is now proved by induction on the natural
length of the residue Tor interval. It constructs a zero-differential residue
model with proved termwise interval bounds, removes one top cell, proves the
smaller cone has the recorded Tor interval from its bounded free residue model,
and represents extensions by actual chain mapping cones,
and normalizes the final bounds. The zero-length, zero-object, empty-product,
and rank-zero cases are included. Arbitrary sheaf-linear differentials are allowed.

New proved ingredients are projectivity of finite powers of the regular module
on a weakly contractible scheme, zero-differential models for arbitrary complexes
with projective homology, closure of bounded projective models under extensions,
and a finite clopen refinement of a pro-etale covering. The last two open results
are genuine separate arguments from Stacks 09C3/098F: geometric clopen preparation,
and lifting/removing one top residue cell. The latter asserts only a triangle
with a single-degree free first object and a complete cone with a shorter
zero-differential residue model. The cohomology and universal Tor-interval
calculations from that model are proved in the parent, not split off.

No existing definition or statement was changed; no consumer adaptation is needed.
All eight sandbox modules compile together through lcompile.py with no warnings.
The original public imports and theorem signature match the shared source.
The updated dependency graph has no missing node or cycle in its 1,286-node
reachable closure; all proof-dependency lists match their proof-step uses.
The delivery dry run passed with review class CODEX. Its declaration and DAG
checks passed. It noted that the axiom probe of
`CompleteConstantResidueFreeModel` exceeded 60 seconds; normal compilation of
that module took 31.6 seconds in the final standalone set run. The delivery and
merge repeat that probe. No axiom-probe success is claimed for the timed-out run.

## Proved and sorry left

Original hole closed:

- `WeilConjectures.residue_lisse_projective_models`: 1 of 1 original holes,
  by a complete combining proof.

New public declarations with no holes:

- `WeilConjectures.complete_constant_residue_free_model`
- `WeilConjectures.finitePower_unit_projective_of_weaklyContractible`
- `CochainComplex.exists_zero_differential_model_of_projective_homology`
- `DerivedCategory.bounded_projective_models_extensions`
- `AlgebraicGeometry.Scheme.weakly_contractible_clopen_refinement`

Every remaining added hole (exactly two):

- `WeilConjectures.residue_clopen_preparation`, node
  `lem-sf-residue-clopen-preparation`.
- `WeilConjectures.complete_residue_top_cell`, node
  `lem-sf-complete-residue-top-cell`.

The prior proposed hole in `complete_constant_residue_free_model` is eliminated.
Against the original item baseline this is a decomposition: 1 original hole
closed and 2 new holes, net -1. This is not a claim of a net reduction in holes.
The proved helper declarations themselves contain no sorry.

## No longer needed

The original module's combining proof now imports only
`Sheaf.Paper.ResidueClopenPreparation` and
`Sheaf.Paper.CompleteConstantResidueFreeModel` for its proof.
Removed direct proof imports:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.Paper.ConstantModuleSectionProperties`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit`
- `Sheaf.AlgebraicGeometry.WeaklyEtaleStability`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.AlgebraicGeometry.EtaleComparison`
- `Sheaf.AlgebraicGeometry.IntegralConstantCompletion`
- `Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties`
- `Sheaf.Paper.CompleteResidueCohomologyBounds`
- `Sheaf.Paper.DerivedNakayamaFirstReduction`
- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`

The coefficient, completion, cohomological-bound and derived-Nakayama arguments
remain in the top-cell node, and the localization/trivialization arguments remain
in the clopen-preparation node. Their imports live in the corresponding new
modules. No transitive mathematical dependency or globally unused module is
claimed pruned. In particular no blueprint unit statement or realized step is
bypassed. The regular-module and zero-differential helpers are used by the actual
local-model proof; the covering-refinement helper is a proved input to the
remaining geometric proof plan.

The original node no longer directly uses these approved tool entries,
so its obsolete `tool_uses` list is cleared (their needed uses are recorded
on the appropriate new nodes):

- `det-prop-integral-criterion-constant-coefficients`
- `lem-weil-l-adic-extension-integers-dvr`
- `lem-weil-pbc-completed-constant-sheaf-reduction`
- `lem-weil-pbc-constant-module-section-properties`
- `lem-pc-bounded-above-flat-kflat-site`
- `lem-weil-proetale-surjective-tower-derived-limit`
- `det-pe-derived-nakayama-first-reduction`
- `det-pe-topos-functoriality-site`
- `sk-lem-pe-weakly-etale-stability`
- `det-pe-morphisms-etale-comparison`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-pc-kflat-resolution`
- `lem-pur-derived-change-of-rings`

The wrappers `sk-lem-pe-weakly-etale-stability` and
`det-pe-morphisms-etale-comparison` are not needed by the refinement proof:
Mathlib's morphism-property stability instances supply the required statements.
Their modules are among the removed direct imports above. This does not assert
that other parents of those wrappers are pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox contained two proposed split statements without DAG records.
This packet supplies complete records and an updated route for the original node.
It also replaces the former open local-model construction by a genuine induction
and mapping-cone proof, leaving only the single top-cell result open on that side.

The original node describes Tor amplitude after every site restriction, while
its unchanged Lean signature records the global resolution-tested predicate.
The new clopen-preparation node states that global hypothesis explicitly.
Localizing it remains part of the geometric argument, not an extra assumption.

Two concrete interface gaps remain in the top-cell argument. The existing
`complete_residue_cohomology_bounds` tests a fixed Tor interval after restriction
to every site object, whereas the item's Tor predicate is global. The supplied bounded finite-free residue model gives a route to that stronger
hypothesis: pull it back exactly, identify the pulled-back unit and finite powers,
and use the bounded-flat tensor calculation on each site object. Those comparison
maps still need formalization in the top-cell proof. Also,
`derived_nakayama_first_reduction` is expressed using continuous coefficients,
while this item uses inverse limits of finite constant coefficient sheaves;
the integral constant-completion comparison must transport its conclusion.
These arguments are stated explicitly in the top-cell docstring and node;
no definitional identification of the different coefficient models is assumed.

`adicResidueLissePerfectLift` and `residue_lisse_perfect_lift` require
Noetherian hypotheses on the scheme, absent in this item, so they do not give
a direct replacement. The chosen proof imposes no such hypothesis.

The initial dry run refused the prior two-hole packet while its split-off
reference budget was early. Subsequent work proved the projectivity, residue
splitting, cone-extension and induction steps. Earlier compile-server response
failures were temporary; current compilations succeed. No prior delivery push
was started or repeated.

The resumed reference clock has reset: the current `.budget.start` is
1792429808.3932662 (2026-10-19 17:10:08 UTC), whereas retained search records
begin much earlier on 2026-10-19. The latest initial dry run displayed only
42 minutes. No attempt identifiers were provided to this worker. The budget
file was read, never changed; proof work continued after the early refusal.

## New nodes

- `lem-sf-residue-clopen-preparation`: simultaneous finite residue
  trivialization and preservation of completion/reduction on a clopen partition;
  Stacks 09C3/098F. Open.
- `lem-sf-complete-residue-top-cell`: one top free cell, its complete cone,
  and its shorter bounded residue model; Stacks 09C3/09C2. Open.
- `lem-sf-complete-constant-residue-free-model`: the now-proved induction
  assembling the one-cell triangles into a bounded finite free sheaf complex.
- `lem-sf-weakly-contractible-unit-projective`: proved projectivity of finite
  powers of an arbitrary regular module sheaf on a weakly contractible scheme.
- `lem-sf-projective-homology-zero-differential-model`: proved cycle lifts
  and their quasi-isomorphism in any abelian category, without boundedness.
- `lem-sf-bounded-projective-models-extensions`: proved actual chain-map
  and shifted-cone representation for a distinguished-triangle extension.
- `lem-sf-weakly-contractible-clopen-refinement`: proved finite nonempty
  disjoint clopen refinement with actual maps to the covering members.

Every new node has source, natural-language proof, dependency list, Lean
attachment, blueprint ancestry and actual Mathlib search records. No change
record is needed because no existing signature or definition changed.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
