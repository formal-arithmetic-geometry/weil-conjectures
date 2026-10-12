## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.Modules.finite_H_pushforward_integral_ideal` without changing
its signature, universes, visibility, scalar action, or existing docstring.

The proof now performs Noetherian induction on `TopologicalSpace.Closeds X`,
simultaneously in all cohomological degrees. Two geometric inputs supply a coherent
Chow module and two common-submodule comparisons with smaller-support filtrations.
All cohomological glue is proved in the item's module: finiteness of an exact
sandwiched term, all three implications for a short exact sequence, zero cohomology,
linear isomorphism invariance, and finite-subobject-filtration induction.
The left-term argument treats degree zero by an injective map rather than inventing
negative natural-number cohomology.

Added proof-only imports of `WeilConjectures.AlgebraicGeometry.Cohomology.LongExact`,
`Sheaf.AlgebraicGeometry.ChowFiniteCohomologyWitness`, and
`Sheaf.AlgebraicGeometry.IntegralIdealComparisonFiltrations`.
The existing public imports remain necessary for the unchanged statement.
Added the two statement modules and their nodes. Updated only `proof`, `proof_deps`,
and `proof_origin` of the item's existing node. No definition or interface changed,
and no other group's module was adapted.

Validation: all three modules compile together with lcompile.py without warnings.
The complete delivered import graph has no cycles; every Lean line is at most 100
characters. The only textual holes are the complete proofs of the two public
geometric theorems. The new signatures and natural-language arguments were checked
against Stacks coherent.tex, `proposition-proper-pushforward-coherent` (02O5),
`lemma-property-irreducible` (01YH), and `lemma-coherent-filter` (01YF).

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.finite_H_pushforward_integral_ideal`
(node `lem-pc-e2-integral-ideal-proper-cohomology`). Its proof has no `sorry`.

Added two holes, each a named public theorem in its own module:

- `AlgebraicGeometry.Scheme.Modules.exists_chow_finite_cohomology_witness`
  (node `lem-pc-v3-chow-finite-cohomology-witness`): the Chow/projective construction,
  coherence, compatible generic-rank-one stalk, and finite cohomology of one module.
- `AlgebraicGeometry.Scheme.Modules.exists_integral_ideal_comparison_filtrations`
  (node `lem-pc-v3-integral-ideal-comparison-filtrations`): purely geometric common
  submodule, two exact sequences, and smaller-support integral-ideal filtrations.

This is a decomposition, not an unconditional proof: one hole closed, two added,
net minus one before any changes to the targets' import closure. Neither new theorem
restates the original. The first supplies one distinguished module independently of
the ideal; the second has no properness, base ring, or cohomology hypothesis or
conclusion. Five private helper proofs are complete and add no holes.

## No longer needed

No import from the original module was removed. The following original planned
proof dependencies no longer occur directly in its node:

- `lem-weil-pbc-chow-noetherian` / `WeilConjectures.AlgebraicGeometry.ChowLemma`;
- `lem-pc-chow-relative-ample` / `Sheaf.AlgebraicGeometry.ChowRelativeAmple`;
- `lem-pc-relative-kill-by-twisting` / `Sheaf.AlgebraicGeometry.RelativeSerreVanishing`;
- `lem-pc-projective-coherent-finiteness` /
  `WeilConjectures.AlgebraicGeometry.Cohomology.Projective`;
- `lem-pc-derived-direct-image-composition` /
  `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`;
- `lem-pc-closed-immersion-coherent-cohomology` /
  `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism`;
- `lem-pc-affine-morphism-hi` /
  `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`;
- `lem-pc-coherent-property-irreducible` /
  `Sheaf.AlgebraicGeometry.CoherentPropertyIrreducible`;
- `lem-weil-pbc-coherent-filtration-integral-subschemes` /
  `Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes`.

Chow, twisting, projective cohomology, derived composition, and closed-pushforward
cohomology remain requirements of the new Chow node. The filtration remains a
requirement of the new geometric comparison node. These are moved dependencies,
not globally eliminated work. The full coherent-property irreducible theorem is
replaced here by its strictly geometric comparison construction: the cohomological
property argument and induction are now Lean proofs. The affine-higher-image node
is not needed by this new route; closed cohomology comparison suffices for the final
closed pushforward. Other targets may still need either removed node/module.
No claim is made that a module leaves the whole project's target closure.

The Noetherian closed-subset induction node, finite-submodule node, and long-exact
sequence node remain direct dependencies. Finite-filtration induction is proved
locally rather than imported through the general proper-coherence theorem.

## Where the brief, the DAG or earlier work was wrong

The planned existing devissage and filtration declarations cannot be imported into
this item without a Lean import cycle. For example:

`CoherentPropertyIrreducible → CoherentFiltrationIntegralSubschemes →
ClosedImmersionCoherentEquivalence → FinitePushforwardCoherent →
Cohomology.DirectImage.AffineMorphism → Cohomology.DirectImage.FiniteFreeComplex →
IntegralIdealProperCohomology`.

Likewise `WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion` imports
`Cohomology.DirectImage`, which reaches this item. These failures were confirmed by
`tools/import_direction.py may`; this is an import-layer problem, not a mathematical
error in the statements. Existing modules were not edited. The two new modules have
only statement/definition imports and the resulting graph is acyclic. Their nodes
retain the mathematical dependencies for subsequent proof work. Those dependencies
will need suitable import layering before they can be used as proof imports.

The projective higher-image theorem in Cohomology.Projective invokes the general
proper-coherence theorem. It cannot justify the Chow module's coherence at this
stage without circular reasoning. The new node and its docstring specify the
independent proof: over affine opens of W, projective cohomology finiteness supplies
finite sections, and quasi-coherent localization gives coherence.

Edge cases checked: zero ideals take the zero branch; zero cokernels have empty
filtrations; degree zero uses left exactness; an integral W is nonempty; for a
one-point integral scheme a nonzero ideal and a residue-field line compare with
zero cokernels. Nilpotents in the ambient X are allowed, and the generic scalar
action is explicitly required to factor through its residue map. If the base is
empty the hypotheses on W cannot hold. The unit's Chow/projective route is kept;
its realized fields contain no extra statement or step being bypassed.

LeanSearch was attempted for each new statement and returned an internal server
error. LeanFinder/Loogle and Mathlib grep ran successfully; no matching construction
was found. Repository and blueprint searches found the existing inclusion,
filtration, and irreducible-property statements, but no theorem stating either new
construction exactly.

## New nodes

`lem-pc-v3-chow-finite-cohomology-witness`, in
`dag/nodes/sec-picard-framework/`, records the Chow construction from Tag 02O5 in
`Sheaf.AlgebraicGeometry.ChowFiniteCohomologyWitness`. It inherits the item's unit,
chapter, and blueprint ancestor and includes source, full proof steps, actual
three-kind search records, and the verbatim Lean signature.

`lem-pc-v3-integral-ideal-comparison-filtrations`, in the same chapter directory,
records the geometric comparison extracted from Tags 01YH and 01YF in
`Sheaf.AlgebraicGeometry.IntegralIdealComparisonFiltrations`. The proof uses the
existing generic-point inclusion and integral-ideal filtration, without assuming
the original cohomological conclusion. Its source, steps, searches, and signature
are recorded. No change record is needed: no existing statement or definition was
changed.

## Second reading by V3

1. I compared the delivered item module with the repository version. The original
 theorem signature, universes, visibility, and docstring are unchanged; the two added
 modules and their declarations are new, and the node files record those additions.
 Verdict: passed.

2. I compiled all three delivered modules with `lcompile.py --all`. They compile without
 errors or warnings. The only remaining `sorry`s are the two named public split-off
 theorems, each documented above and represented by a node; there are no hollow
 definitions, axioms, unsafe declarations, or forbidden implementation features.
 Verdict: passed.

3. I checked both split-off statements against their signatures and source descriptions.
 The Chow witness is independent of the input ideal and supplies exactly the coherent
 generic rank-one module and finite cohomology used by the induction. The comparison
 statement is geometric, has no cohomology hypothesis, and strictly decomposes the
 original argument into common submodule, exact sequences, and smaller-support
 filtrations. Repository and search checks found no existing declaration duplicating
 either result. Edge cases (zero ideal and zero cokernel) are explicitly handled in the
 item proof. Verdict: passed.

4. I traced the item proof and updated its `proof` and `proof_deps` to the declarations
 actually used. The long-exact-sequence import and the two new proof-only imports are
 minimal for this route; all removed planned dependencies are listed under
 `## No longer needed`. The unit's Chow/projective route and realized unit steps remain
 represented by the Chow witness node. Verdict: passed.

5. I checked the DAG nodes against the Lean declarations, including verbatim signatures,
 sources, proof steps, dependency unions, blueprint ancestry, chapter, unit, and split
 status. The target node remains unchanged except for its proof metadata. Verdict: passed.

Changes made during second reading: none to Lean code or nodes; added this review record
 to satisfy the delivery contract.
