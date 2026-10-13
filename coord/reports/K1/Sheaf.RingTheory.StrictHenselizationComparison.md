## What changed

Proved `AlgebraicGeometry.Scheme.strictHenselization_comparison` in
`Sheaf.RingTheory.StrictHenselizationComparison`, preserving its full signature and both
public imports. Added two proof-only imports and two fully proved modules:
`Sheaf.RingTheory.EtaleHenselianRingLift` and
`Sheaf.RingTheory.EtaleLocalizationSeparableClosure`.

The proof transfers the local henselian structures from the colimits supplied by
`strictHenselization_triples` to the specified cocones. It constructs the map from A by
localization, lifts from both colimits, proves the maps are inverse by uniqueness over
R and A, and proves uniqueness of the resulting ring equivalence. Three proved private
helpers handle colimit properties, ring-cocone lifting, and base-residue compatibility.

The single-etale bridge follows the existing, proved private `Algebra.etale_lift_field`
argument in `MapIntoHenselianColimit`; that private declaration cannot be called from
another module. Its same-universe tensor-product argument is reproduced as a private
helper and exposed through a ring-homomorphism theorem, using the existing public
henselian etale retraction theorem. The field bridge descends the compatible map
through the surjective residue evaluation of the local base, then applies Mathlib
separability in towers. It does not require a separate finite-residue-extension lemma.

All three modules compiled individually through lcompile.py and together in import
order. Existing signatures are unchanged; all delivered declarations have complete
proofs. No global build was run. Sources were read at the official Stacks pages for
Tags 04GW, 08HQ, and 08HR; the local Stacks TeX path was absent on this machine.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.strictHenselization_comparison`
(node `lem-sc-strict-henselization-comparison`).

Also proved `AlgebraicGeometry.Scheme.etale_henselian_ring_lift`
(node `lem-sc-etale-henselian-ring-lift`) and
`AlgebraicGeometry.Scheme.etale_localization_separable_closure`
(node `lem-sc-etale-localization-separable-closure`), together with all private helpers.

Holes closed: 1. Holes added: 0. No sorry remains in any delivered module. This is a
proof, not a decomposition into unproved statements. Existing dependencies are used
as stated; this delivery does not claim to close holes in any undelivered dependency.

## No longer needed

Removed proof-only import `Sheaf.RingTheory.MapIntoHenselianColimit` and removed node
`lem-weil-pbc-map-into-henselian-colimit` from this item's proof dependencies. The
comparison no longer needs its algebra-colimit interface, small-index presentation,
universe-lifting helper, or conversion of the desired compatibility to ideal-residue
maps. Its public declaration `Algebra.map_into_henselian_colimit` is not used.

Retained `Sheaf.RingTheory.StrictHenselizationTriples` and node
`lem-weil-pbc-strict-henselization-triples`. The new single-etale lifting module retains
`Sheaf.RingTheory.HenselianEtaleRetraction` and its node; this is not pruned. Every
remaining import in the delivered modules is used. No claim is made that the removed
module is globally unreachable from other targets. The unit record `sk-thm-br` is
untouched, and no realized statement or proof step of that unit is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original proof plan has the correct two-map route,
but the existing mapping theorem uses an algebra-colimit and ideal-residue interface;
its field-valued lifting helper is private. The proved ring-valued bridge resolves
this mismatch without modifying another group's module or exposing private API.

The plan's field step described finite separable residue extensions. The actual proof
only needs compatible residue embeddings and surjectivity of the residue map of R,
so separability in towers suffices. This avoids proving an unused finite-extension
assertion. The DAG proof and proof dependencies now record the actual Lean route.

The edge cases were checked in the interfaces: local rings and unital maps to fields
exclude the zero-ring target; the identity triple recovers the base structural map;
no injectivity of R to its henselization, Noetherian hypothesis, or completion
assumption is used. The tensor-product argument works for every etale algebra, and
surjectivity is explicitly required for the target residue map. No statement or
public visibility in an existing module changed, and no forced adaptations are needed.

## New nodes

`lem-sc-etale-henselian-ring-lift`, in
`dag/nodes/sec-curve-estimates/lem-sc-etale-henselian-ring-lift.json`, records the fully
proved single-etale ring-homomorphism lifting bridge, a strict part of the mapping
argument. Its source is Tag 08HQ using the henselian etale retraction of Tag 04GG.

`lem-sc-etale-localization-separable-closure`, in
`dag/nodes/sec-curve-estimates/lem-sc-etale-localization-separable-closure.json`, records
the fully proved field step needed to apply the triples theorem over A. Its source
is the residue embeddings of Tag 04GW and the separability tower argument made
explicit in the Lean proof. Both inherit the item's chapter, unit, and recorded
blueprint ancestry. Searches of the complete blueprint found no identical statement.

For both nodes LeanSearch returned an HTTP internal-server error, recorded as
unavailable. LeanFinder and Mathlib grep searches ran and found constituent lemmas
but no exact statement. No new node contains a sorry; no change record is necessary.


## Second reading by K1

1. **Interfaces: pass.** Read the repository/sandbox diff for every delivered module.
   `strictHenselization_comparison` is the only existing declaration in these files;
   its entire signature, including all universe, ring, localization, residue-map,
   colimit and compatibility hypotheses and the unique-equivalence conclusion, is
   byte-for-byte identical. Both old public imports remain. The two added modules
   are new, contain proved theorems rather than replacement definitions, and require
   no change record or forced adaptation. The existing node changes only `proof`,
   `proof_deps`, and `proof_origin`.

2. **Proofs and axioms: pass.** Independently compiled all three modules through
   `lcompile.py --all`. Scratch copies with `#print axioms` checked the comparison,
   both new public theorems and all four private helpers. Every result lists exactly
   `propext`, `Classical.choice`, and `Quot.sound`; none lists `sorryAx`. No delivered
   file contains `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`.
   The colimit used in `pointed_colimit_properties` is determined up to its unique
   cocone isomorphism, and its prescribed residue map is identified by colimit
   extensionality. No arbitrary unproved existence witness supplies data. The maps
   betaC, f, g and the equivalence are constructed by localization, colimit descent,
   and the proved unique lifting theorem.

3. **New statements: pass; no split-off holes.** Read both new theorem statements,
   docstring arguments and node records. The single-etale theorem requires the target
   residue map to be surjective and to have maximal-ideal kernel; these are used to
   make the tensor-product residue extension trivial before applying the existing
   henselian etale retraction theorem. For B=R it gives exactly beta; for B=R x R a
   chosen residue projection lifts to the corresponding projection, rather than
   asserting uniqueness without the prescribed point. Maps to a field exclude a
   zero-ring source, and the henselian local target is nontrivial. The field theorem
   constructs the intermediate residue-field embedding by descent through the
   surjective residue evaluation of local R, and its scalar-tower equality is proved,
   not assumed. The identity triple recovers the original separable closure; no
   perfection, finite-extension or Noetherian condition is used. Both theorems are
   strictly smaller ingredients and are fully proved.

   Read Stacks [04GW](https://stacks.math.columbia.edu/tag/04GW),
   [08HQ](https://stacks.math.columbia.edu/tag/08HQ),
   [08HR](https://stacks.math.columbia.edu/tag/08HR),
   [04GG](https://stacks.math.columbia.edu/tag/04GG), and the item's contextual source
   [06LJ](https://stacks.math.columbia.edu/tag/06LJ). The tensor-product lifting and
   stagewise colimit descent agree with 08HQ and 08HR. Independently searched with
   Loogle `IsSepClosure, IsScalarTower`, LeanFinder `lifting a rational point of an
   etale algebra to a henselian base by tensor product`, Mathlib grep
   `IsSepClosure.*IsScalarTower|henselian.*lift|henselian.*hom`, and local rg for
   `existsUnique.*[Hh]ensel|lift.*[Hh]ensel|IsSepClosure.*tower` in lean/Sheaf and
   lean/WeilConjectures. No exact public bridge was found. The existing private
   `Algebra.etale_lift_field` was read and cannot be called from another module;
   its public retraction ingredient is reused. Mathlib supplies the field-tower
   ingredient, not the compatible scheme-residue descent statement.

4. **Route and pruning: pass.** Read from the comparison down through all private
   helpers and the two new modules. Transport along the cocone isomorphisms gives
   henselianity and the prescribed surjective reductions. Nonzero stage residues
   make the elements outside q units, so betaC is the actual localization lift.
   Single-etale uniqueness gives naturality of the lifting cocone and its uniqueness;
   the identity triple supplies base compatibility. After constructing f and g,
   single-etale uniqueness at t and localization extensionality establish g betaC
   = delta. Colimit-lift uniqueness over R and A then gives both inverse identities.
   Any competing equivalence agrees on A by localization and hence on D by lifting
   uniqueness. No stage asserts D is ind-etale over R. Imports used only by proofs
   are plain imports; public imports provide signature notions. The old proof-deps
   had only the triples theorem and the mapping-colimit theorem. The latter is the
   only removed dependency and is fully listed under No longer needed. Read
   dag/units/sk-thm-br.json: its Brauer injection/Tsen route and its `realized` fields
   are untouched; this auxiliary node bypasses no realized unit step.

5. **DAG agreement: pass.** Checked the existing node's five revised steps against
   the Lean: field tower/transport, localization, cocone lifting, inverse maps and
   uniqueness. Its proof_deps are precisely the union of those steps' uses. The two
   new nodes likewise record the tensor-product/retraction and residue-descent/tower
   arguments, respectively, and carry source, ancestry, chapter/unit, searches,
   creation metadata and verbatim Lean signatures. No new node restates the comparison.

**Second-reading repair:** corrected the comparison's proof docstring to describe
surjective residue descent and separability in towers instead of the unused finite
residue-extension argument. Proof terms, imports, signatures and node records needed
no repair. Holes closed: strictHenselization_comparison (1); holes added: none (0).
