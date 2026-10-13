## What changed

Second reading replaced the first worker's two faulty existence/component obligations
with the explicit `AlgebraicGeometry.etaleOpenTensorSectionsComponentIso` construction
and one section naturality obligation in the new proof-only module
`Sheaf.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentificationNaturality`.
The target uses `NatIso.ofComponents` and `ObjectProperty.isoMk`; its component formula
is `rfl`. Both original declaration signatures and the complete definition body of
`etaleOpenSmallRestriction` are unchanged byte for byte. The public-import pruning is recorded in
`coord/changes/etale-open-identification-imports.md`; no declaration changes. The original restriction definition remains in its original module.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.etaleTensorSectionsSheaf_openIdentification` (one of one).
Added exactly one hole:
`AlgebraicGeometry.etaleOpenTensorSectionsComponent_naturality`, node
`lem-weil-pbc-etale-open-qcoherent-identification-naturality`.
The component isomorphism is actual data constructed from existing natural
isomorphisms and `Functor.mapIso`, with no sorry dependency in its axiom printout.
This is a decomposition, not a complete proof: one upper hole closed and one lower
hole added, net zero for these declarations. Existing imported holes remain open.
Removed the first worker's unlanded `etaleTensorSectionsSheaf_openIso` and
`etaleTensorSectionsSheaf_openIso_component` obligations and their nodes; these
removed sandbox obligations are not counted as closed baseline holes.

## No longer needed

Removed direct imports `Sheaf.AlgebraicGeometry.EtaleTensorSections` and
`Sheaf.AlgebraicGeometry.TensorPullback` (already provided by the sheaf import).
Removed `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, since
restriction is constructed directly by the continuous over-map functor.
Replaced `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale` with its smaller
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small` dependency, which provides
`Scheme.isContinuous_overMap` used in the public restriction definition.
The naturality helper is a plain import used only by the proof.

Old proof dependencies no longer invoked:
`lem-weil-pbc-etale-inverse-image-restriction` and
`lem-pc-module-pullback-identity-composition`. The latter's existential comparison
is not the normalized comparison used here; `tensorSectionsComp` is supplied by
`lem-sc-etale-qcoherent-presheaf-functorial`. The three other old dependencies are
retained. No claim is made that any of these modules leaves the entire targets'
import closure, which the maintainer computes.

## Where the brief, the DAG or earlier work was wrong

The first worker chose an arbitrary sheaf isomorphism from a theorem asserting
existence with predicate True, then asserted a canonical component formula for that
choice. The existence theorem does not determine its witness. For an identity open
and a nonzero module, composing a valid comparison with a nontrivial automorphism
(e.g. negation on integer sections) need not preserve the prescribed formula.
This violates the rule against arbitrary data from an unproved existence theorem.
The two proposed nodes also had non-verbatim Lean statements, incomplete word proofs,
unsupported search records, and statement dependencies pointing back to the item.
The moved restriction declaration and its change record were unnecessary.

The repaired argument constructs every component explicitly. The only remaining
obligation is a commuting square, strictly part of the original proof: it says
nothing about existence of a sheaf isomorphism or its invertibility and needs no
quasi-coherence hypothesis. Its docstring gives the full unit/associativity argument.
The component construction uses the existing unit-normalized tensor adjunction;
its selected adjunction is pinned by the original theorem's unit, unlike the faulty
arbitrary isomorphism choice.

## New nodes

`lem-weil-pbc-etale-open-qcoherent-identification-naturality`, in the item's chapter
and unit, with the verbatim Lean signature and matching explicit-component declaration.
Its blueprint ancestor remains `lem-sc-artin-schreier-dimension`, serving the same
proper-case quasi-coherent calculation. Whole-blueprint search for pullback sections
naturality found no existing blueprint node carrying this square. The unit record
`dag/units/sk-prop-cd.json` is unchanged, including `realized`.

## Second reading by P3

1. Compared the delivered module against the repository using diff. Verified by
   byte comparison that both original signatures and the complete restriction
   definition body are unchanged. Restored the moved definition to its original
   module and deleted the unnecessary definition-move change record. Added the public-import
   pruning record after the first dry run requested it. Both direct importers
   compile unchanged against the delivered overlay. Verdict: pass after repair.
2. Compiled both final modules in import order with lcompile, without warnings.
   Scanned for forbidden declarations and sorry in data. Printed axioms for both
   original declarations and both new declarations: restriction and the explicit
   component isomorphism use only propext, Classical.choice, Quot.sound; the target
   and named naturality theorem also use sorryAx, as reported. Verdict: valid
   conditional reduction, not an axiom-free proof of the target.
3. Read the remaining square from the definitions, checked the identity, empty
   scheme and zero-module cases, and checked its general argument by unit
   naturality and normalized composition associativity. Searched Mathlib with
   leanfinder, loogle, grep and leansearch through msearch, and searched lean/Sheaf
   and the upstream WeilConjectures tree with alternate terminology. Leansearch
   returned Internal Server Error, recorded as unavailable; other searches found
   categorical tools but no existing square. Read Stacks 03DR and 03DU online;
   the equation is the compatibility of their successive pullbacks. Verdict:
   one true, strictly smaller sourced obligation; no relabelled target.
4. Built the component isomorphisms directly using existing library definitions
   and Mathlib mapIso/NatIso.ofComponents, with no sheafification or new existential
   data. Pruned imports and the two unused old proof dependencies as above.
   Kept the unit route and its realization record. Verdict: pass; decomposition
   with net zero holes, not counted as proof progress.
5. Updated the item's proof and proof_deps to the four actual dependencies and
   the new node's proof to unit naturality, normalized associativity, module
   naturality, and triangle transport. All new required fields and genuine search
   records are present; the Lean signature is verbatim and there is no dependency
   cycle back to the target. Verdict: pass after repair.

Changed: removed the invalid arbitrary-choice split and its two nodes/modules;
constructed canonical components, left only their naturality square, restored the
original restriction definition, pruned imports, and corrected DAG/report records.

Both original direct importers were compiled unchanged against the sandbox overlay;
no forced adaptations are needed. The final public-import change record is
`coord/changes/etale-open-identification-imports.md`.
