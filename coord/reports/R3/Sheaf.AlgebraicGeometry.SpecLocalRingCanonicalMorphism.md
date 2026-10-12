## What changed

Completed all four proof bodies in `Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`
without changing any statement or definition. The affine description uses uniqueness of
localization and Mathlib's affine factorization. The local properties use Mathlib's range
and closed-point API, Mathlib localization transitivity and uniqueness for spectrum
stalks, and the
stalkwise flatness criterion. The module-stalk isomorphism composes the extension/restriction
unit along a ring isomorphism with the inverse of the recorded pullback-stalk isomorphism;
its germ formula follows by cancellation. The quotient factorization is definitionally
the inverse local-ring correspondence, with closed immersion supplied by surjectivity.

Added the proof-only import `Mathlib.CategoryTheory.Adjunction.FullyFaithful`.
Updated the existing node's proof, proof dependencies, and proof origin to this route.
No new modules, nodes, statements, or definition changes.

## Proved and sorry left

Closed all four original holes:

- `AlgebraicGeometry.Scheme.fromSpecStalk_affine_description`.
- `AlgebraicGeometry.Scheme.fromSpecStalk_local_properties`.
- `AlgebraicGeometry.Scheme.fromSpecStalk_module_stalk`.
- `AlgebraicGeometry.Scheme.fromSpecStalk_quotient_factorization`.

No `sorry` remains in the item, and no hole was added or split off. These are complete
proofs from existing declarations, not claims that their dependency closure is axiom-free.
After the second reading, Mathlib localization transitivity and uniqueness supply the
localized ring isomorphism without an open dependency. Only
`AlgebraicGeometry.Scheme.Modules.exists_tensorPullback_stalk_iso`
(node `lem-weil-pbc-module-stalk-pullback`) remains needed for the tensor-pullback stalk
formula; it was not edited. The affine-description, local-properties and quotient
factorization declarations have only `propext`, `Classical.choice`, and `Quot.sound`
in their axiom closures. The module-stalk declaration also has `sorryAx` from existing
imports. Four item holes closed, zero holes added; three declarations are axiom-clean.

Validation: local single-file compilation succeeds without warnings after import pruning.

## No longer needed

Removed proof-only imports:

- `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` (replaced during second reading
  by Mathlib localization transitivity and uniqueness, already publicly available
  through `Mathlib.AlgebraicGeometry.Stalk`).
- `Sheaf.AlgebraicGeometry.TensorPullback` (already exposed by the statement imports).
- `Sheaf.Topology.PresheafModuleStalkFunctor` (the proof uses the recorded ringed-space
  stalk functor already exposed by the statement imports).
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC`
  (no residue-field computation is needed).

The proof no longer needs these former proof dependencies:

- `lem-weil-pbc-localization-prime-residue-field-iso`.
- `lem-weil-pbc-affine-open-spec-points`.
- `def-weil-affine-spectrum`.
- `def-weil-pbc-module-stalk`.
- `lem-weil-pbc-affine-open-inclusion-spec-map`.
- `lem-weil-pbc-spec-map-residue-field-naturality`.
- `def-weil-open-immersion`.
- `lem-weil-pbc-spec-domain-stalks-function-field`.

For Mathlib dependencies above, pruning means the planned direct dependency is unnecessary;
it does not remove shared Mathlib modules or definitions used by the statement. The
PropertyC module is unnecessary for this item's proof. Other targets may still reach it.
The unit's realized statement and proof-step nodes are unchanged; this item is below that
level and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false or unusable statement was found. The planned affine-neighborhood comparison,
closed-point computation, and quotient stalk-map comparison are already encapsulated in
Mathlib's canonical-morphism API. The planned residue-field naturality import is
unnecessary: Mathlib localization transitivity and uniqueness prove the stalk clause.
The blueprint unit's source file is not available at its recorded path in this checkout;
its full unit record and realized steps were read instead.


## Second reading by R3

1. Compared the delivered module against the repository with `diff -u`: all four
   existing declaration signatures and all definitions are byte-for-byte unchanged.
   Only four proof bodies and private imports differ. The node differs only in
   `proof`, `proof_deps`, and `proof_origin`; there is no statement change record
   because no statement or definition changed. Verdict: pass.
2. Compiled the module using `lcompile.py` without errors or warnings. A scratch
   copy with `#print axioms` for all four declarations shows only the three standard
   axioms for affine description, local properties, and quotient factorization;
   module stalk additionally uses `sorryAx` from existing imported theorems.
   No `sorry`, hollow definition, axiom declaration, unsafe/opaque declaration,
   external implementation, or kernel-check bypass occurs in the delivered module.
   Verdict: pass, with the reported existing open dependency.
3. No statement was split off and no new declaration or node was added. Read the
   existing localization and pullback-stalk statements: the former's final clause
   really identifies the canonical localized map, and the latter specifies exactly
   the chosen adjunction unit used by this module, including its germ formula.
   The pullback-stalk unit sends a germ to `1 ⊗ germ`, so restricting the inverse
   stalk isomorphism after the extension/restriction unit proves the requested map,
   not merely an unspecified isomorphism. Properness of J supplies nontriviality
   before the quotient local-ring instances are used. Checked the field case (the
   stalk localization and extension/restriction unit are identities), J = 0 (identity
   quotient), and J maximal (the residue-field closed immersion); J = top is correctly
   excluded, and an empty scheme has no point y. Verdict: pass.
4. Read Mathlib's Stalk, Spec, AffineScheme and LocalizationLocalization APIs,
   searched the library for canonical-morphism stalk isomorphisms and flatness,
   and read Stacks Schemes 01J6/02NA/01J7 in the available source copy
   `/home/ubuntu/c1-stacks-review/schemes.tex`. The affine factorization, range and
   closed-stalk identity already use Mathlib directly. Found a shorter dependency
   route for the general stalk clause: localization of a localization plus uniqueness
   of localization, with the map equality proved on algebra-map generators.
   Replaced the open localization/residue-field theorem by that route and removed
   its private import. The upstream flatness instance exists, but the present
   three-line stalkwise flatness deduction needs no further import. Every removed
   old proof dependency is listed above. Read `dag/units/sk-thm-p1.json`: this item
   is absent from the unit's realized statement and step lists; those lists and all
   unit routes are unchanged. Verdict: pass after this repair.
5. Checked each DAG proof step against its Lean body and the statements of the
   existing dependencies. Updated step 2 to cite the existing Mathlib leaf
   `lem-weil-pbc-localization-of-localization` instead of the open prime/residue-field
   node; recomputed `proof_deps` as the union of step uses and recorded the repair
   in `proof_origin`. Steps 1, 3, and 4 still describe the actual proofs. The report
   now distinguishes four closed item holes from three axiom-clean declarations.
   Verdict: pass after these metadata and report corrections.

Second reading changed the local stalk-isomorphism proof to use Mathlib directly,
pruned `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` and its node from the
proof dependencies, and updated the DAG and report. No new holes or statements.
