## What changed

Replaced the proposed affine-model admission with a real reduction through the
residue-field fibre. The target now constructs the quotient lift of `Spec.preimage t`,
constructs the intermediate pullback and its map from `Z'`, proves the smaller square
Cartesian by pullback pasting, and combines two restriction maps using
`globalSectionsUpperStarMap_comp'`.

Added `IntegralHenselianClosedFibreSections.lean`, containing the henselian rational
closed-fibre obligation, and `EtaleModuleSectionsFieldExtension.lean`, containing a
proved section-injectivity comparison for arbitrary separably closed base fields and
commutative coefficient rings. The latter generalizes the actual proof in
`AlgClosedExtensionModuleSections.lean`; that existing statement cannot be applied
here because it assumes an algebraically closed base field and ZMod coefficients.
All new proof dependencies are plain imports. The target's original public imports,
signature and docstring are preserved. No existing declaration or definition changed
its interface, and no change record is necessary.

## Proved and sorry left

Closed the original local hole:
`AlgebraicGeometry.Etale.strictHenselianIntegralSections_injective`
(node `lem-sbc-strict-henselian-integral-sections-injective`).

Added and proved:
`AlgebraicGeometry.Etale.etaleModuleSectionsFieldExtension_injective`
(node `new-etale-module-sections-field-extension`). This proof has no local admission;
it still depends on open imported results through the existing field-extension and
coefficient-comparison infrastructure.

Added one local hole, the only `sorry` delivered:
`AlgebraicGeometry.Etale.integralHenselianClosedFibreSections_injective`
(node `new-integral-henselian-closed-fibre-sections`). Its module has its full source
and natural-language proof, including the quotient-fibre identification. This statement
only concerns the rational closed fibre over a henselian local ring: it does not
include the subsequent geometric field extension or the target's composite map.

The target reduction closes one hole and adds one strictly smaller hole. This is a
decomposition, with net local hole change zero, not a complete axiom-free proof of
the target. No library-wide ledger progress is claimed. `#print axioms` for all three
public theorems returned only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`;
the latter is expected from the remaining local and imported admissions.

## No longer needed

Removed the target's direct proof imports:

- `Sheaf.RingTheory.IntegralOverHenselianPair`
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero`
- `Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension`
- `Sheaf.AlgebraicGeometry.EtaleModuleSetPullbackComparison`

They are still needed through the two new modules, so no upstream module is pruned.
All old proof dependencies are retained: `lem-weil-pbc-integral-over-henselian-pair`
and `lemma-weil-pbc-etale-degree-zero` are now dependencies of the rational-fibre
node; `lem-weil-pbc-sections-base-field-extension` and
`lem-sc-etale-module-set-pullback-comparison` are dependencies of the field-extension
node; `lemma-weil-pbc-finite-pullback-composition` is used directly in the target and
in the field-extension proof. No old dependency is wholly unused.

Removed the undelivered `StrictHenselianIntegralSectionsAffineModel.lean`, its
restatement node `new-strict-henselian-integral-sections-affine-model`, the unnecessary
presentation theorem/node `new-strict-henselian-integral-sections-affine-presentation`,
and the obsolete module-move change record. These were sandbox proposals, not
existing library declarations.

## Where the brief, the DAG or earlier work was wrong

The earlier submission changed the target docstring and replaced its admission by
an affine-model statement whose extra witnesses are supplied automatically by
Mathlib. This is effectively the original obligation under a different name. The
second reading rejected that decomposition and restored the original docstring.
The new reduction separates henselian restriction from separably closed field
extension and formally constructs and composes the actual maps.

The source checkout on this machine does not include the untracked Stacks text.
Read the official statements directly at [09XK](https://stacks.math.columbia.edu/tag/09XK),
[0A0C](https://stacks.math.columbia.edu/tag/0A0C), and
[0A3I](https://stacks.math.columbia.edu/tag/0A3I). The ring-theoretic source of 09XK is
More on Algebra, rather than Etale Cohomology; the rational-fibre proof combines
these two chapters.

## New nodes

`new-integral-henselian-closed-fibre-sections` records the rational-fibre injectivity
step over a henselian local ring, with its integral-algebra henselian-pair and
proper-identity comparison dependencies. It is the sole new admission.

`new-etale-module-sections-field-extension` records the proved field-extension step
with arbitrary module coefficients. It uses the existing set-section comparison,
module/set comparison, and composition identity. Both nodes include their verbatim
Lean signatures, sources, the required real Mathlib search categories and provenance. No new
statement duplicates a declaration of Mathlib or the library. The existing
algclosed/ZMod comparison is a special case, whose proof was reused and generalized.

## Second reading by J2

1. Compared every sandbox module with the repository. The only existing module is
   the item: its theorem signature is byte for byte unchanged, its original
   docstring is restored, and all public imports are unchanged. The other two
   modules are new, with new names checked by `rg` in the library. No definitions,
   hypotheses, conclusions or visibility of existing declarations changed. Verdict:
   pass after replacing the earlier affine restatement.
2. All three modules compile in import order with `lcompile.py`, with no errors or
   warnings. Inspected every declaration for forbidden features and data chosen
   from admissions: none. The quotient ring map and pullback lift are explicit
   constructions; no hollow definitions exist. Axiom probes of all three public
   theorems show only the three allowed standard axioms and expected `sorryAx`.
   Verdict: valid conditional proofs with the one documented admission.
3. Read the rational-fibre statement and its complete argument against 09XK and
   0A0C. It holds for empty Z and the zero integral algebra; for A a field the
   rational restriction is an isomorphism. It does not assume a separably closed
   residue field and is strictly one step of the original argument. Read and proved
   the field-extension statement using 0A3I and the canonical unit comparison; it
   handles empty schemes, zero coefficients, identity and transcendental field
   extensions. Attempted LeanSearch (service returned Internal Server Error); searched using
   leanfinder, loogle and grep with queries different
   from the first reader, and searched local Sheaf/upstream files. Found and reused
   the existing algclosed/ZMod proof, without introducing that statement's stronger
   hypotheses. Verdict: true, needed lower statements; field step closed.
4. Read the proof from the target down. Its quotient factorization and Cartesian
   square cancellation genuinely reduce to the two successive restrictions. The
   coefficient-forgetting proof follows the shortest existing library argument.
   Checked `dag/units/sk-lem-universal-datum.json`: the item is not recorded as a
   realized statement or step (those arrays are empty); this repair keeps the
   original node-level henselian/field-extension route and bypasses no unit.
   Removed the four unused direct proof imports; their underlying dependencies
   remain below the corresponding new nodes. Verdict: route preserved, no modules
   pruned.
5. Rebuilt the target node's `proof`, `proof_deps` and `proof_origin` from the actual
   quotient construction, pullback pasting and composition proof. Checked the two
   new nodes against their Lean signatures, sources, dependency unions, provenance
   and genuine recorded searches. Verdict: DAG and Lean agree; the sole admitted
   node accurately records the part still to prove.

Second reading changed the substantive reduction, restored the target's original
API documentation, removed the affine restatement/presentation proposals and their
change record, proved the generalized field-extension comparison, and replaced the
new nodes and dependency records accordingly.
