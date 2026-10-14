## What changed

Replaced the whole-proof sorry of
`RingTheory.dvr_tame_tensor_factor_residue_isSeparable` without changing its signature,
visibility, or public imports. Its proof now establishes finite normalization by Mathlib,
turns the two degree divisibilities into tameness, constructs the left field map from the
tensor quotient, and proves that its image generates the quotient over A by tensor induction.
The private, fully proved helper `isSeparable_of_isUnit_finrank` handles both characteristic
zero and positive characteristic using the inseparable-degree power and divisibility formulas.

Added `Sheaf.RingTheory.DvrNormalizedCompositumLocalDiagram`, proved entirely from Mathlib.
It constructs the map between integral closures, contracts Q to R, proves both localizations
are DVRs, constructs their fraction-field embeddings and the local map between them, proves
the two compatibility diagrams, identifies the ramification exponent by quotient length,
and transports the prime residue algebra to the canonical local residue algebra.

Added `Sheaf.RingTheory.DvrAbhyankarLocalResidue` for the remaining classical local
Abhyankar calculation. It takes a diagram of DVRs and fraction fields, with the two
ramification-index identities and a separable input residue extension. It has no tensor
quotient or normalization hypothesis. The main theorem combines the proved diagram with
this theorem. Both new imports in the item are proof imports. No existing interface or
other group's module was changed.

All three modules compile together without warnings. A quotient field structure must be
supplied explicitly with `Ideal.Quotient.field P`; it is deliberately not a Mathlib instance.
Supplying it removed the expensive failed inference, without a heartbeat or timeout increase.

## Proved and sorry left

Closed the original hole in `RingTheory.dvr_tame_tensor_factor_residue_isSeparable`
(node `lem-sbc-dvr-tame-tensor-factor-residue-separable`). There is no sorry in the item's
module. Its proof still depends on the new Abhyankar theorem, so this is a decomposition,
not a complete proof of the original theorem from the three permitted axioms.

New theorem `RingTheory.dvr_normalized_compositum_local_diagram`
(node `lem-sbc-dvr-normalized-compositum-local-diagram`) is fully proved from Mathlib.
The private helper `isSeparable_of_isUnit_finrank` is also fully proved.

The delivery adds exactly one hole:
`RingTheory.dvr_abhyankar_local_residue_isSeparable`
(node `lem-sbc-dvr-abhyankar-local-residue`), in its own module, with its complete source
argument in the docstring. Its entire proof is `by sorry`.

Holes closed: 1 original. Holes added: 1. Net hole reduction: 0.

## No longer needed

None. The original finite-normalization dependency remains used through
`IsIntegralClosure.finite`. No original imports, planned nodes, or modules are pruned.
The tentative aggregate compositum lemma used during development is not part of this
delivery; the local normalization diagram was proved instead.

## Where the brief, the DAG or earlier work was wrong

The original node's step 3 invoked Abhyankar and a localization-of-normalization
identification without stating either as an available Lean declaration. The new nodes
make these steps explicit; the normalization identification is now proved, leaving only
the classical local ramification calculation.

The new local theorem is strictly the ramification part: it assumes actual DVRs and
compatible fraction-field maps, rather than constructing these from a tensor quotient.
The diagram theorem does not assume `m_B A = m_A^n` and has no conclusion about the
residue extension of T over A. It cannot replace the original theorem on its own.

Edge cases checked: degree one and exponential characteristic one work in the arithmetic
helper; a degree divisible by the positive characteristic is ruled out by the unit
hypothesis. The primes used to construct DVRs are explicitly proved nonzero, using the
nonzero maximal ideals of the original DVRs. No field is silently treated as a DVR.
The residue transport proves compatibility on the surjective image of B, so it uses the
canonical local algebra structure, rather than merely an abstract field isomorphism.
No assertion in the existing statement was weakened or marked disputed.

## New nodes

`lem-sbc-dvr-normalized-compositum-local-diagram`:
`Sheaf.RingTheory.DvrNormalizedCompositumLocalDiagram`, declaration
`RingTheory.dvr_normalized_compositum_local_diagram`. Fully proved structural normalization
and localization result, following Stacks 032L, 00PD/034X and 09EM and Mathlib's canonical
localization maps. This result introduces no hole.

`lem-sbc-dvr-abhyankar-local-residue`:
`Sheaf.RingTheory.DvrAbhyankarLocalResidue`, declaration
`RingTheory.dvr_abhyankar_local_residue_isSeparable`. The remaining local DVR root
calculation of Stacks 0BRM followed by 09E7, separated from normalization and tensor glue.

Both nodes inherit the trait step of `sk-prop-input-spreading`. Blueprint searches for
Abhyankar, local Abhyankar and normalization/DVR/compositum found no matching blueprint
node. Mathlib searches were run through msearch.py: LeanSearch returned an internal server
error (recorded as unavailable); LeanFinder, Loogle and grep supplied the APIs used in
the proved diagram and arithmetic, but no Abhyankar theorem. No change record is needed:
no existing declaration signature, definition, instance or public import changed.

## Second reading by V1

1. **Interfaces: pass.** Compared the delivered item with the repository by `diff` and
   compared the complete existing theorem signature byte for byte. The signature,
   visibility, definitions, and original public imports are unchanged. The only existing
   node fields changed are `proof`, `proof_deps`, and `proof_origin`. Both additional
   modules are new; their declaration statements match their node records verbatim.
   No change record or forced adaptation is needed.
2. **Proofs and axioms: pass as a decomposition.** Independently compiled all three
   modules in import order using lcompile.py. Temporary copies with `#print axioms`
   show only propext, Classical.choice, and Quot.sound for
   `RingTheory.dvr_normalized_compositum_local_diagram`; the original theorem and
   `RingTheory.dvr_abhyankar_local_residue_isSeparable` also use sorryAx, exactly from
   the reported remaining local theorem. No other holes, forbidden declarations, or
   hollow definitions occur. The diagram's ring maps are explicit constructions and
   all its existential witnesses come from fully proved results.
3. **Split statements: pass after documentation repair.** Read the remaining local
   theorem against Stacks [0BRM](https://stacks.math.columbia.edu/tag/0BRM),
   [09EM](https://stacks.math.columbia.edu/tag/09EM), and
   [09E7](https://stacks.math.columbia.edu/tag/09E7).
   It assumes the local DVR and fraction-field diagram that the new proved theorem
   constructs; it is strictly the ramification calculation, not a renamed tensor theorem.
   A is the normalization in its fraction field by integrality and normality. U and T
   are the corresponding local normalizations: the integral closures lie in these DVRs,
   and localization at their centers gives DVRs with the same fraction fields; a local
   inclusion between such DVRs is equality. Generation rules out an extra field extension.
   Checked e=1 and n=1 (unramified base change), residue characteristic zero, and positive
   characteristic with imperfect residue fields. A characteristic-divisible e is excluded
   by the unit assumption; e=0 is excluded as well. The local theorem permits wild base
   change n, as 0BRM does. Repeated LeanFinder, Loogle, and grep searches with divisible
   ramification indices, composita, normalization/residue, and invertible finite degree
   queries found no replacement theorem. The similar arithmetic helper in
   RootNormalizationGenericStalkResidueSeparable is private and cannot be imported as
   a declaration. Closing the remaining Abhyankar calculation is beyond a short repair.
4. **Route and pruning: pass.** Read the tensor-generation proof, finite-normalization
   application, fraction-field/localization diagram, and residue-algebra transport.
   All newly added imports are used for statements or proofs with the correct visibility;
   the original public interface is preserved. The old proof dependency is exactly
   `lem-weil-pbc-noetherian-normal-separable-integral-closure-finite`, and it remains used
   through its Mathlib match IsIntegralClosure.finite. Thus `No longer needed: None` is
   complete. The unit sk-prop-input-spreading has empty realized lists in the repository;
   this delivery preserves them and keeps the trait-case normalization/Abhyankar route.
5. **DAG agreement: pass.** Checked the proof-step uses union against proof_deps in all
   three nodes, their Lean statement records, Mathlib matches for finite normalization
   and Dedekind localization, source attribution, creation fields, and blueprint/unit
   references. The new nodes describe respectively the proved structural diagram and
   the one remaining local calculation.

Second-reading changes: corrected the local node's further-base-change citation from
0BRL (multiplicativity of ramification indices) to
[09EQ](https://stacks.math.columbia.edu/tag/09EQ) (preservation of adic formal smoothness).
Expanded the remaining theorem's docstring to include the intermediate uniformizer-root
field and this further-base-change step, which its original short argument omitted.
Recorded the additional Loogle search in that node. No Lean signature or proof term changed.
The counts remain one original hole closed, one hole added, net zero: a decomposition.
