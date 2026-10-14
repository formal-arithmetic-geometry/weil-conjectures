## What changed

Replaced the proof of `RingTheory.dvr_galois_root_factor_uniformizer` without changing its
signature. The proof uses the existing
`AlgebraicGeometry.Scheme.dvr_uniformizer_root_algebra`, proves the maximal-ideal power
identity from the root equation, supplies finite normalization and Galois divisibility,
and converts formal unramifiedness into the required singleton-span equality using Mathlib.
All added imports in the existing module are private proof imports.

Added three modules, one statement per module:

- `Sheaf.RingTheory.DvrRootTensorFactorIntegralClosureFinite`: a proved finiteness theorem
  for tensor field factors of finite faithful normal Noetherian domain extensions.
  Its proof constructs the compatible fraction-field algebra, proves the tensor map
  surjective, obtains separability through formal unramifiedness, and applies
  `IsIntegralClosure.finite`.
- `Sheaf.RingTheory.DvrGaloisNormalizationRamificationDvd`: a proved numerical theorem.
  It equips the integral closure with the Galois action and finite free module structure,
  uses Mathlib's Galois fundamental identity, and proves both divisibilities.
- `Sheaf.RingTheory.DvrTameTensorFactorUnramified`: the remaining Abhyankar step,
  with normalization finiteness and both divisibility bounds as explicit inputs.
  It assumes an arbitrary finite faithful DVR extension with the specified ideal-power
  identity. It does not construct a root algebra, prove finiteness, or prove Galois bounds.

Updated the item's DAG proof and added the three corresponding nodes. The unit remains
`sk-prop-input-spreading`; its trait/tame-root route is preserved.

## Proved and sorry left

Closed the original hole in `RingTheory.dvr_galois_root_factor_uniformizer`
(`lem-sbc-dvr-galois-root-factor-uniformizer`) by a complete assembly proof.

New declarations proved without any `sorry`:

- `RingTheory.dvr_root_tensor_factor_integralClosure_finite`
  (`lem-sbc-dvr-root-tensor-factor-integral-closure-finite`).
- `RingTheory.dvr_galois_normalization_ramification_dvd`
  (`lem-sbc-dvr-galois-normalization-ramification-dvd`).

Added exactly one hole:
`RingTheory.dvr_tame_tensor_factor_formallyUnramified`
(`lem-sbc-dvr-tame-tensor-factor-unramified`), with its entire proof `:= by sorry`.
There are no other holes in the delivered modules. Closing one upper hole and adding one
lower hole is a decomposition, with net hole change zero, not an unconditional proof of
the original theorem. The two additional helpers have complete Lean proofs.

Edge cases checked: the root construction includes n=1; the Galois numerical lemma
includes the degree-one extension and requires no invertibility of n; the finiteness lemma
requires neither a DVR base nor a degree bound. The Abhyankar statement explicitly requires
n>0, invertibility of n, the ideal-power identity, tame divisibility bounds and finite
normalization. Characteristic zero and imperfect residue fields are included: in positive
residue characteristic the inseparable degree divides the residue degree, hence n, so is one.
No finiteness assumption on a scheme normalization was added to the original statement.

## No longer needed

None. The original module had no proof-dependency imports or named proof dependencies to
prune. Its public statement imports are preserved. The assembly uses all its added proof
imports. No existing node or module is bypassed, and no unit statement or proof step changes.
The source's finite-product-of-fields identification is replaced in the proved finiteness
helper by an explicit surjection from the fraction-field tensor product to its field factor.

## Where the brief, the DAG or earlier work was wrong

The original node's two non-elementary proof steps named no dependencies. In particular,
there was no available Lean declaration for the ring-theoretic Abhyankar step. This delivery
makes that step a separate, strictly smaller interface and proves the tensor finiteness and
Galois degree calculations that precede it.

Mathlib search found the local unramified criterion, trace-pairing finiteness, and the Galois
fundamental identity, but no Abhyankar base-change theorem. LeanSearch returned HTTP 500;
its searches are recorded as unavailable, not as negative results. Loogle, LeanFinder and
source grep supplied the component APIs. Blueprint searches for Abhyankar, Galois
ramification, ramification index and finite separable extensions found no duplicate of
these new interfaces. The existing root-algebra theorem is reused.

During development the root-algebra module was newer than the published compiled snapshot.
The final assembly was tested temporarily with that theorem's exact type as an unfinished
local goal; the delivered proof imports and applies the existing theorem and contains no
such temporary goal. Final validation is the delivery dry run.

## New nodes

`lem-sbc-dvr-root-tensor-factor-integral-closure-finite` records the proved tensor-factor
finiteness calculation, with Tag 032L and the concrete fraction-field/tensor glue.
Its only named proof dependency is the existing Mathlib leaf
`lem-weil-pbc-noetherian-normal-separable-integral-closure-finite`.

`lem-sbc-dvr-galois-normalization-ramification-dvd` records the proved Tag 09EB calculation,
using the same existing trace-pairing leaf and Mathlib's Galois fundamental identity.

`lem-sbc-dvr-tame-tensor-factor-unramified` records the remaining application of Tags 0BRM
and 09E7, followed by the finite-type local unramified criterion. Its hypotheses supply
exactly the finite normalization and tame numerical inputs already established by the
other modules. Its source, proof in words and search history are in its docstring and node.

No definition or existing statement changed, so no change record or forced adaptation is needed.

## Second reading by N2

1. PASS: compared the existing module with the repository by diff and checked its
   theorem signature byte for byte. Only private proof imports, an elaboration
   option, a comment and the proof body changed. The existing node changes only
   proof, proof_deps and proof_origin. No definition or existing interface changed.
2. PASS: independently compiled all four modules with lcompile.py --all. Scratch
   copies with #print axioms show only propext, Classical.choice and Quot.sound
   for both proved helpers. The assembly and the one named Abhyankar hole also
   use sorryAx, as expected from their open dependencies. There is exactly one
   delivered sorry, the complete body of dvr_tame_tensor_factor_formallyUnramified;
   no forbidden declaration or hollow definition occurs.
3. PASS: checked the remaining lemma against Stacks
   [0BRM](https://stacks.math.columbia.edu/tag/0BRM),
   [09E7](https://stacks.math.columbia.edu/tag/09E7), and
   [02FM](https://stacks.math.columbia.edu/tag/02FM). Finite normal A is the
   integral closure of B in Frac(A); thus its displayed ideal identity supplies
   the base ramification index required by Abhyankar. In positive residue
   characteristic p, f divides the unit n, so its inseparable p-power factor
   is one. Finiteness of S supplies the finite residue extension needed by 02FM.
   The identity extension, n=1, characteristic zero and imperfect residue fields
   give the claimed conclusion. The hole isolates the tame base-change step;
   root construction, finite normalization and Galois divisibility are supplied
   by other declarations, rather than hidden in a renamed original statement.
   Independent LeanFinder search for killing tame ramification by divisible-index
   base change, Loogle search for FormallyUnramified and integralClosure, Mathlib
   grep for index-one/unramified results, and repository searches for Abhyankar
   and tame ramification found component APIs and geometric callers, but no
   duplicate of this ring-theoretic interface. Closing this hole requires the
   unavailable Abhyankar argument, rather than a short application of those APIs.
4. PASS: read the proof from the target downward. It reuses the existing root-DVR
   statement, proves the ideal-power identity, obtains finite normalization and
   numerical bounds with proved helpers, and finishes using Mathlib's local
   unramified criterion. Proof-only imports are private; statement imports expose
   the types and predicates in the signatures. The old proof_deps list was empty,
   so No longer needed is complete. The unit's realized fields and its trait/tame
   route are unchanged; this delivery works below that route. No shorter complete
   route was found.
5. PASS: checked all four node signatures against the Lean text verbatim, and
   checked the proof steps and dependency unions against the declarations used.
   The three new nodes carry sources, searches, provenance, creation, blueprint,
   unit/chapter and Lean records. The two proved nodes describe their actual
   Mathlib arguments; the open node describes the remaining sourced argument.

Changes in this second reading: added this independent review and its validation
evidence to the report. No Lean or DAG repair was necessary. One original hole
is closed conditionally and one lower hole is added: this remains a decomposition
with net hole change zero, with two additional helper theorems proved outright.
