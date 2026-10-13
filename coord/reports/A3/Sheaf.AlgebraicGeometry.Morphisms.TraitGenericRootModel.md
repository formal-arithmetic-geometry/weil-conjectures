## What changed

Reduced `AlgebraicGeometry.Scheme.GaloisCover.trait_generic_root_model` to two separate
source-backed parts: punctured Kummer charts with regular divisor data, and normality
of the full root algebras. The original statement, universes and visibility are unchanged.
The new modules are `Sheaf.AlgebraicGeometry.Morphisms.TraitGenericPuncturedRootChart`
and `Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorRootModelNormal`, imported only for
proofs. Existing public Mathlib imports support a complete density proof:
the finite product of monic root algebras is free, hence flat; f remains a nonzerodivisor;
localization away from f is injective and its spectrum has dense image equal to D(f).
The original node now records the two actual dependencies and this assembly.

All three modules compile through lcompile.py without warnings. The source was read at
https://stacks.math.columbia.edu/tag/0EYG, https://stacks.math.columbia.edu/tag/0EYH and
https://stacks.math.columbia.edu/tag/0EYJ. No normalization construction is used.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.GaloisCover.trait_generic_root_model`
(node `lem-sbc-trait-generic-root-model`). Its body has no sorry, including the density
argument. This is a decomposition, not a complete proof from sorry-free dependencies:
one upper hole is closed and two strictly separate lower holes are added (net -1).

Every remaining hole in the delivery is exactly a named theorem body in its own module:

- `AlgebraicGeometry.Scheme.GaloisCover.trait_generic_punctured_root_chart`
  (node `lem-sbc-trait-generic-punctured-root-chart`): chart construction and regular
  divisor data only; asserts neither density nor normality.
- `AlgebraicGeometry.Scheme.regular_divisor_root_model_normal`
  (node `lem-sbc-regular-divisor-root-model-normal`): normality for arbitrary regular
  divisor root algebras, with no trait, torsor, neighborhood or cover identification.

Both have complete natural-language proofs and sources. Edge cases checked: m=0 gives
the empty spectrum and vacuous normality; the density proof compiles uniformly even for
the zero product ring. Unit f gives R/(f)=0, regular vacuously, and all stalks lie in the
etale case. Exponent zero is explicitly excluded; exponent one is included. Neither new
statement assumes connectedness or nonemptiness. No data is defined by choosing an
arbitrary witness from a sorry theorem: the main theorem merely eliminates existentials.

## No longer needed

None of the original imports or dependency nodes was removed (the original proof_deps
was empty). Removed the redundant development imports `Mathlib.RingTheory.Flat.Basic`
and `Mathlib.Algebra.Polynomial.Monic`: the required facts are already publicly available
from the original imports, and compilation passes without both. The density step needs no new sorry theorem, no minimal-prime-avoidance
lemma, and no normalization machinery. In particular no imports were added for
`Sheaf.AlgebraicGeometry.Morphisms.NormalizationDenseOpen`,
`Sheaf.AlgebraicGeometry.Morphisms.TraitGenericNormalizationCharts`, or the DAG branch
`lem-pc-principal-open-dense-of-nonzerodivisor` /
`lem-pc-minimal-prime-avoids-nonzerodivisor`. These were considered alternatives, not
former dependencies, so no existing node or module is claimed pruned from the closure.

## Where the brief, the DAG or earlier work was wrong

The original node has four substantial proof steps but no proof dependencies or Lean
lemmas for them. The two new nodes supply the missing interfaces. The unit's realized
lists are empty; the argument preserves its trait-case tame-root route. The helper
blueprint-ancestor command returns None because created.item records a module rather
than a node, so the new nodes inherit the original node's explicit blueprint ancestor
and extend its via chain. Blueprint searches for tame, punctured root and regular divisor
found no matching chart or normality statement. LeanSearch returned HTTP 500 for both
new statements, recorded as unavailable; Loogle, LeanFinder and source grep ran normally.

## New nodes

`lem-sbc-trait-generic-punctured-root-chart`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-trait-generic-punctured-root-chart.json`,
records the punctured-chart theorem in `TraitGenericPuncturedRootChart.lean` and the
0EYJ/09EB/0EYG argument without full-model normality or density.

`lem-sbc-regular-divisor-root-model-normal`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-regular-divisor-root-model-normal.json`,
records the generic regular-divisor algebra theorem in `RegularDivisorRootModelNormal.lean`
and the local-ring argument of 0EYH. No interface change record or forced adaptation
is needed.

## Second reading by A3

1. Compared the delivered item with the repository using diff and checked its entire
   declaration signature byte for byte. Only two plain proof imports and the proof body
   changed. No existing statement, definition, universe or visibility changed. The two
   sibling modules are new, not adaptations. Verdict: pass.
2. Independently compiled all three modules in dependency order with lcompile.py; no
   errors or warnings. Compiled scratch copies with #print axioms for all three public
   declarations: exactly propext, Classical.choice, Quot.sound and sorryAx. The only
   literal sorries are the entire bodies of the two named split-off theorems. There is
   no definition, witness choice for data, forbidden axiom or kernel bypass. Verdict:
   pass as a decomposition, not a sorry-free proof.
3. Read both new statements, their docstrings and nodes against Stacks 0EYG, 0EYH,
   0EYJ and 09EB. The chart theorem handles only the punctured cover and regular divisor
   data; normality handles arbitrary such root algebras. Neither is a restatement of
   the item. The extra regularity data are exactly what the normality and flatness
   arguments need. Checked m=0, zero R, unit f, exponent one, and positive exponents
   divisible by the residue characteristic (excluded by the unit hypothesis). For
   primes containing the root, the local quotient is regular and the root is a
   nonzerodivisor; elsewhere the derivative is invertible. For charts the smooth
   closed fibre is a regular Cartier divisor, and the stabilizer order makes the
   codimension-one extensions tame. Independent LeanFinder, Loogle and source searches
   found no replacement. Existing KummerTorsor is a construction in the opposite
   direction. Neither lower hole has a short available closure. Verdict: pass.
4. Read the density proof: positive-degree monicity gives free factors, flatness
   preserves injective multiplication, and injective localization has dense spectrum
   image equal to D(f). This handles the empty product uniformly. Both added imports
   are plain proof imports; imports of the new modules provide their signature data.
   The old proof_deps was empty, so no old dependency was omitted from No longer needed.
   Read sk-prop-input-spreading's realized record and trait step: realized lists are
   empty and the tame-root route is preserved. No module is claimed pruned. Verdict:
   pass.
5. Compared the original and delivered node: only proof, proof_deps and proof_origin
   change; the two dependencies are exactly the two Lean theorem applications. New
   nodes have their source-backed proof steps, matching recorded Lean signatures,
   creation information, chapter, unit and inherited blueprint provenance. Found and
   supplied the missing lean_audit records on both new nodes. Added independent search
   records. Verdict: pass after metadata repair.

Second reading changed only the two new nodes' missing lean_audit metadata and their
independent search records, and appended this review. The Lean proof needed no repair.
The declared accounting remains one original hole closed and two lower holes added,
a decomposition with net -1; no pruning.
