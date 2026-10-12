## What changed

Replaced the sole remaining sorry of the assigned module with a complete finite-filtration
induction on sheaf cohomology. The proof handles zero, transports finiteness across quotient
and top-subobject isomorphisms, uses explicit short exact cokernel sequences, and transfers
finiteness through the affine-base semilinear comparison after restricting scalars along
f.appTop. Every existing signature, visibility and docstring is unchanged. Added three proof-only imports.

Added three new modules: FinitePresentationIntegralFiltration (a general filtration input),
IntegralIdealProperCohomology (proper finiteness only for integral-ideal factors), and
CohomologyFiniteExtension (proved using the existing cohomology exact sequence and Mathlib
Submodule.fg_of_fg_map_of_fg_inf_ker). Updated lem-pc-coherent-hi to match the route.
The assigned module and all three modules compile together without warnings. The extension module
publicly imports only cohomology definitions and Noetherian-ring definitions; its long-exact-sequence
import is proof-only. The redundant Finsupp import was removed during the second reading.

## Proved and sorry left

Closed AlgebraicGeometry.Scheme.Modules.finite_sections_higherDirectImage
(lem-pc-coherent-hi): 1 of 1 original holes closed by decomposition, not an unconditional proof.
No sorry remains in the assigned module.

Added two holes, each in its own new module, with a source and complete proof in words:
- AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_integral_filtration
  (lem-pc-e2-finite-presentation-integral-filtration).
- AlgebraicGeometry.Scheme.Modules.finite_H_pushforward_integral_ideal
  (lem-pc-e2-integral-ideal-proper-cohomology).

Proved AlgebraicGeometry.Scheme.Modules.finite_H_of_shortExact
(lem-pc-e2-cohomology-finite-extension), with no new sorry. This is the extension step,
not a use of proper-cohomology finiteness. Net holes for this delivery: one closed, two added.
Existing imported holes remain the next workers' items.

Edge cases checked against the source and signatures: the zero module has a length-zero
filtration (Fin.last 0 = 0); the proof starts with zero cohomology. The ideal-finiteness
input permits the zero ideal. IsIntegral excludes empty integral schemes. The extension
lemma applies in degree zero as well as all higher degrees, requires a Noetherian scalar
ring for submodule finiteness, and does not assume the cohomology map is surjective.
The scalar action is the actual restriction along f.appTop, not an arbitrary action.

## No longer needed

No existing import was removed, and no globally pruned module is claimed. The four existing
proof imports are all used by the already completed perfect-locus and finite-free-model proofs.

The original lem-pc-coherent-hi dependencies are no longer direct inputs to the assigned
module, except lem-pc-cohomology-sections-affine-base. The node also retains its existing proper-basic
and finite-support-hi step for the separate vanishing clause of its natural-language statement. The new integral-support and filtration
inputs keep the needed Chow, twisting, projective-space, support and devissage mathematics
below them; these are a decomposition, not a claim that that theory is unnecessary.
The general sheaf-coherence kernel/cokernel two-out-of-three step is replaced at the top by
ordinary module finiteness under extensions. The general coherent_property_devissage and
coherent_property_devissage_integral_subschemes modules are not imported. The sheaf-level
coherent-modules-kernel-cokernel-sum and affine-open-locnoeth,
finite-type-over-noetherian and coherent-ft-locnoeth inputs are unnecessary as separate top-level
inputs: Noetherianity is obtained by Mathlib and the filtration uses finite presentation
in its interface. Vanishing is a separate existing theorem, not needed for this finiteness proof.

The complete list of old proof_deps removed as direct inputs to lem-pc-coherent-hi is:

- pqf-lem-affine-open-locnoeth
- lem-weil-pbc-finite-type-over-noetherian
- lem-pc-coherent-property-devissage
- lem-weil-pbc-derived-functor-long-exact
- lem-weil-pbc-coherent-modules-kernel-cokernel-sum
- lem-weil-pbc-closed-immersion-proper
- lem-weil-pbc-chow-noetherian
- lem-weil-pbc-proper-composition
- lem-pc-chow-relative-ample
- pqf-lem-coherent-ft-locnoeth
- lem-pc-relative-kill-by-twisting
- lem-pc-projective-coherent-higher-images
- lem-pc-derived-direct-image-composition
- lem-pc-closed-immersion-coherent-cohomology
- lem-weil-pbc-closed-immersion-finite
- lem-pc-affine-morphism-hi
- lem-weil-pbc-finite-type-module-support-closed
- def-pc-integral-scheme

These are removed DAG edges, not globally pruned modules; the geometric inputs needed
by the new integral-ideal theorem are retained below its node. The new filtration input
retains the underlying support-devissage mathematics.

## Where the brief, the DAG or earlier work was wrong

The earlier missing-cache blocker is resolved: both ProperFlatCechModel.olean and
FlatModelFiniteFreeShortening.olean are now published and baseline compilation succeeds.

The existing CoherentFiltrationIntegralSubschemes, CoherentPropertyIrreducible,
CoherentPropertyDevissage and CoherentPropertyDevissageIntegralSubschemes modules reach
FiniteFreeComplex, so importing them here closes a module cycle. The new filtration input
is a deliberately smaller finite-presentation interface to Tag 01YF, which avoids the
RingedSpace.IsCoherent interface and these cyclic imports. Its proof is the existing source
filtration argument, with unnecessary output clauses forgotten; it is a generic theorem,
not a restatement of proper cohomology finiteness.

The original CoherentPropertyDevissage asks for residue-rank-one witnesses at arbitrary
points of an integral closed subscheme; the source 01YI asks only at its generic point.
No statement was changed in this delivery. The integral-support input uses the generic point.
Projective.isFinitePresentation_higherDirectImage_of_isClosedImmersion is proved using this
module's proper-coherence theorem; it cannot prove the proper case. The new input's written
proof requires projective finiteness independently from the projective-space case.

LeanSearch was attempted for each new node but returned Internal Server Error. LeanFinder,
Loogle and Mathlib grep were run and their recorded results inspected. No unavailable-service
answer is treated as a mathematical search verdict. Source proofs of Tags 01YF, 01YH and 02O5
were checked on the Stacks Project website. The unit's proper-coherence/projective-space route
is preserved; no unit statement or unit realization is changed.
The final deliver3.py --no-push check prints OK, except for the second reading that the next
worker writes; nothing was pushed.

## New nodes

lem-pc-e2-finite-presentation-integral-filtration: the part of Tag 01YF needed by this proof.
Module Sheaf.AlgebraicGeometry.FinitePresentationIntegralFiltration; one remaining sorry.
The source already has a stronger coherent-interface filtration statement; the smaller
interface is necessary here because the existing module imports through the assigned module.

lem-pc-e2-integral-ideal-proper-cohomology: the integral-support part of the Chow/devissage
argument of Tags 02O5 and 01YH. Module Sheaf.AlgebraicGeometry.IntegralIdealProperCohomology;
one remaining sorry. This proves finiteness for filtration factors, not for arbitrary
coherent modules, and the assigned module performs the passage to arbitrary modules.

lem-pc-e2-cohomology-finite-extension: fixed-degree finiteness under short exact extensions
with restricted scalars. Module Sheaf.AlgebraicGeometry.CohomologyFiniteExtension; proved.
No existing module, definition, statement or interface was adapted, so no change record
or forced adaptation is required.

## Second reading by E2

1. Compared the assigned module with the repository using diff, and checked the declaration
   signatures with stage3_delivery.diff_module: no statement_changed entries. The only original
   hole closed is AlgebraicGeometry.Scheme.Modules.finite_sections_higherDirectImage. Existing
   definitions, signatures, visibility and docstrings are byte-for-byte unchanged. The three
   other delivered modules are new. No target statement or change record is involved. Verdict: pass.

2. Compiled all four modules in import order through lcompile.py, without errors or warnings.
   Scanned the sources: exactly the two reported named theorem sorries, no definitions containing
   sorry, and no axiom, unsafe, opaque, implemented_by or extern. Scratch-copy #print axioms
   checks cover both structures and all five existing theorems in the assigned module and each
   new theorem. finite_H_of_shortExact uses only propext, Classical.choice and Quot.sound;
   the two open inputs and the existing theorems depending on open inputs additionally use
   sorryAx, with no other axiom. The main proof obtains filtration witnesses only inside a
   theorem proof; it creates no definition by choosing an arbitrary unproved witness. Verdict: pass
   as a decomposition (one original hole closed, two holes added), not an unconditional proof.

3. Read the two split statements hypothesis by hypothesis against Stacks
   [01YF](https://stacks.math.columbia.edu/tag/01YF),
   [01YH](https://stacks.math.columbia.edu/tag/01YH), and
   [02O5](https://stacks.math.columbia.edu/tag/02O5). Finite presentation already implies
   quasi-coherence by the Mathlib instance in Sheaf/Quasicoherent.lean; on a Noetherian scheme
   it gives the coherent input of 01YF. IdealSheafData specifies a quasi-coherent ideal,
   which is coherent on the Noetherian closed subscheme Z. The induced base action is explicitly
   Module.compHom along f.appTop.hom. Checked zero F (m = 0), empty X (only the zero module),
   zero I, integral Z nonempty, q = 0, and the need for Noetherian R in the extension step.
   The integral-factor induction must prove all degrees together: degree q - 1 controls the
   left term, with zero preceding degree-zero cohomology, and degree q + 1 controls the right
   term. Both new holes are strictly smaller inputs, not renamed copies of the target.
   Fresh LeanFinder and Loogle queries with different wording and Mathlib/library rg searches
   yielded no applicable replacement. Read the stronger existing coherent filtration module;
   import_direction.py confirms importing it here creates a cycle through FiniteFreeComplex.
   ProjectiveSpace.finite_H and finite_H_of_isClosedImmersion remain the independent
   projective-space route below the integral factor; the projective higher-image theorem uses
   this proper theorem and cannot be used to prove it. Each hole has its source, proof in words
   and node. Neither geometric hole is a few-minute closure. Verdict: pass.

4. Read the main proof from the target down: Noetherianity from properness over the affine
   Noetherian base; zero cohomology; linear transport under H.mapLinearEquiv; Fin.induction
   over the actual subobjects; short exact inclusion/cokernel sequences; quotient-factor
   transport; top-subobject transport; and the bijective semilinear affine comparison made
   linear by restriction of scalars. The proved extension lemma uses exactness in the middle
   and Mathlib submodule finiteness, without requiring surjectivity on cohomology. Restored
   the original assigned-module docstring, made LongExact proof-only in the new extension
   module, and removed its redundant Finsupp import. The original four proof-only imports
   remain used by the previously completed finite-free-model and perfect-locus arguments.
   Added an exhaustive list of removed old proof_deps to No longer needed; no global module
   pruning is claimed. Read dag/units/sk-thm-picard-coherence.json: its proper-coherence and
   projective-space route is retained below the new inputs. Its realized fields were already
   empty and remain untouched; this delivery does not claim to repair that bookkeeping.
   Verdict: pass.

5. Checked the node JSON against all four Lean modules. All three new lean.statement fields
   match their theorem signatures verbatim. The existing node changes only proof, proof_deps
   and proof_origin. New nodes have chapter/unit, split status, source, created, blueprint,
   Lean record, proof steps and logged Mathlib searches. Checked proof_deps equals the union
   of proof-step uses. Added the LongExact node lem-pc-euler-additive to the integral-factor
   argument so its all-degree two-out-of-three step is recorded explicitly. Verdict: pass.

Second reading changed only import visibility/removal in CohomologyFiniteExtension, restored
the existing assigned-module docstring, added source/blueprint metadata to new module
docstrings, clarified the integral-factor induction in its docstring and node, and completed
the pruning report. No theorem statement or definition changed; no additional hole was closed
or added by the second reading.
