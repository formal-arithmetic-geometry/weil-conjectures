## What changed

Proved the existing support-reduction theorem by a local well-founded induction on closed
support. The empty-support branch detects zero on stalks and uses a length-zero filtration.
The reducible branch concatenates filtrations of the smaller-support submodule and cokernel.
The irreducible branch passes the smaller-support induction hypothesis to the new irreducible
step. Finally every factor is placed in the integral-ideal disjunct. The existing theorem's
signature is byte for byte unchanged. No existing public import, definition, or visibility changes.

The second reader replaced the cyclic J-adic and generic imports by the new module
`Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationIrreducibleSupport`. It states just the
irreducible-support induction step, with an explicit smaller-support hypothesis. Removed the
unpublished `CoherentIntegralFiltrationGenericAnnihilated` module and node, whose proof in
words silently needed that hypothesis. The new reducible-support exact-sequence module stays.
The item's original docstring proof was updated to describe the actual stronger induction.
An obsolete change record for private helpers was removed: no existing interface changes.

## Proved and sorry left

Closed the one original named hole:
`AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_support_reduction_filtration`
(`lem-pc-s3-support-reduction-filtration`). No local sorry remains in the item.

Added exactly two named holes, each in its own new module:

- `AlgebraicGeometry.Scheme.Modules.exists_coherent_submodule_of_reducible_support`
  (`lem-pc-s3-coherent-reducible-support-exact-sequence`).
- `AlgebraicGeometry.Scheme.Modules.coherentIntegralFiltration_of_irreducible_support`
  (`lem-pc-s3-irreducible-support-filtration-step`).

This is a decomposition: one hole closed, two holes added, net -1 locally, with no claimed
net proof progress in the targets' closure. The stronger local induction is assembled from
strictly smaller cases, rather than applying a renamed copy of the item. The proof also uses
existing declarations for coherence/finite-type equivalence, closed support, coherent extension,
and coherent zero-object/iso closure; their import closures may still use sorryAx. Compilation
and the axiom probe do not establish an axiom-free proof of the whole target closure.

## No longer needed

Removed the six original private proof imports:

- `Sheaf.Algebra.Homology.ModuleStalkExact`.
- `Sheaf.AlgebraicGeometry.ClosedPushforwardStalks`.
- `Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.IdealModuleProductStalk`.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`.
- `Sheaf.CategoryTheory.FiniteFiltrationRefinement`.

All original direct node proof dependencies no longer used directly are listed below. Several
remain in the lower steps' proof plans; this list claims no global unreachability:

- `def-pc-integral-scheme`.
- `def-weil-closed-immersion`.
- `def-weil-irreducible-components`.
- `lem-pc-s3-finite-filtration-refinement`.
- `lem-weil-pbc-basic-open-function`.
- `lem-weil-pbc-closed-immersion-coherent-equivalence`.
- `lem-weil-pbc-closed-pushforward-stalks`.
- `lem-weil-pbc-coherent-generic-point-ideal-inclusion`.
- `lem-weil-pbc-coherent-kernel-cokernel-locnoeth`.
- `lem-weil-pbc-coherent-support-power-ideal-kills`.
- `lem-weil-pbc-coherent-support-union-exact-sequence`.
- `lem-weil-pbc-ideal-module-product-stalk`.
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`.
- `lem-weil-pbc-immersion-base-change-lft`.
- `lem-weil-pbc-module-iso-on-stalks`.
- `lem-weil-pbc-module-stalk-exact`.
- `lem-weil-pbc-reduced-induced-closed-subscheme`.
- `pqf-lem-locnoeth-lft`.

The attempted imports of `CoherentFiltrationIntegralSubschemes`,
`CoherentIntegralFiltrationAdicReduction`, and `CoherentIntegralFiltrationGenericStep` are
absent because their source dependencies return to this item. The unpublished generic-case
module is also absent. No module is claimed to be globally pruned. The three original public
imports are retained. Scheme sobriety remains an explicit direct node dependency.

## Where the brief, the DAG or earlier work was wrong

Compiled caches hid source cycles: J-adic reduction reaches this item via
CoherentSupportPowerIdealKills, CoherentFormalModule, ModuleSupportProperOverBase,
ClosedImmersionPushforwardAnnihilated, AffinePushforwardBaseChange, the affine direct-image
modules, and FinitePresentationIntegralFiltration. GenericStep also returns through
CoherentGenericPointClosedDescent and that affine route. These imports cannot be delivered.

The earlier generic-annihilated split had no smaller-support hypothesis, though its proof
in words invoked a filtration of its smaller-support cokernel. The replacement gives the
precise combined irreducible step with that hypothesis, a complete source-based proof in
words, and its own node. It asserts neither the empty case nor the reducible case.
The prior report incorrectly described two added holes as one, repeated historical reading
sections, and named the obsolete generic node repeatedly. All are corrected here.

The sources were checked directly against Stacks Tags 01YD and 01YF. Independent searches
used LeanFinder for closed-cover coherent decompositions and irreducible filtration,
Loogle for IsGenericPoint, Mathlib grep, and project source searches. Existing generic-step
and support-union results were found and read, but their modules have cyclic import routes.
No duplicate signature was introduced. The unit `sk-thm-picard-coherence` has empty realized
statement and step arrays; the unit's route is unchanged.

## New nodes

`lem-pc-s3-coherent-reducible-support-exact-sequence` is the reducible-support exact-sequence
step from Tags 01YD and 01YF. It asserts coherence, short exactness, and strict support
containment only, with no filtration or support induction.

`lem-pc-s3-irreducible-support-filtration-step` combines the J-adic and generic-inclusion
paragraphs of Tag 01YF with the explicit smaller-support induction hypothesis. Its proof
plan names the existing J-adic and generic-step nodes, while its Lean statement does not
import their cyclic modules. No change record is required for these new statements.

## Second reading by P3

1. Compared the existing delivered module against the repository with diff and checked the
   target signature byte for byte. It is identical. Public imports and existing visibility
   are identical; no definitions or target statements are altered. Verdict: pass.
2. Compiled all delivered modules through lcompile.py in import order. All holes are whole
   proofs of the two named public split theorems; there is no sorry in data or definitions
   and no forbidden declaration mechanism. The explicit axiom check and delivery probe
   check the item and both split declarations: each reports only propext, Classical.choice,
   Quot.sound, and sorryAx. Verdict: pass with the two reported holes.
3. Read both split statements and their proofs in words against Tags 01YD/01YF and searched
   independently. Reducible support excludes empty/singleton cases; zero exact-sequence
   terms are allowed. The irreducible step assumes a generic point, hence nonempty support;
   zero graded terms and exponent zero have length-zero filtrations. Proper graded supports
   and the generic cokernel use exactly the explicit hsmaller. Neither lemma restates the
   whole item. Verdict: pass after replacing the unsupported generic-case decomposition.
4. Checked the route from the target downward, the original proof dependencies, the public
   import boundary, and the unit's realized record. Existing shorter full-filtration,
   support-union, J-adic, and generic routes were examined but create source import cycles.
   Unused imports and every removed original proof dependency are listed. Verdict: pass.
5. Read all delivered nodes alongside Lean. Corrected the stale generic dependency in the
   item node, recorded the irreducible step's actual hypotheses and verbatim Lean signature,
   and checked proof_deps equals the union of proof-step uses. Verdict: pass.

Changes by this reader: removed cyclic imports; replaced the unpublished generic-case hole
by the precise irreducible-support induction step; corrected the item docstring and DAG;
removed the obsolete change record and unnecessary global ZeroObject opening; rewrote the report with accurate 1-closed/2-added counts.
