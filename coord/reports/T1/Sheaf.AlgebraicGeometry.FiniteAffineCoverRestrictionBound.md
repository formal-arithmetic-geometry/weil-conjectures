## What changed

Replaced the supplied strong-induction wrapper and undelivered
`subsingleton_H_of_affine_local_acyclic_step` with a real induction in
`Sheaf.AlgebraicGeometry.FiniteAffineCoverRestrictionBound`.
The existing theorem signature, original docstring, and public import are unchanged.
The proof now quantifies inductively over both schemes, the separated morphism,
the inverse-image morphism, the module sheaf and the local hypothesis.
It proves the affine base case using `upperStarComp`, the pullback condition,
`pullback_forget_modules_iso`, `Sheaf.H.map` and `cohomologyMap_bijective`.
In the successor case it constructs and verifies the smaller affine covers of
V and U intersection V, including separated affine intersections, and invokes
induction on those open schemes. Only open-restriction inheritance and two-open
Mayer--Vietoris vanishing remain split off into their own new modules.

Added plain proof imports for `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
`Sheaf.AlgebraicGeometry.EtalePullbackForgetModules`,
`Sheaf.AlgebraicGeometry.AffineLocalAcyclicOpenRestriction`, and
`Sheaf.AlgebraicGeometry.EtaleMayerVietorisModuleVanishing`.
The new modules publicly import only the definitions and instances their signatures
need. No published statement or definition changes; no change record is required.

## Proved and sorry left

Proved the original module's one theorem,
`AlgebraicGeometry.Etale.subsingleton_H_of_affine_local_acyclic`, by the real
base-case and successor induction. Its proof depends on the two explicitly open
lemmas below, so it is not yet an axiom-clean completed target.

The delivery leaves exactly two named theorems with `:= by sorry`, both in new modules:

- `AlgebraicGeometry.Etale.affine_local_acyclic_open_restriction`, in
  `Sheaf.AlgebraicGeometry.AffineLocalAcyclicOpenRestriction`, node
  `lem-weil-pbc-affine-local-acyclic-open-restriction`.
- `AlgebraicGeometry.Etale.subsingleton_H_of_two_open_pullback_cover`, in
  `Sheaf.AlgebraicGeometry.EtaleMayerVietorisModuleVanishing`, node
  `lem-weil-pbc-etale-mayer-vietoris-module-vanishing`.

Neither lemma restates the finite-cover bound: the first only transports a local
hypothesis under one open restriction; the second only uses three adjacent groups
in a two-open exact sequence, without an affine cover or an induction hypothesis.
Each carries its source, complete proof in words, and matching DAG node.

All three modules compile locally without errors or warnings. Explicit
`#print axioms` checks in a scratch copy report only `propext`, `Classical.choice`,
`Quot.sound` and the recorded `sorryAx` dependencies.

## No longer needed

No original public import or published declaration is removed. The undelivered
`lem-weil-pbc-finite-affine-cover-restriction-bound-step` and its theorem were removed
from this sandbox: the whole argument had been delegated to them, so that split
was not accepted as progress.

Of the original parent node's four proof dependencies:

- `lem-weil-pbc-inverse-image-composition` remains directly used in the affine base case.
- `lem-weil-pbc-separated-affine-open-intersection` remains directly used through
  Mathlib `isAffineHom_diagonal_iff` in the successor case.
- `lem-weil-pbc-etale-mayer-vietoris` is no longer a direct parent dependency;
  it remains a dependency of the new two-open vanishing lemma.
- `lemma-weil-pbc-leray-acyclicity` is no longer used by this argument. The precise
  bridge `lem-weil-pbc-sheafH-ext-derived-comparison` belongs to the two-open lemma
  instead. This removes that direct dependency; it makes no claim that the Leray
  module is unreachable from every other target.

No existing module is claimed globally pruned. The unit `sk-thm-p1` and its
`realized` routes stay exactly as read; this is a reduction below the unit level.

## Where the brief, the DAG or earlier work was wrong

The supplied step's `hprev` ranged only over covers of the same X, whereas its
natural-language proof applied induction to the different schemes V and U intersection V.
It also retained the entire finite-cover conclusion as one open obligation,
including its base case. Its earlier report incorrectly attributed composition,
intersection, Mayer--Vietoris and Leray applications to the parent Lean proof,
which only applied the open step theorem. The replacement exposes the actual
base case and geometry in Lean and splits only the two missing comparison/gluing facts.
The original parent docstring was unnecessarily shortened; restored it verbatim.

Read the proof of Stacks Tag 0A51: its local acyclicity input is made explicit here,
so its final Mayer--Vietoris argument applies to arbitrary i and module sheaves,
without importing the closed-immersion/injective/torsion assumptions needed to
establish that local input in Stacks. Also inspected existing EtaleMayerVietoris,
EtaleMayerVietorisPullback, Ext/derived comparison, module-forgetting and inverse-image
composition modules. None has either new lemma's exact signature.

LeanSearch was genuinely attempted twice and returned Internal Server Error;
recorded as unavailable. LeanFinder, Loogle, msearch grep, local `rg`, and upstream
source searches were performed. Results are in the nodes and searches.jsonl;
no failed service is treated as evidence of absence.

## New nodes

`lem-weil-pbc-affine-local-acyclic-open-restriction` isolates transport of the
local affine vanishing hypothesis to an open subscheme. Its proof uses the
isomorphism onto an open image, the pullback universal properties, inverse-image
composition, module-forgetting, and cohomological invariance under a scheme
isomorphism. Its module is `AffineLocalAcyclicOpenRestriction.lean`.

`lem-weil-pbc-etale-mayer-vietoris-module-vanishing` isolates the two-open exact
segment and the coefficient/base-change identifications. Its proof uses open
base change and image isomorphisms, inverse-image composition, module-forgetting,
Mayer--Vietoris and the exact Ext/derived comparison. Its module is
`EtaleMayerVietorisModuleVanishing.lean`.

No change records: all declarations already in the repository retain their signatures.

## Second reading by T1

1. Compared the delivered parent module with the repository using `diff`, then
   compared the complete existing theorem signature as raw text: byte for byte
   identical. Restored the existing docstring verbatim. There are no definition
   changes or changes to public imports. The rejected step was new, unpublished
   work; its removal changes no existing interface. Verdict: pass after repair.

2. Compiled all three delivery modules through lcompile in import order, with
   no errors or warnings. Scanned every delivered Lean file: exactly the two
   named split theorems contain sorry; there is no sorry in a definition and
   no axiom, unsafe, opaque, implemented_by or extern. Scratch-copy
   `#print axioms` checks for the parent and both helpers show only permitted
   axioms and recorded sorryAx. Verdict: a valid partial reduction, not a claim
   that the final target is free of open dependencies.

3. Checked the new restriction theorem against its image/pullback description:
   O is an affine open of W, its image is an affine open of X, and the nested
   pullback coefficient expression is exactly the restriction of the original
   inverse image. Checked W empty, W = top, O empty, and arbitrary i.
   Checked the new gluing theorem against the exact segment at r+1: both opens
   vanish in r+1 and the intersection in r, including r = 0. Repeated or empty
   opens remain valid; no degree-zero bound without its intersection hypothesis
   is asserted. Searched with different phrases and inspected the existing
   library lemmas; no exact duplicate was found. Verdict: both statements are
   true, useful strict parts of the argument, and have complete docstrings and nodes.

4. The parent now implements the shortest elementary cover induction found:
   an actual affine base case and the Mathlib geometric cover operations, with
   no full induction-step restatement. Its IH generalizes the schemes and sheaf,
   so the two recursive uses on V and U intersection V are legitimate.
   The inequalities n+1 < r+1 imply n < r as required for the intersection.
   Every added parent import is used solely by its proof and is plain `import`.
   The No longer needed section accounts for all four old proof dependencies,
   including the now-unused Leray dependency. Read `dag/units/sk-thm-p1.json`:
   its statement and all realized steps are preserved. Verdict: pass after repair.

5. Rewrote the parent proof plan, proof_deps and proof_origin to describe the
   actual Lean induction. Both new nodes introduce their objects, match the Lean
   signatures and have proof_deps equal to the union of step uses, source/search
   records, creation metadata, and the parent's chapter/unit. Neither has a
   reverse statement dependency on the parent. Verdict: pass after repair.

Changed in this reading: replaced the unsuitable fixed-X induction wrapper with
actual generalized induction, proved the affine base case and the geometric cover
steps, replaced the whole-step sorry with two narrower helper theorems in new
modules, restored the original docstring, corrected the nodes and pruning record,
and rewrote this report to distinguish proved reductions from open dependencies.
