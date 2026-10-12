## What changed

Changed `lean/Sheaf/AlgebraicGeometry/FlatBaseChangeResolutionIso.lean` to prove
`AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolutionBeta_isIso`, with its signature
and existing docstring unchanged. The proof imports the separated scalar-extension comparison,
Mayer–Vietoris gluing, quasi-coherence of pullback, and the new affine-section dictionary.
All added imports are proof-only; the existing public imports are unchanged.

The private proved helper `AlgebraicGeometry.flatCohomologyBaseChange_bijective` proves
bijectivity of the canonical `H.baseChange` over arbitrary commutative rings and flat algebras.
It uses compact-open induction with an invariant quantified over open immersions and all
quasi-coherent coefficients. The overlap with the newly adjoined affine open is compact
and separated, and is not assumed affine. The original theorem constructs a basis of affine
opens lying over affine base opens, applies this helper, uses the local dictionary, and
proves global invertibility with Mathlib's abelian-sheaf basis criterion and the
module-sheaf component criterion.

Added `lean/Sheaf/AlgebraicGeometry/FlatBaseChangeResolutionAffineSections.lean` and its
node. The remaining statement is an equivalence between bijectivity on one affine open
and bijectivity of the explicitly specified scalar-extension cohomology map. It asserts
neither global invertibility nor bijectivity of either map. Updated the item's node to
follow the compiled induction and basis argument.

Sources read online: [Stacks 02KH](https://stacks.math.columbia.edu/tag/02KH), including its
Mayer–Vietoris alternative and its reduction of (1) to (2);
[02N7](https://stacks.math.columbia.edu/tag/02N7) for the actual augmented resolution map;
[01XK](https://stacks.math.columbia.edu/tag/01XK) for affine sections of higher images;
and [03FD](https://stacks.math.columbia.edu/tag/03FD) for module/abelian cohomology agreement.
The local Stacks source checkout is absent on this machine, so these were read online.

The separated and gluing nodes `lem-pc-flat-cohomology-separated` and
`lem-pc-flat-cohomology-gluing` are generic tools from the Picard-framework unit. They
supply the scalar-extension argument, rather than replacing any realized step of
`sk-thm-p1`. No unit's statement or realized proof step is bypassed or modified.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolutionBeta_isIso`
(node `lem-weil-pbc-flat-base-change-resolution-iso`). There are no sorries in the item's
module, including its private helper.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolutionBeta_affine_bijective_iff`
(node `lem-weil-pbc-flat-base-change-resolution-affine-sections`), in the new module.
Its entire proof is `by sorry`; its docstring and node give the proof and sources.

This is a decomposition: one original hole closed, one strictly local comparison hole
added, for a nominal net zero. It is not a claim that flat base change is now axiom-free.
The qcqs induction and local-to-global detection are complete Lean proofs from the
existing named statements. Their inherited proof dependencies have not been proved here.

The two modules compile together without warnings with `lcompile.py --all`.
The delivery dry run could not reach preflight: `deliver3.py` failed in
`check_import_sources` with `ImportError: cannot import name refuse_missing from
import_cycles`, resolving that module to the repository tools/import_cycles.py.
That tools module lacks the requested function. No tool was edited or bypassed, and
nothing was pushed.
Edge cases checked in the argument: the empty source is the induction's base case;
the zero coefficient and degree zero are covered by the separated/gluing statements;
if the affine target open is empty, its section ring is zero, the tensor product is zero,
and both local groups are zero. The local dictionary imposes no separatedness on the
source of the affine-local map. No object is defined by choosing an arbitrary witness
from an unproved existence theorem.

## No longer needed

No existing import was removed. No whole module is claimed to be removed from the targets'
import closure.

The original direct proof dependencies no longer used directly are:

- `pqf-def-cohomology` / `Sheaf.Paper.PQFCohomology`: its general derived-category
  identification is not used by the induction or basis detection. The existing definitions
  of module cohomology remain in the local dictionary's statement dependencies.
- `lem-pc-flat-tensor-complex-cohom`: no separate direct invocation is necessary; exact
  tensor comparison is already part of the separated cohomology comparison's proof.
  This node remains needed below that comparison and is not pruned transitively.
- `lem-weil-pbc-flat-base-change-map-sections` /
  `Sheaf.AlgebraicGeometry.FlatBaseChangeMapSections`: the existential canonical-map
  package is unnecessary for the given fixed augmented lift. The local dictionary instead
  needs `lem-weil-pbc-flat-base-change-resolution-sections`.
- `lem-weil-pbc-flat-base-change-resolution-independence` /
  `Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionIndependence`: the argument compares
  the given augmented lift on sections directly and does not change resolutions or lifts.

The actual resolution construction remains necessary. No proof-only import added to the
item is unused.

## Where the brief, the DAG or earlier work was wrong

The old proof plan's listed dependencies did not include a theorem identifying the
Ext-based `H.baseChange` with affine sections of the actual module-derived resolution
comparison. `FlatBaseChangeMapSections` supplies the adjoint class formula, not the affine
section-ring tensor and cohomology dictionary. The new node isolates precisely this
additional local step rather than postulating the global isomorphism under another name.

Searches were made through launcher msearch (LeanFinder, Loogle, grep), with direct `rg`
searches of Mathlib, the source library and Sheaf. LeanSearch was attempted for the new
local dictionary and returned Internal Server Error. LeanFinder found underived flatness
and pushforward/pullback statements but no dictionary; Mathlib grep found no matching
statement. `blueprint_refs.py search 02KH` and `02N7` returned no imported blueprint nodes.
The available separated/gluing declarations are more general than the field-extension
wrapper in `EulerChar`, so the proof uses them directly without assuming a field.

No existing definition, public visibility, target signature or module held by another
group was changed. There are no forced adaptations.

## New nodes

`lem-weil-pbc-flat-base-change-resolution-affine-sections`, at
`dag/nodes/sec-proper-base-change/lem-weil-pbc-flat-base-change-resolution-affine-sections.json`,
records the affine-section equivalence in
`Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionAffineSections`. It separates the
identification of the actual map from proving the scalar-extension map bijective and
from detecting global invertibility. Its proof uses ordinary quasi-coherence of higher
images, affine vanishing and the normalized Leray edge, affine pullback sections,
module/abelian cohomology comparison, and the fixed-lift section formula. These are
existing nodes, not duplicate new statements. No change record is needed: every existing
signature and public import is unchanged.

## Second reading by Y3

1. I compared the item module with the repository version. The existing theorem signature and
   docstring are byte-for-byte unchanged; the only changes are proof code and proof-only imports.
   The added affine-section module is a new node and does not alter an existing declaration.
   Verdict: pass.

2. I compiled both modules with `lcompile.py`; they compile without errors or warnings. The item
   theorem has no `sorry`, and the only remaining `sorry` is the named affine-section theorem,
   whose docstring and DAG node give its source and proof. No forbidden declaration or hollow
   definition was introduced. Verdict: pass, with the documented split hole.

3. I checked the affine-section statement against its local edge cases (zero coefficient, degree
   zero, empty opens) and against the fixed-lift map in the item theorem. It is a genuine local
   equivalence and does not restate the item or assert global invertibility. The node records the
   required source, dependencies, proof plan, and Lean declaration. Verdict: pass.

4. The proof follows the shortest available route through the existing separated and
   Mayer–Vietoris comparison lemmas, then the local dictionary, and uses the affine basis
   criterion. The report lists the direct dependencies no longer invoked. The imports added to
   the item are proof-only, and no unused import was found. Verdict: pass.

5. The item node's proof and `proof_deps` match the private induction, affine local reduction,
   and basis argument in the Lean source. The new node's proof plan matches its remaining
   theorem. The realized unit route through separated comparison, gluing, and affine reduction
   is retained. Verdict: pass.

I changed only this report section after the initial worker delivery; no Lean or DAG content was
altered during second reading.
