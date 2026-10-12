## What changed

Changed only the proof of `AlgebraicGeometry.universallyClosed_of_fpqc_cover` in
`lean/Sheaf/AlgebraicGeometry/UniversallyClosedOfFpqcCover.lean` and added the private
proof import `Mathlib.AlgebraicGeometry.Morphisms.FlatDescent`. The signature, docstrings,
and existing public imports are unchanged.

The proof follows the existing five-step DAG plan. It specializes the already proved
`AlgebraicGeometry.fpqc_local_on_base_criterion` to `@UniversallyClosed`. Mathlib's
`universallyClosed_isZariskiLocalAtTarget` instance supplies the locality and isomorphism
invariance. `MorphismProperty.pullback_snd` supplies arbitrary base-change stability,
which implies the requested flat base-change stability. For affine source and target,
Lean infers `IsAffineHom g` and hence `QuasiCompact g`. The single-map descent instance
`descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`, applied through
`MorphismProperty.of_pullback_snd_of_descendsAlong`, then supplies affine descent.

Searches using LeanFinder, Loogle, the launcher grep search, and rg of both library roots
and Mathlib found the single-map descent instance and universal-closedness property
instances. The existing criterion provides exactly the remaining covering-family argument.
The unit `sk-thm-p1` realized statements and steps are unchanged; no alternate unit route
is used. No node update is needed because the proof follows the recorded route and uses
all of its mathematical dependencies.

The local single-file compile passed without warnings. The delivery dry run performs the
additional axiom probe and preflight. All edits are confined to the prescribed sandbox.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.universallyClosed_of_fpqc_cover`, node
`lem-weil-pbc-fpqc-descend-universally-closed`.

No `sorry` remains in the item's module, and no holes or new declarations were added.
The imported fpqc-local criterion is already proved in this checkout; this is a proof,
not a decomposition into new holed statements.

## No longer needed

None. All existing imports and all six recorded proof dependencies remain needed by the
recorded route. The only additional import supplies Mathlib's affine descent instance.
No new auxiliary modules or nodes are required.

## Where the brief, the DAG or earlier work was wrong

No mathematical mismatch was found. The planned hypotheses match the existing criterion:
isomorphism invariance is encoded with Zariski locality, and affine morphisms supply the
quasi-compactness required by Mathlib's descent instance. The statement keeps arbitrary
index universe `v`, with no nonemptiness assumption; empty-base and empty-family cases
are handled by the existing criterion without additional hypotheses.

The local literature directory contains citation tables but not `descent.tex`; this
proof implements the existing source-backed node plan using the declarations and their
signatures, rather than creating an alternative argument or any source-dependent holes.


## Second reading by Q3

1. PASS: Compared the delivered module with the repository using `diff -u`. The only
   changes are the proof body and the plain import of `Mathlib.AlgebraicGeometry.Morphisms.FlatDescent`.
   The existing theorem signature and docstrings are byte for byte unchanged; no definition,
   public import, or other declaration changed. The arbitrary family universe and all
   hypotheses, including the fpqc membership and universally closed second projections,
   remain exactly as recorded by the node.
2. PASS: Compiled the delivered file through `lcompile.py` without errors or warnings.
   Read the whole proof and scanned for forbidden declarations and `sorry`: none occur.
   Compiled a scratch copy with `#print axioms AlgebraicGeometry.universallyClosed_of_fpqc_cover`;
   the result is exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
   There are no definitions or witness choices in this delivery.
3. PASS: No statements were split off and no new declarations or nodes were introduced.
   Read the criterion, the six recorded dependency nodes, and the Mathlib descent lemma.
   The affine obligation assumes both schemes affine, so `isAffineHom_of_isAffine` and
   the affine-to-quasi-compact instance supply precisely the third conjunct of the descent
   condition. The argument adds no hypothesis on the original source, covering family,
   or its index type. Identity covers and empty targets/families require no extra assumption;
   the criterion retains their cases.
4. PASS: Independently searched both Lean library roots for universal-closedness descent
   and read Mathlib's `FlatDescent`, `UniversallyClosed`, `Affine`, and morphism-property
   descent declarations. The available descent instance is for a single morphism, so
   the already proved covering-family criterion is the appropriate short reduction.
   `pullback_snd` supplies the flat-base-change obligation; Zariski locality and its
   isomorphism invariance are inferred; `of_pullback_snd_of_descendsAlong` has exactly
   the required projection orientation. Both plain proof imports are used. The existing
   public imports supply the statement vocabulary. None of the six old dependencies
   is bypassed, so `No longer needed: None` is complete. Read `sk-thm-p1.json` including
   `realized`: its statement and all steps are preserved by this work below the unit level.
5. PASS: Read `lem-weil-pbc-fpqc-descend-universally-closed.json`, its `proof`,
   `proof_deps`, `proof_origin`, and the dependency declarations. The five recorded steps
   match the specialization of the criterion and its inferred/explicit obligations.
   The definition node for fpqc coverings accounts for `hg`. No node update is required;
   no new-node field requirements apply.

Changed only this report by adding the independent second reading. No Lean repair was needed.
