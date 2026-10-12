## What changed

Replaced the sorry in `AlgebraicGeometry.koszulRegularImmersion_algebraDual`
with a compiling proof from two proper parts of its argument:

- `Sheaf.AlgebraicGeometry.KoszulRegularImmersionAlgebraDualHomology` computes
  the algebra-module **cohomology sheaves**, one integer degree at a time.
  It makes no derived-object comparison or claim that cohomology maps lift.
- `Sheaf.AlgebraicGeometry.ClosedImmersionRankedCohomologyReconstruction`
  reconstructs an arbitrary derived algebra-module from the specified finite
  rank-stratified cohomology pattern. Its module M is arbitrary; it has no
  regularity, conormal-rank, Noetherian, or scalar-adjunction hypotheses.

The item's Lean proof establishes compactness of Z using the closed embedding
into compact Y, proves `(Set.range r).Finite` by `LocallyConstant.range_finite`,
obtains the cohomology pattern degreewise, and applies the reconstruction theorem.
Existing signatures, universes, visibility, definitions, and public imports are
unchanged. Only plain proof imports are replaced in the existing module.
Each new module contains one public theorem, with its full proof in words and
exactly `:= by sorry`; there is no new definition or chosen witness.
The parent node now records these two steps and the proved finite-image step.

All three modules compile together through `lcompile.py --all`.
`deliver3.py V2 Sheaf.AlgebraicGeometry.KoszulRegularImmersionAlgebraDual --no-push`
reported OK: compilation and preflight passed except for the second reading,
which belongs to the next worker. Nothing was pushed.
Edge-case review:
empty Z gives a zero algebra and zero objects; rank zero gives a degree-zero
structure-sheaf comparison; negative degrees vanish; varying ranks split using
idempotents of i_* OZ, without treating the rank images as opens in Y.
For reconstruction arbitrary M is allowed because direct image for a closed
embedding is exact on all sheaf modules, not just quasi-coherent modules.

## Proved and sorry left

Holes closed: `AlgebraicGeometry.koszulRegularImmersion_algebraDual`
(node `lem-sc-koszul-regular-immersion-algebra-dual`), 1 of 1 in the item.
No sorry remains in the item's module.

Holes added:

- `AlgebraicGeometry.koszulRegularImmersion_algebraDual_homology`, node
  `lem-sc-koszul-regular-immersion-algebra-dual-homology`.
- `AlgebraicGeometry.closedImmersion_rankedCohomology_reconstruction`, node
  `lem-sc-closed-immersion-ranked-cohomology-reconstruction`.

This is a **decomposition**, not a completed axiom-free Koszul duality proof:
one upper hole closes and two strictly narrower lower holes are added
(net holes closed minus added = -1 before any closure pruning).
The mathematical assembly and the finite-rank-image step are proved in Lean.
The two lower theorems still require proofs; imported existing holes are unchanged.

## No longer needed

Removed from the item's proof imports:

- `Sheaf.AlgebraicGeometry.AffineDerivedCohomology`, node
  `lem-sc-affine-derived-cohomology`: not needed anywhere in this reduction.
  For this closed immersion, the reconstruction argument uses exactness of
  ordinary module direct image, including algebra-valued direct image.
- `Sheaf.AlgebraicGeometry.KoszulRegularClosedImmersionPerfect`, node
  `lem-sc-koszul-regular-closed-immersion-perfect`: not needed anywhere in this
  reduction. The local resolution needed for the cohomology calculation is the
  existing quotient augmentation in `KoszulRegularSequenceDualComplex`;
  global perfectness is not needed.

The other four original proof imports were removed from the parent and retained
as planned dependencies of the new homology theorem; they are **not pruned**:
`Sheaf.RingTheory.KoszulRegularSequenceDualComplex` /
`lem-sc-koszul-regular-sequence-dual-complex`,
`Sheaf.AlgebraicGeometry.AffineDerivedHomEvaluationCounit` /
`lem-sc-affine-derived-hom-evaluation-counit`,
`Sheaf.AlgebraicGeometry.AffineModuleCorrespondence` /
`lem-weil-pbc-affine-module-correspondence`, and
`Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel` /
`lem-sc-derived-hom-finite-free-model`.
The cohomology calculation additionally names the existing restriction-to-opens
lemma `lem-sc-derived-internal-hom-restrict-open`.
No public import was removed. The two pruned modules may remain reachable from
other targets or imports; this report claims they leave this proof route only.
No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous attempt restated the entire derived comparison for a different
right adjoint and was correctly rejected. Neither theorem here does that:
the first only computes homology objects, and the second assumes that computation
and performs a general rank-stratum reconstruction independent of Koszul duality.
The item has a real proof combining the two, including the finite-image argument.

The original plan's global perfectness theorem asks for neighborhoods of every
point of Y and additional chosen derived categories on opens. Those hypotheses
are not supplied directly by this item and that global conclusion is unnecessary:
use the local quotient augmentation already in the dual-Koszul module.
The affine derived-cohomology theorem is scheme-valued; it does not directly
compute the ringed-space/algebra-valued direct image in this statement. Exact
closed-embedding direct image supplies the reconstruction argument instead.

LeanSearch was unavailable (Internal Server Error). LeanFinder, Loogle, and
Mathlib/library grep produced no exact global cohomology or reconstruction lemma;
Loogle found the standard single-degree t-structure reconstruction used in the
new node's proof plan. Sources were read from the official Stacks pages and
saved only in scratchpad/sources because this clone lacks literature/stacks-project.
The blueprint ancestor helper cannot follow `created.item` recorded as a module
name on the existing parent; new nodes preserve its existing finite-duality
blueprint ancestor and specify their exact place in that calculation.
No interface correction or forced adaptation is made.

## New nodes

`lem-sc-koszul-regular-immersion-algebra-dual-homology` formalizes original steps
1 and 2 plus the gluing of their intrinsic algebra-linear cohomology maps in
step 3. Its conclusion is degreewise cohomology only. The source is Stacks 0BQZ
with the algebra-valued adjunction/action of 0AX3, using the existing local Koszul,
finite-free Hom, open restriction, and affine-module correspondence declarations.

`lem-sc-closed-immersion-ranked-cohomology-reconstruction` formalizes the remaining
part of original step 3: exact closed-embedding direct image, finite orthogonal
rank idempotents, truncation to the one surviving degree on each summand, and
finite-sum assembly. It assumes the cohomology pattern and contains no Koszul or
scalar-adjunction hypotheses. Its proof plan spells out these general steps.
There are no change records because no existing interface changes.

## Second reading by V2

1. **Declarations and statements.** Compared the delivered item module with the repository
   version. The target theorem signature and all existing declarations are unchanged byte for
   byte; only proof imports and the target proof body changed. The two added theorem statements
   match their DAG nodes and are strictly lower-level decompositions.
2. **Compilation and axioms.** Compiled all three delivered modules with `lcompile.py --all`.
   The files compile cleanly. The target has no `sorry`; the only remaining sorries are the two
   named split-off theorems, each public, documented, and represented by a node. No definitions
   contain `sorry`, and no forbidden declarations were added.
3. **Truth and strength of split statements.** Checked edge cases (empty immersion, rank zero,
   negative degrees, and varying finite rank image). The homology theorem asserts only the
   degreewise comparison, while the reconstruction theorem assumes exactly that pattern and
   finite image; neither restates the parent target or weakens it.
4. **Shortest route and pruning.** The target proof uses compactness plus
   `LocallyConstant.range_finite`, then the two strictly simpler split theorems. The old affine
   cohomology and global perfectness proof imports are unused and are removed from the target;
   the remaining dependencies are retained in the homology module. No unit statement or
   realized route step is bypassed.
5. **DAG agreement.** Updated node proof steps, dependencies, origins, and Lean records agree
   with the delivered declarations. Both new nodes carry source locations, searches, chapter and
   unit metadata, and complete proof-plan docstrings in their Lean declarations.

Changed files after this reading: only this report, adding the required review record; no Lean
or DAG repairs were needed.
