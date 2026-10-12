## What changed

The two original public signatures and instance attribute are unchanged.
`CategoryTheory.affineTildeSheaf_preservesZeroMorphisms` is proved using
Mathlib `tilde.map_zero`.
`CategoryTheory.affinePseudoCoherentRHomQuasiCoherent` now compiles without a local
sorry, from the existing finite-free derived-Hom computation and one new model
preparation theorem, `CategoryTheory.affineFiniteProjectiveHomModel`.

The preparation theorem supplies bounded finite-free sheaf models and ordinary
Hom-complex comparisons; it does not assert the item's derived internal Hom
comparison, quasi-coherence, or derived lower-bound conclusion. The item's proof
applies `AlgebraicGeometry.derivedInternalHom_of_boundedAbove_finiteFree`, maps the
coefficient comparison through derived internal Hom, and composes the isomorphisms.
It proves exactness of tilde using the affine adjunction and injectivity of module
localization, then proves quasi-coherence through the homology comparison. Finally,
it proves that the Hom product factors vanish below a-b, deduces strict boundedness,
and transports the derived bound. These are proved private helpers, without holes.

Added proof-only imports:
`Sheaf.AlgebraicGeometry.AffineFiniteProjectiveHomModel`,
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree`, and
`Sheaf.Topology.RingedSpaceModuleCohomology`. The last supplies the shared-carrier
Gamma functor needed to type the affine adjunction; no cohomology theorem from it
is used. Existing public imports are preserved.

The new model statement handles cohomologically bounded-below l by good truncation
before using finite Hom products. Its edge cases include zero complexes, zero-rank
terms, and the empty spectrum. No data definitions or public interfaces changed.

Validation: the preparation module compiled, and the complete item compiled cleanly
in 38.4 seconds through lcompile.py. Generalizing the private product argument to
an abstract ringed space avoids repeated unfolding of Spec R during elaboration.
The sandbox DAG copies follow the implemented route. The unit's realized lists are
empty, and its fixed statement and route are unchanged.

## Proved and sorry left

Original holes closed (2):
- `CategoryTheory.affineTildeSheaf_preservesZeroMorphisms`
  (node `lem-sc-affine-pseudo-coherent-rhom-qcoherent`): a direct proof, no new hole.
- `CategoryTheory.affinePseudoCoherentRHomQuasiCoherent`
  (same node): a decomposition through the new preparation theorem and the existing
  finite-free model theorem, with the assembly, quasi-coherence, and lower-bound
  arguments proved here.

New holes added (1):
- `CategoryTheory.affineFiniteProjectiveHomModel`
  (node `lem-sc-affine-finite-projective-hom-model`), in
  `lean/Sheaf/AlgebraicGeometry/AffineFiniteProjectiveHomModel.lean`.

No sorry remains in the assigned module. Net textual holes closed minus added is 1;
this is not a claim that the main theorem is axiom-free, since its new preparation
and existing finite-free model dependency still have sorry.

## No longer needed

Removed proof-only import `Sheaf.Paper.AffineProjectiveComplexDerivedHom`.
Its node `lem-sc-affine-projective-complex-derived-hom` is not needed by this route;
its one-point-site module statement is replaced, in preparation, by Mathlib's
bounded-above K-projectivity theorem. No claim is made that other consumers cease
to need that module. All other original proof dependencies remain used, either
in the item or in preparation; no additional modules are proposed for pruning.

## Where the brief, the DAG or earlier work was wrong

The original plan treated its finite-projective and one-point-site statements as
though they could be directly composed. Their Lean interfaces do not supply the
finite-free replacement, the truncation comparison for an arbitrary representative
l, or the ordinary sheaf/module Hom-complex comparison. Those missing preparation
steps are now stated together in the new node, and the rest of the plan is in Lean.

The checked source for the finite-projective sheaf Hom calculation is Stacks
Tag 08I5, which Tag 0A6H explicitly cites. Tag 0GM8 is a stalk comparison and is
not itself that calculation. The existing finite-free-model dependency's citation
has that imprecision; its statement is usable and was not changed. Sources were
read at https://stacks.math.columbia.edu/tag/0A6H,
https://stacks.math.columbia.edu/tag/064U, and
https://stacks.math.columbia.edu/tag/08I5 because the literature source files are
not materialized in this clone.

## New nodes

`lem-sc-affine-finite-projective-hom-model`:
`CategoryTheory.affineFiniteProjectiveHomModel`, a single new module containing one
public named theorem with a complete preparation proof in its docstring. It packages
complementary-projective replacement, good truncation, K-projective Hom comparison,
and the finite-product termwise tilde/sheaf Hom identification. It is strictly before
the derived internal Hom computation; the original module performs that computation
and proves its quasi-coherence and boundedness consequences. LeanSearch was attempted
and unavailable, LeanFinder returned K-projectivity tools but no preparation theorem,
and Mathlib/source, Sheaf, DAG, and blueprint searches found no matching statement.
No change records or forced adaptations are needed.

## Second reading by T1

1. Compared the delivered affine RHom module with the repository version. The
   two existing theorem signatures and the zero-morphism instance are unchanged;
   the only interface addition is the separately documented preparation node.
   Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. The item compiles
   cleanly; the sole remaining `sorry` is the named preparation theorem, with
   its matching node. No unsafe declarations, hollow definitions, or extra
   axioms were found in the changed files. Verdict: pass.
3. Checked the preparation statement against the finite-free replacement,
   truncation, and finite Hom-complex argument. Its hypotheses and conclusion
   are strictly preparatory and do not restate the target; edge cases such as
   zero complexes and rank-zero free terms are covered by the formulation.
   Searches recorded in `searches.jsonl` found no existing declaration.
   Verdict: pass.
4. Checked the proof route top-down. It uses the existing finite-free derived
   Hom theorem, the affine tilde exactness argument, and the new preparation
   theorem; the obsolete one-point-site import was removed. The unit statement
   and route remain unchanged. Verdict: pass.
5. Checked the DAG copies: proof steps and `proof_deps` match the imports and
   theorem applications, and the new node has the required source, searches,
   Lean record, and split status. Verdict: pass.

Changed only the sandbox report during this second reading; no proof repair was
needed after compilation.
