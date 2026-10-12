## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence` by a
compiling construction from the ringed-space derived adjunction. The theorem's signature
and definitions are unchanged. The proof lifts the two ambient functors to the full
quasi-coherent subcategories, restricts their adjunction, reflects invertibility through
the inclusions, and takes the inverse of `Adjunction.toEquivalence`.

Scalar restriction is handled in Lean using the existing
`sheafAlgebraRestrictScalars_preservesFiniteLimits` and
`sheafAlgebraRestrictScalars_preservesFiniteColimits` declarations, specialized to
`Under.mk f.c`. The proved source-library exact-postcomposition comparison identifies
`Rg_* ⋙ RT` with `Rf_*`, using the definitional underived composite. This avoids assuming
that `g_*` preserves K-injective complexes. Exact scalar restriction commutes with
cohomology. The affine module correspondence then proves that it preserves
quasi-coherence. Composing the cohomology comparison with
`schemeHigherDirectImage_of_affine` proves that `Rg_*` preserves quasi-coherence too.
All three natural-isomorphism clauses of the target are constructed in Lean.

Two new modules isolate the missing pullback preservation and ambient adjunction-map
invertibility steps. The existing node's proof, proof_deps and proof_origin now describe
the implemented route. No existing statement, definition, public import or target changed.

Validation: all three modules compile together through `lcompile.py --all`, without
warnings. The target uses a scoped heartbeat allowance for elaborating the nested sheaf
category and derived scalar comparisons; its single-file compile stays below 60 seconds.
The source was read at https://stacks.math.columbia.edu/tag/0AVW because the local
`literature/stacks-project/perfect.tex` is absent. Library and DAG searches found no
existing statement for either new intermediate. The Mathlib searches are in searches.jsonl;
LeanSearch returned Internal Server Error and is recorded as unavailable, not no match.

## Proved and sorry left

Closed: `AlgebraicGeometry.finite_affine_derived_equivalence`
(node `lem-sc-finite-affine-derived-equivalence`), one of one original holes.
Its proof contains no sorry.

Added and left: `AlgebraicGeometry.affine_algebra_derived_pullback_preserves_qcoh`
(node `lem-sc-affine-algebra-derived-adjunction-qcoh`) in
`Sheaf.AlgebraicGeometry.AffineAlgebraDerivedAdjunctionQCoh`.

Added and left: `AlgebraicGeometry.affine_algebra_derived_adjunction_isos`
(node `lem-sc-affine-algebra-derived-adjunction-isos`) in
`Sheaf.AlgebraicGeometry.AffineAlgebraDerivedAdjunctionIsos`.

This is a decomposition: one upper hole closed, two strictly smaller holes added,
net holes closed minus added = -1 for the delivered declarations. The mathematical
claims still depend on the named holes in existing imported declarations as well.
The two new statements do not assert an equivalence, construct restricted functors,
or give any scalar comparison; those parts are proved in the target module.

## No longer needed

Removed the redundant direct proof import
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`: its declarations remain necessary
and are already publicly available through `SchemeDerivedDirectImage`. No mathematical
node or module of the original route is pruned from the transitive closure.

The new statement modules contain only the public imports their signatures require;
no unused proof imports of AffineModuleCorrespondence or AffineDerivedCohomology remain
in them. Their DAG proof dependencies retain those genuinely needed mathematical facts.
All proof imports remaining in the target module are used by its proof.

## Where the brief, the DAG or earlier work was wrong

The plan's reference to affine module correspondence supplies an underived equivalence,
not an ambient derived unit/counit theorem. The ringed-space derived adjunction supplies
an ambient left adjoint but does not itself assert preservation of quasi-coherence or
invertibility of its adjunction maps. Those are the precise remaining steps, now isolated.
No statement was found false, and no statement was weakened.

The exactness declarations in DerivedRHomAlgebraModule unnecessarily carry derived-category
instance parameters inherited from their section. Explicit universe specialization and
instance arguments in the proof accommodate their existing signatures without changing
that module. It is used as a generic scalar-exactness tool of this same unit.

The new statements were checked on the identity morphism, the empty source, the zero
complex, degree-zero quasi-coherent modules, affine ring maps B → A, and unbounded objects.
For the identity, the adjunction is transported from identity functors. For the empty
source the algebra is the zero sheaf and its module category is trivial. On affine stalks
A localized at q → A localized at p is a localization, even when B → A is not flat.
Thus no flatness of f, finite hypothesis, Noetherian hypothesis, or boundedness is added.
Arbitrary choices of the left adjoint and adjunction are valid because uniqueness of
left adjoints is compatible with unit and counit and transports their invertibility.

## New nodes

`lem-sc-affine-algebra-derived-adjunction-qcoh` records only preservation of
quasi-coherent cohomology by a left adjoint of the canonical algebra derived direct image.
Its module is `lean/Sheaf/AlgebraicGeometry/AffineAlgebraDerivedAdjunctionQCoh.lean`.
Source: Tag 0AVW, perfect-lemma-affine-morphism-equivalence, exact-localization and
pullback-preservation part of the proof. Its docstring gives the stalk calculation,
cohomology formula, tensor-associativity identification, and uniqueness-of-left-adjoint
transport. It follows the same affine derived-equivalence clause of the blueprint.

`lem-sc-affine-algebra-derived-adjunction-isos` records only the ambient unit/counit
isomorphisms at quasi-coherent derived objects. Its module is
`lean/Sheaf/AlgebraicGeometry/AffineAlgebraDerivedAdjunctionIsos.lean`.
Source: Tag 0AVW, perfect-lemma-affine-morphism-equivalence, final adjunction-map argument.
The docstring explains the cohomology maps as the affine correspondence's alpha and beta,
and detects invertibility degree by degree. Neither statement duplicates a blueprint node:
`blueprint_refs.py search` returned zero matches for the affine derived unit/counit,
scalar-comparison, and quasi-coherent pullback queries. Both use the actual three-kind
search records, including unavailable LeanSearch. No change record is needed.

## Second reading by U3

1. **Statements unchanged.** I compared the delivered target module with the repository version. The `finite_affine_derived_equivalence` signature, hypotheses, quantified functors, and all three comparison clauses are unchanged byte for byte; only imports, the heartbeat scope, and the proof changed. The two added theorem signatures match their DAG nodes exactly and introduce no extra flatness, finiteness, boundedness, or Noetherian hypotheses. I checked identity morphisms, zero objects, degree-zero objects, empty affine schemes, and arbitrary affine ring maps as edge cases. Verdict: pass.

2. **Proof and axioms.** All three delivered modules compile with `lcompile.py --all`, with no warnings. The target contains no `sorry`; the only remaining holes are the two named public split theorems, each with a source, complete proof sketch, and matching node. The target proof constructs the restricted adjunction, reflects isomorphisms through fully faithful inclusions, and constructs each required natural isomorphism. No `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declaration was introduced. Verdict: pass.

3. **Split statements.** I searched the Sheaf and source trees and ran LeanFinder, Loogle, and grep searches recorded in `searches.jsonl`; no existing declaration states either affine derived pullback preservation or the ambient unit/counit isomorphisms. Each split theorem is strictly smaller than the target: one concerns only preservation of quasi-coherence and the other only invertibility of ambient adjunction maps. Their docstrings explain the affine stalk/tensor, cohomology, and adjunction arguments. Verdict: pass.

4. **Pruning and imports.** The removed direct proof import `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage` is redundant because the needed public declarations arrive through `SchemeDerivedDirectImage`; all remaining imports are used by the proof or by the split theorem signatures. The DAG proof dependencies now list the ambient adjunction, affine correspondence/cohomology, scalar exactness, and the two split lemmas used in the implementation. Verdict: pass.

5. **Route and unit.** The proof follows the recorded affine derived-equivalence route: ambient ringed-space adjunction, exact scalar restriction and comparison with direct image, affine quasi-coherence, then restriction to full subcategories and `Adjunction.toEquivalence`. The chapter's affine correspondence is retained as a tool, and no unit statement is bypassed by a weaker special case. Verdict: pass.

I changed only this second-reading report section; no Lean declarations or DAG statements were altered during review.

Source checked independently: [Stacks Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW),
`perfect-lemma-affine-morphism-equivalence`, especially the stalk localization calculation
and the reduction of derived adjunction maps to the underived affine correspondence. For
an affine chart B → A and p over q, the map is S⁻¹A → A_p, S = B minus q; this is a
localization even when B → A is not flat. The identity case reduces to an identity
adjunction up to its canonical isomorphism; for the empty source the algebra module
category is zero. These justify the edge cases without assuming f itself flat.
Mathlib `Adjunction.leftAdjointUniq`, `unit_leftAdjointUniq_hom_app`, and
`leftAdjointUniq_hom_app_counit` give the precise transport formulas for arbitrary adj.
The nearby `affineQCohDerivedAdjunction_unit_counit` concerns tilde/global sections for
Spec A, with explicit comparison hypotheses, rather than the relative ringed-space
functor here; using it would require additional affine descent and functor comparisons.
The generic `derivedPullback_tensor_preserve_QCoh` is scheme-to-scheme, whereas the target of g
is the ringed space (Y,f_*O_X). Neither closes these new holes directly.

I inspected `dag/units/sk-thm-picard-duality.json`: its `realized.statement` is empty and
its single `realized.steps` entry is empty. This item is below that unit's level, and the
original affine correspondence, affine cohomology, and ringed-space adjunction nodes
all remain in the new proof dependencies. No old mathematical proof dependency was
removed, so the complete pruning list is only the redundant direct import, not any
node or transitively needed module. The new node metadata has sources, creation and
blueprint provenance, actual search records, and Lean signatures; each `proof_deps`
list is the union of its proof steps' `uses`. The existing node's proof now records the
exact-postcomposition theorem (read in the source library) rather than assuming g_*
preserves K-injective complexes.

The target's existential L comes from the left-adjoint universal property, which fixes
it up to the natural isomorphism used downstream. No arbitrary object was extracted
from an unproved mere-existence statement to define data in this delivery.

Explicit `#print axioms` on a scratch copy of the target, compiled against the sandbox
overlay through `lcompile.py`, reports exactly `propext`, `Classical.choice`, `Quot.sound`,
and `sorryAx` for the target and each split theorem. Thus there are no additional axioms;
`sorryAx` remains because the split and upstream statements are still open. The scratch
copy was removed before delivery. The result is a decomposition, not a completed
axiom-free proof of the mathematical target.
