## What changed

Replaced the original hole in `AlgebraicGeometry.affineExtensionSections_model_mate_isIso`
by a proof from the ordinary model comparison and a derived factorization equation.
The original declaration's statement and all public imports are unchanged.

Added `AffineExtensionSectionsUnderivedModel`, proving the ordinary natural isomorphism
and its unit equation by composing the two tilde/sections adjunctions with tensor
pullback and extension of scalars, applying uniqueness of left adjoints, and cancelling
the invertible tilde unit. This proof uses no derived categories and creates no hole.

Added `AffineExtensionSectionsModelFactorization`, stating the remaining compatibility
of localization with the ordinary comparison. It accepts an arbitrary natural
transformation with the ordinary unit equation, without assuming invertibility, and
identifies the derived mate with its localized complex map through source and target
model isomorphisms. The main proof uses the proved ordinary isomorphism, lifts it to
complexes, applies the derived factorization, and cancels the target isomorphism.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.affineExtensionSections_model_mate_isIso`
(node `lem-pc-affine-extension-sections-model-mate`). This is a decomposition, not a
sorry-free proof of the entire derived argument: one original hole is closed and one
new hole is added, for net zero holes.

Proved `AlgebraicGeometry.exists_affineExtensionSections_underived_model`
(node `new-affine-extension-sections-underived-model`) without `sorry`.

The only remaining `sorry` in the delivery is
`AlgebraicGeometry.exists_affineExtensionSections_model_factorization`
(node `new-affine-extension-sections-model-factorization`), in its own new module.
Its docstring and node give the K-flat counit and derived-unit argument. No `sorry`
remains in the item's module, and no definition or private lemma has a hole.

Edge cases checked in the statements and argument: zero module/complex, zero rings,
identity ring map, arbitrary unbounded complexes, and nonflat ring maps. The ordinary
proof uses only adjunction identities and fully faithful tilde. The derived statement
uses K-flatness of M and of its tilde, not flatness of g or boundedness of M.

## No longer needed

Removed the item's proof-only imports
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` and
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`.
Their node dependencies `lem-pc-affine-derived-pullback-tensor-tilde` and
`lem-pc-affine-qcoh-derived-equivalence` are no longer used by this route.

For the remaining factorization the narrower inputs are
`Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde`,
`Sheaf.AlgebraicGeometry.TensorPullbackTilde`, and
`Sheaf.AlgebraicGeometry.AffineTildeDerivedSectionsUnitIsIso`.
The affine equivalence's shift and triangulatedness clauses, derived tensor formulas,
open-restriction comparisons, and resolution-independence for arbitrary non-K-flat
inputs are unnecessary here. Other importers may still reach the removed modules;
this report makes no claim that they leave the entire targets' import closure.

The prior attempt's `affineExtensionSections_model_iso_aux` and
`new-affine-extension-sections-model-iso` are removed from the sandbox delivery.
They were never library declarations/nodes and are not needed by this proof.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt applied `exists_affineExtensionSectionsUnit`, whose module imports
this item and whose proof already uses `affineExtensionSections_model_mate_isIso`.
That would be circular. Its auxiliary statement also duplicated the upper unit theorem,
and its report incorrectly described the contents of its proof. The replacement uses
no import of `AffineExtensionSectionsUnit` and no result above this item.

The existing DAG's affine-model computation is valid, but its comparison isomorphisms
alone do not state their compatibility with the fixed adjunction units. The new derived
factorization explicitly isolates that compatibility equation; the ordinary unit
comparison is now actually proved. Neither the blueprint unit's statement nor its
realized steps are changed (the unit record has empty realized lists).

The local checkout lacks the Stacks TeX files. The cited Stacks pages for Tags 06Z0,
08DW and 0AA7 were read online; the new node proof origins are marked `agent` for the
explicit categorical elaboration of their model argument. The existing library's
proved ordinary tilde adjunction and tensor-pullback adjunction provide the ordinary
calculation. No interface change or forced adaptation was needed.

## New nodes

`new-affine-extension-sections-underived-model`, in
`AffineExtensionSectionsUnderivedModel.lean`: the ordinary natural isomorphism and its
precise unit equation, proved by uniqueness of left adjoints and unit naturality.

`new-affine-extension-sections-model-factorization`, in
`AffineExtensionSectionsModelFactorization.lean`: the derived mate's factorization
through the localization of any ordinary comparison satisfying the unit equation.
This is the single remaining hole, separate from invertibility of the ordinary map.
Both new nodes inherit the item's chapter, unit and blueprint ancestor. The existing
item node now records the actual two comparisons and cancellation proof.

## Second reading by H2

1. **Interface and scope: pass.** Read the original module and its diff before the
   delivery tool prepared its branch. The only changes to that existing module are
   its two proof-only imports and the body of
   `AlgebraicGeometry.affineExtensionSections_model_mate_isIso`. Its signature,
   universes, derived-category instances, `hv`, `hr`, K-flat hypothesis, conclusion,
   public imports, and docstring are unchanged. No definition or existing public
   declaration was changed; no change record or forced adaptation is needed.

2. **Proof and trust: pass as a decomposition.** Compiled all three modules in
   dependency order with `lcompile.py`; no errors or warnings. The main proof
   explicitly constructs additive instances, obtains the ordinary comparison `c`,
   applies the localization factorization to `c.hom` and `hc`, lifts the natural
   isomorphism to complexes and through `Q`, and cancels the isomorphism `b`.
   The ordinary comparison proof uses Mathlib `leftAdjointUniq`, its unit equation,
   extension-unit naturality, and cancellation of the invertible tilde unit. It
   does not select arbitrary data from an unproved existence assertion. The new
   witnesses `c`, `a`, and `b` are used only inside proofs, not to define data.
   A scratch `#print axioms` check confirms that the ordinary theorem uses only
   `propext`, `Classical.choice`, and `Quot.sound`; the factorization and main
   theorem additionally use `sorryAx`, exactly as expected for the remaining hole.
   There is exactly one literal `sorry`, in the named public factorization theorem;
   no `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or hollow definition.
   One old hole is closed and one new hole is added: net zero, as reported above.

3. **New statements and sources: pass.** Read
   [Stacks 01I9](https://stacks.math.columbia.edu/tag/01I9),
   [06Z0](https://stacks.math.columbia.edu/tag/06Z0),
   [08DW](https://stacks.math.columbia.edu/tag/08DW), and
   [0AA7](https://stacks.math.columbia.edu/tag/0AA7), and the actual statements of
   `exists_tensorPullback_tilde_iso`, `isKFlat_tilde`,
   `affineTildeDerivedSectionsUnit_isIso`, and `exists_schemeDerivedAdjunction`.
   The ordinary theorem is proved for the given comparison `v`; its identity-on-
   sections hypothesis is harmless and is not needed by the categorical proof.
   The remaining theorem isolates localization compatibility for a supplied
   natural transformation `c` with its unit equation; it does not assume `IsIso c`
   or assert the original `IsIso` conclusion under a new name. The concrete
   complex endpoints and equation `n b = a Q(c_M)` separate this compatibility
   task from the proved ordinary adjunction calculation and the final cancellation.
   `hr` is essential for the specified derived comparison; no flatness of `g`
   or boundedness is silently used. Zero rings and zero complexes cause no
   exception; the identity map gives the usual unit identities. For a nonflat map,
   K-flatness of `M` supplies the extension model, and K-flatness of its tilde
   supplies the pullback model, rather than exactness of extension or pullback.
   Expanded the remaining theorem's proof docstring and node with the precise
   constructions of `a` and `b`, K-flatness of the sections model via the tilde
   unit, and transport of arbitrary `g` to its coordinate-ring map before using
   the `Spec.map`-form pullback theorem. These are categorical elaborations of
   the cited model argument, not statements quoted verbatim from those tags.
   Independent searches used `leanfinder` for localization preserving adjunction
   transposes, `loogle` for adjunctions and `IsIso`, and `grep` for left-derived
   units and invertible Hom transposes. They found generic derived-unit/counit
   and localization lemmas, but no existing affine factorization closing this
   hole directly. Also searched the local `lean/Sheaf` and upstream category-
   theory and module files for mates, unit equations, and comparisons.

4. **Route and pruning: pass.** The ordinary comparison uses the shortest generic
   adjunction calculation found; no derived theorem is needed for it. The new
   imports of the item are proof-only. The factorization module retains the three
   narrower planned inputs for its remaining proof; its public imports are needed
   to express its signature. The two removed proof-dependency modules and their
   nodes are listed under `No longer needed`. The old definition dependency
   `def-pc-affine-global-hom-base-change-map` remains needed for the fixed functors
   and adjunctions, and is not claimed as pruned. Read
   `dag/units/sk-thm-picard-duality.json`: its realized statement and step lists
   are empty and unchanged. This replaces only a route below the unit level.

5. **DAG and records: pass after correction.** Compared all three node records
   with the Lean statements and checked their `proof_deps` are exactly the union
   of their steps' `uses`. New nodes have the source, proof origin, search records,
   creation record, blueprint ancestry, chapter, unit, and verbatim Lean signature.
   The item node changes only stage-3-owned proof fields. Restored its direct
   dependency on `def-pc-affine-global-hom-base-change-map` and explained the
   additive-instance construction in its first step, since the main proof uses
   those fixed adjunctions as well as the two new comparison statements.

Second-reading changes: explicit comparison constructions in the factorization
proof docstring and node; corrected the item's direct dependency accounting;
added this independent review. The Lean proof bodies and theorem signatures
needed no repair. The remaining localization proof was not closed in this reading.
