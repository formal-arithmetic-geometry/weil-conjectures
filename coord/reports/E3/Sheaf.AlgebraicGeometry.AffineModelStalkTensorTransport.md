## What changed

Reduced `AlgebraicGeometry.exists_affine_model_stalk_tensor_transport` to a natural presentation over the original local ring. Added the proof-only import `Sheaf.AlgebraicGeometry.AffineModelStalkPresentation`. Its statement is independent of i, V, z and R: it contains only the geometric restriction/chart/localization part. The original module constructs the extension to R, supplies the scalar tower, cancels the nested tensor product, and proves inverse naturality by tensor induction. Existing signatures and public imports are unchanged. Updated the parent DAG proof to this route.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.exists_affine_model_stalk_tensor_transport` (node `new-e1-affine-model-stalk-tensor-transport`); its complete Lean proof compiles. Added one hole: `AlgebraicGeometry.exists_affine_model_stalk_presentation`, node `new-e3-affine-model-stalk-presentation`, in the new module. No other sorry remains in the delivery. This is a decomposition, with net zero holes closed, not a completed proof of the geometric comparison. The algebraic extension and its naturality are proved without new algebraic holes. The local-ring presentation has no arbitrary extension ring or base-change morphism and is strictly the geometric part of the argument, not a renamed target.

## No longer needed

No existing imports or modules pruned. The old direct proof dependency
`lem-weil-pbc-spec-tilde-stalk-localization` is no longer a direct dependency of
the parent; it remains a transitive dependency through the new presentation node.
The parent directly uses only `new-e3-affine-model-stalk-presentation`; its former direct dependency `lem-weil-pbc-spec-tilde-stalk-localization` remains needed by that new node. Explicit fraction inversion after extension to R is no longer needed: Mathlib tensor cancellation proves that step. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The original DAG's single proof step bundled geometric restriction/chart transport with scalar extension and naturality. It is now split at the original local ring. The pinned Mathlib gives the tilde localization and additive restriction-stalk isomorphisms, but no assembled S-linear comparison for an arbitrary supplied affine model. The source locations were verified online: Stacks 01BH Lemma 17.10.5 (3) and 01HV Lemma 26.5.4 (6)-(7), including functoriality. Zero modules and empty-open vacuity were checked mathematically. The new lemma does not require global quasi-coherence of F. There are no forced adaptations or definition changes.

## New nodes

`new-e3-affine-model-stalk-presentation` states the natural S-linear identification `S tensor_A M ≃ F_x` for a module sheaf with a supplied affine model. Its module is `Sheaf.AlgebraicGeometry.AffineModelStalkPresentation`. Its docstring and node give the restriction/chart maps, localization universal property, scalar compatibility and naturality proof; the sole theorem remains sorry for the next worker. No change record is needed.


## Second reading by E3

1. Compared the complete existing module with the repository by diff, and compared
   the theorem signature byte for byte. The signature, visibility, docstring and
   two public imports are unchanged. The only Lean additions there are a plain
   proof import, an elaboration option and the proof. The existing node changes
   only `proof`, `proof_deps` and `proof_origin`. There are no changed definitions,
   target statements, forced adaptations or undeclared interface changes. Pass.
2. Compiled both modules in import order with lcompile.py. The delivered source
   contains exactly one `sorry`, the named presentation theorem reported above,
   and no forbidden declaration or hollow definition. Independently read the
   scalar-tower `rfl`, inverse base-change equivalence and cancelBaseChange, then
   each tensor-induction branch. On a pure tensor the inverse is
   `r tensor delta(1 tensor m)`; the supplied naturality equation gives precisely
   the induction step, and inverse injectivity gives the original direction.
   The existential witness delta is used within a theorem proof, not as data of
   a public definition. A separate scratch `#print axioms` for both declarations returned exactly
   `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`; the last is the
   reported presentation hole. Pass.
3. Read Stacks 01BH, Lemma 17.10.5 property (3), and 01HV,
   Lemma 26.5.4 (6), (7) and its functoriality sentence. The new theorem assumes
   exactly a point in an affine open and a supplied model isomorphism; it does
   not assume global quasi-coherence, finiteness or flatness. Transport along e
   explains the additional F and c variables. The S-linearity is required for
   extending delta to R. Checked zero modules, zero morphisms, identity models,
   a field affine chart, and empty-open vacuity. It is a true geometric part of
   the argument; the original theorem's scalar extension and naturality remain
   a substantive proved reduction, rather than an application of a renamed
   target. Ran fresh LeanFinder and Loogle searches for scalar-compatible open
   restriction stalk comparisons and grep with stalkLinearMap/restrictStalkNatIso/
   stalkIso. Read Mathlib Modules.Sheaf lines 510–536, Modules.Tilde lines 184–198
   and AffineScheme lines 818–841; these supply components, not this family.
   Searched lean/Sheaf and upstream geometry sources. Read the already proved
   RestrictionStalkExtensionIso and TildeStalkTensorComparison modules: their
   public theorems concern complexes or Spec tensor bifunctors, and their usable
   scalar/germ components are private. IntrinsicFlatModuleStalkTensorPresentation
   concerns affine sections of globally quasi-coherent modules, with no supplied
   model/naturality clause. No duplicate assembled theorem was found. Closing
   the geometric hole requires those scalar/chart calculations and is not a
   few-minute additional proof. Pass as a decomposition, net zero holes.
4. Both existing public imports and both new public imports are needed by the
   signatures: Tilde supplies the affine-model functor, FlatPullbackStalk supplies
   the stalk module instance and Hom.stalkLinearMap. The presentation import is
   proof-only. No existing module import can be removed. No longer needed now
   explicitly lists the former direct proof dependency, which remains used
   transitively. Read dag/units/sk-thm-picard-duality.json: realized statement and
   step entries are empty, and no realized node is bypassed. The parent and its
   ancestor coefficient-stalk-model route stay present. Pass.
5. Matched the parent node's two steps to obtain delta, the scalar tower,
   cancelBaseChange, inverse tensor induction and inverse injectivity. Its sole
   direct dependency is the new presentation node. Matched every variable and
   both clauses of the new node to its verbatim Lean signature; its localization
   dependency is a Mathlib leaf whose statement includes both ring and module
   localization. The remaining theorem has a source and complete germ,
   localization and tensor-naturality proof in its docstring and node. Creation,
   blueprint, chapter, unit, searches and Lean record fields are present. Pass.

Second reading changed no proof or existing signature. Added the missing blueprint
reference to the new module docstring, rendered the new node statement in TeX,
expanded its scalar/chart compatibility step, and replaced its uncited ring
localization wording with the actual cited localization node's ring clause.
Clarified the former direct dependency in No longer needed. The result remains
one original hole closed and one geometric hole added, with no modules pruned.
