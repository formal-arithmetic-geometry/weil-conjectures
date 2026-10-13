## What changed

Replaced the whole-proof sorry of `AlgebraicGeometry.coherentFormalModule_limit_full`
with a compiling categorical reconstruction. At level n the map is the source quotient
isomorphism inverse, the existing `formalModuleQuotientMap` of beta, and the target
quotient isomorphism. The defining cokernel equations prove its projection equation.
The proof derives epimorphic limit projections from these quotient isomorphisms,
cancels them to prove naturality for every index morphism, packages the natural
transformation in the full subcategory, and uses `limit.hom_ext` to prove the limit-map
identity. The existing signature, visibility and docstring are unchanged.

Added the proof-only import of `Sheaf.AlgebraicGeometry.CoherentFormalModuleLimitQuotient`
and its new module/node. Updated the original node's proof route to the actual Lean
argument. The new theorem concerns one system and one level, independent of any beta,
and asserts its canonical quotient identification. Its projection equation determines
the isomorphism uniquely, since the quotient projection is epic; the proof makes no
arbitrary object construction from an existence theorem.

Both modules compile through lcompile.py. This is a decomposition, not a sorry-free
proof of the original target closure. Sources 087W and 088B were read on the Stacks
website because the local coherent.tex is absent. The unit's realized statement/steps
are untouched; this refinement stays below the unit level.

## Proved and sorry left

Closed: `AlgebraicGeometry.coherentFormalModule_limit_full`
(node `lem-weil-pbc-coherent-formal-module-limit-full`), one original hole.
There are no sorries left in the item's module.

Added: `AlgebraicGeometry.coherentFormalModule_limit_quotient`
(node `lem-weil-pbc-coherent-formal-module-limit-quotient`), one whole-proof sorry in
its own new module. Its docstring and node supply the affine-basis kernel/image proof.
The source projection and its kernel formula are already stated by
`AlgebraicGeometry.coherentFormalModule_affine_projections`. The remaining step is
transport to evaluated sheaf limits and the sheaf kernel/image/cokernel identification.
No quasi-coherence of the limit is assumed. Edge cases checked: J=0 (zero kernel),
J=1 (zero terms), zero systems and the empty scheme. Net holes: zero; one decomposition.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`, node
  `lem-weil-pbc-coherent-formal-modules-affine`. The full equivalence with finite
  completed modules, its inverse reconstruction and completed scalar action are
  unnecessary for this proof: only the canonical affine projection calculation is used.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects`, node
  `lem-weil-pbc-coherent-formal-modules-restriction-objects`. Its direct use is removed,
  but it remains needed transitively by the affine projection theorem's affine-open
  section reduction; it is not globally pruned.

The old direct proof dependency `lem-weil-pbc-affine-tilde-gamma-adjunction`
(`Mathlib.AlgebraicGeometry.Modules.Tilde`) is unnecessary in the reconstruction
argument, which stays in module sheaves. Affine finite-level section identification
still uses that dictionary below the affine projection theorem, so this is not a
claim that the Mathlib module leaves the global closure. No other imports were removed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The planned last step was not elementary in Lean: the
arbitrary limit sheaf need not be quasi-coherent, so the affine cokernel/image theorem
for quasi-coherent source and target cannot simply be applied to it. The new theorem
isolates the required sheaf argument and explicitly avoids that extra hypothesis.
Once the one-system quotient identification is available, separate local morphism
gluing is unnecessary: cokernel descent constructs global component maps directly.

## New nodes

`lem-weil-pbc-coherent-formal-module-limit-quotient` is stated in
`lean/Sheaf/AlgebraicGeometry/CoherentFormalModuleLimitQuotient.lean`. It asserts the
canonical quotient identification for one system and one level; it does not repackage
the two-system fullness conclusion. Its proof uses the existing affine projection
node and the ideal-power section clause of the ideal-times-affine-sections node,
then sheaf locality and uniqueness of cokernels. Searches ran through msearch:
LeanSearch unavailable, LeanFinder returned only adic module evaluations, grep no
exact match. Blueprint searches for both “formal module limit quotient” and “087W”
found no duplicate. No definition or existing statement changed; no change record
or forced adaptation is needed.

## Second reading by F2

1. **Interfaces: pass.** Compared both delivered modules with the repository.
   The existing fullness declaration, its docstring, universes and visibility are
   byte for byte unchanged; only its proof and plain proof imports differ. The
   quotient module is new. No existing definition or statement changed and no
   change record or forced adaptation is needed.
2. **Proof and axioms: pass as a decomposition.** Independently compiled both
   modules with lcompile.py in import order. Scratch copies with `#print axioms`
   for both declarations reported exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The sole new sorry is the named whole-proof
   quotient theorem; none occurs in the fullness proof or a definition, and no
   prohibited declaration or implementation escape is present. Choosing the
   quotient isomorphism is permitted: its projection equation determines its
   hom uniquely by cancellation of the cokernel epimorphism, and an isomorphism's
   inverse is then unique. This does not select arbitrary undetermined data.
3. **Split theorem: pass.** Checked the actual formal-module conditions and the
   affine-projection and ideal-power-section theorem signatures. Read Stacks
   [087W](https://stacks.math.columbia.edu/tag/087W) and
   [088B](https://stacks.math.columbia.edu/tag/088B). The quotient assertion is
   true: affine projection kernels are precisely ideal-power multiples, which
   identify the kernel subsheaf with the multiplication image; affine surjectivity
   makes the projection epic, and the cokernel universal property supplies the
   unique quotient isomorphism. Checked n=0, zero ideal, unit ideal, zero systems,
   and the empty scheme. It concerns one system and one projection, hence is a
   strict ingredient of fullness rather than a renamed morphism-lifting statement.
   Independent LeanFinder search for finite-level reduction of sheaf adic limits,
   Loogle cokernel-isomorphism search, and grep with kernel/cokernel/adic terminology
   found only generic categorical and module-completion ingredients, no duplicate
   sheaf theorem. The existing projection-epi theorem supplies surjectivity but
   not the needed kernel identification. Closing the remaining sheaf quotient
   argument requires substantial sheaf image/cokernel work, beyond a few-minute
   repair; it remains explicitly open.
4. **Route and pruning: pass.** Read the categorical reconstruction top down.
   Its defining projection equation follows from cokernel descent; cancelling
   each source projection proves naturality for all index morphisms, and
   limit.hom_ext proves the stated limit-map identity. The new route omits finite
   completed-module equivalence and separate gluing of component maps. Imports
   used by signatures remain public; imports used only by proofs are plain.
   All three old proof dependencies omitted by the reconstruction are listed
   above, with transitive needs distinguished from global pruning. Checked
   dag/units/sk-thm-p1.json realized: no realized unit statement or step is
   bypassed or changed; this replacement is below that level.
5. **Nodes: pass.** Compared the existing node with the repository: only proof,
   proof_deps and proof_origin differ. Their route matches the code. Checked
   the new node's source, dependencies, proof, origin, search records, split
   status, created record, blueprint ancestry, chapter/unit and verbatim Lean
   signature. Its two dependencies supply the affine kernel formula and the
   ideal-power range formula; neither assumes quasi-coherence of the limit.

Second reading changed the new theorem's proof docstring and corresponding node
step to make the sheaf-image argument explicit: use the ideal-power clauses on the
unit sheaf, prove multiplication lands in the kernel by pure tensor germs, and
lift each scalar in an affine kernel expression to a tensor section for the reverse
inclusion. This avoids implicitly treating evaluation as image-preserving for an
arbitrary limit sheaf. No Lean proof or interface needed repair. One original hole
closed, one lower hole added; net zero holes, one decomposition.
