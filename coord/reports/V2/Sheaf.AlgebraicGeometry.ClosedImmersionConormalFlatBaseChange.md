## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_flat_base_change`
to the affine coordinate comparison in the new module
`Sheaf.AlgebraicGeometry.ClosedImmersionConormalAffineBaseChangeComparison`.
The existing theorem's signature and public imports are unchanged. Its proof constructs
compatible affine ambient charts, proves their inverse images form a basis using the
closed embedding, transfers Mathlib's `Ideal.tensorCotangentHom_surjective` and
`Ideal.tensorCotangentHom_injective_of_flat` through the comparison equivalences,
proves local surjectivity directly, and applies the sheaf basis isomorphism criterion.
The proof does not use a categorical cokernel or a quasi-coherence hypothesis for gluing.
All proof imports are ordinary, non-public imports.

The affine comparison states actual equivalences of the section sets with the two
cotangent models, together with their commutation equation. It asserts neither global
invertibility nor sectionwise surjectivity/injectivity, and assumes no flatness.
The global algebra calculation and basis argument are completely proved in the original
module. No definitions, existing signatures, or other groups' modules were changed.
The original and new node records give the precise route and the complete affine argument.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_flat_base_change`
(node `lem-weil-pbc-closed-immersion-conormal-flat-base-change`).
There are no remaining `sorry`s in the original module.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_affine_base_change_comparison`
(node `lem-weil-pbc-closed-immersion-conormal-affine-base-change-comparison`).
Its proof is exactly `by sorry` in its own new module, with a complete proof in words.
No other holes were added. This is a decomposition: one hole closed, one added, net zero;
it is not a sorry-free proof of conormal flat base change. The affine comparison is strictly
part of the argument; Mathlib supplies the ring surjectivity and flat injectivity, and
this delivery proves their transfer to section maps and the entire global step.

Both delivered modules compile through `lcompile.py`, in import order. The original
module compiles without errors or warnings. Neither file exceeds 100 characters per line.

Edge cases for the new statement were checked mathematically before finalizing it:
if the immersion ideal is zero, both cotangent models and both section modules are zero;
if it is the unit ideal, the inverse-image chart is empty and both cotangent models are
zero. Empty affine charts have the same zero models. Identity base change gives the
usual affine conormal equivalences. Flatness is not needed to construct either
comparison equivalence: it is used only later for injectivity of the ring map.
In particular, the source remains `B tensor_A (J/J²)`, with B the ambient ring, not
`B/JB` required to be flat over A. This avoids adding a false quotient-flatness hypothesis.

## No longer needed

Removed these four direct imports from the original module:

- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`: needed only in the remaining
  affine comparison; retained there and already in the functoriality import closure.
- `Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal`: needed only in the remaining
  affine comparison; moved to that module as a proof import.
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`: the global proof now
  proves local surjectivity directly on the basis. Its node
  `lem-weil-pbc-quasi-coherent-module-cokernel-image` is no longer needed by this route.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`: no direct use in the
  global argument; existing affine conormal/pullback modules retain their own uses.

The original node no longer directly needs
`lem-weil-pbc-module-pullback-quasi-coherent` or
`lem-weil-pbc-affine-tilde-gamma-adjunction`: the basis gluing does not require either
source or target to be quasi-coherent. These facts remain in existing lower affine
section proofs where those proofs require them; this is not a claim that they are
unreachable from every target.

The affine-cover criterion, open-preimage pullbacks, cartesian-square pasting,
quotient ideal calculation, and affine pullback sections are retained below the new
comparison node. They were relocated, not pruned. The ring cotangent base-change,
affine flatness criterion, and sheaf basis isomorphism nodes remain used in the original
proof. No unit statement or unit proof step was bypassed. A redundant experimental
`Mathlib.CategoryTheory.Sites.LocallySurjective` import was also removed because
`Mathlib.Topology.Sheaves.LocallySurjective` publicly imports it.

## Where the brief, the DAG or earlier work was wrong

The original route's cokernel and quasi-coherence gluing is unnecessary: surjectivity
on a basis gives local surjectivity directly, and bijectivity on a basis gives the
isomorphism directly. The substantial missing Lean glue is the simultaneous affine
coordinate comparison and its canonical-map equation, now made explicit as its own item.
No original mathematical statement was found false.

The cited Stacks TeX files are absent from this local read-only clone. The actual source
statements and proofs were checked at
https://stacks.math.columbia.edu/tag/0473 and
https://stacks.math.columbia.edu/tag/01JU. LeanSearch returned Internal Server Error on
all attempted natural-language queries; this is recorded as unavailable, without an
absence verdict. Loogle, LeanFinder, repository searches, and Mathlib source searches
were available and used. The ring-level candidates were read in
`Mathlib/RingTheory/Ideal/CotangentBaseChange.lean` and
`Mathlib/RingTheory/Etale/Kaehler.lean`; neither gives the scheme section comparison.

Delivery tooling failure: `deliver3.py --no-push` stopped before compiling or preparing
a delivery, with `ImportError: cannot import name 'refuse_missing' from 'import_cycles'`.
The launcher imports `refuse_missing` and `source_roots` from the clone's
`tools/import_cycles.py`, which currently defines neither. The tools were not edited
and the guard was not bypassed. The tool was updated externally during this session;
a retry printed OK: local compilation and preflight pass except for the expected
second-reading section, which the second reader writes. Nothing was pushed.

## New nodes

`lem-weil-pbc-closed-immersion-conormal-affine-base-change-comparison` records the
conjugation of the canonical map on each compatible affine chart with
`Ideal.tensorCotangentHom`. It has the inherited chapter and unit, a complete proof
through the existing chart, quotient-ideal, affine conormal and affine pullback nodes,
and its new Lean module. It is the only new node and the only new hole. There are no
change records or forced adaptations.

## Second reading by V2

1. **Interface and scope — pass.** I compared the two versions of
   `ClosedImmersionConormalFlatBaseChange.lean` with `diff` and separately extracted
   the theorem signature: it is byte-for-byte identical, including universes, both
   closed-immersion instances, commutativity, the cartesian `IsLimit` hypothesis,
   the actual module morphism `c`, and its canonical-choice equality. The conclusion
   remains `Epi c ∧ (Flat g → IsIso c)`. Only its proof, proof imports and proof
   documentation changed. There is one new theorem in its own module; there are no
   definitions, forced adaptations or signature changes requiring a change record.

2. **Kernel proof and holes — pass as a decomposition.** I compiled both modules
   in import order through `lcompile.py`. The original theorem has no `sorry`;
   the new affine comparison has exactly one named `by sorry`. Neither module
   contains an axiom, unsafe/opaque declaration, implementation override, external
   code or skipped kernel check. Scratch copies with `#print axioms` check both
   declarations; the standard axioms and `sorryAx` are the expected trust boundary
   because the comparison and upstream statements remain open. No object or
   definition was introduced by choosing an arbitrary unproved existence witness:
   the proof eliminates the comparison's existential only inside a proposition.
   The report correctly counts one hole closed and one added, net zero.

3. **New statement, sources, small cases and search — pass.** I read the new
   theorem, its docstring and all three steps of its node, together with
   `affine_conormal_sections`, `exists_tensorPullback_affine_sections`, the affine
   equation in `closedImmersion_conormal_functorial`, and the quotient-base-change
   declaration. I read [Stacks 0473](https://stacks.math.columbia.edu/tag/0473) and
   [Stacks 01JU](https://stacks.math.columbia.edu/tag/01JU). The source and target
   section sets really are `(B/JB) ⊗[A/J] (J/J²)` and `JB/(JB)²`; quotient tensor
   cancellation gives the first displayed model, and multiplication `B ⊗[A] A ≃ B`
   gives the second. The functorial affine equation and the pullback pure-tensor
   formula give the displayed equality on generators, hence on all tensors.
   Quasi-coherence needed by affine pullback is supplied by the first clause of
   `affine_conormal_sections`; no extra hypothesis is needed. The lemma states
   only this coordinate comparison on a fixed chart, and proves neither the ring
   calculation nor the basis/global step, so it is strictly a part of the original
   argument rather than a renamed restatement.

   I checked J=0, J=A, empty charts and identity base change. I also tested the
   non-flat map A=ℤ to B=ℤ/2 with J=(2): the source model is ℤ/2 and the target
   model is zero. The canonical map is zero, so the comparison is consistent
   without erroneously asserting injectivity. Independent searches used LeanFinder
   for “sections of pullback ideal quotient sheaf on affine schemes compatible with
   tensor products under cartesian base change”, Loogle for `"Cotangent", "Equiv"`,
   and msearch grep for `conormal.*(pullback|tensor)|Cotangent.*[Ee]quiv`, plus `rg`
   in both repository roots and Mathlib's algebraic geometry. The hits concern
   affine scheme pullbacks or ring cotangents, not this scheme section comparison.
   I read the existing diagonal comparison: it identifies differentials with the
   diagonal conormal and cannot supply this general cartesian-square comparison.
   Closing the remaining hole requires the chart and scalar transport construction;
   it is not a few-minute application of an existing theorem.

4. **Top-down route and pruning — pass.** I followed `hA` (compatible charts),
   `hB` (pullback along an inducing closed embedding), `hsurj` (transfer through
   the two equivalences), `hloc` (restriction to a basis neighbourhood), and the
   faithful forgetful-functor epi reflection. In the flat branch `g.flat_appLE`
   supplies ambient B-flatness over A, and Mathlib's cotangent injectivity plus
   surjectivity gives bijective basis components; the sheaf basis criterion and
   module-to-presheaf reflection finish. No flatness of B/JB is assumed.
   `## No longer needed` accounts for all twelve old proof dependencies: ring
   cotangents, affine flatness and the sheaf basis criterion stay in the global
   proof; functoriality, affine closed-immersion charts, open-preimage pullbacks,
   square pasting, quotient ideals and affine pullback sections occur below the
   comparison; pullback quasi-coherence, cokernel/image gluing and tilde-Gamma
   adjunction are not direct dependencies of this new global route. Their lower
   uses are not claimed pruned from the whole library. I read `sk-thm-p1.json`'s
   `realized` statement and four step lists: this auxiliary conormal lemma is not
   a unit step being replaced, and no realized node or unit route was changed.
   The proof uses the shortest available ring and sheaf results. The two public
   imports of the original module are unchanged; its new imports serve proofs.

5. **DAG versus Lean — pass after metadata repair.** For both nodes, `proof_deps`
   is exactly the union of the steps' `uses`. The original node describes the
   implemented basis/ring/local-surjectivity argument; the new node records the
   remaining affine transport and generator equation. Its source, inherited
   chapter/unit, creation record, blueprint ancestry, searches and Lean record
   are present. Its Lean statement is verbatim. The original Lean record had
   retained its old single-line signature; I replaced that metadata string with
   the unchanged multiline signature, without altering any mathematical field.

**Second-reader changes:** added the missing blueprint tag to the new module
header; removed its redundant public import
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic` (the signature
still compiles from the other public imports); repaired the original node's
verbatim Lean-signature metadata; added this review. No proof or statement was
rewritten, no further hole was closed or added, and no additional globally
unreachable module is claimed.
