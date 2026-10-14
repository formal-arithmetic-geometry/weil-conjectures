## What changed

Implemented the derived counit and tensorator normalization argument in
`Sheaf.AlgebraicGeometry.DerivedPullbackTensorSuccessiveNormalization` without changing its
public theorem statement. A proved private categorical diagram lemma combines tensorator
naturality, the two canonical normalization equations, counit naturality, the left-derived
composition factorization, and cancellation of two ordinary chain isomorphisms.

Added the proof imports `Sheaf.Algebra.Homology.KFlatPullback` and
`Sheaf.AlgebraicGeometry.PullbackTensorTotalCompositionLocalized`. The new module states
only the ordinary localized tensor/composition square. Its statement contains no derived
pullback tensorator or counit and requires no K-flatness. The original public import stays.
The DAG proof and dependencies follow this reduction.

The intermediate chain tensorators chosen from the canonical predicate are determined by
their equations on every total-complex summand. Joint epimorphy of those summand inclusions
determines their hom maps, and hence the isomorphisms; these are not arbitrary witnesses
of unconstrained existence statements.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.derivedPullback_tensor_successive_normalization`
(`lem-sc-derived-pullback-tensor-successive-normalization`). Its proof has no `sorry`.

Added one hole:
`AlgebraicGeometry.pullback_tensor_total_composition_localized`
(`lem-sc-pullback-tensor-total-composition-localized`), the whole proof of the public theorem
in its own module, with a source and proof in words. This is a decomposition: one upper
hole closed and one strictly smaller ordinary compatibility hole added; net holes zero.
The private diagram lemma and counit factorization are proved in Lean.

## No longer needed

The proof does not use `lem-pc-kflat-tensor-product` or its module
`Sheaf.Algebra.Homology.KFlatTensorProduct`; removed that node from the parent's proof
steps and `proof_deps`. K-flatness of the total tensor complex is unnecessary: the only
K-flatness needed here is that of P,N and their separate g-pullbacks.

No existing public import was removed. The K-flat tensor-product module remains reachable
through `MixedHomTensorPullbackIso`; this is a local dependency removal, with no whole-library
module prune claimed. The other two old direct proof dependencies removed from the parent are
`lem-weil-pbc-module-pullback-tensor` (module
`Sheaf.AlgebraicGeometry.ModulePullbackTensor`) and
`lem-pc-module-pullback-adjunction` (module
`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`). Both remain needed transitively
in the smaller new node; neither is a whole-library prune. The unrelated existing module
`Sheaf.AlgebraicGeometry.PullbackTensorComposition` uses the other pullback interface and
is not imported. No normalization of the direct derived tensorator, no comparison with
it and no final derived cancellation theorem is used.

## Where the brief, the DAG or earlier work was wrong

The DAG's mathematical route is retained, but its K-flat tensor-product dependency was
unnecessary for this successive-route statement. The ordinary total-complex compatibility
calculation was a genuine unstated intermediate step, rather than a consequence of the
existing ordinary pullback tensor-composition theorem with its different functor interface.

This clone contains the literature indexes but not `literature/stacks-project/cohomology.tex`;
the Stacks pages for Tags 079U and 0D5S were read online. LeanSearch returned Internal Server
Error, recorded as unavailable; Loogle, LeanFinder, Mathlib grep, repository grep and the
blueprint search were performed.

## New nodes

`lem-sc-pullback-tensor-total-composition-localized` states the ordinary square for arbitrary
complexes, with the three chain tensorators fixed by their summand equations. It combines
ordinary tensor/composition compatibility with localization tensor naturality. Its module
is `Sheaf.AlgebraicGeometry.PullbackTensorTotalCompositionLocalized`. Identity arrows,
zero complexes and empty schemes satisfy the same universal-property argument. No existing
public definition, signature, visibility or target was changed; no change record is needed.

## Second reading by H3

1. **Visible interface: pass.** Diffed the existing module against the repository.
   The only old declaration is
   `AlgebraicGeometry.derivedPullback_tensor_successive_normalization`; its complete
   signature and existing docstring are byte-for-byte unchanged. The changes are two
   plain proof imports, a proved private diagram lemma, and the replacement proof.
   No definition, public import, visibility, target or other existing module changes.
   The existing node changes only `proof`, `proof_deps` and `proof_origin`.

2. **Proof and data: pass.** Compiled both delivered modules in dependency order
   through `lcompile.py --all`: the ordinary module took 25.0 s and the parent 55.1 s,
   both without warnings or errors. There is exactly one written `sorry`, the named
   ordinary theorem reported above; none occurs in the parent or any definition.
   No prohibited declaration or attribute occurs. Scratch-copy `#print axioms`
   reports only `propext` and `Quot.sound` for the private pasting lemma, and
   `propext`, `Classical.choice`, `Quot.sound`, `sorryAx` for both public theorems;
   `sorryAx` remains expected from the explicitly open ordinary lemma and upstream
   statements. No other axiom appears. Read the seven hypotheses of
   `normalization_pasting`: tensor interchange, the two component factorizations,
   the two normalization equations, tensorator naturality, counit naturality and
   the ordinary square give precisely its conclusion by inverse cancellation.
   Read `fac` against the selected composition comparison in
   `exists_derivedPullbackComposition`: `Functor.leftDerived_fac` gives its actual
   counit equation, including the ordinary mate in the correct direction.
   The choices of psi and theta are determined by all summand equations:
   left-adjoint pullbacks preserve the summand coproducts, so mapped inclusions
   are jointly epimorphic; degreewise equality determines the chain hom and
   `Iso.ext` determines the isomorphism. No arbitrary existence witness is used.

3. **Split statement: pass as a decomposition.** Read the ordinary theorem with
   all three summand hypotheses, its node and the statements of
   `module_pullback_tensor` and `exists_tensorPullbackAdjunction`. The module
   tensorator is pinned by its formula on unit images of pure tensors; the
   adjunction is pinned by its section formula. The composite unit and mate
   identity identify both transposed summand routes. Left adjoints preserve the
   coproducts, giving the chain equality. Naturality of the localization tensor
   map then gives the displayed localized square; theta inverse and f*(psi
   inverse) are on the required side. Identity arrows retain the pinned units
   (no assumption that a chosen adjunction is literally identity); complexes
   concentrated in degree zero reduce to this module square. Zero complexes,
   zero modules and empty schemes require no excluded case or finiteness.
   This lemma has neither K-flat hypotheses nor derived pullback functors,
   tensorators or counits; it isolates the ordinary part rather than restating
   the parent's derived assertion. The reduction proves genuine diagram algebra,
   but one old hole is exchanged for one simpler hole: net zero.
   Independently searched LeanFinder for composition mates of monoidal left
   adjoints and Loogle for conjugateIsoEquiv, and searched the repository and
   Mathlib homology sources for tensor/composition and summand extensionality.
   `Adjunction.isMonoidal_comp`, `unit_conjugateEquiv_symm`,
   `mapCochainComplex_δ_comp_tensorHom` and homological-complex monoidal naturality
   supply generic machinery, not the missing pinned module compatibility.
   `pullbackComp_tensor` is proved but uses ordinary `pullback` and its monoidal
   structure; identifying these with the recorded tensor-formula functor and
   chosen module tensorator remains additional work. No direct existing match
   or quick complete proof of the split statement was found.

4. **Route and pruning: pass after report repair.** The parent uses the canonical
   normalization at P,N, K-flat pullback preservation at g, canonical normalization
   at g*P,g*N, the actual composition counit factorization, and the ordinary square.
   It never invokes the direct derived tensorator or the importing theorem's
   final derived cancellation result. Every import has a use; proof-only imports
   are plain imports. Compared all seven old `proof_deps`: five are retained or
   replaced explicitly, the tensor-product dependency is unnecessary, and the
   module tensor and adjunction dependencies move behind the new node.
   The report now names all three removed direct dependencies and explicitly
   claims no globally pruned module. Read `dag/units/sk-thm-picard-duality.json`:
   its `realized.statement` and sole `realized.steps` entry are empty; no realized
   node or unit step is bypassed, and the unit record is unchanged.

5. **DAG and sources: pass after proof-text repair.** The parent's three steps
   correspond to hg/hf and hPg/hNg, then fac, then normalization_pasting with
   hchain and counit naturality. Both nodes' `proof_deps` equal the union of
   step uses. The new node has its source, searches, origin, creation metadata,
   parent provenance, chapter, unit and verbatim Lean statement. Read Stacks
   [079U](https://stacks.math.columbia.edu/tag/079U),
   [0D5S](https://stacks.math.columbia.edu/tag/0D5S) and
   [01CD](https://stacks.math.columbia.edu/tag/01CD): these supply the total-complex
   tensorator, composition via K-flat pullback, and ordinary module tensorator.
   The explicit ordinary compatibility is the stated unit-formula expansion,
   not a claim that Stacks already writes this exact localized equation.

**Second-reader changes.** Kept the Lean reduction and all signatures. Expanded
only the new theorem's proof docstring with the ordinary chain equation, the
mate/unit identification, preservation of summand coproducts, and the precise
inverse cancellation. Corrected the new node's instruction from postcomposing
with inverses to precomposing the ordinary chain equality with them, then
substituting in tensor naturality. Completed `## No longer needed` for the two
old dependencies moved to the new lemma. Added this independent reading.
