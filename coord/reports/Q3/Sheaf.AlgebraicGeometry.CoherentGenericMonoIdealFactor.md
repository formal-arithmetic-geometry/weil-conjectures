## What changed

Proved `AlgebraicGeometry.Scheme.Modules.coherent_generic_mono_ideal_factor` in
`Sheaf.AlgebraicGeometry.CoherentGenericMonoIdealFactor`, with its existing signature,
visibility, and docstring unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.CoherentKernelCokernelSum`,
`Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`,
`Sheaf.Algebra.Homology.ModuleStalkExact`, `Sheaf.Paper.SchemeTheoreticSupport`,
`Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine`, and
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`.

The proof follows the planned coherent-cokernel annihilator argument. It proves the
cokernel stalk is zero by two surjective lifts and the cokernel condition, identifies
full ideal stalks using the two support descriptions, and proves the product composite
vanishes by the affine section-range formula, linearity, and sheaf separatedness.
The ideal itself is quasi-coherent by the powers clause at n = 1. Mathlib's
`Abelian.monoLift` and `Abelian.monoLift_comp` provide the final factorization.
The existential ideal is used within a theorem, not to define arbitrary data; its
specified affine annihilator ideals also determine the ideal-sheaf data uniquely.

Updated the existing node's proof, proof dependencies, and proof origin to record
these actual steps. No new modules, new nodes, statement changes, or forced
adaptations. The item realizes no unit statement or unit step, and the route of
`sk-thm-p1` is unchanged.

Read the source online because the cited local Stacks tex files are absent here:
[Tag 01YL](https://stacks.math.columbia.edu/tag/01YL), third proof paragraph,
and [Tag 05JU](https://stacks.math.columbia.edu/tag/05JU), affine annihilator support.
The library and Mathlib searches found the general categorical lift rather than a
ready-made coherent sheaf factorization. Searches ran through `msearch.py` with
LeanFinder, Loogle, and grep, supplemented by local source searches.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.Modules.coherent_generic_mono_ideal_factor`
(node `lem-weil-pbc-coherent-generic-mono-ideal-factor`).
No `sorry` remains in the delivered module. Added 0 holes and split off 0 statements.
This is a proof from existing declarations, not a decomposition into new holes.
Some imported declarations may still depend on unfinished proofs; none is restated
or changed in this delivery.

The module compiles through `lcompile.py` with no errors or warnings. The argument
includes zero source, target, and cokernel without extra nonzero hypotheses, requires
no quasi-compactness, and uses arbitrary-point surjectivity, not generic rank.

## No longer needed

Pruned the proof dependency `lem-weil-pbc-abelian-exact-iff-epi-kernel-lift`:
its exactness/epimorphism equivalence is not used. The proof directly uses Mathlib's
`Abelian.monoLift` and `Abelian.monoLift_comp`; no Sheaf module belongs to the pruned
Mathlib leaf. No original import was removed: all three public imports support the
unchanged signature. Removed the trial proof-only import
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`, which the final proof does not use.
All six added Sheaf proof imports are used; all other planned proof nodes remain needed.
No additional Sheaf or WeilConjectures module is claimed globally unreachable.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or interface fault found. The DAG's final step proposed an
image/kernel comparison and cited the epi-kernel-lift exactness criterion. Mathlib's
mono-cokernel lift packages the required universal property directly, so that criterion
is unnecessary. The cokernel-stalk exactness conjunct is likewise unnecessary once
surjectivity of the stalk projection and the cokernel condition are used. The support
and affine product interfaces fit the plan unchanged.

## Second reading by Q3

1. **Interface unchanged — pass.** Read the complete repository and sandbox modules
   and their diff. The sole existing declaration's signature, visibility, universe,
   namespace and docstring are byte-for-byte unchanged. In particular the hypotheses
   remain locally Noetherian X, coherent K and G, mono a, arbitrary point ξ, and
   bijective stalk map; the conclusion retains mono and quasi-coherence of J, full
   ideal stalk, and the exact factorization equality. The only Lean changes are six
   plain proof imports and replacing the theorem's `sorry` with its proof. No
   definition, public import, target statement or other module changed. No change
   record is needed.
2. **Proof and axioms — pass.** Independently compiled the delivered file through
   `lcompile.py`, cleanly (5.9 seconds). Scanned its declarations: one theorem, no
   `sorry`, no definition, and no forbidden axiom/unsafe/opaque/implemented_by/extern
   or kernel-check bypass. Compiled a scratch copy with
   `#print axioms AlgebraicGeometry.Scheme.Modules.coherent_generic_mono_ideal_factor`:
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The last is from
   unfinished dependencies, so this closes the local hole, not the entire dependency
   closure. Checked the two stalk lifts and cokernel condition, the support-set
   contradiction, affine product membership, linearity and annihilator membership,
   restriction naturality and sheaf separatedness, and the final Mathlib mono lift.
   The cokernel is a real categorical construction. The ideal supplied by
   `schemeTheoreticSupport` has each affine ideal specified as Ann(Q(U)); these
   components determine its ideal-sheaf data, with compatibility proofs irrelevant.
   Its repository proof also constructs those components explicitly. There is no
   arbitrary existence witness used to define data.
3. **Split statements and edge cases — pass.** There are no new modules, declarations,
   nodes, or split-off statements. No hole has been relocated under a new name.
   Checked zero Q (unit annihilator and full stalk), zero G, and zero K with the
   stated bijectivity hypothesis: the stalk and affine arguments include them.
   An empty scheme admits no ξ, so does not create an exceptional case. Nothing uses
   a generic-point, integrality, quasi-compactness or nonzero hypothesis.
4. **Shortest route, imports and unit — pass.** Read the six imported theorem
   interfaces and Mathlib's `monoLift`/`monoLift_comp` definitions. A fresh Loogle
   search through `msearch.py` for `CategoryTheory.Abelian.monoLift` confirms precisely
   the direct categorical factorization used; local searches for generic ideal
   factors and annihilators in Sheaf, upstream modules and Mathlib found no ready-made
   theorem replacing this item. The nearby generic-point inclusion and integral
   ideal results have different hypotheses and conclusions. All six proof imports
   supply declarations explicitly used. The three original public imports support
   the unchanged signature. Compared old and new `proof_deps`: the sole removed
   dependency is `lem-weil-pbc-abelian-exact-iff-epi-kernel-lift`, already fully named
   in `No longer needed`; no additional pruning is claimed. Read sk-thm-p1's
   `realized`: this node realizes neither its statement nor a step, so the local
   mono-lift shortcut preserves the unit route. Read Stacks
   [01YL](https://stacks.math.columbia.edu/tag/01YL), the ideal-multiple paragraph,
   and [05JU](https://stacks.math.columbia.edu/tag/05JU), the affine annihilator and
   support clauses: they support this cokernel-annihilator argument.
5. **DAG agrees — pass.** Compared the node files: only `proof`, `proof_deps` and
   `proof_origin` differ. The dependency set is exactly the union of the proof
   steps' `uses`, with no new dependencies. Checked each retained node's statement
   and Lean declaration against its actual use: coherent cokernel, coherence/QC/FT
   equivalence, epi stalk projection, affine annihilator and support, ideal-stalk
   support criterion, and product range plus the n=1 powers clause. The final
   elementary step is the two-line application of Mathlib's mono lift and its
   composition theorem. The proof origin names the literature and Mathlib route.

Changes by the second reader: added this independent review and the explicit axiom
result; no Lean or DAG repair was necessary. Closed 1 original hole, added 0 holes,
and split off 0 statements, as recorded above.
