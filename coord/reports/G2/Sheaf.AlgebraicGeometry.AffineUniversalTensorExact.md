## What changed

Completed `AlgebraicGeometry.Scheme.Modules.affine_universal_tensor_exact`, preserving its
original signature and public imports. The square-zero extension `TrivSqZeroExt A N`
is an explicit algebra; `inrHom` and `sndHom` give an A-linear retraction. Tensoring,
complex formation and homology carry that retraction to the desired homology object.
Universal pullback vanishing and the affine comparison then make its identity zero.

Added two proved modules: `Sheaf.AlgebraicGeometry.AffineTensorPullbackComplexComparison`
and `Sheaf.AlgebraicGeometry.AffineTensorPullbackHomologyComparison`. Completed the
previous attempt's admitted complex comparison using the source-library
`sectionsRestrictFromSpecLinearEquiv`, the affine counit, `tildePullbackIso`, and the
natural composition comparisons lifted to complexes. The homology comparison proves
kernel preservation of tilde through full faithfulness and quasi-coherent kernel
closure, then uses the exact-functor homology comparison. Imports needed only by proofs
are non-public. No definitions, existing interfaces, or other groups' modules changed.

All three modules compile together without warnings. `#print axioms` for the item
reports exactly `propext`, `Classical.choice`, and `Quot.sound`; in particular it does
not reach any admitted theorem. The DAG records now describe the actual Lean proof.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Scheme.Modules.affine_universal_tensor_exact`
(node `lem-pc-affine-universal-tensor-exact`).

The two new declarations are proved:
`AlgebraicGeometry.Scheme.Modules.affine_tensor_pullback_complex_comparison`
(node `lem-pc-affine-tensor-pullback-complex-comparison`) and
`AlgebraicGeometry.Scheme.Modules.affine_tensor_pullback_homology_comparison`
(node `lem-pc-affine-tensor-pullback-homology-comparison`).

No `sorry` remains in any delivered module. Holes closed: 1 original hole;
holes added: 0. This is a proof, not a decomposition into new holes.

## No longer needed

Removed the previous attempt's unused proof import
`WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde` from the homology comparison;
it is used only in the complex comparison now. Replaced the new complex module's
broad `Mathlib.RingTheory.Flat.CategoryTheory` and
`Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex` imports by the statement
requirements `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings` and
`Mathlib.Algebra.Homology.Additive`. The second reader also replaced the new homology module’s broad public import
`Mathlib.RingTheory.Flat.CategoryTheory` by
`Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic`; no flatness result is used.
No original public import of the item was removed.

The original plan's `lem-weil-pbc-quasi-coherent-module-cokernel-closure`, carried by
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`, is not needed for this
proof: tilde preserves colimits by its adjunction, so kernel preservation suffices for
its exactness. Neither comparison imports that module for the cokernel closure theorem.
`lem-weil-pbc-retract-of-zero-object` is no longer a separate proof dependency: the
homology identity calculation proves the retraction-of-zero argument directly.
`def-pc-base-change` remains a statement dependency, but is not a separate proof lemma.
These are per-item prunings; no claim is made that another target cannot need them.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's new node statements were incomplete descriptions, and its
proof dependency lists still mentioned unused cokernel closure. They now state all
objects, assumptions and conclusions and record the actual construction. The item
node's previous last step omitted the crucial retraction; it now describes the
explicit square-zero maps and the identity calculation after applying homology.

The previous report claimed a second reading. Removed that section: the independent
reader has not reviewed this delivery yet. Also removed an unnecessary interface change
record, since only the existing theorem's proof and proof-only imports change.

The source library already proves the natural `tildePullbackIso` for ordinary
`Modules.pullback`; this supplies the affine pullback step directly. The corresponding
DAG node also records a theorem about `tensorPullback`, so the proof uses the proved
source-library counterpart rather than introducing a duplicate comparison with a hole.
Cross-unit affine-equivalence, kernel-closure, and open-restriction facts are used as
proved library/Mathlib tools. The coherence unit's `realized` record is empty, and no
unit statement or realized step has been bypassed or changed.

The new comparison statements were checked for the zero complex, zero module, zero
ring/empty affine scheme, and B=A. Their constructions are natural isomorphisms and
use no flatness, boundedness, finite-presentation or nonzero-ring assumption. In
particular, the proof commutes tilde with homology; it does not assume that global
sections on all sheaves preserves cokernels. Sources read: Stacks Tags
[01IB](https://stacks.math.columbia.edu/tag/01IB) and
[01I9](https://stacks.math.columbia.edu/tag/01I9), along with the cited Lean source proofs.

## New nodes

`lem-pc-affine-tensor-pullback-complex-comparison` records a proved isomorphism between
the sheafified ordinary scalar extension of the fixed global-sections complex and the
affine pullback complex. Its naturality includes every differential. It assumes no
vanishing hypothesis and is one strictly smaller part of the square-zero argument.

`lem-pc-affine-tensor-pullback-homology-comparison` records the proved homology
isomorphism for an arbitrary A-algebra B, including restriction of scalars. It uses
the complex comparison, proves kernel preservation, and commutes exact functors with
homology; it assumes no universal vanishing and has no arbitrary module N to test.
Both nodes carry actual Lean signatures, source places, proof steps and three kinds
of search. LeanSearch was unavailable (Internal Server Error); Loogle, LeanFinder,
and direct source searches supplied the reused ingredients. No change record is needed.

The initial worker dry run flagged the module-level elaboration options as
importer-visible commands. They were moved inside the item's proof, and the
subsequent dry run printed OK (commit `27cd20c338`), accepting the pending second
reading as appropriate for `--no-push`. Nothing was pushed and no second-reading
section has been written by this worker.


## Second reading by G2

1. **Unchanged interface — pass.** Read all three delivered Lean files and diffed
   `AffineUniversalTensorExact.lean` against the repository version. Its only changes
   are two plain proof imports and the replacement of `by sorry` by its proof.
   The existing theorem signature and docstring are byte-for-byte unchanged; its
   explicit affine hypothesis, termwise quasi-coherence, all scheme base-change
   tests, arbitrary A-module N, and ExactAt conclusion are preserved. The two
   comparison modules are new. No existing definition, target, visibility or other
   group's module is changed, and no change record is needed.

2. **Kernel proof and axioms — pass.** Compiled the three modules in import order
   with lcompile.py, without warnings. Searched their source for sorry and forbidden
   declarations: none. In a scratch copy, with explicit imports of both comparison
   modules (the complex comparison is intentionally hidden by its plain import),
   printed axioms of all three public theorems. Each reports exactly propext,
   Classical.choice and Quot.sound, without sorryAx. B is the actual TrivSqZeroExt
   A N, not a witness of an admitted existence theorem. The projection to N is
   A-linear, not asserted to be a ring homomorphism. The equation j ≫ p = id
   survives tensoring, complex formation and homology; the final identity is zero
   because its factorization has a zero intermediate homology object.

3. **New comparisons — pass; no admitted statements split off.** Read Stacks
   [01IB](https://stacks.math.columbia.edu/tag/01IB) (affine equivalence) and
   [01I9](https://stacks.math.columbia.edu/tag/01I9), clause (1) (functorial ordinary
   scalar-extension pullback), and the Lean implementations in Modules.PullbackTilde,
   Modules.LocallyFreeAffine, Modules.QuasicoherentKernel and PreservesQuasiIso.
   For the complex comparison, the affine counit is used only for quasi-coherent
   terms of the open restriction; sectionsRestrictFromSpecLinearEquiv and
   Hom.app_presheaf_map supply naturality. tildePullbackIso, restrictFunctorIsoPullback,
   pullbackComp and fromSpec_top give exactly the stated map Spec B -> S.
   The additive tilde instance explicitly assumed by this comparison is constructed
   from its left adjunction in the homology caller. For homology, the kernel is
   quasi-coherent, its counit is invertible, and full faithfulness lifts and reflects
   the kernel fork. The left adjunction supplies colimits; this proves exactness
   of tilde, without claiming global sections is exact on arbitrary sheaves.
   Tensor commutation is checked on pure tensors and extended by tensor induction.
   B=A recovers the affine presentation, B=0 gives zero modules, and C=0 and the
   empty affine scheme introduce no excluded case. Neither comparison assumes the
   universal vanishing hypothesis, flatness, boundedness or finite presentation;
   each is strictly a part of the argument, and both are proved.

4. **Shortest route, imports and unit — pass after import repair.** Independently
   searched using msearch LeanFinder for associated sheaf preservation of kernels
   and homology, Loogle for `"tilde", "Preserves"`, and grep for
   `toTildeΓNatIso|tildePullbackΓEquiv|preservesKernel`, plus direct rg through
   lean/Sheaf and the source modules. Found general categorical ingredients, not
   the complete tensor/pullback comparison. AffineDerivedTildeHomologyComparison
   has the same kernel argument as a private helper and a derived-category public
   conclusion; AffinePseudoCoherentRHomQuasiCoherent also hides its exactness helper.
   Neither is a shorter accessible replacement for the ordinary comparison here.
   Kept the proved source tildePullbackIso rather than importing the tensorPullback
   counterpart just to convert it back. FreeGenerator is needed for its explicit
   Hom.app_presheaf_map lemma. Narrowed the homology module's public flatness import
   to ModuleCat.Monoidal.Basic, which supplies tensor notation used by its statement.
   All newly added proof-only imports are plain imports. Of the item's six old
   proof dependencies, affine-tilde-gamma-adjunction, quasi-coherent-module-kernel
   and tilde-pullback-base-change remain used through the comparisons; cokernel
   closure and the separate retract-of-zero lemma are unnecessary, while base-change
   remains a statement dependency rather than a proof lemma. The No longer needed
   section accounts for these. Read the coherence unit record and its imported
   section in dag/notes: realized.statement=[] and realized.steps=[[]]. The square-zero
   reduction remains on the flat-model route; no unit statement or step is changed.

5. **DAG agreement — pass after metadata repair.** Matched each new node's lean.statement
   to its full theorem signature and checked its source, chapter, unit, blueprint
   ancestry, created record and search records. The item's three proof steps are
   precisely the explicit retraction, the affine homology comparison and the zero
   identity calculation; its sole direct proof dependency is the homology comparison.
   The complex node records the affine presentation and pullback assembly, while the
   homology node records kernel closure, affine adjunction and the complex comparison.
   Their proof_deps are the unions of the corresponding uses lists. The source-library
   ordinary pullback counterpart used for the tilde base-change node is explicitly
   identified in the report and proof text; the separate tensorPullback interface
   is not silently substituted. Added verdict=unavailable to the two new nodes'
   LeanSearch outage entries, so an unavailable service is not recorded as a failed
   mathematical search. No existing node statement or unit realization changed.

Second-reading changes: narrowed one new-module public import and corrected two
search-outage verdicts; completed this independent review. No proof body, existing
signature or mathematical statement needed repair. The delivery closes one original
hole, adds zero holes, and contains two fully proved comparison lemmas.
