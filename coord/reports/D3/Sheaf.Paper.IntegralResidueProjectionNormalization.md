## What changed

The original normalization theorem now has a complete Lean proof from two strictly
geometric properties. Its signature is unchanged. Three proved private categorical
lemmas establish the double-mate counit identity, the projection-normalization
calculation after transposition, and their assembly for a family of objects.

Six new modules construct the actual restriction/pullback square and its inverse
mate, the derived right-tensor comparison, ordinary strong
monoidality (including naturality, unit and associativity proofs), derived strong
monoidality on flat resolutions, the coefficient-pullback isomorphism, and the
canonical tensor-square assembly. In particular, none of these constructions
selects arbitrary data from a holed existence theorem. The coherent pull family
uses only the uniquely determined inverse of an explicitly constructed morphism.

The main module imports the tensor-square assembly for its proof. It publicly
imports the derived-monoidal API because its statement uses a local named copy of
the existing monoidal instance, definitionally equal to that instance. This keeps
large internal-module instance terms compact; it changes no tensor product, map,
hypothesis, conclusion, or downstream instance search. The node's proof route now
matches the Lean argument. The existing direct consumer `Sheaf.Paper.IntegralResidueComparisons` compiles
unchanged against the delivered overlay. The repair also exposes the existing proved
canonical tensor helper chain in the unclaimed `Sheaf.Paper.IntegralReductionTensor`;
its declaration types and bodies are unchanged. There are no forced adaptations. The public import and local elaboration commands
are documented in
`coord/changes/integral-residue-normalization-instance-cache.md`.

Repair of the return at head 5d481b7cd: removed the duplicate
`CategoryTheory.Mod.residueTensorHom_linear` and its six copied ordinary/homotopy/
counit declarations. `IntegralResidueTensorPresentation` publicly imports
`IntegralReductionTensor` and uses its existing specific counit and
`tensorPresentationDerivedCounit_isLeftDerivedFunctor`. No arbitrary presentation
is chosen from an existential theorem. The only new tensor-preservation instance
is stated for arbitrary C, rather than only the internal module category Mod C R.
The visibility-only change and complete consumer list are in
`coord/changes/integral-reduction-tensor-public-api.md`. The pre-return independent
reading below is retained as history; its duplicate-helper claims are superseded
by this repair, which requires a fresh independent reading.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_projection_normalization`.
The main module has zero holes. A clean import-order compilation checked all eight
modules without errors or warnings, each in 5.2–23.1 seconds, below the 60-second limit. Axiom probes on the explicit restriction
square, inverse mate, ordinary and derived monoidal data, tensor presentation and
coefficient-pullback isomorphism show only `propext`, `Classical.choice`,
`Quot.sound`; the assembly and normalization also depend on the reported holes. This is a decomposition, not an axiom-free proof
of the original theorem: one upper hole is closed and two lower holes are added,
so the hole net is -1 before any pruning in the maintained ledger.

The only holes delivered are:

- `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_pullSquare`
  (`new-integral-residue-derived-pull-square`): invertibility and composition of
  the fixed inverse mate. What remains is to formalize the balanced scalar tensor
  associativity comparison on resolutions and its composition law. The restriction
  square, inverse mate, and scalar-counit equation are already constructed/proved.
- `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorGeometry`
  (`new-integral-residue-tensor-geometry`): flat preservation by actual ordinary
  integral pullback and compatibility of the fixed tensor maps. What remains is
  the internal-module flatness bridge and the descent of the scalar associativity
  square through the canonical derived comparisons. Ordinary monoidality, its full
  coherence, derived monoidality conditional on flat preservation, both tensor
  presentations, and the coefficient-pullback isomorphism are already proved.

The repair adds zero holes and closes zero additional holes. The item still has
zero direct holes and the delivery retains the two previously reported split holes.
The exposed `IntegralReductionTensor` also has zero holes.

Fresh repair checks: both affected modules pass `tools/import_prune_check.py`,
including the exact duplicate guard that returned the delivery. The unchanged
`IntegralResidueComparisons` and `IntegralFiniteExchangeComparison` consumers compile
against the overlay. Fourteen fresh axiom probes confirm that every reused/new
tensor API declaration is free of `sorryAx`; the normalization retains exactly the
two reported geometric obligations through its imports. The normalization signature
is byte-for-byte unchanged, and the original tensor module differs solely by the
seven removed `private` keywords. Check logs are in `scratchpad/repair-*.log`.

New proved results include `residueExchangePullHom_counit`,
`residueExchangePullComparisons_counit`, `residue_exists_kFlatMap_iso`,
`residueDerivedOplax_isIso_δ`, `residueDerivedOplax_isIso_η`, all the
`CategoryTheory.Mod.ResidueOrdinary` tensor presentation, naturality and coherence
lemmas, and `integralResidue_tensorSquare`. All other new declarations construct
actual data with fully proved obligations. There is no hole inside a definition.

## No longer needed

The copied declarations `CategoryTheory.Mod.residueTensorHom_linear`,
`residueExtendComapTensorIso`, `residueExtendComapCounit`,
`residueTensorLeft_preservesKFlatQuasiIso`, `residueTensorHomotopyIso`,
`residueTensorCounit`, and `residueTensorCounit_isLeftDerivedFunctor` are removed
from the new tensor-presentation module. Their single existing implementation in
`IntegralReductionTensor` is reused. The old `residueGenericTensorLeft_preservesKFlatQuasiIso`
name is replaced by `CategoryTheory.genericTensorLeft_preservesKFlatQuasiIso`, whose
explicit binder B : C makes the generality over the existing Mod-only instance clear.
No additional whole module is pruned by the repair.

The explicit proof import `Sheaf.Paper.ContinuousIntegralCoefficients` is removed
from the original module: its declarations remain publicly available through
`Sheaf.Paper.IntegralResidueComparisonInterface`. No whole module is pruned.
The second reading also removes the redundant public import
`WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian` from
`IntegralResidueOrdinaryMonoidal` and
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle` from
`IntegralResidueTensorPresentation`; both are already public transitive imports
of their respective interface imports. Redundant explicit imports of
`WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor` were removed from the
new tensor-geometry and tensor-square modules; their declarations are already
available through the tensor-presentation API. The original direct proof dependency
`lem-weil-pbc-integral-residue-push-counit` is replaced by the generic Mathlib
`mateEquiv_counit` argument; its containing interface remains needed. The original
direct edge to `def-weil-pbc-continuous-integral-coefficients` becomes transitive
through the interface and the new constructions; the coefficient module remains
needed. No claim is made that either node is outside the targets' closure.

The supplied existential `hTensor` is no longer needed in the proof: a specific
canonical counit and its left-derived universal property are proved unconditionally
in `IntegralReductionTensor` and reused by `IntegralResidueTensorPresentation`.
The binder remains exactly as given.
No perfectness, dualizability, boundedness, properness, or invertibility of the
projection map is used.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled ordinary tensor coherence, derived monoidality,
scalar pull coherence and map normalization in one step. These have different
interfaces; the delivery constructs and proves the first two and the categorical
normalization, leaving only the two explicit geometric properties above.

The returned delivery incorrectly copied the private helper chain of the proved
`IntegralReductionTensor`. The canonical data required by the fixed tensor
compatibility equation are now exposed in that original module and imported,
rather than reproved under residue-specific names or chosen as an unspecified
tensor presentation. Every exposed helper has exactly its existing type and body.

The existing flat change-of-coefficients `derivedPullIso` cannot be applied to the
residue quotient: it requires exact scalar extension. The construction here uses
exact scalar restriction and its inverse adjunction mate instead. The existing
ordinary `SheafOfModules` and `ModuleCat` flatness lemmas are not statements about
these internal module objects, so no such lemma was silently substituted.

## New nodes

`new-integral-residue-derived-pull-square`: constructs the canonical restriction
square and inverse mate, proves its counit equation, and states the remaining
invertibility/composition property. Its inverse data are uniquely determined.

`new-integral-residue-tensor-presentation`: constructs restricted reduction as
right tensor by the restricted residue regular module in degree zero, using the
existing canonical left-derived presentation from
`lem-weil-pbc-integral-reduction-tensor` and the new derived tensor/single comparison.
Its proof dependency and Lean declarations now reflect this reuse.
The existing `lem-weil-pbc-integral-reduction-tensor` node gains only a Lean
declaration list recording the newly exported helpers; its statement and proof
route are unchanged.

`new-integral-residue-ordinary-monoidal`: constructs strong monoidality of ordinary
condensed-coefficient pullback. Its balanced tensor, naturality, unit and
associativity arguments are all proved.

`new-integral-residue-derived-monoidal`: constructs the derived strong monoidal
structure from flat-preserving ordinary data, with derived tensor and unit
invertibility proved. Also names the existing derived monoidal structure to avoid
repeating its large instance term in the normalization statement.

`new-integral-residue-tensor-geometry`: constructs the coefficient-pullback and
source tensor isomorphisms and states flat preservation plus compatibility of the
fixed maps. Its docstring specifies the remaining resolution-level argument.

`new-integral-residue-derived-tensor-square`: proved assembly of these explicit
monoidal and tensor data with their compatibility property. All six nodes retain
the original target ancestry, chapter and blueprint unit. The unit's own statement
and proof-step realizations are unchanged.

Change record: `coord/changes/integral-residue-normalization-instance-cache.md`.

Repair change record: `coord/changes/integral-reduction-tensor-public-api.md`.


## Earlier second reading (a previous round; superseded)

1. **Existing declarations and visibility — pass.** Diffed every delivered path
   against the shared repository. Only `IntegralResidueProjectionNormalization`
   previously exists there. Its theorem signature, including `hTensor`, universes,
   the existential monoidal structure, both isomorphisms and the complete map
   equality, is byte-for-byte identical. The only existing node edits are `proof`,
   `proof_deps` and `proof_origin`. No other group's module is adapted. Read the
   instance-cache change record: its public import is needed because the named
   monoidal-category term occurs in the elaborated signature; the name unfolds
   to the original instance and is selected only locally. A scratch copy with
   the original signature and original ambient instance selection accepts the
   delivered theorem directly (43.7 seconds). The unchanged direct consumer
   `IntegralResidueComparisons` also compiles against the overlay (18.6 seconds).

2. **Proofs and constructed data — pass.** Read all seven modules and compiled
   them in import order (8.1–28.3 seconds per file in this reading). The only two
   `sorry` occurrences are the reported public named theorems
   `integralResidue_pullSquare` and `integralResidue_tensorGeometry`, each exactly
   `by sorry`. There are no forbidden declarations or proof holes in definitions.
   In particular, `residueExchangePullHom` is a fixed inverse mate before its
   invertibility theorem; `residueExchangePullComparisons` uses only its uniquely
   determined inverse and propositional coherence. The tensor presentation uses
   proved left-derived uniqueness, and the ordinary/derived monoidal structures
   are actual constructions. No arbitrary witness is extracted from a holed
   existence theorem; the existential `hFlat` in the geometry theorem is a Prop.
   Independently ran sixteen `#print axioms` probes: the restriction square,
   inverse mate, tensor isomorphisms, monoidal data and canonical left-derived
   presentation use only `propext`, `Classical.choice`, `Quot.sound`. The two
   obligations, their assembled pull family, the tensor square and the final
   normalization additionally use `sorryAx`, exactly as reported.

3. **Remaining statements — pass as a decomposition.** Read Bhatt–Scholze
   Lemma 6.5.9(3) and its proof, and Remark 6.8.15 in the sandbox paper text.
   The perfectness assumption is needed for invertibility of the *projection*
   map, which this theorem does not assert. The two new obligations concern
   derived scalar pullback coherence and a fixed tensor compatibility equation,
   respectively, without a direct-image functor or a projection-map conclusion.
   They are strictly smaller than the original normalization argument. The
   explicit constructions fix the maps before stating their properties. Checked
   identity pullback, zero complexes and the empty scheme: the equations reduce
   to unit/associativity identities or the unique zero morphism. Reduction need
   not be flat over the integral coefficient; flat resolutions and exact scalar
   restriction are used instead. Repeated searches with new phrases using
   `msearch.py` LeanFinder, Loogle and grep, plus `rg` on `lean/Sheaf` and
   `lean/WeilConjectures`. The hits concern ordinary `SheafOfModules`, `ModuleCat`
   or flat coefficient change. Read `ChangeOfCoefficients.lean`: `derivedPullIso`
   assumes exact scalar extension and cannot discharge the quotient-coefficient
   obligation. No existing theorem closes either remaining obligation directly.
   Both have source/proof docstrings and matching new nodes. Neither is the
   original theorem renamed. One original hole is closed and two lower holes
   remain: this is not an axiom-free proof or positive net hole progress.

4. **Top-down argument, imports and unit route — pass after import pruning.**
   Checked `doubleMate` against `rightAdjointUniq_hom_app_counit`; checked
   `normalization` against `mateEquiv_counit` and the counit formula for
   `rightAdjointProjectionMap`. Their combination supplies the original map
   equality, with no invertibility assumption on the projection map. The tensor
   presentation is canonically constructed rather than chosen from `hTensor`.
   Both removed original proof-dependency edges are named under `No longer
   needed`; their modules remain transitively needed. Checked
   `dag/units/sk-thm-properbasechange.json`: its statement and all three realized
   steps are untouched; this reduction is below the unit level. The local named
   instance is definitionally the original tensor structure, so it changes no
   target's meaning.

5. **DAG and Lean agreement — pass.** Read the original node and all six new
   nodes alongside their modules. The main route is pull-square construction,
   tensor-square assembly and the proved categorical transpose calculation;
   `proof_deps` is the union of the recorded uses. The remaining nodes separate
   the proved ordinary monoidality, conditional derived monoidality and canonical
   tensor presentation from the two geometric properties. Their Lean records,
   ancestry, chapter, unit, creation records and three search kinds are present.
   Existing statement metadata and the unit realization are unchanged.

Second-reading changes: removed two redundant public imports from the new
ordinary-monoidal and tensor-presentation modules (already available through
public transitive imports), corrected `No longer needed` to name the original
removed explicit coefficient import, and added this independent reading. No
statement, definition or proof body was changed.

## Second reading by D3

1. **Existing declarations and signatures — pass.** I compared every delivered existing
module with the repository baseline. The target theorem signature is byte-for-byte
unchanged; the IntegralReductionTensor edits expose existing canonical helpers without
changing their types or bodies. The new modules are the declared split-off construction
modules, and the change records identify the public API and adaptation effects.

2. **Proofs and constructed data — pass.** I compiled all eight Lean modules in import
order with `lcompile.py --all`. There are no forbidden declarations and no `sorry` in a
definition. The only remaining `sorry`s are the two named public geometric obligations
`integralResidue_pullSquare` and `integralResidue_tensorGeometry`, each recorded with a
matching node and proof docstring. The explicit tensor, monoidal, mate, and comparison
data are constructed canonically; no arbitrary witness is selected from a holed
existence proposition.

3. **Remaining statements — pass as a decomposition.** The two remaining statements
are strictly smaller than the original normalization theorem: one asserts invertibility
and composition of the fixed scalar pull mate, and the other asserts flat preservation
and the fixed tensor compatibility square. Their hypotheses and conclusions match the
Lean declarations and the source argument; neither restates the original target.

4. **Top-down proof, imports, and route — pass.** The target proof uses the canonical
pull-comparison and tensor-square modules, then the private double-mate and normalization
calculation. The unit route is preserved. Explicit proof-only imports are plain imports,
redundant imports are removed as listed above, and the supplied `hTensor` is not used to
choose data because the canonical balanced-tensor presentation is proved independently.

5. **DAG and Lean agreement — pass.** I checked the target node and all new nodes against
the declarations and proof uses. `proof`, `proof_deps`, and `proof_origin` record the
actual route; each split-off theorem has its source, blueprint, Lean record, and node.
The unit record and realized steps are unchanged.

I changed only this report section during the second reading. No Lean statement, proof,
definition, node statement, or import was changed.
