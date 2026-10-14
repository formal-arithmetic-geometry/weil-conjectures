## What changed

In Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso, retain the first worker's
componentwise construction of AlgebraicGeometry.schemeHomTensorPullbackIso using
NatIso.ofComponents and asIso. Its hom components are the original witness's hom
components; Iso.ext identifies the reconstructed iso with that witness. The already
proved IsCanonicalPullbackTensorComparison.unique determines these components for
the fixed shared counit. All retained existing declaration signatures and visibility are unchanged.
The two retired declarations are private proof helpers, named below.

The second reader removed the redundant added public theorem
schemeHomTensorPullbackIso_unique: component uniqueness and Mathlib Iso.ext/NatTrans.ext
already give this consequence, and no proof needs a separate declaration. No new
statement or node is delivered. Demote the upstream ExactFunctor import to a plain
proof/construction import;
its imported instance infrastructure is needed locally but none of its extension
declarations occurs in an interface. Respect transparency in the choice wrapper,
and replace the repeated K-flat invertibility proof with the already proved
canonicalPullbackTensor_monoidal_realization. It identifies each component with
an inverse tensorator, so IsIso follows immediately. Remove the now-unused private
helpers pullbackTensorModelMap_isIso and pullbackCounit_isIso.
Retain local irreducibility of the adjunction and tensor wrappers for the mate proofs.

Change record: coord/changes/schemeHomTensorPullbackIso-uniqueness.md.

## Proved and sorry left

Original holes closed: none (the baseline module has zero textual sorry proofs).
Holes added: none. Split-off statements: none. The existing
exists_schemeHomTensorPullbackIso is proved by the shorter inverse tensorator route. The unchanged schemeGlobalHomAdjunctionMap_isIso remains proved.
Two private, sorry-free helpers are retired because this route no longer uses them.
This is a partial choice-data repair, not a net reduction of proof holes.

The independent normalization issue for schemeHomPullbackAdjunction remains open.
exists_schemeDerivedAdjunction and exists_derivedPullbackComposition are proved,
but their fresh shared counit need not equal the original derivedPullback counit.
No assertion of independence under changing that counit is made. No arbitrary
witness from an unproved mere-existence theorem is newly introduced.

## No longer needed

Removed imports: Sheaf.Algebra.Homology.KFlatResolution,
Sheaf.Algebra.Homology.KFlatTensorProduct, Sheaf.Algebra.Homology.KFlatPullback.
Their proof nodes lem-pc-kflat-resolution, lem-pc-kflat-tensor-product and
lem-pc-kflat-pullback-preservation are no longer directly needed by this item.
The node instead uses the already proved
lem-pc-canonical-pullback-tensor-monoidal-realization. Add its module as a plain
proof import. No module is claimed pruned from the whole targets' closure.

Demoted to plain import:
WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor. Its instance
infrastructure is needed locally (removal was tested and rejected), while
mapDerivedCategory and its homotopy factorization are from the Mathlib interface
already imported publicly by GlobalDerivedHom. The remaining old proof
dependencies continue to be used; derived pullback and tensor-structure definition
dependencies are retained in the evaluation-mate step.

## Where the brief, the DAG or earlier work was wrong

The dispatched module has no original proof holes; its queue entry is a choice-data
audit. The tensor audit predates the proved canonical comparison uniqueness result.
The tensor family is determined with the shared counit fixed; this does not repair
normalization of the separate pullback adjunction. The original worker added an
unnecessary public uniqueness wrapper in the item's module and kept a proof/construction
import public. The wrapper is removed and the import demoted in the second reading.

Independent searches: leanfinder on equality of natural isomorphisms found Iso.ext,
NatTrans.ext, and NatIso.isIso_of_isIso_app; loogle on CategoryTheory.Iso.ext found
the exact extensionality theorem. Mathlib grep for extensionality in the Iso path
returned no hits (it is a file rather than that directory). Local rg on alternative
pullback/tensor/uniqueness terms found the existing canonical comparison uniqueness
at CanonicalPullbackTensorComparison.lean:381. No new mathematical lemma is needed.
A local search additionally found the
proved canonicalPullbackTensor_monoidal_realization and its available compiled
module; its statement supplies the exact inverse-tensorator equation used.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module and node with the repository versions using diff.
   Every retained old declaration signature and visibility is unchanged. The two
   unused private helpers are explicitly retired. The sole changed
   data body is schemeHomTensorPullbackIso, explicitly recorded. Its reconstruction
   preserves each hom component, and Iso.ext therefore preserves the entire iso,
   including the inverse components used by the four direct declaration users.
   A scratch example proved equality with the exact old Classical.choose body
   by explicit unfolding, Iso.ext and component extensionality. A second scratch
   example verified the canonical predicate for the reconstructed iso; both
   compiled cleanly in 29.3 seconds.
   The downstream importer checks require a forced proof adaptation of MixedHomTensorPullbackIso, which uses import all to access the deleted private helpers.
2. Read the entire module, including the generic evaluation mate and tensor-Hom
   adjunction helpers, the right-derived Leray universal comparison, K-flat tensor
   invertibility, coherator detection, and naturality. No textual sorry or forbidden
   declaration occurs. The delivered module compiled cleanly in 29.1 seconds.
   The delivery dry run passed, including the all-declaration axiom probe.
   Direct #print axioms checks show only propext, Classical.choice and Quot.sound
   for the tensor iso and its existence theorem. The global-Hom invertibility
   theorem and packaged iso additionally reach sorryAx through existing imported
   dependencies; no local or new hole accounts for it. This is not a claim that
   their entire dependency closure is complete.
3. No split-off statement survives. The proposed uniqueness wrapper was true:
   canonical family uniqueness followed by functor-category Iso.ext proves it for
   arbitrary schemes and every pair of derived objects, including zero objects and
   the empty scheme; no nonempty or boundedness hypothesis is needed. It is redundant
   and has been removed instead of adding another module or node.
4. Read Stacks Tag 079U (lemma-pullback-tensor-product) and Tag 0B6I
   (lemma-iso-global-hom) at https://stacks.math.columbia.edu/tag/079U and
   https://stacks.math.columbia.edu/tag/0B6I. The monoidal-realization dependency
   proves the K-flat total tensor/counit argument
   once; this module now uses its exact inverse-tensorator equation. The Leray/
   coherator reduction follows Tag 0B6I. The final statement keeps
   X and Y qcqs, the restricted right adjoint a, P on X and K on Y, the actual
   counit-induced map, and both invertibility and naturality clauses. The extension import is
   retained privately for its needed instance infrastructure. sk-thm-picard-duality.realized has empty
   statement and step lists; no unit statement or route is changed.
5. Read lem-pc-global-hom-adjunction and all its proof steps/dependencies. The node
   records component invertibility from the proved monoidal realization, evaluation
   mate, qcqs sheaf Hom comparison, and global-sections detection. Its first step
   and proof_deps now match the shorter route. Component uniqueness and Iso.ext
   justify equality of the reconstructed iso. No new declaration/node, statement,
   unit, or blueprint field is changed.

Second-reading changes: remove the redundant new theorem and demote the proof/construction import;
replace the repeated K-flat proof by the proved monoidal realization, remove two
private helpers and three imports, and respect transparency in the choice wrapper;
correct the node, report and change record accordingly. The separate adjunction
normalization repair is explicitly left open.


## Forced adaptations

Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso is unclaimed. Its original
source compiles against baseline but fails against the delivered
GlobalHomAdjunctionIso at 65:12 with `Unknown identifier pullbackTensorModelMap_isIso`;
lines 69–71 also reference the deleted `pullbackCounit_isIso`. The `import all`
exposes those private helpers in baseline, so retiring them forces this adaptation.
Every existing declaration signature and visibility remains unchanged.

After line 8, add this proof import:

```lean
import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorMonoidalRealization
```

Replace the entire proof block from `  have hflat (P N : CochainComplex`
through `  have (Z : schemeDerivedCategory S × schemeDerivedCategory S) := hc Z`
with exactly:

```lean
  obtain ⟨m, hm⟩ := canonicalPullbackTensor_monoidal_realization h τ hτ
  have (Z : schemeDerivedCategory S × schemeDerivedCategory S) : IsIso (c.app Z) := by
    change IsIso (τ Z.1 Z.2)
    rw [← hm Z.1 Z.2]
    infer_instance
```

The following `exact ⟨NatIso.ofComponents ...` block is unchanged. The canonical
realization identifies each comparison component with an inverse tensorator,
providing its invertibility without the deleted helpers. No other lines of the
adapted module change. The sandbox set compiled successfully with lcompile.py --all:
GlobalHomAdjunctionIso in 33.1 seconds and MixedHomTensorPullbackIso in 4.6 seconds.
Thus the adaptation compiles against the delivered module, with no compiler errors
or warnings.


## Second reading by Q3

This is the dispatcher's independent final reading of the delivered set, including
MixedHomTensorPullbackIso, on 2026-10-14. The earlier reading above is historical.

1. Interface verdict: pass. Read both complete modules and diffed each against the
   read-only repository. The declaration-table comparison reports no changed
   existing statement in either module. All retained signatures and visibility
   are byte-for-byte unchanged. The data-body reconstruction and the public import
   demotion are declared in schemeHomTensorPullbackIso-uniqueness.md. The two
   deleted declarations are private proof helpers. Recompiled the scratch equality
   with the exact old Classical.choose body: unfold, Iso.ext, component extensionality
   and rfl prove equality of the entire iso, including inverses. Thus downstream
   statements retain their meanings. The adjunction body itself is unchanged.
2. Proof verdict: pass for this partial repair. lcompile.py --all compiled
   GlobalHomAdjunctionIso in 37.4 seconds and MixedHomTensorPullbackIso in 5.5 seconds,
   without warnings or errors. A token search found no sorry or forbidden declaration
   in either delivered module. The independently recompiled scratch checks took
   32.1 seconds and also verified the reconstructed canonical predicate.
   #print axioms reports only propext, Classical.choice and Quot.sound for
   schemeHomTensorPullbackIso and exists_schemeHomTensorPullbackIso. The unchanged
   schemeGlobalHomAdjunctionMap_isIso and schemeGlobalHomAdjunctionIso also use
   sorryAx through their existing imported dependencies, as already disclosed.
   No hole is closed or added, and no arbitrary data from an unproved existence
   statement is introduced by this delivery. The remaining adjunction normalization
   repair is explicitly not claimed complete.
3. Split-statement verdict: pass, vacuously. There are no new statements, nodes or
   split-off holes. Read canonicalPullbackTensor_monoidal_realization and the
   existing canonical-comparison uniqueness theorem: its equality of inverse
   tensorators supplies exactly the component invertibility needed, for every
   scheme morphism and every pair of unbounded derived objects. No extra flatness,
   nonemptiness or boundedness assumption is used; zero objects and empty schemes
   are included. Independently ran Loogle for CategoryTheory.Iso.ext and found the
   exact extensionality theorem; local rg checked alternative comparison/adjunction
   uses. No redundant uniqueness wrapper needs to be restored.
4. Route and pruning verdict: pass. Read the Stacks source online, Tag 079U,
   lemma-pullback-tensor-product, and Tag 0B6I, lemma-iso-global-hom. The latter's
   qcqs hypotheses, counit map and global-sections/coherator reduction are retained.
   The existing monoidal-realization theorem is the shorter route for the tensor
   step and preserves its canonical-coordinate condition. The three removed
   direct K-flat imports and their three old dependency nodes are all listed under
   No longer needed. No whole-closure module pruning is claimed. The unit record
   sk-thm-picard-duality has no realized statement or step nodes to bypass.
   MixedHomTensorPullbackIso's retained imports are outside the forced-line edit.
   Independently compiled a scratch copy of its repository original against the
   sandbox build: line 65 fails with Unknown identifier pullbackTensorModelMap_isIso.
   The adapted module compiles, and its only edits are the proof import and the
   replacement invertibility argument described under Forced adaptations.
5. DAG verdict: pass. The only changed node fields are proof, proof_deps and
   proof_origin. The dependency list equals the union of every proof step's uses.
   Step 1 now cites the proved monoidal realization for inverse tensorators; the
   remaining evaluation-mate, qcqs Hom and derived Leray/coherator steps match the
   actual proof. No statement, unit or blueprint record is modified.

Changes in this final reading: appended this independent review and reproduced the
compilation, equality, axiom and forced-adaptation checks. No further Lean repair was
needed; retained the earlier proof shortening, import demotion and forced adaptation.

## Forced adaptations

### Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso
Original against changed dependencies failed:
```
/tmp/forced-adaptation-ckmdra1g/lean/Sheaf/AlgebraicGeometry/MixedHomTensorPullbackIso.lean:65:12: error(lean.unknownIdentifier): Unknown identifier `pullbackTensorModelMap_isIso`

(with the modules compiled into /tmp/forced-adaptation-ckmdra1g/.lbuild) [7.5 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
