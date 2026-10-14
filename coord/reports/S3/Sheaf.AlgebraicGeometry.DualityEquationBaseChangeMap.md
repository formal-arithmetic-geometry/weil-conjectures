## What changed

Repair landing return X-503ae after the earlier X-63956 A9/A10 repair.
Remove the duplicate open_secondMate_formula and use the existing private
AlgebraicGeometry.secondMate_formula via a proof-only import all of
Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate. This preserves all visibility.
The delivery tool rebases onto the fetched sheaf-dag before preflight.
The definition remains the explicit
inverse ordinary-square mate `(mateEquiv adjf adjf' (inv β)).app K`, with the same
signature and naturality proof as the returned delivery. For A9,
Mathlib.CategoryTheory.Adjunction.Mates is now a proof-only import in the item.

For A10, deliver all three forced importers: FlatPrecomposePus,
ProperFlatGlobalHomCompositeIso and ProperFlatOpenSquareMateIso. The first two
prove their counit square using Mathlib mateEquiv_counit for inv β followed by
inverse cancellation. The open-square proof locally constructs auxiliary open
adjunctions and uses the existing imported private secondMate_formula to recover its
original three-factor isomorphism argument from the public inverse mate.
QCohInverseBaseChangeMate keeps the earlier forced reflexivity repair.
All existing signatures and visibility are unchanged. No target is changed.

Update the main and inverse-square identification nodes from the earlier delivery,
and the three forced importer proof records to match these proofs.
Change record: coord/changes/dualityEquationBaseChangeMap-inverse-mate.md.

## Proved and sorry left

Holes closed: none (0 of 0 direct holes in the assigned module).
Holes added: none. Split-off statements: none. No direct sorry remains in any
of the five delivered modules. This is a definition-construction and forced-proof
repair, not a net sorry reduction.

AlgebraicGeometry.dualityEquationBaseChangeMap is explicit noncomputable data.
AlgebraicGeometry.dualityEquationBaseChangeMap_eq_inverseSquareMate is reflexive.
The existing flat_precompose_pus, properFlatGlobalHomComposite_isIso and
proper_flat_openSquare_mate_isIso retain complete proofs against the new data.
The duplicate private open_secondMate_formula is removed; no new declaration is added.
Inherited upstream sorry dependencies remain; this delivery does not claim to
close the target import closure.

## No longer needed

The open-square module removes the duplicate open_secondMate_formula and its direct
Mathlib.CategoryTheory.Adjunction.Mates import, using the existing formula from
QCohInverseBaseChangeMate instead. No module becomes unreachable through this repair.

The item removes Mathlib.CategoryTheory.Adjunction.Restrict and no longer
constructs Rg, RgX, adjg or adjgX as part of its data. Mates is imported only for
the construction. The open-square proof still needs Restrict locally as a proof
import, to construct auxiliary adjunctions for its factorization identity.

The main node no longer has direct proof dependencies
lem-pc-ringed-spaces-derived-adjoint and lem-pc-derived-direct-image-composition.
It directly uses def-pc-derived-base-change-map and def-weil-pbc-adjunction-mate.
The discarded nodes/modules remain reachable elsewhere; no whole-library module
pruning is claimed. The unit sk-thm-picard-duality and its realized record are
unchanged; the generic mates tools operate below unit level.

## Where the brief, the DAG or earlier work was wrong

The previous review missed the duplicate formula, and import_prune_check refused
the landing. Lean import all allows reuse of the existing private theorem without
changing its signature or visibility.

The assigned module has no direct sorry: it is a class-2 construction repair.
The earlier unchanged first-worker delivery did not repair it. The returned
inverse-mate delivery also exposed Mates unnecessarily (A9) and omitted three
importers whose proofs extracted lets removed by the construction change (A10).
This repair restricts the import visibility and delivers those forced proofs.

Auxiliary pullback adjunctions cancel for fixed β by the generic iterated-mates
identity. The definition now makes that independence explicit. Auxiliary
adjunctions used in the open-square proof are only proof tools: their arbitrary
choice cannot change the public map. No arbitrary existence witness is introduced
into public data. The ordinary base-change construction is unchanged.

## Forced adaptations

All four adapted modules are unclaimed in the local claim records. Their original
versions were compiled separately against the changed dependency overlay. Every
existing signature, visibility, definition and unrelated proof is retained.

Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate: original line 177 fails with `Type mismatch` when
applying secondMate_formula to a goal that is now definitionally the inverse mate.
The only changed proof line is the final `rfl` (the earlier delivery's repair).

Sheaf.AlgebraicGeometry.FlatPrecomposePus: original lines 168–169 fail with `Unknown identifier adjgX`,
`Unknown identifier β`, and a type mismatch because adjg is extracted as an IsIso
proof. Add a proof-only Mates import; extract only PX, PY, PY', PX', Lg, LgX,
Rf, Rf' and β. Apply mateEquiv_counit to inv β, precompose by β and cancel. The
private mate_counit theorem, public signature and remaining proof are unchanged.

Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso: original lines 176–178 fail with the same unknown
identifiers and wrong adjg type at composite_mate_counit. Add a proof-only Mates
import and use the same counit-square calculation with the current lets. The
private helper, public signature and all other proof steps are unchanged.

Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso: original line 161 extracts wrong lets. Later lines
186, 188, 190, 203 and 206 fail with wrong functor arguments, `Invalid field unit`
and an unsolved inverse-mate goal. Extract the current eleven lets; construct
proof-local Rg, RgX, adjg and adjgX explicitly, supplying compactness and
quasi-separatedness of X from proper f. Add a proof-only Restrict import
and import all QCohInverseBaseChangeMate to reuse its existing secondMate_formula.
Rewrite the public inverse mate
with this identity; the original restriction/unit argument and invertible-counit
argument then prove the goal. These edits are necessary because the definition
no longer exposes auxiliary adjunction lets. They leave all existing declarations'
signatures and visibility unchanged.

### Sheaf.AlgebraicGeometry.FlatPrecomposePus
Original against changed dependencies failed:
```
/tmp/forced-adaptation-f3eoeot7/lean/Sheaf/AlgebraicGeometry/FlatPrecomposePus.lean:168:57: warning: unused name

Note: This linter can be disabled with `set_option linter.tactic.unusedName false`
/tmp/forced-adaptation-f3eoeot7/lean/Sheaf/AlgebraicGeometry/FlatPrecomposePus.lean:168:63: warning: unused name

Note: This linter can be disabled with `set_option linter.tactic.unusedName false`
/tmp/forced-adaptation-f3eoeot7/lean/Sheaf/AlgebraicGeometry/FlatPrecomposePus.lean:169:59: error: Application type mismatch: The argument
  adjg
has type
  IsIso Rf
of sort `Prop` but is expected to have type
  ?m.985 ⊣ ?m.986
of sort `Type (max (uMain + 1) wMain)` in the application
  mate_counit adjf adjf' adjg
/tmp/forced-adaptation-f3eoeot7/lean/Sheaf/AlgebraicGeometry/FlatPrecomposePus.lean:169:64: error(lean.unknownIdentifier): Unknown identifier `adjgX`
/tmp/forced-adaptation-f3eoeot7/lean/Sheaf/AlgebraicGeometry/FlatPrecomposePus.lean:169:70: error(lean.unknownIdentifier): Unknown identifier `β`

(with the modules compiled into /tmp/forced-adaptation-f3eoeot7/.lbuild) [7.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso
Original against changed dependencies failed:
```
/tmp/forced-adaptation-oh715hxb/lean/Sheaf/AlgebraicGeometry/ProperFlatGlobalHomCompositeIso.lean:176:59: warning: unused name

Note: This linter can be disabled with `set_option linter.tactic.unusedName false`
/tmp/forced-adaptation-oh715hxb/lean/Sheaf/AlgebraicGeometry/ProperFlatGlobalHomCompositeIso.lean:176:65: warning: unused name

Note: This linter can be disabled with `set_option linter.tactic.unusedName false`
/tmp/forced-adaptation-oh715hxb/lean/Sheaf/AlgebraicGeometry/ProperFlatGlobalHomCompositeIso.lean:178:40: error: Application type mismatch: The argument
  adjg
has type
  IsIso Rf
of sort `Prop` but is expected to have type
  ?m.1130 ⊣ ?m.1131
of sort `Type (max (u + 1) w)` in the application
  composite_mate_counit adjf adjf' adjg
/tmp/forced-adaptation-oh715hxb/lean/Sheaf/AlgebraicGeometry/ProperFlatGlobalHomCompositeIso.lean:178:45: error(lean.unknownIdentifier): Unknown identifier `adjgX`
/tmp/forced-adaptation-oh715hxb/lean/Sheaf/AlgebraicGeometry/ProperFlatGlobalHomCompositeIso.lean:178:51: error(lean.unknownIdentifier): Unknown identifier `β`

(with the modules compiled into /tmp/forced-adaptation-oh715hxb/.lbuild) [30.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso
Original against changed dependencies failed:
```
irectImage f) ⋯
RgX : PX'.FullSubcategory ⥤ PY'.FullSubcategory := PY'.lift (PX'.ι ⋙ schemeDerivedDirectImage (pullback.snd f W.ι)) ⋯
Rf : Rg ⋙ Lg ⟶ LgX ⋙ RgX :=
  {
    app := fun E ↦
      ObjectProperty.homMk (schemeDerivedBaseChangeMap f (pullback.snd f W.ι) W.ι (pullback.fst f W.ι) ⋯ E.obj),
    naturality := ⋯ }
Rf' : ∀ (E : PX.FullSubcategory), IsIso (Rf.app E) := dualityEquationBaseChangeMap._proof_11 f W.ι hβ
adjg : IsIso Rf := dualityEquationBaseChangeMap._proof_12 f W.ι Rf'
adjJ : derivedPullback W.ι ⊣ schemeDerivedDirectImage W.ι := Classical.choose ⋯
eW : (schemeOpenRestriction Y W).mapDerivedCategory ≅ derivedPullback W.ι
adjW : (schemeOpenRestriction Y W).mapDerivedCategory ⊣ schemeDerivedDirectImage W.ι := adjJ.ofNatIsoLeft eW.symm
hopen : ∀ (E : schemeDerivedQCohCategory Y),
  PY ((schemeDerivedDirectImage W.ι).obj ((schemeOpenRestriction Y W).mapDerivedCategory.obj E.obj)) :=
  fun E ↦
    have hp :=
      Exists.fst (schemeDerivedDirectImage_qcqs_hasRightAdjoint (↑W) Y W.ι) ((derivedPullback W.ι).obj E.obj)
        ((derivedPullback_tensor_preserve_QCoh W.ι).left E.obj E.property);
    fun n ↦
    ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace))
      ((DerivedCategory.homologyFunctor (SheafOfModules (moduleRings Y.toRingedSpace)) n).mapIso
        ((schemeDerivedDirectImage W.ι).mapIso (eW.app E.obj).symm))
      (hp n)
η : K ⟶
  { obj := (schemeDerivedDirectImage W.ι).obj ((schemeOpenRestriction Y W).mapDerivedCategory.obj K.obj),
    property := ⋯ } :=
  ObjectProperty.homMk (adjW.unit.app K.obj)
γ : { obj := (schemeDerivedDirectImage W.ι).obj ((schemeOpenRestriction Y W).mapDerivedCategory.obj K.obj),
    property := ⋯ } ≅
  Rg.obj sorry :=
  PY.isoMk sorry
hu : sorry = η ≫ γ.hom
hres : IsIso ((schemeOpenRestriction X (f ⁻¹ᵁ W)).mapDerivedCategory.map (PX.ι.map (a.map η)))
⊢ IsIso (((mateEquiv adjf adjf') (inv Rf)).app K)

(with the modules compiled into /tmp/forced-adaptation-fv9jgs10/.lbuild) [30.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate
Original against changed dependencies failed:
```
/tmp/forced-adaptation-6y36rx9k/lean/Sheaf/AlgebraicGeometry/QCohInverseBaseChangeMate.lean:177:2: error: Type mismatch
  secondMate_formula ?m.318 ?m.319 ?m.320 ?m.321 (qcBaseChange f g) K
has type
  (qcPullback (pullback.fst f g)).map (CategoryTheory.Functor.map ?m.311 ((Adjunction.unit ?m.321).app K)) ≫
      (qcPullback (pullback.fst f g)).map
          (inv
            (((conjugateEquiv (Adjunction.comp ?m.320 ?m.319) (Adjunction.comp ?m.318 ?m.321)) (qcBaseChange f g)).app
              ((qcPullback g).obj K))) ≫
        (Adjunction.counit ?m.320).app (Functor.obj ?m.313 ((qcPullback g).obj K)) =
    ((mateEquiv ?m.318 ?m.319) (inv (qcBaseChange f g))).app K
but is expected to have type
  (let PX := schemeDerivedQCohProperty X;
    let PY := schemeDerivedQCohProperty Y;
    let PY' := schemeDerivedQCohProperty Y';
    let PX' := schemeDerivedQCohProperty (pullback f g);
    let Lg := PY'.lift (PY.ι ⋙ derivedPullback g) ⋯;
    let LgX := PX'.lift (PX.ι ⋙ derivedPullback (pullback.fst f g)) ⋯;
    let Rf := PY.lift (PX.ι ⋙ schemeDerivedDirectImage f) ⋯;
    let Rf' := PY'.lift (PX'.ι ⋙ schemeDerivedDirectImage (pullback.snd f g)) ⋯;
    let β :=
      {
        app := fun E ↦
          ObjectProperty.homMk (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g) ⋯ E.obj),
        naturality := ⋯ };
    have this := ⋯;
    have this := ⋯;
    ((mateEquiv adjf adjf') (inv β)).app K) =
    ((mateEquiv adjf adjf') (qcInverseBaseChange f g hβ)).app K

(with the modules compiled into /tmp/forced-adaptation-6y36rx9k/.lbuild) [10.5 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by S3

1. **Interfaces and meaning: pass.** Diffed all five modules against this checkout
   and checked their declaration tables: no existing signature or visibility changes,
   no new declaration, and no added hypothesis or weakened conclusion. The sole data
   change is the recorded body of dualityEquationBaseChangeMap in
   coord/changes/dualityEquationBaseChangeMap-inverse-mate.md. Read the complete
   construction and the existing secondMate_formula: the latter identifies the old
   three-factor arrow with the new inverse mate for arbitrary auxiliary adjunctions.
   Thus the removed auxiliary choices cannot affect the map for fixed beta. This also
   corrects the fresh-counit-rescaling concern in the item's hollow-definition row:
   the conjugate changes with those adjunctions and cancels the corresponding unit
   and counit changes. The ordinary schemeDerivedBaseChangeMap and its separate
   pending construction repair are unchanged. The change record explicitly reopens
   target statement review; no target signature is edited.

2. **Compilation and proof integrity: pass.** Compiled the complete delivered set
   locally through lcompile.py in import order, without errors or warnings (9.5,
   10.1, 40.4, 10.9 and 29.3 seconds). Searched all delivered Lean files: no direct
   sorry, axiom, unsafe, opaque, implemented_by or extern. A scratch axiom probe
   against the sandbox overlay checks dualityEquationBaseChangeMap, its inverse-square
   identification and each of the three adapted public theorems. Their axioms are
   precisely propext, Classical.choice, Quot.sound and inherited sorryAx. The reused
   private secondMate_formula has only propext, Classical.choice and Quot.sound.
   The explicit inverse mate adds no arbitrary existence witness to public data:
   inverse morphisms are determined by their inverse equations. The auxiliary
   adjunctions in the open-square adaptation occur only inside a theorem proof.

3. **Split statements and duplication: pass, none introduced.** There are no new
   statements, nodes or holes to validate or close. Read the existing generic
   secondMate_formula and searched Mathlib Mates under iterated mates, conjugation
   of inverse transformations and counit identities. It follows from
   conjugateEquiv_comm and iterated_mateEquiv_conjugateEquiv; the two counit-square
   repairs use mateEquiv_counit directly. The generic identity has no nonempty,
   geometric or boundedness hypothesis, so empty schemes, zero objects and identity
   squares introduce no exceptional case. No duplicate formula is delivered.

4. **Route, imports and pruning: pass.** Read the forced proof diffs and their
   surrounding proofs. The two counit-square changes are exactly inverse cancellation;
   the open-square change reconstructs the removed proof-local adjunctions and then
   reuses the existing formula. No unrelated proof is rewritten. The original-error
   evidence establishes why all four adaptations are necessary. New proof imports
   are nonpublic, including import all for the existing private formula. The report's
   No longer needed section accounts for both old dependencies removed from the main
   node, lem-pc-ringed-spaces-derived-adjoint and
   lem-pc-derived-direct-image-composition, and the removed direct Restrict import.
   No whole module is claimed pruned. Read sk-thm-picard-duality.json: its realized
   record and unit route are unchanged; the mates calculation is below unit level.

5. **DAG agreement: pass.** Compared all five node JSON records with the repository.
   Only proof, proof_deps and proof_origin change; statements, Lean signatures,
   sources and unit attachments are preserved. Read each revised proof step and
   checked that its uses union matches proof_deps. The main record describes the
   explicit inverse mate and its identification with the displayed formula; the
   identification record describes reflexivity; the three forced proof records
   describe the actual counit and open-restriction calculations. The dependency on
   QCohInverseBaseChangeMate records the reused generic formula in that module.

Second reading changed only this report by adding the independent review and its
verification evidence. No Lean code, node, import or change record needed repair.
Holes closed: none (0 of 0); holes added: none; split off: none.

## Forced adaptations

### Sheaf.AlgebraicGeometry.FlatPrecomposePus
Original against changed dependencies failed:
```
/tmp/forced-adaptation-kx1qf_xz/lean/Sheaf/AlgebraicGeometry/FlatPrecomposePus.lean:168:57: warning: unused name

Note: This linter can be disabled with `set_option linter.tactic.unusedName false`
/tmp/forced-adaptation-kx1qf_xz/lean/Sheaf/AlgebraicGeometry/FlatPrecomposePus.lean:168:63: warning: unused name

Note: This linter can be disabled with `set_option linter.tactic.unusedName false`
/tmp/forced-adaptation-kx1qf_xz/lean/Sheaf/AlgebraicGeometry/FlatPrecomposePus.lean:169:59: error: Application type mismatch: The argument
  adjg
has type
  IsIso Rf
of sort `Prop` but is expected to have type
  ?m.985 ⊣ ?m.986
of sort `Type (max (uMain + 1) wMain)` in the application
  mate_counit adjf adjf' adjg
/tmp/forced-adaptation-kx1qf_xz/lean/Sheaf/AlgebraicGeometry/FlatPrecomposePus.lean:169:64: error(lean.unknownIdentifier): Unknown identifier `adjgX`
/tmp/forced-adaptation-kx1qf_xz/lean/Sheaf/AlgebraicGeometry/FlatPrecomposePus.lean:169:70: error(lean.unknownIdentifier): Unknown identifier `β`

(with the modules compiled into /tmp/forced-adaptation-kx1qf_xz/.lbuild) [8.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso
Original against changed dependencies failed:
```
/tmp/forced-adaptation-3fmcsui5/lean/Sheaf/AlgebraicGeometry/ProperFlatGlobalHomCompositeIso.lean:176:59: warning: unused name

Note: This linter can be disabled with `set_option linter.tactic.unusedName false`
/tmp/forced-adaptation-3fmcsui5/lean/Sheaf/AlgebraicGeometry/ProperFlatGlobalHomCompositeIso.lean:176:65: warning: unused name

Note: This linter can be disabled with `set_option linter.tactic.unusedName false`
/tmp/forced-adaptation-3fmcsui5/lean/Sheaf/AlgebraicGeometry/ProperFlatGlobalHomCompositeIso.lean:178:40: error: Application type mismatch: The argument
  adjg
has type
  IsIso Rf
of sort `Prop` but is expected to have type
  ?m.1130 ⊣ ?m.1131
of sort `Type (max (u + 1) w)` in the application
  composite_mate_counit adjf adjf' adjg
/tmp/forced-adaptation-3fmcsui5/lean/Sheaf/AlgebraicGeometry/ProperFlatGlobalHomCompositeIso.lean:178:45: error(lean.unknownIdentifier): Unknown identifier `adjgX`
/tmp/forced-adaptation-3fmcsui5/lean/Sheaf/AlgebraicGeometry/ProperFlatGlobalHomCompositeIso.lean:178:51: error(lean.unknownIdentifier): Unknown identifier `β`

(with the modules compiled into /tmp/forced-adaptation-3fmcsui5/.lbuild) [29.4 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso
Original against changed dependencies failed:
```
irectImage f) ⋯
RgX : PX'.FullSubcategory ⥤ PY'.FullSubcategory := PY'.lift (PX'.ι ⋙ schemeDerivedDirectImage (pullback.snd f W.ι)) ⋯
Rf : Rg ⋙ Lg ⟶ LgX ⋙ RgX :=
  {
    app := fun E ↦
      ObjectProperty.homMk (schemeDerivedBaseChangeMap f (pullback.snd f W.ι) W.ι (pullback.fst f W.ι) ⋯ E.obj),
    naturality := ⋯ }
Rf' : ∀ (E : PX.FullSubcategory), IsIso (Rf.app E) := dualityEquationBaseChangeMap._proof_11 f W.ι hβ
adjg : IsIso Rf := dualityEquationBaseChangeMap._proof_12 f W.ι Rf'
adjJ : derivedPullback W.ι ⊣ schemeDerivedDirectImage W.ι := Classical.choose ⋯
eW : (schemeOpenRestriction Y W).mapDerivedCategory ≅ derivedPullback W.ι
adjW : (schemeOpenRestriction Y W).mapDerivedCategory ⊣ schemeDerivedDirectImage W.ι := adjJ.ofNatIsoLeft eW.symm
hopen : ∀ (E : schemeDerivedQCohCategory Y),
  PY ((schemeDerivedDirectImage W.ι).obj ((schemeOpenRestriction Y W).mapDerivedCategory.obj E.obj)) :=
  fun E ↦
    have hp :=
      Exists.fst (schemeDerivedDirectImage_qcqs_hasRightAdjoint (↑W) Y W.ι) ((derivedPullback W.ι).obj E.obj)
        ((derivedPullback_tensor_preserve_QCoh W.ι).left E.obj E.property);
    fun n ↦
    ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace))
      ((DerivedCategory.homologyFunctor (SheafOfModules (moduleRings Y.toRingedSpace)) n).mapIso
        ((schemeDerivedDirectImage W.ι).mapIso (eW.app E.obj).symm))
      (hp n)
η : K ⟶
  { obj := (schemeDerivedDirectImage W.ι).obj ((schemeOpenRestriction Y W).mapDerivedCategory.obj K.obj),
    property := ⋯ } :=
  ObjectProperty.homMk (adjW.unit.app K.obj)
γ : { obj := (schemeDerivedDirectImage W.ι).obj ((schemeOpenRestriction Y W).mapDerivedCategory.obj K.obj),
    property := ⋯ } ≅
  Rg.obj sorry :=
  PY.isoMk sorry
hu : sorry = η ≫ γ.hom
hres : IsIso ((schemeOpenRestriction X (f ⁻¹ᵁ W)).mapDerivedCategory.map (PX.ι.map (a.map η)))
⊢ IsIso (((mateEquiv adjf adjf') (inv Rf)).app K)

(with the modules compiled into /tmp/forced-adaptation-6wwadjba/.lbuild) [26.4 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate
Original against changed dependencies failed:
```
/tmp/forced-adaptation-5ho_7df2/lean/Sheaf/AlgebraicGeometry/QCohInverseBaseChangeMate.lean:177:2: error: Type mismatch
  secondMate_formula ?m.318 ?m.319 ?m.320 ?m.321 (qcBaseChange f g) K
has type
  (qcPullback (pullback.fst f g)).map (CategoryTheory.Functor.map ?m.311 ((Adjunction.unit ?m.321).app K)) ≫
      (qcPullback (pullback.fst f g)).map
          (inv
            (((conjugateEquiv (Adjunction.comp ?m.320 ?m.319) (Adjunction.comp ?m.318 ?m.321)) (qcBaseChange f g)).app
              ((qcPullback g).obj K))) ≫
        (Adjunction.counit ?m.320).app (Functor.obj ?m.313 ((qcPullback g).obj K)) =
    ((mateEquiv ?m.318 ?m.319) (inv (qcBaseChange f g))).app K
but is expected to have type
  (let PX := schemeDerivedQCohProperty X;
    let PY := schemeDerivedQCohProperty Y;
    let PY' := schemeDerivedQCohProperty Y';
    let PX' := schemeDerivedQCohProperty (pullback f g);
    let Lg := PY'.lift (PY.ι ⋙ derivedPullback g) ⋯;
    let LgX := PX'.lift (PX.ι ⋙ derivedPullback (pullback.fst f g)) ⋯;
    let Rf := PY.lift (PX.ι ⋙ schemeDerivedDirectImage f) ⋯;
    let Rf' := PY'.lift (PX'.ι ⋙ schemeDerivedDirectImage (pullback.snd f g)) ⋯;
    let β :=
      {
        app := fun E ↦
          ObjectProperty.homMk (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g) ⋯ E.obj),
        naturality := ⋯ };
    have this := ⋯;
    have this := ⋯;
    ((mateEquiv adjf adjf') (inv β)).app K) =
    ((mateEquiv adjf adjf') (qcInverseBaseChange f g hβ)).app K

(with the modules compiled into /tmp/forced-adaptation-5ho_7df2/.lbuild) [9.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
