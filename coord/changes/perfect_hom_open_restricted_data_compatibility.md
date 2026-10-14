# perfect_hom_open_restricted_data compatibility repair

## Reason

The old stage, apex and conjunction assertions quantified over arbitrary independently
supplied hB. Simultaneously negating its stage and apex equivalences preserves naturality
and transition compatibility. For the full open of Spec(Q), a singleton constant diagram,
and nonzero structure sheaf in degree zero, the pinned equations cannot hold both before
and after this twist. The existential parent is correct: it needs a compatible choice.

The item owns all three corrected helper signatures. No other existing module uses these
helpers. Replace hB by equivalence/naturality fields e and require the identity equations
which actually characterize compatibility. Prove propagation to every testing morphism.
Construct compatible e from h, prove transition coherence, obtain the existing QCoh fields,
and assemble hB. The parent's full elaborated signature and all target signatures remain
unchanged. This is a repair of false intermediate assertions, not proofs of their old types.

Move the three concrete map definitions unchanged into PerfectHomOpenRestrictionMap,
re-exported publicly by the item, so the new proof modules can use them without an import
cycle. Names, bodies, signatures and visibility of these definitions stay the same.
The existing parent docstring is preserved. Its final sentence mentions right-adjoint
essential surjectivity; the implemented proof uses supported extension-by-zero testing
objects and does not assume that restriction lifts arbitrary morphisms out of a right
adjoint image. No target meaning or construction data changes.

## Old

```lean
theorem perfect_hom_open_restricted_stage_pinned {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R) {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i)) [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι) (Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F) (h : PerfectHomPushPullData R c s Q F d) (hB : PerfectHomPushPullData R c (B.ι ≫ s) ((schemeMVDerivedRestriction Y B).obj Q) (F ⋙ schemeMVDerivedRestriction Y B) ((schemeMVDerivedRestriction Y B).mapCocone d)) : ∀ (j : Set.Ici i) (M : schemeDerivedCategory Y) (f : M ⟶ F.obj j), hB.stageEquiv j ((schemeMVDerivedRestriction Y B).obj M) ((schemeMVDerivedRestriction Y B).map f) = perfectHomOpenRestrictionMap s B (Spec.map (R.map (homOfLE j.property))) a (h.stageEquiv j M f)
```

```lean
theorem perfect_hom_open_restricted_limit_pinned {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R) {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i)) [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι) (Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F) (h : PerfectHomPushPullData R c s Q F d) (hB : PerfectHomPushPullData R c (B.ι ≫ s) ((schemeMVDerivedRestriction Y B).obj Q) (F ⋙ schemeMVDerivedRestriction Y B) ((schemeMVDerivedRestriction Y B).mapCocone d)) : ∀ (M : schemeDerivedCategory Y) (f : M ⟶ d.pt), hB.limitEquiv ((schemeMVDerivedRestriction Y B).obj M) ((schemeMVDerivedRestriction Y B).map f) = perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a (h.limitEquiv M f)
```

```lean
theorem perfect_hom_open_restricted_data_pinned {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R) {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i)) [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι) (Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F) (h : PerfectHomPushPullData R c s Q F d) (hB : PerfectHomPushPullData R c (B.ι ≫ s) ((schemeMVDerivedRestriction Y B).obj Q) (F ⋙ schemeMVDerivedRestriction Y B) ((schemeMVDerivedRestriction Y B).mapCocone d)) : (∀ (j : Set.Ici i) (M : schemeDerivedCategory Y) (f : M ⟶ F.obj j), hB.stageEquiv j ((schemeMVDerivedRestriction Y B).obj M) ((schemeMVDerivedRestriction Y B).map f) = perfectHomOpenRestrictionMap s B (Spec.map (R.map (homOfLE j.property))) a (h.stageEquiv j M f)) ∧ (∀ (M : schemeDerivedCategory Y) (f : M ⟶ d.pt), hB.limitEquiv ((schemeMVDerivedRestriction Y B).obj M) ((schemeMVDerivedRestriction Y B).map f) = perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a (h.limitEquiv M f))
```

The map definitions lived in Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedData.
The parent chose arbitrary hB using perfect_hom_open_restricted_data_exists and applied the
false universal conjunction. The public imports were PerfectHomPushPullCocone and
DerivedMayerVietorisCanonicalData, and the ordinary import was PerfectHomOpenRestrictedDataExists.

## New

```lean
theorem perfect_hom_open_restricted_stage_pinned {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R) {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i)) [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι) (Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F) (h : PerfectHomPushPullData R c s Q F d) (e : PerfectHomOpenRestrictedEquivFields R c s B Q F d) (he : ∀ j : Set.Ici i, e.stageEquiv j ((schemeMVDerivedRestriction Y B).obj (F.obj j)) (𝟙 _) = perfectHomOpenRestrictionMap s B (Spec.map (R.map (homOfLE j.property))) a (h.stageEquiv j (F.obj j) (𝟙 _))) : ∀ (j : Set.Ici i) (M : schemeDerivedCategory Y) (f : M ⟶ F.obj j), e.stageEquiv j ((schemeMVDerivedRestriction Y B).obj M) ((schemeMVDerivedRestriction Y B).map f) = perfectHomOpenRestrictionMap s B (Spec.map (R.map (homOfLE j.property))) a (h.stageEquiv j M f)
```

```lean
theorem perfect_hom_open_restricted_limit_pinned {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R) {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i)) [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι) (Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F) (h : PerfectHomPushPullData R c s Q F d) (e : PerfectHomOpenRestrictedEquivFields R c s B Q F d) (he : e.limitEquiv ((schemeMVDerivedRestriction Y B).obj d.pt) (𝟙 _) = perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a (h.limitEquiv d.pt (𝟙 _))) : ∀ (M : schemeDerivedCategory Y) (f : M ⟶ d.pt), e.limitEquiv ((schemeMVDerivedRestriction Y B).obj M) ((schemeMVDerivedRestriction Y B).map f) = perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a (h.limitEquiv M f)
```

```lean
theorem perfect_hom_open_restricted_data_pinned {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R) {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i)) [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι) (Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F) (h : PerfectHomPushPullData R c s Q F d) (e : PerfectHomOpenRestrictedEquivFields R c s B Q F d) (hs : ∀ j : Set.Ici i, e.stageEquiv j ((schemeMVDerivedRestriction Y B).obj (F.obj j)) (𝟙 _) = perfectHomOpenRestrictionMap s B (Spec.map (R.map (homOfLE j.property))) a (h.stageEquiv j (F.obj j) (𝟙 _))) (hl : e.limitEquiv ((schemeMVDerivedRestriction Y B).obj d.pt) (𝟙 _) = perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a (h.limitEquiv d.pt (𝟙 _))) : (∀ (j : Set.Ici i) (M : schemeDerivedCategory Y) (f : M ⟶ F.obj j), e.stageEquiv j ((schemeMVDerivedRestriction Y B).obj M) ((schemeMVDerivedRestriction Y B).map f) = perfectHomOpenRestrictionMap s B (Spec.map (R.map (homOfLE j.property))) a (h.stageEquiv j M f)) ∧ (∀ (M : schemeDerivedCategory Y) (f : M ⟶ d.pt), e.limitEquiv ((schemeMVDerivedRestriction Y B).obj M) ((schemeMVDerivedRestriction Y B).map f) = perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a (h.limitEquiv M f))
```

The map definitions are verbatim in Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictionMap.
The item publicly imports that module and PerfectHomOpenRestrictedEquivFields. Its proof
imports PerfectHomOpenRestrictedPinnedEquiv, PerfectHomOpenRestrictedPinnedMaps and
PerfectHomOpenRestrictedQCoh. Thus the previous public definitions remain available to
importers. The new equivalence theorem uses existing supported test objects and bijective
restriction, then proves normalization by lifting id of LM to x with Lx=t.inv and cancelling
pullback(t.hom) followed by pullback(t.inv). The new maps theorem proves coherence at stage
identities and extends it to every testing morphism by naturality. Its transport wrapper is
a specialization of the existing perfect_hom_open_transport_square.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedData | P1 | The three helper signatures are corrected and proved; parent signature unchanged; three concrete definitions re-exported unchanged. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenStageMaps | unclaimed | Calls only perfect_hom_open_restricted_data, whose signature stays identical; no source adaptation required. |

Source searches and tools/downstream.py --uses show that the corrected helpers and concrete
map definitions are mentioned only by the item in the existing library. The direct consumer
uses only the unchanged parent theorem. All 442 transitive downstream modules consequently
keep their current statements and definitions. No module owned by another group is edited;
there are no forced adaptations. The unchanged PerfectHomOpenStageMaps was copied to
scratchpad and compiled against the delivered overlay in 5.8 seconds with no warnings.

The statement_change citer inventory is included in each corrected node. The stage and
apex nodes' former dependence on the conjunction is removed, eliminating that bad cycle.
The conjunction now applies the two corrected, independently proved naturality lemmas.
The parent supplies the identity normalization from its construction.

## Status

landed 20261014T022549-L-4046919 2026-10-14 (merge of deliver/P1/Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedData)
