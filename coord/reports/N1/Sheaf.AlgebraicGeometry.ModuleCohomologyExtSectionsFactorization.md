## What changed

Closed the sole `sorry` in
`Sheaf.AlgebraicGeometry.ModuleCohomologyExtSectionsFactorization`:
`AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.ext_sections_factorization`.
The theorem statement, binders, universe and visibility are unchanged. Its proof uses a
proved private component-evaluation lemma for the generic three-isomorphism constructor,
then unfolds only the fixed comparison and cohomology types before applying that lemma.
The common resolution comparison is never unfolded.

Adapted the currently unclaimed
`Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality` module. The upstream
comparison now caches existing sheafification and Ext instances, uses the fixed Ext
functor before specialization, exposes the corresponding explicit Ext group in
`siteSectionsObjIso`, and composes the three comparison isomorphisms through
`sectionsComparisonNatIso`. The mathematical maps and all existing theorem signatures
are preserved; no arbitrary witness is introduced. The requested item module is held by
N1; its public theorem signature is unchanged and only its proof is replaced.
The interface change is recorded in
`coord/changes/N1-module-ext-comparison-components.md`.

The two changed modules compile in import order within the per-file limit. Their eight
unchanged direct and adjacent consumers also compile against the delivered artifacts:
`ModuleCohomologyExtResolutionNormalization`, `ModuleCohomologyExtResolutionEdge`,
`ModuleCohomologyExtStandardResolutionFormula`,
`ModuleCohomologyStandardSectionsFactorization`, `AbelianCounitCocycleCalculation`,
`AbelianCounitResolutionCalculation`, `AbelianResolutionComparisonEvaluation`, and
`ModuleCohomologyExtEdgeComparison`.

## Forced adaptations

The sole additional module is
`Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality` (unclaimed).
No module held by another group is adapted. The brief's 2026-10-14 unclaimed-module
exception permits its comparison-definition refactor; the interface edits are recorded
in `coord/changes/N1-module-ext-comparison-components.md`. The forced proof repair
within this module is `forgottenInjectiveAcyclic`, whose existing signature and
visibility are unchanged.

To reproduce the original compiler error against the changed definitions, I copied the
complete delivered Naturality module to
`scratchpad/original-acyclic-proof/lean/Sheaf/AlgebraicGeometry/` and removed only the
four-line explicit Ext `Subsingleton` instance (delivered lines 402–405). This restores
exactly the original `forgottenInjectiveAcyclic` proof while retaining the delivered
preceding definitions, including `siteSectionsObjIso`. The authorized single-file
runner rejected it in 34.7 seconds with exit code 1. The exact diagnostic below omits
only the scratch-directory prefix from its location:

```text
ModuleCohomologyExtResolutionNaturality.lean:402:9: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Subsingleton
    ↑(AddCommGrpCat.of
        (Ext ((presheafToSheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat).obj (yoneda.obj ⊤ ⋙ AddCommGrpCat.free))
          ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj I) (n + 1)))
```

The original proof supplies a local instance at `Sheaf.H'`, whereas the changed
`siteSectionsObjIso` exposes its definitionally equal source as an explicit Ext group.
Instance search at `AddCommGrpCat.isZero_of_subsingleton` does not make that conversion.
The four added lines restate the same proved local instance at exactly the requested
type, with `:= this`; no new vanishing assertion, hypothesis or witness is introduced.
The delivered proof compiles with those lines restored.

Every changed line of the additional module is listed in this diff. Line numbers
in the explanations refer to the delivered source:

```diff
--- original/lean/Sheaf/AlgebraicGeometry/ModuleCohomologyExtResolutionNaturality.lean
+++ delivered/lean/Sheaf/AlgebraicGeometry/ModuleCohomologyExtResolutionNaturality.lean
@@ -31,6 +31,20 @@
 open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
 noncomputable section
 namespace AlgebraicGeometry.Scheme.Modules
+/-- Cache the sheafification proof used by the comparison on the Zariski site.
+Source: Mathlib's sheafification theorem for abelian sheaves.
+(blueprint: new-module-cohomology-ext-resolution-naturality) -/
+@[instance 2000]
+theorem comparisonHasSheafify (X : Scheme.{u}) :
+    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance
+
+/-- Cache the Ext-size proof used by the comparison on the Zariski site.
+Source: the Grothendieck abelian category instance for abelian sheaves.
+(blueprint: new-module-cohomology-ext-resolution-naturality) -/
+@[instance 2000]
+theorem comparisonHasExt (X : Scheme.{u}) :
+    HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
+
 namespace ExtEdgeResolution
 
 open CategoryTheory.Abelian CochainComplex HomComplex
@@ -280,10 +294,9 @@
 def siteSectionsNatIso
     {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
     [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
-    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{u})]
     (U : C) (q : ℕ) :
-    Sheaf.cohomologyPresheafFunctor J q ⋙
-      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
+    (extFunctor q).obj (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
+      (yoneda.obj U ⋙ AddCommGrpCat.free))) ≅
       (sheafToPresheaf J AddCommGrpCat.{u} ⋙
         (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q := by
   let e : (extFunctor q).obj (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
@@ -294,17 +307,14 @@
       ((presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)) F q)
       (fun φ ↦ extRightDerivedHomObjIso_naturality
         ((presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)) φ q)
-  exact (show Sheaf.cohomologyPresheafFunctor J q ⋙
-    (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
-      (extFunctor q).obj (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
-        (yoneda.obj U ⋙ AddCommGrpCat.free))) from Iso.refl _) ≪≫ e ≪≫
-          derivedSectionsIso J U q
+  exact e ≪≫ derivedSectionsIso J U q
 
 def siteSectionsObjIso
     {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
     [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
     (U : C) (F : Sheaf J AddCommGrpCat.{u}) (q : ℕ) :
-    Sheaf.H' F q U ≅
+    AddCommGrpCat.of (Ext ((presheafToSheaf J AddCommGrpCat.{u}).obj
+      (yoneda.obj U ⋙ AddCommGrpCat.free)) F q) ≅
       ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
         (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj F :=
   (siteSectionsNatIso J U q).app F
@@ -389,6 +399,10 @@
   let : Subsingleton (Sheaf.H' ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj I)
       (n + 1) (⊤ : X.Opens)) :=
     injective_module_abelian_acyclic ⊤ I (n + 1) (Nat.succ_pos n)
+  let : Subsingleton (Ext
+      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
+        (yoneda.obj (⊤ : X.Opens) ⋙ AddCommGrpCat.free))
+      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj I) (n + 1)) := this
   exact (AddCommGrpCat.isZero_of_subsingleton _).of_iso
     (siteSectionsObjIso _ ⊤ _ (n + 1)).symm
 
@@ -553,6 +567,17 @@
       (L.map f) (moduleComparisonEquiv η M x) := by
   exact ConcreteCategory.congr_hom (η.hom.naturality f) x
 
+/-- Compose section comparisons before specializing the functors and the Ext source change.
+Source: Stacks Project, Tags 03FD and 06XR; the three constructed comparison maps.
+(blueprint: new-module-cohomology-ext-resolution-naturality) -/
+noncomputable def sectionsComparisonNatIso
+    {A E : Type*} [Category A] [Category E]
+    {R : Type u} [Ring R] {K : A ⥤ ModuleCat.{u} R} {T : A ⥤ E}
+    {B L Q : E ⥤ AddCommGrpCat.{u}}
+    (a : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ T ⋙ B)
+    (b : L ≅ B) (c : L ≅ Q) : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ T ⋙ Q :=
+  a ≪≫ Functor.isoWhiskerLeft T (b.symm ≪≫ c)
+
 end ExtEdgeResolution
 
 /-- The coefficient comparison as a natural isomorphism of additive functors.
@@ -574,14 +599,13 @@
   let V := forget₂ (ModuleCat.{u}
     ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
   change (G.rightDerived q ⋙ V) ≅ T ⋙ Sheaf.functorH (Opens.grothendieckTopology X) q
-  exact ExtEdgeResolution.resolutionSectionsNatIso G V T Γ q
-    (ExtEdgeResolution.sectionHomologyIso X q)
-    (fun M _ ↦ ExtEdgeResolution.forgottenInjectiveAcyclic X M) ≪≫
-      Functor.isoWhiskerLeft T
-        ((ExtEdgeResolution.siteSectionsNatIso (Opens.grothendieckTopology X) ⊤ q).symm ≪≫
-          ExtEdgeResolution.siteExtNatIso (Opens.grothendieckTopology X) ⊤ q ≪≫
-            ExtEdgeResolution.extSourceNatIso (ExtEdgeResolution.terminalSourceIso X) q ≪≫
-              ExtEdgeResolution.siteHNatIso (Opens.grothendieckTopology X) q)
+  exact ExtEdgeResolution.sectionsComparisonNatIso
+    (ExtEdgeResolution.resolutionSectionsNatIso G V T Γ q
+      (ExtEdgeResolution.sectionHomologyIso X q)
+      (fun M _ ↦ ExtEdgeResolution.forgottenInjectiveAcyclic X M))
+    (ExtEdgeResolution.siteSectionsNatIso (Opens.grothendieckTopology X) ⊤ q)
+    (ExtEdgeResolution.extSourceNatIso (ExtEdgeResolution.terminalSourceIso X) q)
+
 
 /-- The same resolution-normalized module/Ext comparison, read from its natural square.
 Its terminal-source map is Ext precomposition by the inverse of `terminalSourceIso`.
```

- Lines 34–46 add `comparisonHasSheafify` and `comparisonHasExt`, their instance
  attributes and source docstrings. Each theorem proves an already available
  proposition by `inferInstance`. Naming these proofs shares the site-instance
  arguments in the specialized comparison and its factorization, which previously
  exceeded the fixed compile limit. These are part of the authorized unclaimed
  definition refactor, not a claimed failure of an unchanged consumer.
- Lines 294–310 remove the redundant `HasInjectiveResolutions` binder, expose the
  fixed Ext source of `siteSectionsNatIso`, and remove its leading identity factor.
  Mathlib supplies the removed proposition. The explicit functor source allows the
  comparison to use the generic three-factor constructor without repeatedly
  elaborating the evaluated-cohomology presentation. The original map and inverse
  remain the compositions of `extRightDerivedHomObjIso` and `derivedSectionsIso`.
- Lines 316–317 expose the same source of `siteSectionsObjIso` as
  `AddCommGrpCat.of (Ext ... F q)`. This keeps its object component aligned with the
  revised `siteSectionsNatIso` and the factorization's Ext-valued type. The object
  and the component function are definitionally the original ones.
- Lines 402–405 are the forced proof adaptation explained by the exact compiler
  error above. They translate the existing local vanishing instance into the source
  type now requested by `siteSectionsObjIso`; removing them reproduces the failure.
- Lines 570–579 add the concrete `sectionsComparisonNatIso` constructor and its
  source docstring. Its data is precisely `a ≪≫ Functor.isoWhiskerLeft T (b.symm ≪≫ c)`.
  This lets the item prove its private component-evaluation formula by `rfl` for
  abstract functors before scheme specialization, without unfolding the acyclic
  section comparison or adding any mathematical obligation.
- Lines 602–607 replace the original specialized composition with that constructor
  applied to the same three isomorphisms. Only `siteExtNatIso` and `siteHNatIso`,
  both identity factors, are omitted. This makes the fixed comparison use the
  constructor whose component equation the item proves. The removed identity factors
  change neither component function nor inverse; `Iso.trans_refl` and
  `Iso.refl_trans` give the same composite. The added blank line at 608 is formatting.

The original unchanged consumers named in `## What changed` require no source edits.
The existing theorem signatures, including `forgottenInjectiveAcyclic` and
`ext_sections_factorization`, and all five Challenge target signatures are unchanged.
This repair changes the report and corrects the requested item's holder in the change
record; it changes no delivered Lean source or DAG node.

## Proved and sorry left

Proved
`AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.ext_sections_factorization`
(the blueprint node `new-module-cohomology-ext-sections-factorization`). No `sorry`
remains in either delivered module, and no new theorem or split-off node is added.
The private `sectionsComparisonNatIso_apply` lemma, the two instance caches, and the
three-isomorphism constructor are all fully proved or definitions with concrete data.

## No longer needed

No import, DAG proof dependency, or module is removed. The old identity factors
`siteExtNatIso` and `siteHNatIso` are no longer needed inside the comparison constructor,
but their public declarations remain available to consumers. No supplied resolution,
normalization, or edge-map lemma is needed by the pointwise calculation. No module is
claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The statement and its DAG proof plan are correct. The earlier direct unfold-and-`rfl`
proof exceeded the fixed 60-second compilation limit because scheme specialization made
Lean compare hidden site and resolution instance arguments repeatedly. The generic
constructor and component formula move that definitional calculation before specialization
and use the shared existing instance proofs. This preserves the fixed comparison maps and
keeps all edge cases, including degree zero, zero coefficients, and empty schemes.

## Earlier second reading (a previous round; superseded)

1. I compared both delivered modules with the repository versions. The public target
   theorem `ext_sections_factorization` has identical binders and conclusion. The
   adapted naturality module changes only the explicitly recorded comparison definitions
   and adds the concrete helper declarations in the change record; no target statement
   or unrelated declaration was changed.
2. I compiled the two modules in sandbox import order with `lcompile.py --all`; both
   compile cleanly within the per-file limit. I searched the delivered files for
   `sorry`, axioms, unsafe or opaque declarations, and implementation escapes; none
   occur. The target proof applies the generic component equation and then unfolds the
   fixed comparison types, so it proves the unchanged statement rather than a weakened
   variant.
3. The only added statement in the item is the private component-evaluation lemma,
   whose type is a direct definitional calculation for arbitrary functors. The public
   helpers in the adapted module are concrete compositions or cached existing instances,
   and their declarations are recorded in the naturality node. I checked the zero-degree,
   zero-coefficient, and empty-scheme cases mentioned by the node; no extra hypothesis
   is introduced. Searches recorded in `searches.jsonl` found no existing project or
   Mathlib declaration for this component factorization.
4. The proof uses the existing naturality comparison and its three-map constructor;
   no old proof dependency or import can be removed. The node proof and proof origin
   now describe the generic component route, and the unit `sk-thm-p1` route remains
   realized through the naturality node and the supplied resolution comparison.
5. The adapted module is unclaimed, so the interface adaptation is allowed and is
   documented in `coord/changes/N1-module-ext-comparison-components.md`. Its direct
   consumers were compiled against the delivered artifacts; their source and public
   signatures remain unchanged. I changed only the target proof, the forced naturality
   definitions, the matching node proof metadata, and this report.

## Second reading by N1

1. I compared the delivered factorization module with the repository version. The public
   theorem `ext_sections_factorization` has the same binders and conclusion byte for byte.
   The Naturality edits are the recorded, forced adaptations; no unrelated public statement
   or target declaration changed.
2. I compiled both delivered modules with `lcompile.py --all` in import order. The files
   contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or
   `debug.skipKernelTC`. The factorization proof closes the original theorem by a real
   component calculation, with no new hypothesis or weakened conclusion.
3. The private component lemma is a strict definitional calculation for the concrete
   three-isomorphism constructor. The public Naturality helpers either cache existing
   instances or compose existing comparison isomorphisms; no split-off statement or new
   node was added. The recorded searches found no duplicate declaration, and the formula
   covers degree zero, zero coefficients, and empty schemes.
4. The proof follows the node's supplied resolution comparison and the unit route through
   the Naturality node. No import or proof dependency is removed, and the node's proof,
   dependencies, and origin match the delivered proof.
5. The forced Naturality adaptation is allowed because that module is unclaimed; its
   original compiler error, changed lines, and necessity are documented above and in
   `coord/changes/N1-module-ext-comparison-components.md`. All existing consumers retain
   their signatures and compiled successfully against the delivered definitions.

I changed no Lean source during this second reading; I added this review section and
confirmed the existing forced-adaptation documentation is complete.
