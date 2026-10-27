# CategoryTheory.InternalActionSite.InternalModulePullback

## Reason

Extract the seven existing specification declarations, with unchanged names,
signatures and bodies, from InternalRestrictionModuleTensor into the new
InternalRestrictionModuleTensorData. This lets the three strict argument pieces
import their specifications without an import cycle back to the theorem they prove.
The original module publicly imports the data module, preserving access to all
seven declarations and their original public dependencies. Only ownership tags
and the module description change. No object is chosen from an existence theorem,
and no definition acquires a sorry. The main theorem signature remains verbatim.
There are no existing Lean importers of the assigned item (checked with
`tools/downstream.py`); unfinished DAG parents still need its theorem and are
retained. This is an extraction for proof decomposition, not a withdrawal.

## Old

The following block lives in lean/Sheaf/CategoryTheory/InternalRestrictionModuleTensor.lean:

```lean
/-- The supplied geometric morphism has the prescribed inverse image and identity
structural map. The equality includes maps, and does not just identify objects.
Source: paragraph (3), the hypotheses on p_K and q_theta
(blueprint: lem-sfb-internal-restriction-module-tensor). -/
structure InternalPrecompositionMorphism {D : Type u} [SmallCategory D]
    (J : GrothendieckTopology C) (T : GrothendieckTopology D) (F : D ⥤ C)
    (R : Sheaf J CommRingCat.{u}) (hR : Presheaf.IsSheaf T (F.op ⋙ R.obj)) where
  /-- The given ringed geometric morphism. -/
  ringed : RingedToposMorphism
    (baseRing T (⟨F.op ⋙ R.obj, hR⟩ : Sheaf T CommRingCat.{u})) (baseRing J R)
  /-- Its inverse image, including its maps, is precomposition. -/
  inverse : ringed.inverse ⋙ sheafToPresheaf T (Type u) =
    sheafToPresheaf J (Type u) ⋙ (Functor.whiskeringLeft _ _ (Type u)).obj F.op
  /-- The structural map is the identity after that identification. -/
  structural : (eqToIso inverse).inv.app
      ((sheafCompose J (forget RingCat)).obj (baseRing J R)) ≫ ringed.ringMap.hom = 𝟙 _

/-- The monoidal unit map, expressed using the actual regular coefficient modules.
This is the existing unit map with its definitionally equal regular-module type.
Source: Stacks 03EK, regular coefficient unit
(blueprint: lem-sfb-internal-restriction-module-tensor). -/
def internalRegularUnitMap {D : Type u} [SmallCategory D]
    {J : GrothendieckTopology C} {T : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf T CommRingCat.{u})
    (G : ringedSiteModules.{u} (baseRing J R) ⥤ ringedSiteModules.{u} (baseRing T S))
    (m : G.Monoidal) :
    SheafOfModules.unit (baseRing T S) ⟶ G.obj (SheafOfModules.unit (baseRing J R)) :=
  @Functor.LaxMonoidal.ε _ _ _ _ _ _ G m.toLaxMonoidal

attribute [local irreducible] SheafOfModules.monoidalCategory

/-- Full normalization of the module pullback, including the actual scalar-extension
formula, its regular-ring unitor, exactness, and the canonical coherent tensor maps.
Source: paragraph (3), Stacks 03D7 and 03EK
(blueprint: lem-sfb-internal-restriction-module-tensor). -/
structure InternalModulePullback {D : Type u} [SmallCategory D]
    {J : GrothendieckTopology C} {T : GrothendieckTopology D} {F : D ⥤ C}
    {R : Sheaf J CommRingCat.{u}} {hR : Presheaf.IsSheaf T (F.op ⋙ R.obj)}
    (p : InternalPrecompositionMorphism J T F R hR) where
  /-- Algebraic inverse image, with all operations transported along inverse image. -/
  algebraic : AlgebraicInverseImage p.ringed.inverse R
    (⟨F.op ⋙ R.obj, hR⟩ : Sheaf T CommRingCat.{u})
  /-- The actual section modules of the algebraic inverse image. -/
  sections (M : ringedSiteModules.{u} (baseRing J R)) (U : Dᵒᵖ) :
    (algebraic.modules.obj M).val.obj U ≃ₗ[R.obj.obj (F.op.obj U)] M.val.obj (F.op.obj U)
  /-- The tensor-formula module pullback. -/
  pullback : ringedSiteModules.{u} (baseRing J R) ⥤
    ringedSiteModules.{u} (baseRing T (⟨F.op ⋙ R.obj, hR⟩ : Sheaf T CommRingCat.{u}))
  /-- Scalar extension is along the identity structural ring map. -/
  objects (M : ringedSiteModules.{u} (baseRing J R)) :
    pullback.obj M = changeOfRings
      (𝟙 (⟨F.op ⋙ R.obj, hR⟩ : Sheaf T CommRingCat.{u})) (algebraic.modules.obj M)
  /-- This is the module pullback adjunction, not an unrelated tensor functor. -/
  adjunction : pullback ⊣ p.ringed.modules
  /-- Multiplication R tensor_R M to M, naturally in M. -/
  unitor : pullback ≅ algebraic.modules
/-- Equations specifying the normalized inverse image, multiplication unitor,
and exactness of the existing module pullback.
Source: paragraph (3), Stacks 03D7, 03DA, 03EK
(blueprint: lem-sfb-internal-restriction-module-tensor). -/
def InternalModulePullbackLaws {D : Type u} [SmallCategory D]
    {J : GrothendieckTopology C} {T : GrothendieckTopology D} {F : D ⥤ C}
    {R : Sheaf J CommRingCat.{u}} {hR : Presheaf.IsSheaf T (F.op ⋙ R.obj)}
    {p : InternalPrecompositionMorphism J T F R hR}
    (core : InternalModulePullback p) : Prop :=
  (core.algebraic.ringUnderlying.hom = p.ringed.ringMap) ∧
  (∀ (M : ringedSiteModules.{u} (baseRing J R)) (U : Dᵒᵖ)
        (m : (core.algebraic.modules.obj M).val.obj U),
      ((core.algebraic.moduleUnderlying.hom.app M).hom ≫ (eqToIso p.inverse).hom.app
        ((toSheaf (baseRing J R) ⋙ sheafCompose J (forget AddCommGrpCat.{u})).obj M)).app U m =
          core.sections M U m) ∧
  (∀ (M : ringedSiteModules.{u} (baseRing J R)) {U V : Dᵒᵖ} (a : U ⟶ V)
        (m : (core.algebraic.modules.obj M).val.obj U),
      core.sections M V ((core.algebraic.modules.obj M).val.map a m) =
        M.val.map (F.op.map a) (core.sections M U m)) ∧
  (∀ {M N : ringedSiteModules.{u} (baseRing J R)} (b : M ⟶ N) (U : Dᵒᵖ)
        (m : (core.algebraic.modules.obj M).val.obj U),
      core.sections N U ((core.algebraic.modules.map b).val.app U m) =
        b.val.app (F.op.obj U) (core.sections M U m)) ∧
  (∀ (M : ringedSiteModules.{u} (baseRing J R)) (U : Dᵒᵖ)
        (r : R.obj.obj (F.op.obj U)) (m : (core.algebraic.modules.obj M).val.obj U),
      (core.unitor.hom.app M).val.app U ((eqToIso (core.objects M)).inv.val.app U
        (ringedComparisonScalarSection (𝟙 (⟨F.op ⋙ R.obj, hR⟩ : Sheaf T CommRingCat.{u}))
          (core.algebraic.modules.obj M) U r m)) = r • m) ∧
  (∀ (M : ringedSiteModules.{u} (baseRing J R)) (U : Dᵒᵖ)
        (m : (core.algebraic.modules.obj M).val.obj U),
      (core.unitor.inv.app M).val.app U m = (eqToIso (core.objects M)).inv.val.app U
        (ringedComparisonScalarSection (𝟙 (⟨F.op ⋙ R.obj, hR⟩ : Sheaf T CommRingCat.{u}))
          (core.algebraic.modules.obj M) U 1 m)) ∧
  (core.pullback.Additive) ∧
  (PreservesFiniteLimits core.pullback) ∧
  (PreservesFiniteColimits core.pullback)

/-- Tensor preservation and coherence for the specified module pullback.
Source: paragraph (3), Stacks 03EK
(blueprint: lem-sfb-internal-restriction-module-tensor). -/
structure InternalExactTensorPullback {D : Type u} [SmallCategory D]
    {J : GrothendieckTopology C} {T : GrothendieckTopology D} {F : D ⥤ C}
    {R : Sheaf J CommRingCat.{u}} {hR : Presheaf.IsSheaf T (F.op ⋙ R.obj)}
    (p : InternalPrecompositionMorphism J T F R hR) where
  /-- The normalized scalar-extension module pullback. -/
  core : InternalModulePullback p
  /-- All section and multiplication equations, and exactness. -/
  laws : InternalModulePullbackLaws core
  /-- The normalized canonical comparison, including generalized pure tensors. -/
  comparison : CanonicalRingedTensorComparison R (⟨F.op ⋙ R.obj, hR⟩ : Sheaf T CommRingCat.{u})
    (⟨F.op ⋙ R.obj, hR⟩ : Sheaf T CommRingCat.{u}) p.ringed.inverse core.algebraic
    (𝟙 (⟨F.op ⋙ R.obj, hR⟩ : Sheaf T CommRingCat.{u})) core.pullback core.objects
  /-- After the multiplication identification, the comparison is the identity on
  presheaf pure tensors followed by the existing module sheafification. -/
  tensor_pure (M N : ringedSiteModules.{u} (baseRing J R)) (U : Dᵒᵖ)
      (x : (core.pullback.obj M).val.obj U) (y : (core.pullback.obj N).val.obj U) :
    core.sections (M ⊗ N) U ((core.unitor.hom.app (M ⊗ N)).val.app U
      ((comparison.mu M N).inv.val.app U
        (ringedComparisonPure (⟨F.op ⋙ R.obj, hR⟩ : Sheaf T CommRingCat.{u})
          (core.pullback.obj M) (core.pullback.obj N) U x y))) =
      ringedComparisonPure R M N (F.op.obj U)
        (core.sections M U ((core.unitor.hom.app M).val.app U x))
        (core.sections N U ((core.unitor.hom.app N).val.app U y))
  /-- The canonical tensorator and regular unit have all associativity, symmetry
  and unit coherence equations. -/
  coherence : ∃ monoidal : core.pullback.Monoidal,
    (∀ M N : ringedSiteModules.{u} (baseRing J R),
      @Functor.LaxMonoidal.μ _ _ _ _ _ _ core.pullback monoidal.toLaxMonoidal M N =
        (comparison.mu M N).inv) ∧
    (∀ M N : ringedSiteModules.{u} (baseRing J R),
      (β_ (core.pullback.obj M) (core.pullback.obj N)).hom ≫ (comparison.mu N M).inv =
        (comparison.mu M N).inv ≫ core.pullback.map (β_ M N).hom) ∧
    (∀ (U : Dᵒᵖ) (r : R.obj.obj (F.op.obj U)),
      core.sections (SheafOfModules.unit (baseRing J R)) U
        ((core.unitor.hom.app (SheafOfModules.unit (baseRing J R))).val.app U
          ((internalRegularUnitMap R (⟨F.op ⋙ R.obj, hR⟩ : Sheaf T CommRingCat.{u})
            core.pullback monoidal).val.app U r)) = r)

/-- The section identification of the recorded presentation, including its underlying
presheaf comparison. No new equivalence or section module is chosen.
Source: action-site section formula in paragraph (3)
(blueprint: lem-sfb-internal-restriction-module-tensor). -/
noncomputable def internalPresentationSection [HasFiniteLimits C] {J : Precoverage C}
    {hJ : J.IsSiteForCoverings} {K : Cᵒᵖ ⥤ GrpCat.{u}}
    {R : Sheaf J.toGrothendieck CommRingCat.{u}} (P : Presentation K J hJ R)
    (M : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck R))
    (X : C) (x : (P.sheafEquivalence.functor.obj M).val.obj (op (Object.mk X))) :
    M.obj.val.obj (op X) :=
  P.sections M.obj X ((P.underlying.inv.app M).app _ x)

/-- Tensor on the action site is the base sheaf tensor with diagonal action.
The two isomorphisms specify this identification on the sheafification images of
presheaf pure tensors, rather than choosing unrelated tensor objects.
Source: paragraph (3), Stacks 03EK
(blueprint: lem-sfb-internal-restriction-module-tensor). -/
def InternalDiagonalTensor [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings) (K : Cᵒᵖ ⥤ GrpCat.{u})
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) (P : Presentation K J hJ R) : Prop :=
  ∀ M N : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck R),
    ∃ (H : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck R))
      (e : P.sheafEquivalence.functor.obj H ≅
        P.sheafEquivalence.functor.obj M ⊗ P.sheafEquivalence.functor.obj N)
      (b : (forgetSheaf J.toGrothendieck (baseRing J.toGrothendieck R)).obj H ≅
        (forgetSheaf J.toGrothendieck (baseRing J.toGrothendieck R)).obj M ⊗
          (forgetSheaf J.toGrothendieck (baseRing J.toGrothendieck R)).obj N),
      (∀ (U : Cᵒᵖ) (a : K.obj U) (x : M.obj.val.obj U) (y : N.obj.val.obj U),
        b.hom.val.app U (H.obj.action.act U a
          (b.inv.val.app U (ringedComparisonPure R
            ((forgetSheaf _ _).obj M) ((forgetSheaf _ _).obj N) U x y))) =
          ringedComparisonPure R ((forgetSheaf _ _).obj M) ((forgetSheaf _ _).obj N) U
            (M.obj.action.act U a x) (N.obj.action.act U a y)) ∧
      (∀ (X : C) (x : (P.sheafEquivalence.functor.obj M).val.obj (op (Object.mk X)))
        (y : (P.sheafEquivalence.functor.obj N).val.obj (op (Object.mk X))),
        b.hom.val.app (op X) (internalPresentationSection P H X
          (e.inv.val.app (op (Object.mk X))
            (ringedComparisonPure (coefficientSheaf K J hJ R)
              (P.sheafEquivalence.functor.obj M) (P.sheafEquivalence.functor.obj N)
                (op (Object.mk X)) x y))) =
          ringedComparisonPure R ((forgetSheaf _ _).obj M) ((forgetSheaf _ _).obj N)
            (op X) (internalPresentationSection P M X x) (internalPresentationSection P N X y))

```

## New

The same block, with only blueprint ownership tags changed to
`def-sfb-internal-restriction-module-tensor-data`, lives in
lean/Sheaf/CategoryTheory/InternalRestrictionModuleTensorData.lean.
The original module now begins its imports with:

```lean
public import Sheaf.CategoryTheory.InternalRestrictionModuleTensorData
```

The extracted declarations are InternalPrecompositionMorphism, internalRegularUnitMap,
InternalModulePullback, InternalModulePullbackLaws, InternalExactTensorPullback,
internalPresentationSection and InternalDiagonalTensor, all in the existing
CategoryTheory.InternalActionSite namespace. The data module publicly retains
all seven original public imports. The original theorem module privately imports
the three strict argument pieces and SheafActionGrothendieckInflation.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.InternalRestrictionModuleTensor | G3 | Same specification names and bodies publicly re-exported; main theorem type unchanged. |
| Sheaf.CategoryTheory.InternalRestrictionModuleTensorData | G3, new | Owns the extracted declarations without semantic changes. |
| Sheaf.CategoryTheory.InternalRestrictionModulePullback | G3, new | Imports specifications for the exact scalar-extension and section-identification subargument. |
| Sheaf.CategoryTheory.InternalActionDiagonalTensor | G3, new | Imports specifications for the diagonal tensor subargument. |
| Sheaf.CategoryTheory.NormalizedPrecompositionTensor | G3, new | Imports specifications for tensor enhancement of a supplied core. |

No other module imports or uses the original assigned module. The existing DAG
parents, notably lem-sfb-action-topos-geometric-restriction, keep their dependency
on the original node and theorem. No target statement changes.

## Status

landed 20261026T081855-L-2094745 2026-10-26 (merge of deliver/G3/Sheaf.CategoryTheory.InternalRestrictionModuleTensor)
