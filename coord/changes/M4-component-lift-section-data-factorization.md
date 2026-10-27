# Component lift section data: module factorization

## Reason

The item combines geometric component pullback, local finite-free duality and evaluation
of module sections in one theorem. Its auxiliary data have to be imported by the three
separate proof obligations without an import cycle. Move the data, constructions and
proved exactness instances verbatim to `Sheaf.Paper.ComponentLiftSectionDefs`; the item
publicly imports that module. This changes only declaration ownership. Every elaborated
signature, definition body, instance name and attribute remains the same. The blueprint
tags now name the definition node owning these declarations. No target meaning changes.

## Old

In `Sheaf.Paper.ComponentLiftLisseSectionComparison`:

```lean
/-- Relative tests transported along the specified component homeomorphism.
Source: HRS (4.1) (blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
def componentLiftTests (T : Scheme.{u}) [IsAffine T] (S : Profinite.{u})
    (e : affineComponentSpace T ≃ₜ S) : Over S ⥤ T.ProEt :=
  Over.map (ConcreteCategory.ofHom
    (⟨e.symm, e.symm.continuous⟩ : C(S, affineComponentSpace T))) ⋙ componentTests T

/-- Coefficient-normalized inverse-image data for the relative component tests.
Source: HRS (4.1) and Proposition 4.3(3)
(blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
structure ComponentLiftCoefficient (Λ : Profinite.CondensedRing.{u})
    [IsCommMonObj Λ.X] (S : Profinite.{u}) (T : Scheme.{u}) [IsAffine T]
    (e : affineComponentSpace T ≃ₜ S) where
  projection : ∀ E : Over S, C(((componentLiftTests T S e).obj E).left, E.left)
  projection_over : ∀ (E : Over S) (x : ((componentLiftTests T S e).obj E).left),
    E.hom (projection E x) = e (ConnectedComponents.mk
      (((componentLiftTests T S e).obj E).hom x))
  projection_natural : ∀ (E E' : Over S) (a : E ⟶ E')
      (x : ((componentLiftTests T S e).obj E).left),
    projection E' (((componentLiftTests T S e).map a).left x) = a.left (projection E x)
  projection_universal : ∀ (W : Over T) (E : Over S) (p : C(W.left, E.left)),
    (∀ w : W.left, E.hom (p w) = e (ConnectedComponents.mk (W.hom w))) →
    ∃! a : W ⟶ (Scheme.ProEt.forget T).obj ((componentLiftTests T S e).obj E),
      ∀ w : W.left, projection E (a.left w) = p w
  continuous : (componentLiftTests T S e).IsContinuous
    ((coherentTopology Profinite.{u}).over S) (Scheme.ProEt.topology T)
  inverse : Sheaf ((coherentTopology Profinite.{u}).over S) Ab.{u + 1} ⥤
    Sheaf (Scheme.ProEt.topology T) Ab.{u + 1} :=
      Functor.sheafPullbackConstruction.sheafPullback (componentLiftTests T S e) Ab.{u + 1}
        ((coherentTopology Profinite.{u}).over S) (Scheme.ProEt.topology T)
  inverse_eq : inverse =
    Functor.sheafPullbackConstruction.sheafPullback (componentLiftTests T S e) Ab.{u + 1}
      ((coherentTopology Profinite.{u}).over S) (Scheme.ProEt.topology T) := by rfl
  adj : inverse ⊣ (componentLiftTests T S e).sheafPushforwardContinuous Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over S) (Scheme.ProEt.topology T)
  adj_eq : HEq adj (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (componentLiftTests T S e) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over S) (Scheme.ProEt.topology T))
  braided : inverse.Braided
  limits : PreservesFiniteLimits inverse
  colimits : PreservesFiniteColimits inverse
  coefficient : inverse.mapMon.obj (Mon.mk (profiniteCoefficient Λ.X S)) ≅
    Mon.mk (condensedRingObj Λ.X T)
  point : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} S ⋙ inverse ≅
    upperStarFromPoint T
  point_monoidal : NatTrans.IsMonoidal point.hom
  coefficient_eq : coefficient.hom.hom = point.hom.app Λ.X

/-- The module inverse image with scalar transport through the specified coefficient iso.
Source: HRS (4.1) (blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
def componentLiftModules {Λ : Profinite.CondensedRing.{u}} [IsCommMonObj Λ.X]
    {S : Profinite.{u}} {T : Scheme.{u}} [IsAffine T]
    {e : affineComponentSpace T ≃ₜ S} (d : ComponentLiftCoefficient Λ S T e) :=
  letI := d.braided
  d.inverse.mapMod (profiniteCoefficient Λ.X S) ⋙ Mod.comap d.coefficient.inv.hom

/-- Exactness on modules is inherited from exact inverse image and scalar restriction.
Source: HRS (4.1) (blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
instance componentLiftModules_limits {Λ : Profinite.CondensedRing.{u}}
    [IsCommMonObj Λ.X] {S : Profinite.{u}} {T : Scheme.{u}} [IsAffine T]
    {e : affineComponentSpace T ≃ₜ S} (d : ComponentLiftCoefficient Λ S T e) :
    PreservesFiniteLimits (componentLiftModules d) :=
  letI := d.braided
  letI := d.limits
  inferInstanceAs (PreservesFiniteLimits
    (d.inverse.mapMod (profiniteCoefficient Λ.X S) ⋙ Mod.comap d.coefficient.inv.hom))

/-- Right exactness on modules is inherited from inverse image and scalar restriction.
Source: HRS (4.1) (blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
instance componentLiftModules_colimits {Λ : Profinite.CondensedRing.{u}}
    [IsCommMonObj Λ.X] {S : Profinite.{u}} {T : Scheme.{u}} [IsAffine T]
    {e : affineComponentSpace T ≃ₜ S} (d : ComponentLiftCoefficient Λ S T e) :
    PreservesFiniteColimits (componentLiftModules d) :=
  letI := d.braided
  letI := d.colimits
  inferInstanceAs (PreservesFiniteColimits
    (d.inverse.mapMod (profiniteCoefficient Λ.X S) ⋙ Mod.comap d.coefficient.inv.hom))

/-- The module inverse image is additive by preservation of binary products.
Source: HRS (4.1) (blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
instance componentLiftModules_additive {Λ : Profinite.CondensedRing.{u}}
    [IsCommMonObj Λ.X] {S : Profinite.{u}} {T : Scheme.{u}} [IsAffine T]
    {e : affineComponentSpace T ≃ₜ S} (d : ComponentLiftCoefficient Λ S T e) :
    (componentLiftModules d).Additive := Functor.additive_of_preserves_binary_products _

/-- The exact component pullback on ordinary unbounded derived categories.
Source: HRS (4.1) (blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
def componentLiftDerived {Λ : Profinite.CondensedRing.{u}} [IsCommMonObj Λ.X]
    {S : Profinite.{u}} {T : Scheme.{u}} [IsAffine T]
    {e : affineComponentSpace T ≃ₜ S} (d : ComponentLiftCoefficient Λ S T e) :=
  (componentLiftModules d).mapDerivedCategory

/-- Actual section pullback: the module unit at U followed by terminal base-change restriction.
Source: HRS (4.2); Stacks 08JJ, evaluation on the coefficient unit
(blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
def componentLiftSectionPullback
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U V : Scheme.{u}} (g : V ⟶ U)
    (L : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ.X U)) :
    (condensedModuleSections Λ.X U).obj L ⟶
      (condensedModuleSections Λ.X V).obj ((upperStar Λ.X g).obj L) :=
  ((upperStarLowerStarAdjunction Λ.X g).unit.app L).hom.hom.app
      (op (Scheme.ProEt.mk (𝟙 U))) ≫
    ((upperStar Λ.X g).obj L).X.obj.map (overPullbackObjMkIdIso g).inv.op

/-- Evaluation on 1 after the fully faithful degree-zero embedding.
Source: HRS (4.2), Stacks 08JJ
(blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
def componentLiftHomSection
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (T : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T))
    (b : (DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ.X T)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj L) : (condensedModuleSections Λ.X T).obj L :=
  ((DerivedCategory.singleFunctor _ 0).preimage b).hom.hom.app
    (op (Scheme.ProEt.mk (𝟙 T))) (sfbSectionOne Λ.X T (Scheme.ProEt.mk (𝟙 T)))

/-- The local finite-free dual, both K-flat complexes, and the two derived duality identities.
Source: HRS Definition 3.3; Stacks 08JJ, lemma-dual-perfect-complex
(blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
def ComponentLiftLisseFacts
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (T : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T)) : Prop :=
  ∃ P : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T),
    IsLisseCoefficientModule Λ.X P ∧ Nonempty (ExactPairing L P) ∧
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      ((HomologicalComplex.single _ (.up ℤ) 0).obj L) ∧
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      ((HomologicalComplex.single _ (.up ℤ) 0).obj P) ∧
    Nonempty (ExactPairing ((DerivedCategory.singleFunctor _ 0).obj L)
      ((DerivedCategory.singleFunctor _ 0).obj P))

/-- Unit-normalized comparison on ordinary derived Hom groups. Its source and target units
are the actual monoidal units; the final single-complex iso fixes the heart normalization.
Source: HRS Proposition 4.3(3), (4.2)
(blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
def ComponentLiftHomIdentity
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V] (g : V ⟶ U)
    {S : Profinite.{u}} {eU : affineComponentSpace U ≃ₜ S}
    {eV : affineComponentSpace V ≃ₜ S}
    (dU : ComponentLiftCoefficient Λ S U eU) (dV : ComponentLiftCoefficient Λ S V eV)
    (mU : (componentLiftDerived dU).Monoidal) (mV : (componentLiftDerived dV).Monoidal)
    (c : componentLiftDerived dU ⋙ moduleObjectDerivedPullback Λ.X g ≅
      componentLiftDerived dV) : Prop :=
  letI := mU
  letI := mV
  ∀ (N : Evaluation.D ((coherentTopology Profinite.{u}).over S) (profiniteCoefficient Λ.X S)),
    IsDualizable N →
    ∀ (L : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ.X U)),
      IsLisseCoefficientModule Λ.X L →
      ∀ (a : (componentLiftDerived dU).obj N ≅ (DerivedCategory.singleFunctor _ 0).obj L)
        (b : 𝟙_ (Evaluation.D ((coherentTopology Profinite.{u}).over S)
          (profiniteCoefficient Λ.X S)) ⟶ N),
        (leftDerivedUpperStarUnitIso Λ.X g).inv ≫
          (moduleObjectDerivedPullback Λ.X g).map
            ((Functor.Monoidal.εIso (componentLiftDerived dU)).hom ≫
              (componentLiftDerived dU).map b ≫ a.hom) =
        (Functor.Monoidal.εIso (componentLiftDerived dV)).hom ≫
          (componentLiftDerived dV).map b ≫ (c.app N).inv ≫
          (moduleObjectDerivedPullback Λ.X g).map a.hom

/-- A monoidal comparison includes the tensor equation and the coefficient unit equation.
Source: HRS (4.1) (blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
def ComponentLiftMonoidal {Λ : Profinite.CondensedRing.{u}} [IsCommMonObj Λ.X]
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V] {g : V ⟶ U}
    {S : Profinite.{u}} {eU : affineComponentSpace U ≃ₜ S}
    {eV : affineComponentSpace V ≃ₜ S}
    {dU : ComponentLiftCoefficient Λ S U eU} {dV : ComponentLiftCoefficient Λ S V eV}
    (mU : (componentLiftDerived dU).Monoidal) (mV : (componentLiftDerived dV).Monoidal)
    (c : componentLiftDerived dU ⋙ moduleObjectDerivedPullback Λ.X g ≅
      componentLiftDerived dV) : Prop :=
  letI := mU
  letI := mV
  letI : (moduleObjectDerivedPullback Λ.X g).Monoidal := monoidal_leftDerivedUpperStar Λ.X g
  NatTrans.IsMonoidal c.hom

/-- The Hom pullback commutes with evaluation at 1 and with the actual section unit map.
Source: HRS (4.2); Stacks 08JJ
(blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
def ComponentLiftSectionIdentity
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U V : Scheme.{u}} (g : V ⟶ U) : Prop :=
  ∀ (L : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ.X U))
    (b : (DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ.X U)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj L),
    componentLiftHomSection Λ V ((upperStar Λ.X g).obj L)
      ((leftDerivedUpperStarUnitIso Λ.X g).inv ≫
        (moduleObjectDerivedPullback Λ.X g).map b ≫
        ((Functor.singleFunctorCompLeftDerivedFunctorIso (upperStar Λ.X g)).app L).hom) =
      (componentLiftSectionPullback Λ g L) (componentLiftHomSection Λ U L b)

/-- A morphism of component lifts means that its induced map on the fixed quotient is id.
Source: HRS Proposition 4.3(3)
(blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
def IsComponentLiftMap {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    {S : Profinite.{u}} (eU : affineComponentSpace U ≃ₜ S)
    (eV : affineComponentSpace V ≃ₜ S) (g : V ⟶ U) : Prop :=
  ∀ v : V, eU (ConnectedComponents.mk (g v)) = eV (ConnectedComponents.mk v)

/-- The component inverse-image unit on a specified relative test.
Source: HRS (4.1) (blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
def componentLiftTestUnit {Λ : Profinite.CondensedRing.{u}} [IsCommMonObj Λ.X]
    {S : Profinite.{u}} {T : Scheme.{u}} [IsAffine T]
    {e : affineComponentSpace T ≃ₜ S} (d : ComponentLiftCoefficient Λ S T e)
    (M : Sheaf ((coherentTopology Profinite.{u}).over S) Ab.{u + 1}) (E : Over S) :
    M.obj.obj (op E) ⟶ (d.inverse.obj M).obj.obj
      (op ((componentLiftTests T S e).obj E)) :=
  (d.adj.unit.app M).hom.app (op E)

/-- An ordinary module comparison is induced by the projection-preserving test iso exactly
when its composite with the two adjunction units agrees on every test and every module.
Source: HRS (4.1) (blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
def ComponentLiftInducedComparison {Λ : Profinite.CondensedRing.{u}} [IsCommMonObj Λ.X]
    {S : Profinite.{u}} {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    {eU : affineComponentSpace U ≃ₜ S} {eV : affineComponentSpace V ≃ₜ S}
    (dU : ComponentLiftCoefficient Λ S U eU) (dV : ComponentLiftCoefficient Λ S V eV)
    (g : V ⟶ U)
    (k : componentLiftTests V S eV ≅ componentLiftTests U S eU ⋙
      MorphismProperty.Over.pullback @WeaklyEtale ⊤ g)
    (q : componentLiftModules dU ⋙ upperStar Λ.X g ≅ componentLiftModules dV) : Prop :=
  ∀ (M : Mod (Sheaf ((coherentTopology Profinite.{u}).over S) Ab.{u + 1})
      (profiniteCoefficient Λ.X S)) (E : Over S),
    componentLiftTestUnit dU M.X E ≫
      ((upperStarLowerStarAdjunction Λ.X g).unit.app
        ((componentLiftModules dU).obj M)).hom.hom.app
          (op ((componentLiftTests U S eU).obj E)) ≫
      ((upperStar Λ.X g).obj ((componentLiftModules dU).obj M)).X.obj.map
        (k.app E).hom.op ≫
      (q.app M).hom.hom.hom.app (op ((componentLiftTests V S eV).obj E)) =
    componentLiftTestUnit dV M.X E

/-- The localization of an ordinary component module comparison, using the canonical
comparison between the derived pullback and its termwise exact model.
Source: HRS (4.1) (blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
def componentLiftDerivedComparison {Λ : Profinite.CondensedRing.{u}} [IsCommMonObj Λ.X]
    {S : Profinite.{u}} {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    {eU : affineComponentSpace U ≃ₜ S} {eV : affineComponentSpace V ≃ₜ S}
    (dU : ComponentLiftCoefficient Λ S U eU) (dV : ComponentLiftCoefficient Λ S V eV)
    (g : V ⟶ U) (q : componentLiftModules dU ⋙ upperStar Λ.X g ≅ componentLiftModules dV) :
    componentLiftDerived dU ⋙ moduleObjectDerivedPullback Λ.X g ≅ componentLiftDerived dV :=
  Functor.isoWhiskerLeft (componentLiftDerived dU)
      (leftDerivedUpperStarIsoMapDerivedCategory Λ.X g) ≪≫
    (Functor.mapDerivedCategoryCompIso (componentLiftModules dU) (upperStar Λ.X g)).symm ≪≫
    Functor.mapDerivedCategoryNatIso q

/-- Full faithfulness and essential surjectivity on the full dualizable subcategories.
Source: HRS Proposition 4.3(3)
(blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
def ComponentLiftEquivalence {Λ : Profinite.CondensedRing.{u}} [IsCommMonObj Λ.X]
    {S : Profinite.{u}} {T : Scheme.{u}} [IsAffine T] {e : affineComponentSpace T ≃ₜ S}
    (d : ComponentLiftCoefficient Λ S T e) : Prop :=
  (∀ (M N : Evaluation.D ((coherentTopology Profinite.{u}).over S)
      (profiniteCoefficient Λ.X S)), IsDualizable M → IsDualizable N →
    Function.Bijective (fun f : M ⟶ N ↦ (componentLiftDerived d).map f)) ∧
  (∀ N : Evaluation.D ((coherentTopology Profinite.{u}).over S) (profiniteCoefficient Λ.X S),
    IsDualizable N → IsDualizable ((componentLiftDerived d).obj N)) ∧
  ∀ L : Evaluation.D (Scheme.ProEt.topology T) (condensedRingObj Λ.X T), IsDualizable L →
    ∃ N : Evaluation.D ((coherentTopology Profinite.{u}).over S) (profiniteCoefficient Λ.X S),
      IsDualizable N ∧ Nonempty ((componentLiftDerived d).obj N ≅ L)

/-- Composition of actual section pullbacks under the ordinary module-composition iso.
Source: HRS (4.2) (blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
def ComponentLiftSectionComposition
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U V W : Scheme.{u}} (g : V ⟶ U) (h : W ⟶ V) : Prop :=
  ∀ (L : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ.X U))
    (s : (condensedModuleSections Λ.X U).obj L),
    (condensedModuleSections Λ.X W).map ((upperStarComp Λ.X h g).hom.app L)
      ((componentLiftSectionPullback Λ (h ≫ g) L) s) =
    (componentLiftSectionPullback Λ h ((upperStar Λ.X g).obj L))
      ((componentLiftSectionPullback Λ g L) s)

/-- Naturality of the actual section map, on every morphism of modules.
Source: HRS (4.2) (blueprint: lem-sfb-component-lift-lisse-section-comparison). -/
def ComponentLiftSectionNaturality
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U V : Scheme.{u}} (g : V ⟶ U) : Prop :=
  ∀ (L L' : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ.X U))
    (f : L ⟶ L') (s : (condensedModuleSections Λ.X U).obj L),
    (condensedModuleSections Λ.X V).map ((upperStar Λ.X g).map f)
      ((componentLiftSectionPullback Λ g L) s) =
    (componentLiftSectionPullback Λ g L') ((condensedModuleSections Λ.X U).map f s)

```

## New

The item publicly imports the new module:

```lean
public import Sheaf.Paper.ComponentLiftSectionDefs
```

The declarations in `Sheaf.Paper.ComponentLiftSectionDefs` are:

```lean
/-- Relative tests transported along the specified component homeomorphism.
Source: HRS (4.1) (blueprint: def-sfb-component-lift-section-data). -/
def componentLiftTests (T : Scheme.{u}) [IsAffine T] (S : Profinite.{u})
    (e : affineComponentSpace T ≃ₜ S) : Over S ⥤ T.ProEt :=
  Over.map (ConcreteCategory.ofHom
    (⟨e.symm, e.symm.continuous⟩ : C(S, affineComponentSpace T))) ⋙ componentTests T

/-- Coefficient-normalized inverse-image data for the relative component tests.
Source: HRS (4.1) and Proposition 4.3(3)
(blueprint: def-sfb-component-lift-section-data). -/
structure ComponentLiftCoefficient (Λ : Profinite.CondensedRing.{u})
    [IsCommMonObj Λ.X] (S : Profinite.{u}) (T : Scheme.{u}) [IsAffine T]
    (e : affineComponentSpace T ≃ₜ S) where
  projection : ∀ E : Over S, C(((componentLiftTests T S e).obj E).left, E.left)
  projection_over : ∀ (E : Over S) (x : ((componentLiftTests T S e).obj E).left),
    E.hom (projection E x) = e (ConnectedComponents.mk
      (((componentLiftTests T S e).obj E).hom x))
  projection_natural : ∀ (E E' : Over S) (a : E ⟶ E')
      (x : ((componentLiftTests T S e).obj E).left),
    projection E' (((componentLiftTests T S e).map a).left x) = a.left (projection E x)
  projection_universal : ∀ (W : Over T) (E : Over S) (p : C(W.left, E.left)),
    (∀ w : W.left, E.hom (p w) = e (ConnectedComponents.mk (W.hom w))) →
    ∃! a : W ⟶ (Scheme.ProEt.forget T).obj ((componentLiftTests T S e).obj E),
      ∀ w : W.left, projection E (a.left w) = p w
  continuous : (componentLiftTests T S e).IsContinuous
    ((coherentTopology Profinite.{u}).over S) (Scheme.ProEt.topology T)
  inverse : Sheaf ((coherentTopology Profinite.{u}).over S) Ab.{u + 1} ⥤
    Sheaf (Scheme.ProEt.topology T) Ab.{u + 1} :=
      Functor.sheafPullbackConstruction.sheafPullback (componentLiftTests T S e) Ab.{u + 1}
        ((coherentTopology Profinite.{u}).over S) (Scheme.ProEt.topology T)
  inverse_eq : inverse =
    Functor.sheafPullbackConstruction.sheafPullback (componentLiftTests T S e) Ab.{u + 1}
      ((coherentTopology Profinite.{u}).over S) (Scheme.ProEt.topology T) := by rfl
  adj : inverse ⊣ (componentLiftTests T S e).sheafPushforwardContinuous Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over S) (Scheme.ProEt.topology T)
  adj_eq : HEq adj (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (componentLiftTests T S e) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over S) (Scheme.ProEt.topology T))
  braided : inverse.Braided
  limits : PreservesFiniteLimits inverse
  colimits : PreservesFiniteColimits inverse
  coefficient : inverse.mapMon.obj (Mon.mk (profiniteCoefficient Λ.X S)) ≅
    Mon.mk (condensedRingObj Λ.X T)
  point : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} S ⋙ inverse ≅
    upperStarFromPoint T
  point_monoidal : NatTrans.IsMonoidal point.hom
  coefficient_eq : coefficient.hom.hom = point.hom.app Λ.X

/-- The module inverse image with scalar transport through the specified coefficient iso.
Source: HRS (4.1) (blueprint: def-sfb-component-lift-section-data). -/
def componentLiftModules {Λ : Profinite.CondensedRing.{u}} [IsCommMonObj Λ.X]
    {S : Profinite.{u}} {T : Scheme.{u}} [IsAffine T]
    {e : affineComponentSpace T ≃ₜ S} (d : ComponentLiftCoefficient Λ S T e) :=
  letI := d.braided
  d.inverse.mapMod (profiniteCoefficient Λ.X S) ⋙ Mod.comap d.coefficient.inv.hom

/-- Exactness on modules is inherited from exact inverse image and scalar restriction.
Source: HRS (4.1) (blueprint: def-sfb-component-lift-section-data). -/
instance componentLiftModules_limits {Λ : Profinite.CondensedRing.{u}}
    [IsCommMonObj Λ.X] {S : Profinite.{u}} {T : Scheme.{u}} [IsAffine T]
    {e : affineComponentSpace T ≃ₜ S} (d : ComponentLiftCoefficient Λ S T e) :
    PreservesFiniteLimits (componentLiftModules d) :=
  letI := d.braided
  letI := d.limits
  inferInstanceAs (PreservesFiniteLimits
    (d.inverse.mapMod (profiniteCoefficient Λ.X S) ⋙ Mod.comap d.coefficient.inv.hom))

/-- Right exactness on modules is inherited from inverse image and scalar restriction.
Source: HRS (4.1) (blueprint: def-sfb-component-lift-section-data). -/
instance componentLiftModules_colimits {Λ : Profinite.CondensedRing.{u}}
    [IsCommMonObj Λ.X] {S : Profinite.{u}} {T : Scheme.{u}} [IsAffine T]
    {e : affineComponentSpace T ≃ₜ S} (d : ComponentLiftCoefficient Λ S T e) :
    PreservesFiniteColimits (componentLiftModules d) :=
  letI := d.braided
  letI := d.colimits
  inferInstanceAs (PreservesFiniteColimits
    (d.inverse.mapMod (profiniteCoefficient Λ.X S) ⋙ Mod.comap d.coefficient.inv.hom))

/-- The module inverse image is additive by preservation of binary products.
Source: HRS (4.1) (blueprint: def-sfb-component-lift-section-data). -/
instance componentLiftModules_additive {Λ : Profinite.CondensedRing.{u}}
    [IsCommMonObj Λ.X] {S : Profinite.{u}} {T : Scheme.{u}} [IsAffine T]
    {e : affineComponentSpace T ≃ₜ S} (d : ComponentLiftCoefficient Λ S T e) :
    (componentLiftModules d).Additive := Functor.additive_of_preserves_binary_products _

/-- The exact component pullback on ordinary unbounded derived categories.
Source: HRS (4.1) (blueprint: def-sfb-component-lift-section-data). -/
def componentLiftDerived {Λ : Profinite.CondensedRing.{u}} [IsCommMonObj Λ.X]
    {S : Profinite.{u}} {T : Scheme.{u}} [IsAffine T]
    {e : affineComponentSpace T ≃ₜ S} (d : ComponentLiftCoefficient Λ S T e) :=
  (componentLiftModules d).mapDerivedCategory

/-- Actual section pullback: the module unit at U followed by terminal base-change restriction.
Source: HRS (4.2); Stacks 08JJ, evaluation on the coefficient unit
(blueprint: def-sfb-component-lift-section-data). -/
def componentLiftSectionPullback
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U V : Scheme.{u}} (g : V ⟶ U)
    (L : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ.X U)) :
    (condensedModuleSections Λ.X U).obj L ⟶
      (condensedModuleSections Λ.X V).obj ((upperStar Λ.X g).obj L) :=
  ((upperStarLowerStarAdjunction Λ.X g).unit.app L).hom.hom.app
      (op (Scheme.ProEt.mk (𝟙 U))) ≫
    ((upperStar Λ.X g).obj L).X.obj.map (overPullbackObjMkIdIso g).inv.op

/-- Evaluation on 1 after the fully faithful degree-zero embedding.
Source: HRS (4.2), Stacks 08JJ
(blueprint: def-sfb-component-lift-section-data). -/
def componentLiftHomSection
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (T : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T))
    (b : (DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ.X T)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj L) : (condensedModuleSections Λ.X T).obj L :=
  ((DerivedCategory.singleFunctor _ 0).preimage b).hom.hom.app
    (op (Scheme.ProEt.mk (𝟙 T))) (sfbSectionOne Λ.X T (Scheme.ProEt.mk (𝟙 T)))

/-- The local finite-free dual, both K-flat complexes, and the two derived duality identities.
Source: HRS Definition 3.3; Stacks 08JJ, lemma-dual-perfect-complex
(blueprint: def-sfb-component-lift-section-data). -/
def ComponentLiftLisseFacts
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (T : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T)) : Prop :=
  ∃ P : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T),
    IsLisseCoefficientModule Λ.X P ∧ Nonempty (ExactPairing L P) ∧
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      ((HomologicalComplex.single _ (.up ℤ) 0).obj L) ∧
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      ((HomologicalComplex.single _ (.up ℤ) 0).obj P) ∧
    Nonempty (ExactPairing ((DerivedCategory.singleFunctor _ 0).obj L)
      ((DerivedCategory.singleFunctor _ 0).obj P))

/-- Unit-normalized comparison on ordinary derived Hom groups. Its source and target units
are the actual monoidal units; the final single-complex iso fixes the heart normalization.
Source: HRS Proposition 4.3(3), (4.2)
(blueprint: def-sfb-component-lift-section-data). -/
def ComponentLiftHomIdentity
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V] (g : V ⟶ U)
    {S : Profinite.{u}} {eU : affineComponentSpace U ≃ₜ S}
    {eV : affineComponentSpace V ≃ₜ S}
    (dU : ComponentLiftCoefficient Λ S U eU) (dV : ComponentLiftCoefficient Λ S V eV)
    (mU : (componentLiftDerived dU).Monoidal) (mV : (componentLiftDerived dV).Monoidal)
    (c : componentLiftDerived dU ⋙ moduleObjectDerivedPullback Λ.X g ≅
      componentLiftDerived dV) : Prop :=
  letI := mU
  letI := mV
  ∀ (N : Evaluation.D ((coherentTopology Profinite.{u}).over S) (profiniteCoefficient Λ.X S)),
    IsDualizable N →
    ∀ (L : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ.X U)),
      IsLisseCoefficientModule Λ.X L →
      ∀ (a : (componentLiftDerived dU).obj N ≅ (DerivedCategory.singleFunctor _ 0).obj L)
        (b : 𝟙_ (Evaluation.D ((coherentTopology Profinite.{u}).over S)
          (profiniteCoefficient Λ.X S)) ⟶ N),
        (leftDerivedUpperStarUnitIso Λ.X g).inv ≫
          (moduleObjectDerivedPullback Λ.X g).map
            ((Functor.Monoidal.εIso (componentLiftDerived dU)).hom ≫
              (componentLiftDerived dU).map b ≫ a.hom) =
        (Functor.Monoidal.εIso (componentLiftDerived dV)).hom ≫
          (componentLiftDerived dV).map b ≫ (c.app N).inv ≫
          (moduleObjectDerivedPullback Λ.X g).map a.hom

/-- A monoidal comparison includes the tensor equation and the coefficient unit equation.
Source: HRS (4.1) (blueprint: def-sfb-component-lift-section-data). -/
def ComponentLiftMonoidal {Λ : Profinite.CondensedRing.{u}} [IsCommMonObj Λ.X]
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V] {g : V ⟶ U}
    {S : Profinite.{u}} {eU : affineComponentSpace U ≃ₜ S}
    {eV : affineComponentSpace V ≃ₜ S}
    {dU : ComponentLiftCoefficient Λ S U eU} {dV : ComponentLiftCoefficient Λ S V eV}
    (mU : (componentLiftDerived dU).Monoidal) (mV : (componentLiftDerived dV).Monoidal)
    (c : componentLiftDerived dU ⋙ moduleObjectDerivedPullback Λ.X g ≅
      componentLiftDerived dV) : Prop :=
  letI := mU
  letI := mV
  letI : (moduleObjectDerivedPullback Λ.X g).Monoidal := monoidal_leftDerivedUpperStar Λ.X g
  NatTrans.IsMonoidal c.hom

/-- The Hom pullback commutes with evaluation at 1 and with the actual section unit map.
Source: HRS (4.2); Stacks 08JJ
(blueprint: def-sfb-component-lift-section-data). -/
def ComponentLiftSectionIdentity
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U V : Scheme.{u}} (g : V ⟶ U) : Prop :=
  ∀ (L : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ.X U))
    (b : (DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ.X U)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj L),
    componentLiftHomSection Λ V ((upperStar Λ.X g).obj L)
      ((leftDerivedUpperStarUnitIso Λ.X g).inv ≫
        (moduleObjectDerivedPullback Λ.X g).map b ≫
        ((Functor.singleFunctorCompLeftDerivedFunctorIso (upperStar Λ.X g)).app L).hom) =
      (componentLiftSectionPullback Λ g L) (componentLiftHomSection Λ U L b)

/-- A morphism of component lifts means that its induced map on the fixed quotient is id.
Source: HRS Proposition 4.3(3)
(blueprint: def-sfb-component-lift-section-data). -/
def IsComponentLiftMap {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    {S : Profinite.{u}} (eU : affineComponentSpace U ≃ₜ S)
    (eV : affineComponentSpace V ≃ₜ S) (g : V ⟶ U) : Prop :=
  ∀ v : V, eU (ConnectedComponents.mk (g v)) = eV (ConnectedComponents.mk v)

/-- The component inverse-image unit on a specified relative test.
Source: HRS (4.1) (blueprint: def-sfb-component-lift-section-data). -/
def componentLiftTestUnit {Λ : Profinite.CondensedRing.{u}} [IsCommMonObj Λ.X]
    {S : Profinite.{u}} {T : Scheme.{u}} [IsAffine T]
    {e : affineComponentSpace T ≃ₜ S} (d : ComponentLiftCoefficient Λ S T e)
    (M : Sheaf ((coherentTopology Profinite.{u}).over S) Ab.{u + 1}) (E : Over S) :
    M.obj.obj (op E) ⟶ (d.inverse.obj M).obj.obj
      (op ((componentLiftTests T S e).obj E)) :=
  (d.adj.unit.app M).hom.app (op E)

/-- An ordinary module comparison is induced by the projection-preserving test iso exactly
when its composite with the two adjunction units agrees on every test and every module.
Source: HRS (4.1) (blueprint: def-sfb-component-lift-section-data). -/
def ComponentLiftInducedComparison {Λ : Profinite.CondensedRing.{u}} [IsCommMonObj Λ.X]
    {S : Profinite.{u}} {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    {eU : affineComponentSpace U ≃ₜ S} {eV : affineComponentSpace V ≃ₜ S}
    (dU : ComponentLiftCoefficient Λ S U eU) (dV : ComponentLiftCoefficient Λ S V eV)
    (g : V ⟶ U)
    (k : componentLiftTests V S eV ≅ componentLiftTests U S eU ⋙
      MorphismProperty.Over.pullback @WeaklyEtale ⊤ g)
    (q : componentLiftModules dU ⋙ upperStar Λ.X g ≅ componentLiftModules dV) : Prop :=
  ∀ (M : Mod (Sheaf ((coherentTopology Profinite.{u}).over S) Ab.{u + 1})
      (profiniteCoefficient Λ.X S)) (E : Over S),
    componentLiftTestUnit dU M.X E ≫
      ((upperStarLowerStarAdjunction Λ.X g).unit.app
        ((componentLiftModules dU).obj M)).hom.hom.app
          (op ((componentLiftTests U S eU).obj E)) ≫
      ((upperStar Λ.X g).obj ((componentLiftModules dU).obj M)).X.obj.map
        (k.app E).hom.op ≫
      (q.app M).hom.hom.hom.app (op ((componentLiftTests V S eV).obj E)) =
    componentLiftTestUnit dV M.X E

/-- The localization of an ordinary component module comparison, using the canonical
comparison between the derived pullback and its termwise exact model.
Source: HRS (4.1) (blueprint: def-sfb-component-lift-section-data). -/
def componentLiftDerivedComparison {Λ : Profinite.CondensedRing.{u}} [IsCommMonObj Λ.X]
    {S : Profinite.{u}} {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    {eU : affineComponentSpace U ≃ₜ S} {eV : affineComponentSpace V ≃ₜ S}
    (dU : ComponentLiftCoefficient Λ S U eU) (dV : ComponentLiftCoefficient Λ S V eV)
    (g : V ⟶ U) (q : componentLiftModules dU ⋙ upperStar Λ.X g ≅ componentLiftModules dV) :
    componentLiftDerived dU ⋙ moduleObjectDerivedPullback Λ.X g ≅ componentLiftDerived dV :=
  Functor.isoWhiskerLeft (componentLiftDerived dU)
      (leftDerivedUpperStarIsoMapDerivedCategory Λ.X g) ≪≫
    (Functor.mapDerivedCategoryCompIso (componentLiftModules dU) (upperStar Λ.X g)).symm ≪≫
    Functor.mapDerivedCategoryNatIso q

/-- Full faithfulness and essential surjectivity on the full dualizable subcategories.
Source: HRS Proposition 4.3(3)
(blueprint: def-sfb-component-lift-section-data). -/
def ComponentLiftEquivalence {Λ : Profinite.CondensedRing.{u}} [IsCommMonObj Λ.X]
    {S : Profinite.{u}} {T : Scheme.{u}} [IsAffine T] {e : affineComponentSpace T ≃ₜ S}
    (d : ComponentLiftCoefficient Λ S T e) : Prop :=
  (∀ (M N : Evaluation.D ((coherentTopology Profinite.{u}).over S)
      (profiniteCoefficient Λ.X S)), IsDualizable M → IsDualizable N →
    Function.Bijective (fun f : M ⟶ N ↦ (componentLiftDerived d).map f)) ∧
  (∀ N : Evaluation.D ((coherentTopology Profinite.{u}).over S) (profiniteCoefficient Λ.X S),
    IsDualizable N → IsDualizable ((componentLiftDerived d).obj N)) ∧
  ∀ L : Evaluation.D (Scheme.ProEt.topology T) (condensedRingObj Λ.X T), IsDualizable L →
    ∃ N : Evaluation.D ((coherentTopology Profinite.{u}).over S) (profiniteCoefficient Λ.X S),
      IsDualizable N ∧ Nonempty ((componentLiftDerived d).obj N ≅ L)

/-- Composition of actual section pullbacks under the ordinary module-composition iso.
Source: HRS (4.2) (blueprint: def-sfb-component-lift-section-data). -/
def ComponentLiftSectionComposition
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U V W : Scheme.{u}} (g : V ⟶ U) (h : W ⟶ V) : Prop :=
  ∀ (L : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ.X U))
    (s : (condensedModuleSections Λ.X U).obj L),
    (condensedModuleSections Λ.X W).map ((upperStarComp Λ.X h g).hom.app L)
      ((componentLiftSectionPullback Λ (h ≫ g) L) s) =
    (componentLiftSectionPullback Λ h ((upperStar Λ.X g).obj L))
      ((componentLiftSectionPullback Λ g L) s)

/-- Naturality of the actual section map, on every morphism of modules.
Source: HRS (4.2) (blueprint: def-sfb-component-lift-section-data). -/
def ComponentLiftSectionNaturality
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U V : Scheme.{u}} (g : V ⟶ U) : Prop :=
  ∀ (L L' : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ.X U))
    (f : L ⟶ L') (s : (condensedModuleSections Λ.X U).obj L),
    (condensedModuleSections Λ.X V).map ((upperStar Λ.X g).map f)
      ((componentLiftSectionPullback Λ g L) s) =
    (componentLiftSectionPullback Λ g L') ((condensedModuleSections Λ.X U).map f s)

```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ComponentLiftLisseSectionComparison | M4 | Same signature and all original public imports reexported through the data module; imports the three new obligations. |

The repository has no direct Lean importer of the item, checked by an anchored import
search over both roots. Its DAG parents remain unchanged: the item's theorem and its
public auxiliary API are preserved. The new obligations import the factored definitions.
The parent node retains its theorem attachment; the new definition node owns the moved
declarations. No existing module outside the item is edited, and no consumer adaptation
is required.

## Status

landed 20261026T082500-L-2181902 2026-10-26 (merge of deliver/M4/Sheaf.Paper.ComponentLiftLisseSectionComparison)
