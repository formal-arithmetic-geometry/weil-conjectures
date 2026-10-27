# Internal scalar pullback normalization comparison data

## Reason

The original file bundles eight definitions with the existence theorem. Reusing the
existing section transport and canonical coefficient tensor theorems from that existence
proof creates import cycles. Move the definitions verbatim into
`Sheaf.Paper.InternalScalarPullbackNormalizationData`, publicly imported by the original
module. This changes their file ownership only; all names, signatures, attributes and
bodies remain the same, as does the globally registered scalar-pair additive instance.
No target definition or target statement changes its meaning.

The shared library gained the completed `RestrictedCoefficientMateProjection` proof
while this packet waited for delivery capacity. The module is now unclaimed. Preserve
its entire current proof and private helpers. Move its two regular coefficient pullback
definitions verbatim into `RestrictedCoefficientPullbackData`, publicly re-exported
by the original module. Change the canonical tensor module's public import to this
definition-only module. The only direct consumer `CoefficientPushFilteredLegs` gets
an explicit private proof import of the mate module, replacing its previous transitive
access. This breaks the cycle without discarding any completed proof.
`SectionPullNormalizationTransport` remains unclaimed and imports the unchanged
internal scalar data module. Existing public imports of the item and mate module remain
available transitively; all public signatures, attributes and definition bodies remain
unchanged.

The canonical coefficient tensor node previously cited the restricted coefficient mate
**theorem** to name `regularPullback`. That theorem genuinely depends on this item's
normalization and cannot be a statement dependency here. The new definition node owns
only the two already constructed `regularPullback₀`/`regularPullback` definitions; the
canonical node now cites that definition node. This changes no mathematical assertion.
The section-pull transport node similarly uses the supplied `PullNormalized` hypothesis,
not existence from the theorem now proved from it; its obsolete proof dependency is removed.

## Old

In `Sheaf.Paper.InternalScalarPullbackNormalization`:

```lean
/-- Comparison of the specified internal scalar functor with an actual section-ring
left-derived pair. SectionScalarNormalized below requires the ordinary balanced-generator
identity and pins the derived comparison by its flat-term K-flat computation counits.
Source: Stacks 03EK, 06YY and 07A6; blueprint integral proper-base-change proof (1)
(blueprint: lem-sfb-internal-scalar-pullback-normalization). -/
structure SectionScalarComparison (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) where
  pair : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
    (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))
  restriction : V₀ a T ⋙ (ModuleRingedComparison.equivalence Λ T).functor ≅
    (ModuleRingedComparison.equivalence Λ' T).functor ⋙
      SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))
  ordinary : extension a T ⋙ (ModuleRingedComparison.equivalence Λ' T).functor ≅
    (ModuleRingedComparison.equivalence Λ T).functor ⋙ pair.extension
  derived : D a T ⋙ (ModuleRingedComparison.derivedEquivalence Λ' T).functor ≅
    (ModuleRingedComparison.derivedEquivalence Λ T).functor ⋙ pair.derived

/-- The ordinary generator and K-flat counit equations for the specified D comparison.
These are properties of the same scalar data used below in both conjugation equations.
Source: Stacks 03EK, 06YY and 07A6; blueprint integral proper-base-change proof (1)
(blueprint: lem-sfb-internal-scalar-pullback-normalization). -/
def SectionScalarNormalized (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) : Prop :=
  (∀ (N : Modules Λ' T) (U : T.ProEtᵒᵖ) (x : N.X.obj.obj U),
    (s.restriction.hom.app N).val.app U x = x) ∧
  (∀ (M : Modules Λ T) (U : T.ProEtᵒᵖ)
    (z : (condensedRingObj Λ' T).obj.obj U) (x : M.X.obj.obj U),
    (eqToHom (s.pair.extension_obj
      ((ModuleRingedComparison.equivalence Λ T).functor.obj M))).val.app U
        ((s.ordinary.hom.app M).val.app U
          (internalScalarGenerator (Scheme.ProEt.topology T) (coefficientMap a T) M U z x)) =
      (toSheafify (Scheme.ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))
          ((ModuleRingedComparison.equivalence Λ T).functor.obj M)).presheaf).app U
            (z ⊗ₜ[(ModuleRingedComparison.ring Λ T).obj.obj U,
              ((sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
                (coefficientMap a T)).hom.app U).hom] x)) ∧
  ∀ (P : CochainComplex (Modules Λ T) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := ModuleRingedComparison.ring Λ T)
      (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := ModuleRingedComparison.ring Λ T)
      (((ModuleRingedComparison.equivalence Λ T).functor).obj (P.X n))) →
    (ModuleRingedComparison.derivedEquivalence Λ' T).functor.map (compute a T P) ≫
        (ModuleRingedComparison.sectionLocalizationComparison Λ' T
          (((extension a T).mapHomologicalComplex (.up ℤ)).obj P)).hom ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex s.ordinary (.up ℤ)).hom.app P) =
      s.derived.hom.app (DerivedCategory.Q.obj P) ≫
        s.pair.derived.map (ModuleRingedComparison.sectionLocalizationComparison Λ T P).hom ≫
        SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
          s.pair.extension s.pair.extension_additive
          s.pair.derived s.pair.counit
          (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P)

/-- Localization of the section restriction comparison, using the fixed exact functors.
Source: Stacks 07A6; blueprint integral proper-base-change proof (1)
(blueprint: lem-sfb-internal-scalar-pullback-normalization). -/
def sectionScalarRestriction (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) :
    V a T ⋙ (ModuleRingedComparison.derivedEquivalence Λ T).functor ≅
      (ModuleRingedComparison.derivedEquivalence Λ' T).functor ⋙
        SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)) :=
  (Functor.mapDerivedCategoryCompIso (V₀ a T)
    (ModuleRingedComparison.equivalence Λ T).functor).symm ≪≫
  Functor.mapDerivedCategoryNatIso s.restriction ≪≫
  Functor.mapDerivedCategoryCompIso (ModuleRingedComparison.equivalence Λ' T).functor
    (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)))

/-- Tensor with the restricted regular coefficient in the existing section derived tensor.
Source: Stacks 06YU; blueprint integral proper-base-change proof (1)
(blueprint: lem-sfb-internal-scalar-pullback-normalization). -/
def sectionScalarTensor (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    DerivedCategory (ModuleRingedComparison.modules Λ T) ⥤
      DerivedCategory (ModuleRingedComparison.modules Λ T) :=
  (𝟭 _).prod' ((Functor.const _).obj
    ((ModuleRingedComparison.derivedEquivalence Λ T).functor.obj (B a T))) ⋙
      ModuleRingedComparison.tensor Λ T

/-- The exact section equivalence carries the actual coefficient in degree zero to
its section module in degree zero, with the canonical localization and single factors.
Source: Stacks 06YU; blueprint integral proper-base-change proof (1)
(blueprint: lem-sfb-internal-scalar-pullback-normalization). -/
def sectionScalarCoefficient (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    (ModuleRingedComparison.derivedEquivalence Λ T).functor.obj (B a T) ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
        ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T))) :=
  ModuleRingedComparison.sectionLocalizationComparison Λ T
      ((CochainComplex.singleFunctor _ 0).obj (B₀ a T)) ≪≫
    DerivedCategory.Q.mapIso
      (((ModuleRingedComparison.equivalence Λ T).functor.mapCochainComplexSingleFunctor 0).app
        (B₀ a T))

/-- The chosen internal tensor identification, conjugated to sections, is the section
K-flat balanced construction. Its ordinary map sends s tensor x to x tensor s on every
local generator; its derived map has that ordinary map as its K-flat computation.
Source: Stacks 03EK and 06YY; blueprint integral proper-base-change proof (1)
(blueprint: lem-sfb-internal-scalar-pullback-normalization). -/
def SectionTensorNormalized (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) (t : TensorNormalization a T) : Prop :=
  ∃ o : s.pair.extension ⋙ SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)) ≅
        tensorRight ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)),
  (∀ (M : ModuleRingedComparison.modules Λ T) (U : T.ProEtᵒᵖ)
      (z : (ModuleRingedComparison.ring Λ' T).obj.obj U) (x : M.val.obj U),
    (o.hom.app M).val.app U
      ((eqToHom (s.pair.extension_obj M).symm).val.app U
        ((toSheafify (Scheme.ProEt.topology T)
          (SheafOfModules.changeOfRingsPresheaf
            (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
              (coefficientMap a T)) M).presheaf).app U
              (z ⊗ₜ[(ModuleRingedComparison.ring Λ T).obj.obj U,
                ((sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
                  (coefficientMap a T)).hom.app U).hom] x))) =
      ModuleRingedComparison.sectionPureTensor Λ T M
        ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)) U x z) ∧
  ∃ e : s.pair.derived ⋙ SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)) ≅
        sectionScalarTensor a T,
  (∀ (P : CochainComplex (ModuleRingedComparison.modules Λ T) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := ModuleRingedComparison.ring Λ T) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := ModuleRingedComparison.ring Λ T) (P.X n)) →
    e.hom.app (DerivedCategory.Q.obj P) ≫
        (ModuleRingedComparison.tensor Λ T).map
          (Prod.mkHom (𝟙 _) (sectionScalarCoefficient a T).hom) ≫
        (ModuleRingedComparison.qTensor Λ T).app
          (P, (CochainComplex.singleFunctor _ 0).obj
            ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T))) ≫
        DerivedCategory.Q.map (CochainComplex.mapBifunctorSingle₂Iso
          (curriedTensor (ModuleRingedComparison.modules Λ T))
          ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)) P).hom =
      (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))).map
          (SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
          s.pair.extension s.pair.extension_additive
            s.pair.derived s.pair.counit P) ≫
        (SheafOfModules.scalarRestrictionComparison.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
            (coefficientMap a T))).hom.app
            ((SheafOfModules.scalarComplex.{u + 1, u, u + 1}
              s.pair.extension s.pair.extension_additive).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso o (.up ℤ)).hom.app P)) ∧
  ∀ M : DerivedCategory (Modules Λ T),
    (ModuleRingedComparison.derivedEquivalence Λ T).functor.map (t.derived.hom.app M) ≫
        (ModuleRingedComparison.tensorComparison Λ T).hom.app (M, B a T) =
      (sectionScalarRestriction a T s).hom.app ((D a T).obj M) ≫
        (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))).map
            (s.derived.hom.app M) ≫
        e.hom.app ((ModuleRingedComparison.derivedEquivalence Λ T).functor.obj M)

/-- The fixed geometric section comparison with the scalar interface's name L.
This only unfolds that name for the actual total derived pullback; its components
are the existing derivedPullComparison, with no new comparison choice.
Source: Stacks 07A6; blueprint integral proper-base-change proof (1)
(blueprint: lem-sfb-internal-scalar-pullback-normalization). -/
def scalarSectionPullComparison
    (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ₀ T)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L Λ₀ f ⋙ (ModuleRingedComparison.derivedEquivalence Λ₀ X).functor ≅
      (ModuleRingedComparison.derivedEquivalence Λ₀ Y).functor ⋙
        ModuleRingedComparison.derivedPullback Λ₀ f := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact ModuleRingedComparison.derivedPullComparison Λ₀ f

/-- The chosen scalar/pullback map is the section-ring K-flat balanced map after the
fixed scalar and geometric comparisons. The ordinary comparison is specified as the
conjugate of the identity restriction/direct-image square. Since the scalar units insert
1 and the geometric adjunction is the specified ringed adjunction, this is exactly
f inverse (x tensor s) mapping to f inverse x tensor f inverse s, using alpha_f.
Source: Stacks 03D7, 0B65, 0D6D and 0G7E; blueprint integral proper-base-change proof (1)
(blueprint: lem-sfb-internal-scalar-pullback-normalization). -/
def SectionPullNormalized (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sX : SectionScalarComparison a X) (sY : SectionScalarComparison a Y)
    (b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) : Prop :=
  ∃ r : ModuleRingedComparison.pushforward Λ' f ⋙ SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology Y) (coefficientMap a Y)) ≅
        SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X) (coefficientMap a X)) ⋙
            ModuleRingedComparison.pushforward Λ f,
  (∀ (N : ModuleRingedComparison.modules Λ' X) (U : Y.ProEtᵒᵖ)
      (x : ((ModuleRingedComparison.pushforward Λ' f).obj N).val.obj U),
    (r.hom.app N).val.app U x = x) ∧
  ∃ c : sY.pair.extension ⋙ ModuleRingedComparison.pullback Λ' f ≅
    ModuleRingedComparison.pullback Λ f ⋙ sX.pair.extension,
  (conjugateEquiv (sY.pair.ordinaryAdjunction.comp (ModuleRingedComparison.adjunction Λ' f))
    ((ModuleRingedComparison.adjunction Λ f).comp sX.pair.ordinaryAdjunction) c.inv = r.hom) ∧
  ∃ d : sY.pair.derived ⋙ ModuleRingedComparison.derivedPullback Λ' f ≅
    ModuleRingedComparison.derivedPullback Λ f ⋙ sX.pair.derived,
  (∀ (P : CochainComplex (ModuleRingedComparison.modules Λ Y) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := ModuleRingedComparison.ring Λ Y) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := ModuleRingedComparison.ring Λ Y) (P.X n)) →
    d.hom.app (DerivedCategory.Q.obj P) ≫
        sX.pair.derived.map
          ((ModuleRingedComparison.pullback Λ f).mapDerivedCategoryFactors.hom.app P) ≫
        SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
          sX.pair.extension sX.pair.extension_additive
          sX.pair.derived sX.pair.counit
          (((ModuleRingedComparison.pullback Λ f).mapHomologicalComplex (.up ℤ)).obj P) =
      (ModuleRingedComparison.derivedPullback Λ' f).map
        (SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
          sY.pair.extension sY.pair.extension_additive
          sY.pair.derived sY.pair.counit P) ≫
        (ModuleRingedComparison.pullback Λ' f).mapDerivedCategoryFactors.hom.app
          ((SheafOfModules.scalarComplex.{u + 1, u, u + 1}
              sY.pair.extension sY.pair.extension_additive).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso c (.up ℤ)).hom.app P)) ∧
  ∀ M : DerivedCategory (Modules Λ Y),
    (ModuleRingedComparison.derivedEquivalence Λ' X).functor.map (b.hom.app M) ≫
        sX.derived.hom.app ((L Λ f).obj M) ≫
        sX.pair.derived.map ((scalarSectionPullComparison Λ f).hom.app M) =
      (scalarSectionPullComparison Λ' f).hom.app ((D a Y).obj M) ≫
        (ModuleRingedComparison.derivedPullback Λ' f).map (sY.derived.hom.app M) ≫
        d.hom.app ((ModuleRingedComparison.derivedEquivalence Λ Y).functor.obj M)
```

Additionally, in `Sheaf.Paper.RestrictedCoefficientMateProjection`:

```lean
/-- The ordinary restricted-regular pullback identification: restrict the regular
S-module after pullback and apply the specified monoidal unit comparison.
Source: blueprint rational proper-base-change proof (1), cartesian coefficients;
Stacks 07A4 (blueprint: lem-sfb-restricted-coefficient-mate-projection). -/
def regularPullback₀ (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar R f).obj (B₀ a Y) ≅ B₀ a X :=
  (CondensedRing.comapUpperStarIso a f).symm.app _ ≪≫
    (V₀ a X).mapIso (Functor.Monoidal.εIso (CondensedRing.upperStar S f)).symm

/-- The canonical rho, using exact inverse image, its localization comparison and
its degree-zero comparison, followed by the ordinary cartesian identification.
Source: blueprint rational proper-base-change proof (1); Stacks 07A4 and 07A6
(blueprint: lem-sfb-restricted-coefficient-mate-projection). -/
def regularPullback (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (L R f).obj (B a Y) ≅ B a X := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f).app (B a Y) ≪≫
    (CondensedRing.upperStar R f).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor _ 0).obj (B₀ a Y)) ≪≫
    DerivedCategory.Q.mapIso
      (((CondensedRing.upperStar R f).mapCochainComplexSingleFunctor 0).app (B₀ a Y) ≪≫
        (CochainComplex.singleFunctor _ 0).mapIso (regularPullback₀ a f))
```

## New

The same declarations, verbatim, in
`Sheaf.Paper.InternalScalarPullbackNormalizationData`, publicly re-exported by
`Sheaf.Paper.InternalScalarPullbackNormalization`:

```lean
/-- Comparison of the specified internal scalar functor with an actual section-ring
left-derived pair. SectionScalarNormalized below requires the ordinary balanced-generator
identity and pins the derived comparison by its flat-term K-flat computation counits.
Source: Stacks 03EK, 06YY and 07A6; blueprint integral proper-base-change proof (1)
(blueprint: lem-sfb-internal-scalar-pullback-normalization). -/
structure SectionScalarComparison (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) where
  pair : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
    (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))
  restriction : V₀ a T ⋙ (ModuleRingedComparison.equivalence Λ T).functor ≅
    (ModuleRingedComparison.equivalence Λ' T).functor ⋙
      SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))
  ordinary : extension a T ⋙ (ModuleRingedComparison.equivalence Λ' T).functor ≅
    (ModuleRingedComparison.equivalence Λ T).functor ⋙ pair.extension
  derived : D a T ⋙ (ModuleRingedComparison.derivedEquivalence Λ' T).functor ≅
    (ModuleRingedComparison.derivedEquivalence Λ T).functor ⋙ pair.derived

/-- The ordinary generator and K-flat counit equations for the specified D comparison.
These are properties of the same scalar data used below in both conjugation equations.
Source: Stacks 03EK, 06YY and 07A6; blueprint integral proper-base-change proof (1)
(blueprint: lem-sfb-internal-scalar-pullback-normalization). -/
def SectionScalarNormalized (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) : Prop :=
  (∀ (N : Modules Λ' T) (U : T.ProEtᵒᵖ) (x : N.X.obj.obj U),
    (s.restriction.hom.app N).val.app U x = x) ∧
  (∀ (M : Modules Λ T) (U : T.ProEtᵒᵖ)
    (z : (condensedRingObj Λ' T).obj.obj U) (x : M.X.obj.obj U),
    (eqToHom (s.pair.extension_obj
      ((ModuleRingedComparison.equivalence Λ T).functor.obj M))).val.app U
        ((s.ordinary.hom.app M).val.app U
          (internalScalarGenerator (Scheme.ProEt.topology T) (coefficientMap a T) M U z x)) =
      (toSheafify (Scheme.ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))
          ((ModuleRingedComparison.equivalence Λ T).functor.obj M)).presheaf).app U
            (z ⊗ₜ[(ModuleRingedComparison.ring Λ T).obj.obj U,
              ((sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
                (coefficientMap a T)).hom.app U).hom] x)) ∧
  ∀ (P : CochainComplex (Modules Λ T) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := ModuleRingedComparison.ring Λ T)
      (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := ModuleRingedComparison.ring Λ T)
      (((ModuleRingedComparison.equivalence Λ T).functor).obj (P.X n))) →
    (ModuleRingedComparison.derivedEquivalence Λ' T).functor.map (compute a T P) ≫
        (ModuleRingedComparison.sectionLocalizationComparison Λ' T
          (((extension a T).mapHomologicalComplex (.up ℤ)).obj P)).hom ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex s.ordinary (.up ℤ)).hom.app P) =
      s.derived.hom.app (DerivedCategory.Q.obj P) ≫
        s.pair.derived.map (ModuleRingedComparison.sectionLocalizationComparison Λ T P).hom ≫
        SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
          s.pair.extension s.pair.extension_additive
          s.pair.derived s.pair.counit
          (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P)

/-- Localization of the section restriction comparison, using the fixed exact functors.
Source: Stacks 07A6; blueprint integral proper-base-change proof (1)
(blueprint: lem-sfb-internal-scalar-pullback-normalization). -/
def sectionScalarRestriction (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) :
    V a T ⋙ (ModuleRingedComparison.derivedEquivalence Λ T).functor ≅
      (ModuleRingedComparison.derivedEquivalence Λ' T).functor ⋙
        SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)) :=
  (Functor.mapDerivedCategoryCompIso (V₀ a T)
    (ModuleRingedComparison.equivalence Λ T).functor).symm ≪≫
  Functor.mapDerivedCategoryNatIso s.restriction ≪≫
  Functor.mapDerivedCategoryCompIso (ModuleRingedComparison.equivalence Λ' T).functor
    (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)))

/-- Tensor with the restricted regular coefficient in the existing section derived tensor.
Source: Stacks 06YU; blueprint integral proper-base-change proof (1)
(blueprint: lem-sfb-internal-scalar-pullback-normalization). -/
def sectionScalarTensor (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    DerivedCategory (ModuleRingedComparison.modules Λ T) ⥤
      DerivedCategory (ModuleRingedComparison.modules Λ T) :=
  (𝟭 _).prod' ((Functor.const _).obj
    ((ModuleRingedComparison.derivedEquivalence Λ T).functor.obj (B a T))) ⋙
      ModuleRingedComparison.tensor Λ T

/-- The exact section equivalence carries the actual coefficient in degree zero to
its section module in degree zero, with the canonical localization and single factors.
Source: Stacks 06YU; blueprint integral proper-base-change proof (1)
(blueprint: lem-sfb-internal-scalar-pullback-normalization). -/
def sectionScalarCoefficient (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    (ModuleRingedComparison.derivedEquivalence Λ T).functor.obj (B a T) ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
        ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T))) :=
  ModuleRingedComparison.sectionLocalizationComparison Λ T
      ((CochainComplex.singleFunctor _ 0).obj (B₀ a T)) ≪≫
    DerivedCategory.Q.mapIso
      (((ModuleRingedComparison.equivalence Λ T).functor.mapCochainComplexSingleFunctor 0).app
        (B₀ a T))

/-- The chosen internal tensor identification, conjugated to sections, is the section
K-flat balanced construction. Its ordinary map sends s tensor x to x tensor s on every
local generator; its derived map has that ordinary map as its K-flat computation.
Source: Stacks 03EK and 06YY; blueprint integral proper-base-change proof (1)
(blueprint: lem-sfb-internal-scalar-pullback-normalization). -/
def SectionTensorNormalized (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) (t : TensorNormalization a T) : Prop :=
  ∃ o : s.pair.extension ⋙ SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)) ≅
        tensorRight ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)),
  (∀ (M : ModuleRingedComparison.modules Λ T) (U : T.ProEtᵒᵖ)
      (z : (ModuleRingedComparison.ring Λ' T).obj.obj U) (x : M.val.obj U),
    (o.hom.app M).val.app U
      ((eqToHom (s.pair.extension_obj M).symm).val.app U
        ((toSheafify (Scheme.ProEt.topology T)
          (SheafOfModules.changeOfRingsPresheaf
            (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
              (coefficientMap a T)) M).presheaf).app U
              (z ⊗ₜ[(ModuleRingedComparison.ring Λ T).obj.obj U,
                ((sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
                  (coefficientMap a T)).hom.app U).hom] x))) =
      ModuleRingedComparison.sectionPureTensor Λ T M
        ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)) U x z) ∧
  ∃ e : s.pair.derived ⋙ SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)) ≅
        sectionScalarTensor a T,
  (∀ (P : CochainComplex (ModuleRingedComparison.modules Λ T) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := ModuleRingedComparison.ring Λ T) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := ModuleRingedComparison.ring Λ T) (P.X n)) →
    e.hom.app (DerivedCategory.Q.obj P) ≫
        (ModuleRingedComparison.tensor Λ T).map
          (Prod.mkHom (𝟙 _) (sectionScalarCoefficient a T).hom) ≫
        (ModuleRingedComparison.qTensor Λ T).app
          (P, (CochainComplex.singleFunctor _ 0).obj
            ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T))) ≫
        DerivedCategory.Q.map (CochainComplex.mapBifunctorSingle₂Iso
          (curriedTensor (ModuleRingedComparison.modules Λ T))
          ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)) P).hom =
      (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))).map
          (SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
          s.pair.extension s.pair.extension_additive
            s.pair.derived s.pair.counit P) ≫
        (SheafOfModules.scalarRestrictionComparison.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
            (coefficientMap a T))).hom.app
            ((SheafOfModules.scalarComplex.{u + 1, u, u + 1}
              s.pair.extension s.pair.extension_additive).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso o (.up ℤ)).hom.app P)) ∧
  ∀ M : DerivedCategory (Modules Λ T),
    (ModuleRingedComparison.derivedEquivalence Λ T).functor.map (t.derived.hom.app M) ≫
        (ModuleRingedComparison.tensorComparison Λ T).hom.app (M, B a T) =
      (sectionScalarRestriction a T s).hom.app ((D a T).obj M) ≫
        (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))).map
            (s.derived.hom.app M) ≫
        e.hom.app ((ModuleRingedComparison.derivedEquivalence Λ T).functor.obj M)

/-- The fixed geometric section comparison with the scalar interface's name L.
This only unfolds that name for the actual total derived pullback; its components
are the existing derivedPullComparison, with no new comparison choice.
Source: Stacks 07A6; blueprint integral proper-base-change proof (1)
(blueprint: lem-sfb-internal-scalar-pullback-normalization). -/
def scalarSectionPullComparison
    (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ₀ T)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L Λ₀ f ⋙ (ModuleRingedComparison.derivedEquivalence Λ₀ X).functor ≅
      (ModuleRingedComparison.derivedEquivalence Λ₀ Y).functor ⋙
        ModuleRingedComparison.derivedPullback Λ₀ f := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact ModuleRingedComparison.derivedPullComparison Λ₀ f

/-- The chosen scalar/pullback map is the section-ring K-flat balanced map after the
fixed scalar and geometric comparisons. The ordinary comparison is specified as the
conjugate of the identity restriction/direct-image square. Since the scalar units insert
1 and the geometric adjunction is the specified ringed adjunction, this is exactly
f inverse (x tensor s) mapping to f inverse x tensor f inverse s, using alpha_f.
Source: Stacks 03D7, 0B65, 0D6D and 0G7E; blueprint integral proper-base-change proof (1)
(blueprint: lem-sfb-internal-scalar-pullback-normalization). -/
def SectionPullNormalized (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sX : SectionScalarComparison a X) (sY : SectionScalarComparison a Y)
    (b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) : Prop :=
  ∃ r : ModuleRingedComparison.pushforward Λ' f ⋙ SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology Y) (coefficientMap a Y)) ≅
        SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X) (coefficientMap a X)) ⋙
            ModuleRingedComparison.pushforward Λ f,
  (∀ (N : ModuleRingedComparison.modules Λ' X) (U : Y.ProEtᵒᵖ)
      (x : ((ModuleRingedComparison.pushforward Λ' f).obj N).val.obj U),
    (r.hom.app N).val.app U x = x) ∧
  ∃ c : sY.pair.extension ⋙ ModuleRingedComparison.pullback Λ' f ≅
    ModuleRingedComparison.pullback Λ f ⋙ sX.pair.extension,
  (conjugateEquiv (sY.pair.ordinaryAdjunction.comp (ModuleRingedComparison.adjunction Λ' f))
    ((ModuleRingedComparison.adjunction Λ f).comp sX.pair.ordinaryAdjunction) c.inv = r.hom) ∧
  ∃ d : sY.pair.derived ⋙ ModuleRingedComparison.derivedPullback Λ' f ≅
    ModuleRingedComparison.derivedPullback Λ f ⋙ sX.pair.derived,
  (∀ (P : CochainComplex (ModuleRingedComparison.modules Λ Y) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := ModuleRingedComparison.ring Λ Y) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := ModuleRingedComparison.ring Λ Y) (P.X n)) →
    d.hom.app (DerivedCategory.Q.obj P) ≫
        sX.pair.derived.map
          ((ModuleRingedComparison.pullback Λ f).mapDerivedCategoryFactors.hom.app P) ≫
        SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
          sX.pair.extension sX.pair.extension_additive
          sX.pair.derived sX.pair.counit
          (((ModuleRingedComparison.pullback Λ f).mapHomologicalComplex (.up ℤ)).obj P) =
      (ModuleRingedComparison.derivedPullback Λ' f).map
        (SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
          sY.pair.extension sY.pair.extension_additive
          sY.pair.derived sY.pair.counit P) ≫
        (ModuleRingedComparison.pullback Λ' f).mapDerivedCategoryFactors.hom.app
          ((SheafOfModules.scalarComplex.{u + 1, u, u + 1}
              sY.pair.extension sY.pair.extension_additive).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso c (.up ℤ)).hom.app P)) ∧
  ∀ M : DerivedCategory (Modules Λ Y),
    (ModuleRingedComparison.derivedEquivalence Λ' X).functor.map (b.hom.app M) ≫
        sX.derived.hom.app ((L Λ f).obj M) ≫
        sX.pair.derived.map ((scalarSectionPullComparison Λ f).hom.app M) =
      (scalarSectionPullComparison Λ' f).hom.app ((D a Y).obj M) ≫
        (ModuleRingedComparison.derivedPullback Λ' f).map (sY.derived.hom.app M) ≫
        d.hom.app ((ModuleRingedComparison.derivedEquivalence Λ Y).functor.obj M)
```

Additionally, the identical definitions in
`Sheaf.Paper.RestrictedCoefficientPullbackData`, re-exported publicly by the original:

```lean
/-- The ordinary restricted-regular pullback identification: restrict the regular
S-module after pullback and apply the specified monoidal unit comparison.
Source: blueprint rational proper-base-change proof (1), cartesian coefficients;
Stacks 07A4 (blueprint: lem-sfb-restricted-coefficient-mate-projection). -/
def regularPullback₀ (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar R f).obj (B₀ a Y) ≅ B₀ a X :=
  (CondensedRing.comapUpperStarIso a f).symm.app _ ≪≫
    (V₀ a X).mapIso (Functor.Monoidal.εIso (CondensedRing.upperStar S f)).symm

/-- The canonical rho, using exact inverse image, its localization comparison and
its degree-zero comparison, followed by the ordinary cartesian identification.
Source: blueprint rational proper-base-change proof (1); Stacks 07A4 and 07A6
(blueprint: lem-sfb-restricted-coefficient-mate-projection). -/
def regularPullback (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (L R f).obj (B a Y) ≅ B a X := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f).app (B a Y) ≪≫
    (CondensedRing.upperStar R f).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor _ 0).obj (B₀ a Y)) ≪≫
    DerivedCategory.Q.mapIso
      (((CondensedRing.upperStar R f).mapCochainComplexSingleFunctor 0).app (B₀ a Y) ≪≫
        (CochainComplex.singleFunctor _ 0).mapIso (regularPullback₀ a f))
```

## Users

`tools/downstream.py Sheaf.Paper.InternalScalarPullbackNormalization --uses
SectionScalarComparison` and the corresponding queries for `SectionScalarNormalized`,
`sectionScalarRestriction`, `sectionScalarTensor`, `sectionScalarCoefficient`,
`SectionTensorNormalized`, `scalarSectionPullComparison`, and `SectionPullNormalized` report
these 22 downstream modules. For the additional regular pullback data,
`tools/downstream.py Sheaf.Paper.RestrictedCoefficientMateProjection --uses regularPullback`
lists the canonical tensor module and the mate module itself; `--uses regularPullback₀`
lists the mate module itself. Both are covered in the table. All moved definitions have
unchanged
public re-export; consumers therefore see the identical declarations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FieldScalarProjectionMateCoherence | unclaimed | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.CanonicalCoefficientTensorNormalization | unclaimed | Public import changes to the independent regular pullback data module; declarations unchanged. |
| Sheaf.Paper.CoefficientPushFilteredLegs | unclaimed | Add a private proof import of RestrictedCoefficientMateProjection, formerly visible through the canonical module; declarations unchanged. |
| Sheaf.Paper.CountableNormProjectionCriterion | unclaimed | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.FiniteStageSupportedGeneration | unclaimed | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.FlatCoefficientSquareNormalization | unclaimed | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.FlatScalarGeometricCoherence | unclaimed | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.FlatScalarUnitNormalization | unclaimed | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | unclaimed | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | D7 | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | K9 | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.IntegralQuotientSectionMateRealization | S5 | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.InternalScalarMateProjection | J3 | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.InternalScalarMateTransitivity | J4 | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.KummerStratumScalarMateDetection | unclaimed | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.NormalizedScalarRestrictionPush | unclaimed | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.NormalizedScalarSectionFamily | unclaimed | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.QuotientPullbackTensorCoherence | W7 | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.QuotientSectionTensorNormalization | W8 | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.RestrictedCoefficientMateProjection | unclaimed | Re-export the two unchanged regular pullback definitions from the new data module; current completed proof preserved verbatim. |
| Sheaf.Paper.ScalarGeometricExchangeRectangle | unclaimed | Unchanged signatures and bodies; the item publicly re-exports all eight definitions. |
| Sheaf.Paper.SectionPullNormalizationTransport | unclaimed | Import the unchanged data module so the parent theorem can use this transport result. |

## Status

landed 20261025T033928-L-171853 2026-10-25 (merge of deliver/K5/Sheaf.Paper.InternalScalarPullbackNormalization)
