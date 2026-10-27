# SheafOfModules.RingedTensor.FiniteFreeCoordinatesInverseImage

## Reason

The original predicate nests thirteen proof-class witnesses and eight isomorphism
witnesses before a large conjunction containing three further derived isomorphisms.
Its fully proved constructor repeatedly exceeded the 60-second per-file limit.
Group the thirteen independent proof-class witnesses in a proposition-valued record,
and the eight independent ordinary isomorphisms in the generic data record
`OrdinaryComparisonTuple`, specialized by `FiniteFreeCoordinatePullbackData`. State their equations
separately, and factor the derived comparison equations through a generic predicate on
abelian categories. This shares the categorical expressions and avoids repeating their
elaboration. No proof was split into another module and no compiler limit was increased.

The predicate is logically equivalent to the previous one. In the forward direction,
pack the original thirteen witnesses into `FiniteFreeCoordinatePullbackExactness` and
the original eight isomorphisms into `FiniteFreeCoordinatePullbackData`, retaining each
conjunct. In the reverse direction, project those same thirteen fields and eight maps
and retain each conjunct. The proof-class fields are propositions, so the differing
instance witnesses agree by proof irrelevance. `FiniteFreeCoordinatePullbackLaws`
contains the original ordinary equations verbatim with record projections replacing
bound variables. `DerivedCoordinateCompatibility` is the original final derived
existential and its five equations, generalized to four abelian categories; its
`Normalized` argument is instantiated with precisely the original
`IsDerivedFiniteFreeScalarCoordinateIso` predicate. No equation, quantifier, hypothesis,
or normalization has been omitted or relaxed. The theorem's existing signature and
the other four original public definitions are unchanged.

No target statement changes. Definition-sensitive statement review is reopened for
targets depending on this predicate, to check the equivalent repackaging. Rank zero,
identity inverse image, arbitrary small sites and unbounded complexes are included
with exactly the previous quantifiers.

## Old

```lean
def FiniteFreeCoordinatesInverseImage
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S)))
    (φ : tensorFunctor a ⋙ restriction.{u, u} a ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf S))]
    [PreservesFiniteLimits (tensorFunctor a)] [PreservesFiniteColimits (tensorFunctor a)]
    [PreservesFiniteLimits (restriction.{u, u} a)]
    [PreservesFiniteColimits (restriction.{u, u} a)]
    [(Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _)).Additive]
    [PreservesFiniteLimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _))]
    [PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _))]
    (E : DerivedCategory (SheafOfModules.{u} (ringSheaf R)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringSheaf S)))
    (ε : DerivedCategory.Q ⋙ E ⟶
      (tensorFunctor a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (Φ : E ⋙ (restriction.{u, u} a).mapDerivedCategory ≅
      Functor.const (Discrete (Fin d)) ⋙ lim) : Prop :=
  ∀ {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
    (g : GeometricMorphism (Sheaf J' (Type u)) (Sheaf J (Type u)))
    (R' S' : Sheaf J' CommRingCat.{u})
    (IR : AlgebraicInverseImage g.inverse R R')
    (IS : AlgebraicInverseImage g.inverse S S')
    (a' : R' ⟶ S')
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf R'))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf S'))],
    g.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat)).map a) ≫
      IS.ringUnderlying.hom = IR.ringUnderlying.hom ≫
        (sheafCompose J' (CategoryTheory.forget CommRingCat)).map a' →
    ∃ (_ : IR.modules.Additive)
      (_ : PreservesFiniteLimits IR.modules) (_ : PreservesFiniteColimits IR.modules)
      (_ : IS.modules.Additive)
      (_ : PreservesFiniteLimits IS.modules) (_ : PreservesFiniteColimits IS.modules)
      (_ : PreservesFiniteLimits (tensorFunctor a'))
      (_ : PreservesFiniteColimits (tensorFunctor a'))
      (_ : PreservesFiniteLimits (restriction.{u, u} a'))
      (_ : PreservesFiniteColimits (restriction.{u, u} a'))
      (_ : (Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _)).Additive)
      (_ : PreservesFiniteLimits (Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _)))
      (_ : PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _)))
      (χ : tensorFunctor a ⋙ IS.modules ≅ IR.modules ⋙ tensorFunctor a')
      (ρ : restriction.{u, u} a ⋙ IR.modules ≅ IS.modules ⋙ restriction.{u, u} a')
      (σ : (Functor.const (Discrete (Fin d)) ⋙ lim) ⋙ IR.modules ≅
        IR.modules ⋙ (Functor.const (Discrete (Fin d)) ⋙ lim))
      (κ : IR.modules.obj (unit (ringSheaf R)) ≅ unit (ringSheaf R'))
      (κS : IS.modules.obj (unit (ringSheaf S)) ≅ unit (ringSheaf S'))
      (τ : IR.modules.obj (∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R))) ≅
        ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R')))
      (θ' : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R')) ≅
        (restriction.{u, u} a').obj (unit (ringSheaf S')))
      (φ' : tensorFunctor a' ⋙ restriction.{u, u} a' ≅
        Functor.const (Discrete (Fin d)) ⋙ lim),
      IsScalarInverseImageComparison g.inverse IR IS a a' χ ∧
      (underlying R').map κ.hom =
        IR.moduleUnderlying.hom.app (unit (ringSheaf R)) ≫ IR.ringUnderlying.hom ∧
      (underlying S').map κS.hom =
        IS.moduleUnderlying.hom.app (unit (ringSheaf S)) ≫ IS.ringUnderlying.hom ∧
      (∀ i : Fin d, τ.hom ≫ Pi.π (fun _ : Fin d ↦ unit (ringSheaf R')) i =
        IR.modules.map (Pi.π (fun _ : Fin d ↦ unit (ringSheaf R)) i) ≫ κ.hom) ∧
      (τ.hom ≫ θ'.hom = IR.modules.map θ.hom ≫
        ρ.hom.app (unit (ringSheaf S)) ≫ (restriction.{u, u} a').map κS.hom) ∧
      IsFiniteFreeScalarCoordinateIso a' d θ' φ' ∧
      (∀ N : SheafOfModules.{u} (ringSheaf S),
        (underlying R').map (ρ.hom.app N) ≫
          IS.moduleUnderlying.hom.app N =
        IR.moduleUnderlying.hom.app ((restriction.{u, u} a).obj N)) ∧
      (∀ (M : SheafOfModules.{u} (ringSheaf R)) (i : Fin d),
        σ.hom.app M ≫ Pi.π (fun _ : Fin d ↦ IR.modules.obj M) i =
          IR.modules.map (Pi.π (fun _ : Fin d ↦ M) i)) ∧
      (∀ M : SheafOfModules.{u} (ringSheaf R),
        IR.modules.map (φ.hom.app M) ≫ σ.hom.app M =
          ρ.hom.app ((tensorFunctor a).obj M) ≫
            (restriction.{u, u} a').map (χ.hom.app M) ≫ φ'.hom.app (IR.modules.obj M)) ∧
      ∀ (E' : DerivedCategory (SheafOfModules.{u} (ringSheaf R')) ⥤
          DerivedCategory (SheafOfModules.{u} (ringSheaf S')))
        (ε' : DerivedCategory.Q ⋙ E' ⟶
          (tensorFunctor a').mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        [E'.IsLeftDerivedFunctor ε'
          (HomologicalComplex.quasiIso (SheafOfModules.{u} (ringSheaf R')) (.up ℤ))],
        ∃ (Φ' : E' ⋙ (restriction.{u, u} a').mapDerivedCategory ≅
            Functor.const (Discrete (Fin d)) ⋙ lim)
          (β : E ⋙ IS.modules.mapDerivedCategory ≅ IR.modules.mapDerivedCategory ⋙ E')
          (σD : (Functor.const (Discrete (Fin d)) ⋙ lim) ⋙ IR.modules.mapDerivedCategory ≅
            IR.modules.mapDerivedCategory ⋙ (Functor.const (Discrete (Fin d)) ⋙ lim)),
          (∀ K : CochainComplex (SheafOfModules.{u} (ringSheaf R')) ℤ,
            IsIso (ε'.app K)) ∧
          IsDerivedFiniteFreeScalarCoordinateIso a' d E' ε' φ' Φ' ∧
          (∀ (K : DerivedCategory (SheafOfModules.{u} (ringSheaf R))) (i : Fin d),
            σD.hom.app K ≫ Pi.π (fun _ : Fin d ↦ IR.modules.mapDerivedCategory.obj K) i =
              IR.modules.mapDerivedCategory.map (Pi.π (fun _ : Fin d ↦ K) i)) ∧
          (∀ K : CochainComplex (SheafOfModules.{u} (ringSheaf R)) ℤ,
            β.hom.app (DerivedCategory.Q.obj K) ≫
                E'.map (IR.modules.mapDerivedCategoryFactors.hom.app K) ≫
                ε'.app ((IR.modules.mapHomologicalComplex (.up ℤ)).obj K) =
              IS.modules.mapDerivedCategory.map (ε.app K) ≫
                IS.modules.mapDerivedCategoryFactors.hom.app
                  (((tensorFunctor a).mapHomologicalComplex (.up ℤ)).obj K) ≫
                DerivedCategory.Q.map
                  ((Functor.mapHomologicalComplexCompIso
                      (Iso.refl (tensorFunctor a ⋙ IS.modules)) (.up ℤ)).hom.app K ≫
                    (χ.hom.mapHomologicalComplex (.up ℤ)).app K ≫
                    (Functor.mapHomologicalComplexCompIso
                      (Iso.refl (IR.modules ⋙ tensorFunctor a')) (.up ℤ)).inv.app K)) ∧
          ∀ K : DerivedCategory (SheafOfModules.{u} (ringSheaf R)),
            IR.modules.mapDerivedCategory.map (Φ.hom.app K) ≫ σD.hom.app K =
              ((Functor.mapDerivedCategoryCompIso (restriction.{u, u} a) IR.modules).symm ≪≫
                Functor.mapDerivedCategoryNatIso ρ ≪≫
                Functor.mapDerivedCategoryCompIso IS.modules (restriction.{u, u} a')).hom.app
                  (E.obj K) ≫
                (restriction.{u, u} a').mapDerivedCategory.map (β.hom.app K) ≫
                Φ'.hom.app (IR.modules.mapDerivedCategory.obj K)
```

## New

```lean
structure OrdinaryComparisonTuple (A B C D E F G H : Type*) where
  chi : A
  rho : B
  sigma : C
  unitR : D
  unitS : E
  powerUnit : F
  basis : G
  coordinate : H

section DerivedCompatibilityDefinition
variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A']
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B']
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} A'] [HasDerivedCategory.{w} B']

/-- The three normalized derived comparisons associated to an ordinary coordinate square.
Source: Stacks 03EL, 06YY, 015F, localization of the ordinary square
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
def DerivedCoordinateCompatibility
    (T : A ⥤ B) [T.Additive] (U : B ⥤ A) [U.Additive] (d : ℕ)
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (F : A ⥤ A') (G : B ⥤ B') (T' : A' ⥤ B') [T'.Additive]
    (U' : B' ⥤ A') [U'.Additive]
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
    (E : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ E ⟶ T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (E' : DerivedCategory A' ⥤ DerivedCategory B')
    (ε' : DerivedCategory.Q ⋙ E' ⟶ T'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (χ : T ⋙ G ≅ F ⋙ T') (ρ : U ⋙ F ≅ G ⋙ U')
    (Φ : E ⋙ U.mapDerivedCategory ≅ Functor.const (Discrete (Fin d)) ⋙ lim)
    (Normalized : (E' ⋙ U'.mapDerivedCategory ≅
      Functor.const (Discrete (Fin d)) ⋙ lim) → Prop) : Prop :=
    ∃ (Φ' : E' ⋙ U'.mapDerivedCategory ≅
        Functor.const (Discrete (Fin d)) ⋙ lim)
      (β : E ⋙ G.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ E')
      (σD : (Functor.const (Discrete (Fin d)) ⋙ lim) ⋙ F.mapDerivedCategory ≅
        F.mapDerivedCategory ⋙ (Functor.const (Discrete (Fin d)) ⋙ lim)),
      (∀ K : CochainComplex A' ℤ,
        IsIso (ε'.app K)) ∧
      Normalized Φ' ∧
      (∀ (K : DerivedCategory A) (i : Fin d),
        σD.hom.app K ≫ Pi.π (fun _ : Fin d ↦ F.mapDerivedCategory.obj K) i =
          F.mapDerivedCategory.map (Pi.π (fun _ : Fin d ↦ K) i)) ∧
      (∀ K : CochainComplex A ℤ,
        β.hom.app (DerivedCategory.Q.obj K) ≫
            E'.map (F.mapDerivedCategoryFactors.hom.app K) ≫
            ε'.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
          G.mapDerivedCategory.map (ε.app K) ≫
            G.mapDerivedCategoryFactors.hom.app
              ((T.mapHomologicalComplex (.up ℤ)).obj K) ≫
            DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso
                  (Iso.refl (T ⋙ G)) (.up ℤ)).hom.app K ≫
                (χ.hom.mapHomologicalComplex (.up ℤ)).app K ≫
                (Functor.mapHomologicalComplexCompIso
                  (Iso.refl (F ⋙ T')) (.up ℤ)).inv.app K)) ∧
      ∀ K : DerivedCategory A,
        F.mapDerivedCategory.map (Φ.hom.app K) ≫ σD.hom.app K =
          ((Functor.mapDerivedCategoryCompIso U F).symm ≪≫
            Functor.mapDerivedCategoryNatIso ρ ≪≫
            Functor.mapDerivedCategoryCompIso G U').hom.app
              (E.obj K) ≫
            U'.mapDerivedCategory.map (β.hom.app K) ≫
            Φ'.hom.app (F.mapDerivedCategory.obj K)

end DerivedCompatibilityDefinition

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (d : ℕ)

attribute [local instance 50000]
  CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize

/-- The basis inclusion, with the finite product serving also as the finite direct sum.
Source: Stacks 03EL, finite-basis calculation
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
def scalarBasisInclusion
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S))) (i : Fin d) :
    unit (ringSheaf R) ⟶ (restriction.{u, u} a).obj (unit (ringSheaf S)) :=
  Pi.lift (fun j : Fin d ↦ if i = j then 𝟙 _ else 0) ≫ θ.hom

/-- The inverse basis coordinate. Source: Stacks 03EL, finite-basis calculation
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
def scalarBasisCoordinate
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S))) (i : Fin d) :
    (restriction.{u, u} a).obj (unit (ringSheaf S)) ⟶ unit (ringSheaf R) :=
  θ.inv ≫ Pi.π (fun _ : Fin d ↦ unit (ringSheaf R)) i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two local formulas, expressed using sheafification images of elementary tensors.
Source: Stacks 03EL and the blueprint finite-basis calculation
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
def IsFiniteFreeScalarCoordinateIso
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S)))
    (φ : tensorFunctor a ⋙ restriction.{u, u} a ≅
      Functor.const (Discrete (Fin d)) ⋙ lim) : Prop :=
  (∀ (M : SheafOfModules.{u} (ringSheaf R)) (U : Cᵒᵖ)
    (s : S.obj.obj U) (m : M.val.obj U) (i : Fin d),
    ((φ.hom.app M) ≫ Pi.π (fun _ : Fin d ↦ M) i).val.app U
      (scalarPure a M U s m) =
        (scalarBasisCoordinate a d θ i).val.app U s • m) ∧
  ∀ (M : SheafOfModules.{u} (ringSheaf R)) (U : Cᵒᵖ)
    (x : ((Functor.const (Discrete (Fin d)) ⋙ lim).obj M).val.obj U),
    (φ.inv.app M).val.app U x =
      ∑ i : Fin d, scalarPure a M U
        ((scalarBasisInclusion a d θ i).val.app U
          (@id ((unit (ringSheaf R)).val.obj U) (1 : R.obj.obj U)))
        ((Pi.π (fun _ : Fin d ↦ M) i).val.app U x)

/-- Counit-normalized coordinates on every unbounded cochain representative.
Source: Stacks 03EL and blueprint finite-basis calculation
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
def IsDerivedFiniteFreeScalarCoordinateIso
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf S))]
    [PreservesFiniteLimits (restriction.{u, u} a)]
    [PreservesFiniteColimits (restriction.{u, u} a)]
    (E : DerivedCategory (SheafOfModules.{u} (ringSheaf R)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringSheaf S)))
    (ε : DerivedCategory.Q ⋙ E ⟶
      (tensorFunctor a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (φ : tensorFunctor a ⋙ restriction.{u, u} a ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    (Φ : E ⋙ (restriction.{u, u} a).mapDerivedCategory ≅
      Functor.const (Discrete (Fin d)) ⋙ lim) : Prop :=
  ∀ (K : CochainComplex (SheafOfModules.{u} (ringSheaf R)) ℤ) (i : Fin d),
    Φ.hom.app (DerivedCategory.Q.obj K) ≫
      Pi.π (fun _ : Fin d ↦ DerivedCategory.Q.obj K) i =
    (restriction.{u, u} a).mapDerivedCategory.map (ε.app K) ≫
      (restriction.{u, u} a).mapDerivedCategoryFactors.hom.app
        (((tensorFunctor a).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((((Functor.mapHomologicalComplexCompIso (Iso.refl
          (tensorFunctor a ⋙ restriction.{u, u} a)) (.up ℤ)).hom.app K) ≫
          (φ.hom.mapHomologicalComplex (.up ℤ)).app K) ≫
          ((Functor.whiskerLeft (Functor.const (Discrete (Fin d)))
            (lim.π ⟨i⟩)).mapHomologicalComplex (.up ℤ)).app K)

/-- Exactness assumptions for the pullback coordinate frame.
Source: Stacks 03EL, exactness of finite powers
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
structure FiniteFreeCoordinatePullbackExactness
    {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
    (g : GeometricMorphism (Sheaf J' (Type u)) (Sheaf J (Type u)))
    (R' S' : Sheaf J' CommRingCat.{u})
    (IR : AlgebraicInverseImage g.inverse R R')
    (IS : AlgebraicInverseImage g.inverse S S') (a' : R' ⟶ S') : Prop where
  irAdd : IR.modules.Additive
  irLim : PreservesFiniteLimits IR.modules
  irColim : PreservesFiniteColimits IR.modules
  isAdd : IS.modules.Additive
  isLim : PreservesFiniteLimits IS.modules
  isColim : PreservesFiniteColimits IS.modules
  tensorLim : PreservesFiniteLimits (tensorFunctor a')
  tensorColim : PreservesFiniteColimits (tensorFunctor a')
  resLim : PreservesFiniteLimits (restriction.{u, u} a')
  resColim : PreservesFiniteColimits (restriction.{u, u} a')
  powerAdd : (Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _)).Additive
  powerLim : PreservesFiniteLimits (Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _))
  powerColim : PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _))

/-- Chosen ordinary inverse-image coordinate maps, with equations stated separately.
Source: Stacks 03EL, finite-basis calculation
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
abbrev FiniteFreeCoordinatePullbackData
    {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
    (g : GeometricMorphism (Sheaf J' (Type u)) (Sheaf J (Type u)))
    (R' S' : Sheaf J' CommRingCat.{u})
    (IR : AlgebraicInverseImage g.inverse R R')
    (IS : AlgebraicInverseImage g.inverse S S') (a' : R' ⟶ S') :=
  OrdinaryComparisonTuple
    (tensorFunctor a ⋙ IS.modules ≅ IR.modules ⋙ tensorFunctor a')
    (restriction.{u, u} a ⋙ IR.modules ≅ IS.modules ⋙ restriction.{u, u} a')
    ((Functor.const (Discrete (Fin d)) ⋙ lim) ⋙ IR.modules ≅
        IR.modules ⋙ (Functor.const (Discrete (Fin d)) ⋙ lim))
    (IR.modules.obj (unit (ringSheaf R)) ≅ unit (ringSheaf R'))
    (IS.modules.obj (unit (ringSheaf S)) ≅ unit (ringSheaf S'))
    (IR.modules.obj (∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R))) ≅
        ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R')))
    (∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R')) ≅
        (restriction.{u, u} a').obj (unit (ringSheaf S')))
    (tensorFunctor a' ⋙ restriction.{u, u} a' ≅
        Functor.const (Discrete (Fin d)) ⋙ lim)

/-- Normalization equations for a pullback coordinate frame, verbatim from
`FiniteFreeCoordinatesInverseImage`. Source: Stacks 03EL
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
def FiniteFreeCoordinatePullbackLaws
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S)))
    (φ : tensorFunctor a ⋙ restriction.{u, u} a ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf S))]
    [PreservesFiniteLimits (tensorFunctor a)] [PreservesFiniteColimits (tensorFunctor a)]
    [PreservesFiniteLimits (restriction.{u, u} a)]
    [PreservesFiniteColimits (restriction.{u, u} a)]
    [(Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _)).Additive]
    [PreservesFiniteLimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _))]
    [PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _))]
    (E : DerivedCategory (SheafOfModules.{u} (ringSheaf R)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringSheaf S)))
    (ε : DerivedCategory.Q ⋙ E ⟶
      (tensorFunctor a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (Φ : E ⋙ (restriction.{u, u} a).mapDerivedCategory ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
    (g : GeometricMorphism (Sheaf J' (Type u)) (Sheaf J (Type u)))
    (R' S' : Sheaf J' CommRingCat.{u})
    (IR : AlgebraicInverseImage g.inverse R R')
    (IS : AlgebraicInverseImage g.inverse S S')
    (a' : R' ⟶ S')
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf R'))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf S'))]
    [IR.modules.Additive]
    [PreservesFiniteLimits IR.modules]
    [PreservesFiniteColimits IR.modules]
    [IS.modules.Additive]
    [PreservesFiniteLimits IS.modules]
    [PreservesFiniteColimits IS.modules]
    [PreservesFiniteLimits (tensorFunctor a')]
    [PreservesFiniteColimits (tensorFunctor a')]
    [PreservesFiniteLimits (restriction.{u, u} a')]
    [PreservesFiniteColimits (restriction.{u, u} a')]
    [(Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _)).Additive]
    [PreservesFiniteLimits (Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _))]
    [PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
        (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R')) ⥤ _))]
    (D : FiniteFreeCoordinatePullbackData a d g R' S' IR IS a') : Prop :=
      IsScalarInverseImageComparison g.inverse IR IS a a' D.chi ∧
      (underlying R').map D.unitR.hom =
        IR.moduleUnderlying.hom.app (unit (ringSheaf R)) ≫ IR.ringUnderlying.hom ∧
      (underlying S').map D.unitS.hom =
        IS.moduleUnderlying.hom.app (unit (ringSheaf S)) ≫ IS.ringUnderlying.hom ∧
      (∀ i : Fin d, D.powerUnit.hom ≫ Pi.π (fun _ : Fin d ↦ unit (ringSheaf R')) i =
        IR.modules.map (Pi.π (fun _ : Fin d ↦ unit (ringSheaf R)) i) ≫ D.unitR.hom) ∧
      (D.powerUnit.hom ≫ D.basis.hom = IR.modules.map θ.hom ≫
        D.rho.hom.app (unit (ringSheaf S)) ≫ (restriction.{u, u} a').map D.unitS.hom) ∧
      IsFiniteFreeScalarCoordinateIso a' d D.basis D.coordinate ∧
      (∀ N : SheafOfModules.{u} (ringSheaf S),
        (underlying R').map (D.rho.hom.app N) ≫
          IS.moduleUnderlying.hom.app N =
        IR.moduleUnderlying.hom.app ((restriction.{u, u} a).obj N)) ∧
      (∀ (M : SheafOfModules.{u} (ringSheaf R)) (i : Fin d),
        D.sigma.hom.app M ≫ Pi.π (fun _ : Fin d ↦ IR.modules.obj M) i =
          IR.modules.map (Pi.π (fun _ : Fin d ↦ M) i)) ∧
      (∀ M : SheafOfModules.{u} (ringSheaf R),
        IR.modules.map (φ.hom.app M) ≫ D.sigma.hom.app M =
          D.rho.hom.app ((tensorFunctor a).obj M) ≫
            (restriction.{u, u} a').map (D.chi.hom.app M) ≫
              D.coordinate.hom.app (IR.modules.obj M)) ∧
      ∀ (E' : DerivedCategory (SheafOfModules.{u} (ringSheaf R')) ⥤
          DerivedCategory (SheafOfModules.{u} (ringSheaf S')))
        (ε' : DerivedCategory.Q ⋙ E' ⟶
          (tensorFunctor a').mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        [E'.IsLeftDerivedFunctor ε'
          (HomologicalComplex.quasiIso (SheafOfModules.{u} (ringSheaf R')) (.up ℤ))],
        DerivedCoordinateCompatibility (tensorFunctor a) (restriction a) d
          IR.modules IS.modules (tensorFunctor a') (restriction a') E ε E' ε'
          D.chi D.rho Φ (IsDerivedFiniteFreeScalarCoordinateIso a' d E' ε' D.coordinate)

/-- Inverse image respects the specified coordinate morphisms. Restriction is normalized
on underlying sheaves, finite sums by their projections, and scalar extension by the
balanced comparison on arbitrary generalized elements. Thus none of the comparisons
is an arbitrary isomorphism.
Source: Stacks 03EL and blueprint finite-basis calculation
(blueprint: lem-sfb-derived-finite-free-scalar-coordinates). -/
def FiniteFreeCoordinatesInverseImage
    (θ : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf R)) ≅
      (restriction.{u, u} a).obj (unit (ringSheaf S)))
    (φ : tensorFunctor a ⋙ restriction.{u, u} a ≅
      Functor.const (Discrete (Fin d)) ⋙ lim)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf S))]
    [PreservesFiniteLimits (tensorFunctor a)] [PreservesFiniteColimits (tensorFunctor a)]
    [PreservesFiniteLimits (restriction.{u, u} a)]
    [PreservesFiniteColimits (restriction.{u, u} a)]
    [(Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _)).Additive]
    [PreservesFiniteLimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _))]
    [PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ SheafOfModules.{u} (ringSheaf R)) ⥤ _))]
    (E : DerivedCategory (SheafOfModules.{u} (ringSheaf R)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringSheaf S)))
    (ε : DerivedCategory.Q ⋙ E ⟶
      (tensorFunctor a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (Φ : E ⋙ (restriction.{u, u} a).mapDerivedCategory ≅
      Functor.const (Discrete (Fin d)) ⋙ lim) : Prop :=
  ∀ {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
    (g : GeometricMorphism (Sheaf J' (Type u)) (Sheaf J (Type u)))
    (R' S' : Sheaf J' CommRingCat.{u})
    (IR : AlgebraicInverseImage g.inverse R R')
    (IS : AlgebraicInverseImage g.inverse S S')
    (a' : R' ⟶ S')
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf R'))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf S'))],
    g.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat)).map a) ≫
      IS.ringUnderlying.hom = IR.ringUnderlying.hom ≫
        (sheafCompose J' (CategoryTheory.forget CommRingCat)).map a' →
    ∃ h : FiniteFreeCoordinatePullbackExactness d g R' S' IR IS a',
      letI := h.irAdd
      letI := h.irLim
      letI := h.irColim
      letI := h.isAdd
      letI := h.isLim
      letI := h.isColim
      letI := h.tensorLim
      letI := h.tensorColim
      letI := h.resLim
      letI := h.resColim
      letI := h.powerAdd
      letI := h.powerLim
      letI := h.powerColim
      ∃ (D : FiniteFreeCoordinatePullbackData a d g R' S' IR IS a'),
      FiniteFreeCoordinatePullbackLaws a d θ φ E ε Φ g R' S' IR IS a' D
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.DerivedFiniteFreeScalarCoordinates
--uses FiniteFreeCoordinatesInverseImage` finds no external textual user of the
changed predicate. Both transitive importers are also listed below.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.DerivedFiniteFreeScalarCoordinates | Y6 | Constructor adapted to grouped witnesses; theorem signature unchanged. |
| Sheaf.CategoryTheory.ToposFiniteFreeCounitComparison | unclaimed | Uses the unchanged coordinate predicates; no adaptation required. |
| Sheaf.Paper.FiniteFreeExceptionalMate | unclaimed | Imports the theorem module; no adaptation required. |

## Status

landed 20261024T191823-L-504525 2026-10-24 (merge of deliver/Y6/Sheaf.CategoryTheory.DerivedFiniteFreeScalarCoordinates)

## Elaboration interfaces

Six proved public theorem constants cache the existing proposition-valued sheafification
and sheaf-composition instances, and finite-product shapes: `coordinateAbelianSheafify`,
`coordinateAbelianLocalEquivalences`, `coordinateCommRingToRingCompose`,
`coordinateCommRingToTypeCompose`, `coordinateAddCommGrpToTypeCompose` and
`coordinateFiniteProductShape`. They are local
instances only. Their priorities exceed Mathlib's generic multicospan search, avoiding
reconstruction of the same witness in each concrete signature. Every cache theorem is
proved by the existing instance. No mathematical data is chosen by these theorems.
The generic eight-field tuple also avoids generating a specialized record API with
large sheaf-category types. The unused K-flat coefficient-universe import is removed; the small-site Mathlib
instances suffice. Reducibility and transparency settings are adjusted at individual
proof steps; no kernel check or linter is disabled.
