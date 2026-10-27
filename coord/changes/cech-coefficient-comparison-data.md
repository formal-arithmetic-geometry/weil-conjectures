# CategoryTheory.CechCoefficientCommutations and its comparison API

## Reason

Move the existing comparison records and constructors into
`Sheaf.CategoryTheory.CechCoefficientComparisonData`, publicly imported by the original module.
A separate strict coefficient-map theorem must use these records without importing the derived
comparison theorem that uses it. This removes an import cycle. All declaration names, signatures,
visibility and construction terms remain identical. No target meaning changes. This is not a
split to evade the compile limit.

## Old

In `Sheaf.CategoryTheory.CechCoefficientDerivedComparison`:

```lean
/-- Restrict a ring morphism to the element site, section by section.
Source: Stacks 04IE and node proof step 3
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
def cechCoefficientRingMap
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}} (φ : R' ⟶ R) (A : Sheaf J (Type u)) :
    elementRing R' A ⟶ elementRing R A :=
  ObjectProperty.homMk (Functor.whiskerLeft (elementProjection A).op φ.hom)

section Commutations

variable {C Y : Type u} [SmallCategory C] [SmallCategory Y]
  {J : GrothendieckTopology C} {L : GrothendieckTopology Y}
  {R R' : Sheaf J RingCat.{u}} {S S' : Sheaf L RingCat.{u}}

/-- Canonical scalar commutations. The base map is fixed on underlying sheaves by the
recorded direct-image identifications, the pullback map is the identity on sections,
and the pushforward map is its counit mate. Thus none of these is an arbitrary map.
Source: Stacks 04IE, 04J4 and node proof step 3
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
structure CechCoefficientCommutations
    (f : RingedToposMorphism R S) (f' : RingedToposMorphism R' S')
    (φ : R' ⟶ R) (ψ : S' ⟶ S) (hd : f.direct = f'.direct)
    (D : CoherentCechImageModel R) (D' : CoherentCechImageModel R') where
  base : f.modules ⋙ SheafOfModules.restrictScalars ψ ≅
    SheafOfModules.restrictScalars φ ⋙ f'.modules
  base_underlying : ∀ M : ringedSiteModules.{u} R,
    (SheafOfModules.toSheaf S' ⋙ sheafCompose L (forget AddCommGrpCat)).map
        (base.hom.app M) ≫
      f'.underlying.hom.app ((SheafOfModules.restrictScalars φ).obj M) =
    f.underlying.hom.app M ≫ eqToHom
      (congrArg (fun G ↦ G.obj
        ((SheafOfModules.toSheaf R ⋙ sheafCompose J (forget AddCommGrpCat)).obj M)) hd)
  pull : ∀ A : Sheaf J (Type u),
    elementModulePullback R A ⋙
        SheafOfModules.restrictScalars (cechCoefficientRingMap φ A) ≅
      SheafOfModules.restrictScalars φ ⋙ elementModulePullback R' A
  pull_sections : ∀ (A : Sheaf J (Type u)) (M : ringedSiteModules.{u} R)
    (U : A.obj.Elementsᵒᵖᵒᵖ)
    (x : ((elementModulePullback R A).obj M).val.obj U),
    HEq (((pull A).hom.app M).val.app U x) x
  push : ∀ A : Sheaf J (Type u),
    D.push A ⋙ SheafOfModules.restrictScalars φ ≅
      SheafOfModules.restrictScalars (cechCoefficientRingMap φ A) ⋙ D'.push A
  push_counit : ∀ (A : Sheaf J (Type u))
    (N : ringedSiteModules.{u} (elementRing R A)),
    (elementModulePullback R' A).map ((push A).hom.app N) ≫
      (D'.adj A).counit.app
        ((SheafOfModules.restrictScalars (cechCoefficientRingMap φ A)).obj N) =
    (pull A).inv.app ((D.push A).obj N) ≫
      (SheafOfModules.restrictScalars (cechCoefficientRingMap φ A)).map
        ((D.adj A).counit.app N)

namespace CechCoefficientCommutations

variable {f : RingedToposMorphism R S} {f' : RingedToposMorphism R' S'}
  {φ : R' ⟶ R} {ψ : S' ⟶ S} {hd : f.direct = f'.direct}
  {D : CoherentCechImageModel R} {D' : CoherentCechImageModel R'}
  (E : CechCoefficientCommutations f f' φ ψ hd D D')

/-- The scalar commutation for `j_* j^*` is the composite of the specified pull and push
commutations through the recorded localization presentations.
Source: Stacks 04IE, 04J4 and proof step 3
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
def image (A : Sheaf J (Type u)) :
    D.image.obj (op A) ⋙ SheafOfModules.restrictScalars φ ≅
      SheafOfModules.restrictScalars φ ⋙ D'.image.obj (op A) :=
  isoWhiskerRight (D.imageIso A) _ ≪≫ associator _ _ _ ≪≫
    isoWhiskerLeft _ (E.push A) ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight (E.pull A) _ ≪≫ associator _ _ _ ≪≫
    isoWhiskerLeft _ (D'.imageIso A).symm

/-- The column's underived square uses the base and slice pushforward commutations.
Source: Stacks 04IE, 04J4 and proof step 5
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
def column (A : Sheaf J (Type u)) :
    (D.push A ⋙ f.modules) ⋙ SheafOfModules.restrictScalars ψ ≅
      SheafOfModules.restrictScalars (cechCoefficientRingMap φ A) ⋙
        (D'.push A ⋙ f'.modules) :=
  associator _ _ _ ≪≫ isoWhiskerLeft _ E.base ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight (E.push A) _ ≪≫ associator _ _ _

end CechCoefficientCommutations
end Commutations

section Derived

universe a b a' b' va vb va' vb' wa wb wa' wb'
variable {A : Type a} {B : Type b} {A' : Type a'} {B' : Type b'}
  [Category.{va} A] [Category.{vb} B] [Category.{va'} A'] [Category.{vb'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
  [HasDerivedCategory.{wa'} A'] [HasDerivedCategory.{wb'} B']

/-- A total right-derived pair with its defining unit and localization universal property.
This is only a record of the existing Mathlib notion, with no new derived category.
Source: Stacks 070Y, def-sfb-right-derived-functor and proof step 4
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
structure CechCoefficientDerivedPair (F : A ⥤ B) [F.Additive] where
  functor : DerivedCategory A ⥤ DerivedCategory B
  unit : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ functor
  universal : functor.IsRightDerivedFunctor unit
    (HomologicalComplex.quasiIso A (.up ℤ))

/-- The unit equation defining the canonical coefficient comparison. Composition and
localization identifications are written explicitly; no invertibility is required.
Source: Stacks 070Y, lem-sfb-exact-square-right-derived-unit and proof step 4
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
def CechCoefficientUnitEquation
    (F : A ⥤ B) (G : A' ⥤ B') (U : A ⥤ A') (V : B ⥤ B')
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (c : F ⋙ V ≅ U ⋙ G) (RF : CechCoefficientDerivedPair F)
    (RG : CechCoefficientDerivedPair G)
    (γ : RF.functor ⋙ V.mapDerivedCategory ⟶ U.mapDerivedCategory ⋙ RG.functor) : Prop :=
  ∀ P : CochainComplex A ℤ,
    V.mapDerivedCategory.map (RF.unit.app P) ≫ γ.app (DerivedCategory.Q.obj P) =
      V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app P) ≫
        RG.unit.app ((U.mapHomologicalComplex (.up ℤ)).obj P) ≫
        RG.functor.map (U.mapDerivedCategoryFactors.inv.app P)

end Derived

universe a b va vb

/-- Apply a nonnegative augmentation after extension by zero, using the canonical
comparison with applying the additive functor before extension.
Source: Stacks 015F and proof step 5
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
def cechCoefficientExtendMap
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive]
    {I : CochainComplex A ℕ} {T : CochainComplex B ℕ}
    (b : (F.mapHomologicalComplex (.up ℕ)).obj I ⟶ T) :
    (F.mapHomologicalComplex (.up ℤ)).obj (I.extend ComplexShape.embeddingUpNat) ⟶
      T.extend ComplexShape.embeddingUpNat :=
  (I.mapExtendIso ComplexShape.embeddingUpNat F).hom ≫
    HomologicalComplex.extendMap b ComplexShape.embeddingUpNat


/-- Scalar restriction applied to a complex, using Mathlib's actual functor.
Source: Stacks 015F and proof step 2
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
abbrev cechCoefficientComplex
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}} (φ : R' ⟶ R)
    {ι : Type a} (c : ComplexShape ι) :=
  (SheafOfModules.restrictScalars.{u} φ).mapHomologicalComplex c

/-- The resolution-lift equation after localization, including the canonical identification
of the scalar restriction of a degree-zero complex.
Source: Stacks 070I and proof step 2
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
def IsCechCoefficientResolutionLift
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}} (φ : R' ⟶ R)
    [HasDerivedCategory.{wXp} (ringedSiteModules.{u} R')]
    (M : ringedSiteModules.{u} R) (I : InjectiveResolution M)
    (I' : InjectiveResolution ((SheafOfModules.restrictScalars φ).obj M))
    (t : (cechCoefficientComplex φ (.up ℕ)).obj I.cocomplex ⟶ I'.cocomplex) : Prop :=
  DerivedCategory.Q.map (HomologicalComplex.extendMap
      ((cechCoefficientComplex φ (.up ℕ)).map I.ι) ComplexShape.embeddingUpNat) ≫
    DerivedCategory.Q.map (HomologicalComplex.extendMap t ComplexShape.embeddingUpNat) =
  DerivedCategory.Q.map (HomologicalComplex.extendMap
    ((HomologicalComplex.singleMapHomologicalComplex
      (SheafOfModules.restrictScalars.{u} φ) (.up ℕ) 0).hom.app M ≫ I'.ι)
        ComplexShape.embeddingUpNat)

/-- The scalar coefficient formula in one localization, followed by direct image.
Source: Stacks 04IE, 04J4 and proof step 3
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
def cechCoefficientComponent
    {C Y : Type u} [SmallCategory C] [SmallCategory Y]
    {J : GrothendieckTopology C} {L : GrothendieckTopology Y}
    {R R' : Sheaf J RingCat.{u}} {S S' : Sheaf L RingCat.{u}}
    {f : RingedToposMorphism R S} {f' : RingedToposMorphism R' S'}
    {φ : R' ⟶ R} {ψ : S' ⟶ S} {hd : f.direct = f'.direct}
    {D : CoherentCechImageModel R} {D' : CoherentCechImageModel R'}
    (E : CechCoefficientCommutations f f' φ ψ hd D D')
    (A : Sheaf J (Type u)) {M : ringedSiteModules.{u} R}
    {N : ringedSiteModules.{u} R'} (t : (SheafOfModules.restrictScalars φ).obj M ⟶ N) :
    (SheafOfModules.restrictScalars ψ).obj (f.modules.obj ((D.image.obj (op A)).obj M)) ⟶
      f'.modules.obj ((D'.image.obj (op A)).obj N) :=
  E.base.hom.app _ ≫ f'.modules.map ((E.image A).hom.app M) ≫
    f'.modules.map ((D'.image.obj (op A)).map t)

/-- The componentwise criterion for the finite-diagonal total comparison. Its equation
uses every diagonal coprojection, so it specifies the finite-biproduct comparison.
Source: Stacks Homology 0133 and proof step 3
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
def IsCechCoefficientTotalMap
    {C Y : Type u} [SmallCategory C] [SmallCategory Y]
    {J : GrothendieckTopology C} {L : GrothendieckTopology Y}
    {R R' : Sheaf J RingCat.{u}} {S S' : Sheaf L RingCat.{u}}
    (f : RingedToposMorphism R S) (f' : RingedToposMorphism R' S') (ψ : S' ⟶ S)
    (D : CoherentCechImageModel R) (D' : CoherentCechImageModel R')
    (V : Sheaf J (Type u))
    (I : CochainComplex (ringedSiteModules.{u} R) ℕ)
    (I' : CochainComplex (ringedSiteModules.{u} R') ℕ)
    (β : ((cechCoefficientComplex ψ (.up ℕ)).mapHomologicalComplex (.up ℕ)).obj
      (D.bicomplex f.modules V I) ⟶ D'.bicomplex f'.modules V I')
    (b : (cechCoefficientComplex ψ (.up ℕ)).obj
      ((D.bicomplex f.modules V I).total (.up ℕ)) ⟶
        (D'.bicomplex f'.modules V I').total (.up ℕ)) : Prop :=
  ∀ n q k : ℕ, ∀ h : n + q = k,
    (SheafOfModules.restrictScalars ψ).map
        ((D.bicomplex f.modules V I).ιTotal (.up ℕ) n q k h) ≫ b.f k =
      (β.f n).f q ≫ (D'.bicomplex f'.modules V I').ιTotal (.up ℕ) n q k h


/-- A bicomplex map and its finite total, fixed by the actual scalar component formula.
Source: Stacks 015F, 070I and proof step 3
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
structure CechCoefficientMapData
    {C Y : Type u} [SmallCategory C] [SmallCategory Y]
    {J : GrothendieckTopology C} {L : GrothendieckTopology Y}
    {R R' : Sheaf J RingCat.{u}} {S S' : Sheaf L RingCat.{u}}
    {f : RingedToposMorphism R S} {f' : RingedToposMorphism R' S'}
    {φ : R' ⟶ R} {ψ : S' ⟶ S} {hd : f.direct = f'.direct}
    {D : CoherentCechImageModel R} {D' : CoherentCechImageModel R'}
    (E : CechCoefficientCommutations f f' φ ψ hd D D')
    (V : Sheaf J (Type u))
    (I : CochainComplex (ringedSiteModules.{u} R) ℕ)
    (I' : CochainComplex (ringedSiteModules.{u} R') ℕ)
    (t : (cechCoefficientComplex φ (.up ℕ)).obj I ⟶ I') where
  bicomplex : ((cechCoefficientComplex ψ (.up ℕ)).mapHomologicalComplex (.up ℕ)).obj
    (D.bicomplex f.modules V I) ⟶ D'.bicomplex f'.modules V I'
  components : ∀ n q : ℕ, (bicomplex.f n).f q =
    cechCoefficientComponent E ((sheafCoverNerve V).obj (op (SimplexCategory.mk n))) (t.f q)
  total : (cechCoefficientComplex ψ (.up ℕ)).obj
    ((D.bicomplex f.modules V I).total (.up ℕ)) ⟶
      (D'.bicomplex f'.modules V I').total (.up ℕ)
  total_components : IsCechCoefficientTotalMap f f' ψ D D' V I I' bicomplex total

/-- The scalar-restricted resolution augmentation from the termwise image of `M[0]`.
The single-complex and extension comparisons are both canonical Mathlib maps.
Source: Stacks 015F, 070I and proof step 2
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
def cechCoefficientResolutionAugmentation
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}} (φ : R' ⟶ R) (M : ringedSiteModules.{u} R)
    (I' : InjectiveResolution ((SheafOfModules.restrictScalars φ).obj M)) :
    (cechCoefficientComplex φ (.up ℤ)).obj
        (((CochainComplex.single₀ _).obj M).extend ComplexShape.embeddingUpNat) ⟶
      I'.cocomplex.extend ComplexShape.embeddingUpNat :=
  (((CochainComplex.single₀ _).obj M).mapExtendIso ComplexShape.embeddingUpNat
    (SheafOfModules.restrictScalars φ)).hom ≫
      HomologicalComplex.extendMap
        ((HomologicalComplex.singleMapHomologicalComplex
          (SheafOfModules.restrictScalars.{u} φ) (.up ℕ) 0).hom.app M ≫ I'.ι)
            ComplexShape.embeddingUpNat

section Comparison

universe a' b' va' vb' wa wb wa' wb'
variable {A : Type a} {B : Type b} {A' : Type a'} {B' : Type b'}
  [Category.{va} A] [Category.{vb} B] [Category.{va'} A'] [Category.{vb'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
  [HasDerivedCategory.{wa'} A'] [HasDerivedCategory.{wb'} B']

/-- Normalization of a resolution comparison by the right-derived unit.
Source: Stacks 070Y and proof step 4
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
def IsCechResolutionComparison (F : A ⥤ B) [F.Additive]
    (RF : CechCoefficientDerivedPair F) {P I : CochainComplex A ℤ}
    (a : P ⟶ I)
    (e : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
      RF.functor.obj (DerivedCategory.Q.obj P)) : Prop :=
  e.hom ≫ RF.functor.map (DerivedCategory.Q.map a) = RF.unit.app I

/-- One column represents precisely the canonical derived square comparison, with the
right-derived unit evaluated at `U(I)`. The two resolution isomorphisms are normalized
by their units, and the equation explicitly transports exact scalar restriction.
Source: Stacks 070I, 070Y and proof steps 4--5
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
def IsCechCoefficientColumnComparison
    (F : A ⥤ B) (G : A' ⥤ B') (U : A ⥤ A') (V : B ⥤ B')
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (c : F ⋙ V ≅ U ⋙ G)
    {P I : CochainComplex A ℤ} {I' : CochainComplex A' ℤ}
    (a : P ⟶ I) (a' : (U.mapHomologicalComplex (.up ℤ)).obj P ⟶ I')
    (t : (U.mapHomologicalComplex (.up ℤ)).obj I ⟶ I') : Prop :=
  ∃ (RF : CechCoefficientDerivedPair F) (RG : CechCoefficientDerivedPair G)
    (γ : RF.functor ⋙ V.mapDerivedCategory ⟶ U.mapDerivedCategory ⋙ RG.functor)
    (e : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
      RF.functor.obj (DerivedCategory.Q.obj P))
    (e' : DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj I') ≅
      RG.functor.obj (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj P))),
    CechCoefficientUnitEquation F G U V c RF RG γ ∧
    IsCechResolutionComparison F RF a e ∧ IsCechResolutionComparison G RG a' e' ∧
    V.mapDerivedCategory.map e.inv ≫
        V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app I) ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map t) =
      γ.app (DerivedCategory.Q.obj P) ≫
        RG.functor.map (U.mapDerivedCategoryFactors.hom.app P) ≫ e'.inv

end Comparison


/-- Apply the specified scalar-pullback commutation to integer-indexed complexes.
The adjunction supplies the additive structures; all components remain the given maps.
Source: Stacks 04IE and proof steps 3 and 5
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
def cechCoefficientPullComplexIso
    {C Y : Type u} [SmallCategory C] [SmallCategory Y]
    {J : GrothendieckTopology C} {L : GrothendieckTopology Y}
    {R R' : Sheaf J RingCat.{u}} {S S' : Sheaf L RingCat.{u}}
    {f : RingedToposMorphism R S} {f' : RingedToposMorphism R' S'}
    {φ : R' ⟶ R} {ψ : S' ⟶ S} {hd : f.direct = f'.direct}
    {D : CoherentCechImageModel R} {D' : CoherentCechImageModel R'}
    (E : CechCoefficientCommutations f f' φ ψ hd D D') (A : Sheaf J (Type u))
    (I : CochainComplex (ringedSiteModules.{u} R) ℤ) :
    (cechCoefficientComplex (cechCoefficientRingMap φ A) (.up ℤ)).obj
        ((cechColumnRestrictComplex D A).obj I) ≅
      (cechColumnRestrictComplex D' A).obj ((cechCoefficientComplex φ (.up ℤ)).obj I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ (E.pull A).app (I.X q)) (fun _ _ _ ↦ ((E.pull A).hom.naturality _).symm)

/-- The actual map in one localized column, with scalar restriction on its source.
Source: Stacks 04IE, 04J4 and proof step 5
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
def cechCoefficientLocalizedMap
    {C Y : Type u} [SmallCategory C] [SmallCategory Y]
    {J : GrothendieckTopology C} {L : GrothendieckTopology Y}
    {R R' : Sheaf J RingCat.{u}} {S S' : Sheaf L RingCat.{u}}
    {f : RingedToposMorphism R S} {f' : RingedToposMorphism R' S'}
    {φ : R' ⟶ R} {ψ : S' ⟶ S} {hd : f.direct = f'.direct}
    {D : CoherentCechImageModel R} {D' : CoherentCechImageModel R'}
    (E : CechCoefficientCommutations f f' φ ψ hd D D') (A : Sheaf J (Type u))
    {I : CochainComplex (ringedSiteModules.{u} R) ℤ}
    {I' : CochainComplex (ringedSiteModules.{u} R') ℤ}
    (t : (cechCoefficientComplex φ (.up ℤ)).obj I ⟶ I') :
    (cechCoefficientComplex (cechCoefficientRingMap φ A) (.up ℤ)).obj
        ((cechColumnRestrictComplex D A).obj I) ⟶
      (cechColumnRestrictComplex D' A).obj I' :=
  (cechCoefficientPullComplexIso E A I).hom ≫ (cechColumnRestrictComplex D' A).map t


/-- The actual scalar-restricted chain map after extension from nonnegative degrees.
Source: Stacks 015F and proof steps 2--3
(blueprint: lem-sfb-cech-coefficient-derived-comparison). -/
def cechCoefficientLiftExtend
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}} (φ : R' ⟶ R)
    {I : CochainComplex (ringedSiteModules.{u} R) ℕ}
    {I' : CochainComplex (ringedSiteModules.{u} R') ℕ}
    (t : (cechCoefficientComplex φ (.up ℕ)).obj I ⟶ I') :
    (cechCoefficientComplex φ (.up ℤ)).obj (I.extend ComplexShape.embeddingUpNat) ⟶
      I'.extend ComplexShape.embeddingUpNat :=
  (I.mapExtendIso ComplexShape.embeddingUpNat (SheafOfModules.restrictScalars φ)).hom ≫
    HomologicalComplex.extendMap t ComplexShape.embeddingUpNat
```

## New

The same declarations, verbatim except for their blueprint links, in
`Sheaf.CategoryTheory.CechCoefficientComparisonData`:

```lean
/-- Restrict a ring morphism to the element site, section by section.
Source: Stacks 04IE and node proof step 3
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
def cechCoefficientRingMap
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}} (φ : R' ⟶ R) (A : Sheaf J (Type u)) :
    elementRing R' A ⟶ elementRing R A :=
  ObjectProperty.homMk (Functor.whiskerLeft (elementProjection A).op φ.hom)

section Commutations

variable {C Y : Type u} [SmallCategory C] [SmallCategory Y]
  {J : GrothendieckTopology C} {L : GrothendieckTopology Y}
  {R R' : Sheaf J RingCat.{u}} {S S' : Sheaf L RingCat.{u}}

/-- Canonical scalar commutations. The base map is fixed on underlying sheaves by the
recorded direct-image identifications, the pullback map is the identity on sections,
and the pushforward map is its counit mate. Thus none of these is an arbitrary map.
Source: Stacks 04IE, 04J4 and node proof step 3
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
structure CechCoefficientCommutations
    (f : RingedToposMorphism R S) (f' : RingedToposMorphism R' S')
    (φ : R' ⟶ R) (ψ : S' ⟶ S) (hd : f.direct = f'.direct)
    (D : CoherentCechImageModel R) (D' : CoherentCechImageModel R') where
  base : f.modules ⋙ SheafOfModules.restrictScalars ψ ≅
    SheafOfModules.restrictScalars φ ⋙ f'.modules
  base_underlying : ∀ M : ringedSiteModules.{u} R,
    (SheafOfModules.toSheaf S' ⋙ sheafCompose L (forget AddCommGrpCat)).map
        (base.hom.app M) ≫
      f'.underlying.hom.app ((SheafOfModules.restrictScalars φ).obj M) =
    f.underlying.hom.app M ≫ eqToHom
      (congrArg (fun G ↦ G.obj
        ((SheafOfModules.toSheaf R ⋙ sheafCompose J (forget AddCommGrpCat)).obj M)) hd)
  pull : ∀ A : Sheaf J (Type u),
    elementModulePullback R A ⋙
        SheafOfModules.restrictScalars (cechCoefficientRingMap φ A) ≅
      SheafOfModules.restrictScalars φ ⋙ elementModulePullback R' A
  pull_sections : ∀ (A : Sheaf J (Type u)) (M : ringedSiteModules.{u} R)
    (U : A.obj.Elementsᵒᵖᵒᵖ)
    (x : ((elementModulePullback R A).obj M).val.obj U),
    HEq (((pull A).hom.app M).val.app U x) x
  push : ∀ A : Sheaf J (Type u),
    D.push A ⋙ SheafOfModules.restrictScalars φ ≅
      SheafOfModules.restrictScalars (cechCoefficientRingMap φ A) ⋙ D'.push A
  push_counit : ∀ (A : Sheaf J (Type u))
    (N : ringedSiteModules.{u} (elementRing R A)),
    (elementModulePullback R' A).map ((push A).hom.app N) ≫
      (D'.adj A).counit.app
        ((SheafOfModules.restrictScalars (cechCoefficientRingMap φ A)).obj N) =
    (pull A).inv.app ((D.push A).obj N) ≫
      (SheafOfModules.restrictScalars (cechCoefficientRingMap φ A)).map
        ((D.adj A).counit.app N)

namespace CechCoefficientCommutations

variable {f : RingedToposMorphism R S} {f' : RingedToposMorphism R' S'}
  {φ : R' ⟶ R} {ψ : S' ⟶ S} {hd : f.direct = f'.direct}
  {D : CoherentCechImageModel R} {D' : CoherentCechImageModel R'}
  (E : CechCoefficientCommutations f f' φ ψ hd D D')

/-- The scalar commutation for `j_* j^*` is the composite of the specified pull and push
commutations through the recorded localization presentations.
Source: Stacks 04IE, 04J4 and proof step 3
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
def image (A : Sheaf J (Type u)) :
    D.image.obj (op A) ⋙ SheafOfModules.restrictScalars φ ≅
      SheafOfModules.restrictScalars φ ⋙ D'.image.obj (op A) :=
  isoWhiskerRight (D.imageIso A) _ ≪≫ associator _ _ _ ≪≫
    isoWhiskerLeft _ (E.push A) ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight (E.pull A) _ ≪≫ associator _ _ _ ≪≫
    isoWhiskerLeft _ (D'.imageIso A).symm

/-- The column's underived square uses the base and slice pushforward commutations.
Source: Stacks 04IE, 04J4 and proof step 5
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
def column (A : Sheaf J (Type u)) :
    (D.push A ⋙ f.modules) ⋙ SheafOfModules.restrictScalars ψ ≅
      SheafOfModules.restrictScalars (cechCoefficientRingMap φ A) ⋙
        (D'.push A ⋙ f'.modules) :=
  associator _ _ _ ≪≫ isoWhiskerLeft _ E.base ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight (E.push A) _ ≪≫ associator _ _ _

end CechCoefficientCommutations
end Commutations

section Derived

universe a b a' b' va vb va' vb' wa wb wa' wb'
variable {A : Type a} {B : Type b} {A' : Type a'} {B' : Type b'}
  [Category.{va} A] [Category.{vb} B] [Category.{va'} A'] [Category.{vb'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
  [HasDerivedCategory.{wa'} A'] [HasDerivedCategory.{wb'} B']

/-- A total right-derived pair with its defining unit and localization universal property.
This is only a record of the existing Mathlib notion, with no new derived category.
Source: Stacks 070Y, def-sfb-right-derived-functor and proof step 4
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
structure CechCoefficientDerivedPair (F : A ⥤ B) [F.Additive] where
  functor : DerivedCategory A ⥤ DerivedCategory B
  unit : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ functor
  universal : functor.IsRightDerivedFunctor unit
    (HomologicalComplex.quasiIso A (.up ℤ))

/-- The unit equation defining the canonical coefficient comparison. Composition and
localization identifications are written explicitly; no invertibility is required.
Source: Stacks 070Y, lem-sfb-exact-square-right-derived-unit and proof step 4
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
def CechCoefficientUnitEquation
    (F : A ⥤ B) (G : A' ⥤ B') (U : A ⥤ A') (V : B ⥤ B')
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (c : F ⋙ V ≅ U ⋙ G) (RF : CechCoefficientDerivedPair F)
    (RG : CechCoefficientDerivedPair G)
    (γ : RF.functor ⋙ V.mapDerivedCategory ⟶ U.mapDerivedCategory ⋙ RG.functor) : Prop :=
  ∀ P : CochainComplex A ℤ,
    V.mapDerivedCategory.map (RF.unit.app P) ≫ γ.app (DerivedCategory.Q.obj P) =
      V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app P) ≫
        RG.unit.app ((U.mapHomologicalComplex (.up ℤ)).obj P) ≫
        RG.functor.map (U.mapDerivedCategoryFactors.inv.app P)

end Derived

universe a b va vb

/-- Apply a nonnegative augmentation after extension by zero, using the canonical
comparison with applying the additive functor before extension.
Source: Stacks 015F and proof step 5
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
def cechCoefficientExtendMap
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive]
    {I : CochainComplex A ℕ} {T : CochainComplex B ℕ}
    (b : (F.mapHomologicalComplex (.up ℕ)).obj I ⟶ T) :
    (F.mapHomologicalComplex (.up ℤ)).obj (I.extend ComplexShape.embeddingUpNat) ⟶
      T.extend ComplexShape.embeddingUpNat :=
  (I.mapExtendIso ComplexShape.embeddingUpNat F).hom ≫
    HomologicalComplex.extendMap b ComplexShape.embeddingUpNat


/-- Scalar restriction applied to a complex, using Mathlib's actual functor.
Source: Stacks 015F and proof step 2
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
abbrev cechCoefficientComplex
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}} (φ : R' ⟶ R)
    {ι : Type a} (c : ComplexShape ι) :=
  (SheafOfModules.restrictScalars.{u} φ).mapHomologicalComplex c

/-- The resolution-lift equation after localization, including the canonical identification
of the scalar restriction of a degree-zero complex.
Source: Stacks 070I and proof step 2
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
def IsCechCoefficientResolutionLift
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}} (φ : R' ⟶ R)
    [HasDerivedCategory.{wXp} (ringedSiteModules.{u} R')]
    (M : ringedSiteModules.{u} R) (I : InjectiveResolution M)
    (I' : InjectiveResolution ((SheafOfModules.restrictScalars φ).obj M))
    (t : (cechCoefficientComplex φ (.up ℕ)).obj I.cocomplex ⟶ I'.cocomplex) : Prop :=
  DerivedCategory.Q.map (HomologicalComplex.extendMap
      ((cechCoefficientComplex φ (.up ℕ)).map I.ι) ComplexShape.embeddingUpNat) ≫
    DerivedCategory.Q.map (HomologicalComplex.extendMap t ComplexShape.embeddingUpNat) =
  DerivedCategory.Q.map (HomologicalComplex.extendMap
    ((HomologicalComplex.singleMapHomologicalComplex
      (SheafOfModules.restrictScalars.{u} φ) (.up ℕ) 0).hom.app M ≫ I'.ι)
        ComplexShape.embeddingUpNat)

/-- The scalar coefficient formula in one localization, followed by direct image.
Source: Stacks 04IE, 04J4 and proof step 3
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
def cechCoefficientComponent
    {C Y : Type u} [SmallCategory C] [SmallCategory Y]
    {J : GrothendieckTopology C} {L : GrothendieckTopology Y}
    {R R' : Sheaf J RingCat.{u}} {S S' : Sheaf L RingCat.{u}}
    {f : RingedToposMorphism R S} {f' : RingedToposMorphism R' S'}
    {φ : R' ⟶ R} {ψ : S' ⟶ S} {hd : f.direct = f'.direct}
    {D : CoherentCechImageModel R} {D' : CoherentCechImageModel R'}
    (E : CechCoefficientCommutations f f' φ ψ hd D D')
    (A : Sheaf J (Type u)) {M : ringedSiteModules.{u} R}
    {N : ringedSiteModules.{u} R'} (t : (SheafOfModules.restrictScalars φ).obj M ⟶ N) :
    (SheafOfModules.restrictScalars ψ).obj (f.modules.obj ((D.image.obj (op A)).obj M)) ⟶
      f'.modules.obj ((D'.image.obj (op A)).obj N) :=
  E.base.hom.app _ ≫ f'.modules.map ((E.image A).hom.app M) ≫
    f'.modules.map ((D'.image.obj (op A)).map t)

/-- The componentwise criterion for the finite-diagonal total comparison. Its equation
uses every diagonal coprojection, so it specifies the finite-biproduct comparison.
Source: Stacks Homology 0133 and proof step 3
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
def IsCechCoefficientTotalMap
    {C Y : Type u} [SmallCategory C] [SmallCategory Y]
    {J : GrothendieckTopology C} {L : GrothendieckTopology Y}
    {R R' : Sheaf J RingCat.{u}} {S S' : Sheaf L RingCat.{u}}
    (f : RingedToposMorphism R S) (f' : RingedToposMorphism R' S') (ψ : S' ⟶ S)
    (D : CoherentCechImageModel R) (D' : CoherentCechImageModel R')
    (V : Sheaf J (Type u))
    (I : CochainComplex (ringedSiteModules.{u} R) ℕ)
    (I' : CochainComplex (ringedSiteModules.{u} R') ℕ)
    (β : ((cechCoefficientComplex ψ (.up ℕ)).mapHomologicalComplex (.up ℕ)).obj
      (D.bicomplex f.modules V I) ⟶ D'.bicomplex f'.modules V I')
    (b : (cechCoefficientComplex ψ (.up ℕ)).obj
      ((D.bicomplex f.modules V I).total (.up ℕ)) ⟶
        (D'.bicomplex f'.modules V I').total (.up ℕ)) : Prop :=
  ∀ n q k : ℕ, ∀ h : n + q = k,
    (SheafOfModules.restrictScalars ψ).map
        ((D.bicomplex f.modules V I).ιTotal (.up ℕ) n q k h) ≫ b.f k =
      (β.f n).f q ≫ (D'.bicomplex f'.modules V I').ιTotal (.up ℕ) n q k h


/-- A bicomplex map and its finite total, fixed by the actual scalar component formula.
Source: Stacks 015F, 070I and proof step 3
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
structure CechCoefficientMapData
    {C Y : Type u} [SmallCategory C] [SmallCategory Y]
    {J : GrothendieckTopology C} {L : GrothendieckTopology Y}
    {R R' : Sheaf J RingCat.{u}} {S S' : Sheaf L RingCat.{u}}
    {f : RingedToposMorphism R S} {f' : RingedToposMorphism R' S'}
    {φ : R' ⟶ R} {ψ : S' ⟶ S} {hd : f.direct = f'.direct}
    {D : CoherentCechImageModel R} {D' : CoherentCechImageModel R'}
    (E : CechCoefficientCommutations f f' φ ψ hd D D')
    (V : Sheaf J (Type u))
    (I : CochainComplex (ringedSiteModules.{u} R) ℕ)
    (I' : CochainComplex (ringedSiteModules.{u} R') ℕ)
    (t : (cechCoefficientComplex φ (.up ℕ)).obj I ⟶ I') where
  bicomplex : ((cechCoefficientComplex ψ (.up ℕ)).mapHomologicalComplex (.up ℕ)).obj
    (D.bicomplex f.modules V I) ⟶ D'.bicomplex f'.modules V I'
  components : ∀ n q : ℕ, (bicomplex.f n).f q =
    cechCoefficientComponent E ((sheafCoverNerve V).obj (op (SimplexCategory.mk n))) (t.f q)
  total : (cechCoefficientComplex ψ (.up ℕ)).obj
    ((D.bicomplex f.modules V I).total (.up ℕ)) ⟶
      (D'.bicomplex f'.modules V I').total (.up ℕ)
  total_components : IsCechCoefficientTotalMap f f' ψ D D' V I I' bicomplex total

/-- The scalar-restricted resolution augmentation from the termwise image of `M[0]`.
The single-complex and extension comparisons are both canonical Mathlib maps.
Source: Stacks 015F, 070I and proof step 2
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
def cechCoefficientResolutionAugmentation
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}} (φ : R' ⟶ R) (M : ringedSiteModules.{u} R)
    (I' : InjectiveResolution ((SheafOfModules.restrictScalars φ).obj M)) :
    (cechCoefficientComplex φ (.up ℤ)).obj
        (((CochainComplex.single₀ _).obj M).extend ComplexShape.embeddingUpNat) ⟶
      I'.cocomplex.extend ComplexShape.embeddingUpNat :=
  (((CochainComplex.single₀ _).obj M).mapExtendIso ComplexShape.embeddingUpNat
    (SheafOfModules.restrictScalars φ)).hom ≫
      HomologicalComplex.extendMap
        ((HomologicalComplex.singleMapHomologicalComplex
          (SheafOfModules.restrictScalars.{u} φ) (.up ℕ) 0).hom.app M ≫ I'.ι)
            ComplexShape.embeddingUpNat

section Comparison

universe a' b' va' vb' wa wb wa' wb'
variable {A : Type a} {B : Type b} {A' : Type a'} {B' : Type b'}
  [Category.{va} A] [Category.{vb} B] [Category.{va'} A'] [Category.{vb'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
  [HasDerivedCategory.{wa'} A'] [HasDerivedCategory.{wb'} B']

/-- Normalization of a resolution comparison by the right-derived unit.
Source: Stacks 070Y and proof step 4
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
def IsCechResolutionComparison (F : A ⥤ B) [F.Additive]
    (RF : CechCoefficientDerivedPair F) {P I : CochainComplex A ℤ}
    (a : P ⟶ I)
    (e : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
      RF.functor.obj (DerivedCategory.Q.obj P)) : Prop :=
  e.hom ≫ RF.functor.map (DerivedCategory.Q.map a) = RF.unit.app I

/-- One column represents precisely the canonical derived square comparison, with the
right-derived unit evaluated at `U(I)`. The two resolution isomorphisms are normalized
by their units, and the equation explicitly transports exact scalar restriction.
Source: Stacks 070I, 070Y and proof steps 4--5
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
def IsCechCoefficientColumnComparison
    (F : A ⥤ B) (G : A' ⥤ B') (U : A ⥤ A') (V : B ⥤ B')
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (c : F ⋙ V ≅ U ⋙ G)
    {P I : CochainComplex A ℤ} {I' : CochainComplex A' ℤ}
    (a : P ⟶ I) (a' : (U.mapHomologicalComplex (.up ℤ)).obj P ⟶ I')
    (t : (U.mapHomologicalComplex (.up ℤ)).obj I ⟶ I') : Prop :=
  ∃ (RF : CechCoefficientDerivedPair F) (RG : CechCoefficientDerivedPair G)
    (γ : RF.functor ⋙ V.mapDerivedCategory ⟶ U.mapDerivedCategory ⋙ RG.functor)
    (e : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
      RF.functor.obj (DerivedCategory.Q.obj P))
    (e' : DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj I') ≅
      RG.functor.obj (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj P))),
    CechCoefficientUnitEquation F G U V c RF RG γ ∧
    IsCechResolutionComparison F RF a e ∧ IsCechResolutionComparison G RG a' e' ∧
    V.mapDerivedCategory.map e.inv ≫
        V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app I) ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map t) =
      γ.app (DerivedCategory.Q.obj P) ≫
        RG.functor.map (U.mapDerivedCategoryFactors.hom.app P) ≫ e'.inv

end Comparison


/-- Apply the specified scalar-pullback commutation to integer-indexed complexes.
The adjunction supplies the additive structures; all components remain the given maps.
Source: Stacks 04IE and proof steps 3 and 5
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
def cechCoefficientPullComplexIso
    {C Y : Type u} [SmallCategory C] [SmallCategory Y]
    {J : GrothendieckTopology C} {L : GrothendieckTopology Y}
    {R R' : Sheaf J RingCat.{u}} {S S' : Sheaf L RingCat.{u}}
    {f : RingedToposMorphism R S} {f' : RingedToposMorphism R' S'}
    {φ : R' ⟶ R} {ψ : S' ⟶ S} {hd : f.direct = f'.direct}
    {D : CoherentCechImageModel R} {D' : CoherentCechImageModel R'}
    (E : CechCoefficientCommutations f f' φ ψ hd D D') (A : Sheaf J (Type u))
    (I : CochainComplex (ringedSiteModules.{u} R) ℤ) :
    (cechCoefficientComplex (cechCoefficientRingMap φ A) (.up ℤ)).obj
        ((cechColumnRestrictComplex D A).obj I) ≅
      (cechColumnRestrictComplex D' A).obj ((cechCoefficientComplex φ (.up ℤ)).obj I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ (E.pull A).app (I.X q)) (fun _ _ _ ↦ ((E.pull A).hom.naturality _).symm)

/-- The actual map in one localized column, with scalar restriction on its source.
Source: Stacks 04IE, 04J4 and proof step 5
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
def cechCoefficientLocalizedMap
    {C Y : Type u} [SmallCategory C] [SmallCategory Y]
    {J : GrothendieckTopology C} {L : GrothendieckTopology Y}
    {R R' : Sheaf J RingCat.{u}} {S S' : Sheaf L RingCat.{u}}
    {f : RingedToposMorphism R S} {f' : RingedToposMorphism R' S'}
    {φ : R' ⟶ R} {ψ : S' ⟶ S} {hd : f.direct = f'.direct}
    {D : CoherentCechImageModel R} {D' : CoherentCechImageModel R'}
    (E : CechCoefficientCommutations f f' φ ψ hd D D') (A : Sheaf J (Type u))
    {I : CochainComplex (ringedSiteModules.{u} R) ℤ}
    {I' : CochainComplex (ringedSiteModules.{u} R') ℤ}
    (t : (cechCoefficientComplex φ (.up ℤ)).obj I ⟶ I') :
    (cechCoefficientComplex (cechCoefficientRingMap φ A) (.up ℤ)).obj
        ((cechColumnRestrictComplex D A).obj I) ⟶
      (cechColumnRestrictComplex D' A).obj I' :=
  (cechCoefficientPullComplexIso E A I).hom ≫ (cechColumnRestrictComplex D' A).map t


/-- The actual scalar-restricted chain map after extension from nonnegative degrees.
Source: Stacks 015F and proof steps 2--3
(blueprint: def-sfb-cech-coefficient-comparison-data). -/
def cechCoefficientLiftExtend
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}} (φ : R' ⟶ R)
    {I : CochainComplex (ringedSiteModules.{u} R) ℕ}
    {I' : CochainComplex (ringedSiteModules.{u} R') ℕ}
    (t : (cechCoefficientComplex φ (.up ℕ)).obj I ⟶ I') :
    (cechCoefficientComplex φ (.up ℤ)).obj (I.extend ComplexShape.embeddingUpNat) ⟶
      I'.extend ComplexShape.embeddingUpNat :=
  (I.mapExtendIso ComplexShape.embeddingUpNat (SheafOfModules.restrictScalars φ)).hom ≫
    HomologicalComplex.extendMap t ComplexShape.embeddingUpNat
```

The original module publicly imports this module. The unused public proof import
`Sheaf.CategoryTheory.ExactSquareRightDerivedUnit` is removed; the given unit equation is
sufficient for the comparison calculation.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.CechCoefficientDerivedComparison | W7 | Publicly reexports the unchanged API. |
| Sheaf.CategoryTheory.CechCoefficientStrictMaps | W7 (new) | Imports the API to state the independent strict construction. |

`tools/downstream.py Sheaf.CategoryTheory.CechCoefficientDerivedComparison --uses
CategoryTheory.CechCoefficientCommutations` reports zero downstream modules and only the original
module as a user. No other module needs adaptation.

## Status

landed 20261024T021944-L-2882117 2026-10-24 (merge of deliver/W7/Sheaf.CategoryTheory.CechCoefficientDerivedComparison)
