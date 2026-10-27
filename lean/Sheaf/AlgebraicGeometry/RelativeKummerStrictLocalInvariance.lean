module

public import Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback
public import Sheaf.AlgebraicGeometry.KummerLineGeometry
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.ClosedOpen
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.Sites.TorsorPullback
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Strict-local invariance of the actual relative Kummer pullback

Source: blueprint main-20261015, prop-pur-gm-relative-kummer.proof.md, Step 2;
Stacks Project, Tags 0EYU, 03Q9, 03QO, 01F8 and 03PL
(blueprint: lem-pur-relative-kummer-strict-local-invariance).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Etale

attribute [-instance] CategoryTheory.catToReflQuiver
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀
  CategoryTheory.Abelian.Ext.mapExactFunctor

/-- The existing finite root line in the ordinary bounded below derived category.
Source: blueprint relative Kummer calculation, Step 2
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
abbrev relativeKummerLinePlus (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u}) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj (Scheme.finiteEtaleTateLine T m A hA)

/-- The normalized inverse-image comparison, derived from its sectionwise pure-tensor map.
Source: Stacks Tag 03PK and blueprint relative Kummer calculation, Step 2
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
@[irreducible]
def relativeKummerLinePullback (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.obj
        (relativeKummerLinePlus A m hA Y) ≅ relativeKummerLinePlus A m hA X :=
  (Functor.mapDerivedCategoryPlusSingleFunctor
    (upperStar (ModuleCat.{u + 1} A) f) 0).app _ ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso
        ((Scheme.finiteEtaleTwistPullbackData A m hm hA).c f hY hX 1)

/-- The actual adjunction unit followed by the canonical coefficient identification.
Source: Stacks Tag 0EYU and blueprint relative Kummer calculation, Step 2
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
@[irreducible]
def relativeKummerUnit (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) :
    relativeKummerLinePlus A m hA Y ⟶
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus.obj
        (relativeKummerLinePlus A m hA X) :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).derivedPlus.unit.app
      (relativeKummerLinePlus A m hA Y) ≫
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus.map
      (relativeKummerLinePullback A m hm hA f hY hX).hom

/-- The resolution-defined derived pullback with the normalized root-line comparison.
Source: Stacks Tags 01F8--01FA and blueprint relative Kummer calculation, Step 2
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
@[irreducible]
def relativeKummerGlobalPullback (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) :
    (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.obj
        (relativeKummerLinePlus A m hA Y) ⟶
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.obj
        (relativeKummerLinePlus A m hA X) :=
  moduleDerivedCohomologyPullback A f (relativeKummerLinePlus A m hA Y) ≫
    (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.map
      (relativeKummerLinePullback A m hm hA f hY hX).hom

/-- Apply the scalar-forgetting comparison and then a module coefficient morphism.
Source: Stacks Tags 03D3 and 03D7
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
@[irreducible]
def relativeKummerUnderlyingPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (c : (upperStar (ModuleCat.{u + 1} A) f).obj F ⟶ G) :
    (upperStar AddCommGrpCat.{u + 1} f).obj
      ((RawModuleScalarComparison.forget A Y).obj F) ⟶
    (RawModuleScalarComparison.forget A X).obj G :=
  (RawModuleScalarComparison.pullbackIso A f).inv.app F ≫
    (RawModuleScalarComparison.forget A X).map c

/-- The canonical comparison on underlying root-line sheaves, isolated before applying
cohomology so no scalar-forgetting constructions are unfolded in the cohomology type.
Source: Stacks Tags 03PK and 03D7
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
@[irreducible]
def relativeKummerAbelianPullback (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) :
    (upperStar AddCommGrpCat.{u + 1} f).obj
      ((RawModuleScalarComparison.forget A Y).obj (Scheme.finiteEtaleTateLine Y m A hA)) ⟶
    (RawModuleScalarComparison.forget A X).obj (Scheme.finiteEtaleTateLine X m A hA) :=
  relativeKummerUnderlyingPullback A f
    ((Scheme.finiteEtaleTwistPullbackData A m hm hA).c f hY hX 1).hom

/-- Apply the existing cohomology morphism with an abstract site interface, keeping the
canonical map unchanged while sharing its type conversions.
Source: Stacks Tag 01F8
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
def relativeKummerMapOnCohomology {D : Type (u + 1)} [Category.{u} D]
    {J : GrothendieckTopology D} [HasSheafify J AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
    {F G : Sheaf J AddCommGrpCat.{u + 1}} (c : F ⟶ G) (q : ℕ)
    (x : Sheaf.H F q) : Sheaf.H G q :=
  Sheaf.H.map c q x

/-- Sheafification exists on the small etale site.
Source: the existing small-etale sheafification instance
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
theorem relativeKummerHasSheafify (T : Scheme.{u}) :
    HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1} := by infer_instance
/-- Ext groups are small for abelian sheaves on the small etale site.
Source: the existing small-etale Ext instance
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
theorem relativeKummerHasExt (T : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) := by infer_instance

section
attribute [local instance] relativeKummerHasSheafify relativeKummerHasExt
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Pull back cohomology and then apply a specified comparison of coefficients.
The abstract coefficient arguments share the type conversions in the Kummer specialization.
Source: Stacks Tag 01F8
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
@[irreducible]
def relativeKummerPullbackOnCohomology {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (c : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ G) (q : ℕ) :
    Sheaf.H F q → Sheaf.H G q :=
  fun x ↦ relativeKummerMapOnCohomology c q
    ((CategoryTheory.Abelian.Ext.mk₀
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom).comp
      (x.mapExactFunctor (upperStar AddCommGrpCat.{u + 1} f)) (zero_add q))

/-- The degree-zero class of a module-sheaf section on the identity étale object.
Source: Stacks Tag 01F8
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
@[irreducible]
def relativeKummerModuleSectionClass (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (x : F.obj.obj (op (Scheme.Etale.mk (𝟙 T)))) :
    Sheaf.H ((RawModuleScalarComparison.forget A T).obj F) 0 :=
  (Sheaf.H.equiv₀ ((RawModuleScalarComparison.forget A T).obj F)
    (show IsTerminal (Scheme.Etale.mk (𝟙 T)) from
      MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).symm x

/-- Canonical pullback on underlying abelian cohomology, with coefficient comparison.
Source: Stacks Tag 01F8 and blueprint relative Kummer calculation, Step 2
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
@[irreducible]
def relativeKummerCohomologyPullback (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) (q : ℕ) :
    Sheaf.H ((RawModuleScalarComparison.forget A Y).obj
      (Scheme.finiteEtaleTateLine Y m A hA)) q →
    Sheaf.H ((RawModuleScalarComparison.forget A X).obj
      (Scheme.finiteEtaleTateLine X m A hA)) q :=
  relativeKummerPullbackOnCohomology f
    (relativeKummerAbelianPullback A m hm hA f hY hX) q

/-- The constant section zeta tensor a, expressed in H0 by the standard section comparison.
Source: Stacks Tag 03PK and blueprint relative Kummer calculation, Step 2
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
@[irreducible]
def relativeKummerConstant (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) {k : Type u} [Field k] {ζ : k}
    (hζ : IsPrimitiveRoot ζ m) (T : Scheme.{u}) (aT : T ⟶ Spec (.of k)) (a : A) :
    Sheaf.H ((RawModuleScalarComparison.forget A T).obj
      (Scheme.finiteEtaleTateLine T m A hA)) 0 :=
  letI : NeZero m := ⟨ne_of_gt hm⟩
  relativeKummerModuleSectionClass A T (Scheme.finiteEtaleTateLine T m A hA)
    (Scheme.finiteEtaleTateOneGenerator A m T hA (op (Scheme.Etale.mk (𝟙 T))) a
      ((T.constantZModIsoRootsOfUnitySheaf m aT hζ).hom.hom.app
        (op (Scheme.Etale.mk (𝟙 T)))
          ((toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod m))))).app
                (op (Scheme.Etale.mk (𝟙 T))) (ULift.up 1))))

/-- The scalar-extended ordinary Kummer boundary of a specified global unit.
Source: Stacks Tag 03PL and blueprint relative Kummer calculation, Step 2
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
@[irreducible]
def relativeKummerClass (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤)))
    (v : Γ(T, ⊤)ˣ) :
    Sheaf.H ((RawModuleScalarComparison.forget A T).obj
      (Scheme.finiteEtaleTateLine T m A hA)) 1 :=
  relativeKummerMapOnCohomology (ordinaryFiniteRootMap A m hA T) 1
    (T.kummerδ₀ m hT (Additive.ofMul v))

set_option linter.defProp false in
/-- The algebra structure supplies the annihilator used by the existing root-line API.
Source: blueprint finite free Z/m-algebra convention
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
def relativeKummerAnnihilator (A : Type (u + 1)) [CommRing A] (m : ℕ)
    [Algebra (ZMod m) A] : (m : A) = 0 :=
  (map_natCast (algebraMap (ZMod m) A) m).symm.trans
    ((congrArg (algebraMap (ZMod m) A) (ZMod.natCast_self m)).trans
      (map_zero (algebraMap (ZMod m) A)))

set_option linter.defProp false in
/-- Invertibility is transported along the k-structure map, including on the empty scheme.
Source: blueprint relative Kummer calculation, Step 2
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
def relativeKummerExponentUnit {k : Type u} [Field k] (m : ℕ) (hm : IsUnit (m : k))
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of k)) : IsUnit (m : Γ(T, ⊤)) :=
  (map_natCast (((Scheme.ΓSpecIso (.of k)).inv ≫ aT.appTop).hom) m) ▸
    hm.map (((Scheme.ΓSpecIso (.of k)).inv ≫ aT.appTop).hom)

/-- The structure morphism Spec H to Spec k, with no finiteness assumption on H.
Source: blueprint relative Kummer calculation, Step 2
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
def relativeKummerBaseMap (k H : Type u) [Field k] [CommRing H] [Algebra k H] :
    Spec (.of H) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k H))

/-- The specified base-changed affine or punctured line.
Source: blueprint relative Kummer calculation, Step 2
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
abbrev relativeKummerBaseCurve (k H : Type u) [Field k] [CommRing H] [Algebra k H]
    (b : Bool) : Scheme.{u} :=
  pullback (KummerLine.structureMap k b) (relativeKummerBaseMap k H)

/-- The projection h of the node.
Source: blueprint relative Kummer calculation, Step 2
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
abbrev relativeKummerProjection (k H : Type u) [Field k] [CommRing H] [Algebra k H]
    (b : Bool) : relativeKummerBaseCurve k H b ⟶ KummerLine.curve k b :=
  pullback.fst (KummerLine.structureMap k b) (relativeKummerBaseMap k H)

/-- The k-structure of the specified fibre product.
Source: blueprint relative Kummer calculation, Step 2
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
abbrev relativeKummerBaseStructure (k H : Type u) [Field k] [CommRing H] [Algebra k H]
    (b : Bool) : relativeKummerBaseCurve k H b ⟶ Spec (.of k) :=
  relativeKummerProjection k H b ≫ KummerLine.structureMap k b

set_option linter.defProp false in
/-- The prime-power exponent is invertible in k.
Source: blueprint coefficient convention
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
def relativeKummerFieldExponentUnit {k : Type u} [Field k] (ℓ N : ℕ)
    (hℓk : IsUnit (ℓ : k)) : IsUnit ((ℓ ^ N : ℕ) : k) :=
  (Nat.cast_pow (α := k) ℓ N).symm ▸ hℓk.pow N

set_option linter.defProp false in
/-- The four assertions for a given projection: actual unit, its Leray identification,
canonical pullback invertibility and preservation of every specified constant.
Source: blueprint relative Kummer calculation, Step 2
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
@[irreducible]
def RelativeKummerPullbackInvariance (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {k : Type u} [Field k] {ζ : k}
    (hζ : IsPrimitiveRoot ζ m) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aY : Y ⟶ Spec (.of k))
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) : Prop :=
  IsIso (relativeKummerUnit A m hm hA f hY hX) ∧
    (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.map
        (relativeKummerUnit A m hm hA f hY hX) ≫
      (moduleLerayPlus A f).hom.app (relativeKummerLinePlus A m hA X) =
        relativeKummerGlobalPullback A m hm hA f hY hX ∧
    IsIso (relativeKummerGlobalPullback A m hm hA f hY hX) ∧
    ∀ a : A, relativeKummerCohomologyPullback A m hm hA f hY hX 0
        (relativeKummerConstant A m hm hA hζ Y aY a) =
      relativeKummerConstant A m hm hA hζ X (f ≫ aY) a

set_option linter.defProp false in
/-- Preservation of the scalar-extended Kummer class of a specified unit.
Source: Stacks Tag 03PL and blueprint relative Kummer calculation, Step 2
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
@[irreducible]
def RelativeKummerClassInvariance (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤)))
    (v : Γ(Y, ⊤)ˣ) : Prop :=
  relativeKummerCohomologyPullback A m hm hA f hY hX 1
      (relativeKummerClass A m hA Y hY v) =
    relativeKummerClass A m hA X hX (Units.map f.appTop.hom.toMonoidHom v)




end

set_option backward.isDefEq.respectTransparency false

private theorem relativeKummerPullbackOnCohomology_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (c : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ G) (q : ℕ) (x : Sheaf.H F q) :
    relativeKummerPullbackOnCohomology f c q x =
      Sheaf.H.map c q (cohomologyMap f F q x) := by
  unfold relativeKummerPullbackOnCohomology relativeKummerMapOnCohomology
  rw [cohomologyMap_apply]

private theorem derivedPullback_eq_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [EnoughInjectives D]
    (L : C ⥤ D) (R : D ⥤ C) (G : C ⥤ E) (H : D ⥤ E)
    [L.Additive] [R.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] [PreservesFiniteLimits R]
    (adj : L ⊣ R) (e : R ⋙ G ≅ H) (K : DerivedCategory.Plus C) :
    (Functor.rightDerivedDesc _ G.rightDerivedFunctorPlusUnit
      (HomotopyCategory.Plus.quasiIso _)
      (L.mapDerivedCategoryPlus ⋙ H.rightDerivedFunctorPlus)
      (Functor.whiskerRight
      (NatTrans.mapHomotopyCategoryPlus
        ((Functor.leftUnitor G).inv ≫ Functor.whiskerRight adj.unit G ≫
          (Functor.associator L R G).hom ≫ Functor.whiskerLeft L e.hom))
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ H))).inv
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft L.mapHomotopyCategoryPlus H.rightDerivedFunctorPlusUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.inv H.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom)).app K =
      G.rightDerivedFunctorPlus.map (adj.derivedPlus.unit.app K) ≫
        (@Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
          R G _ _ _ _
          (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj)
          e).hom.app (L.mapDerivedCategoryPlus.obj K) := by
  have : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  let β := Functor.whiskerRight
      (NatTrans.mapHomotopyCategoryPlus
        ((Functor.leftUnitor G).inv ≫ Functor.whiskerRight adj.unit G ≫
          (Functor.associator L R G).hom ≫ Functor.whiskerLeft L e.hom))
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ H))).inv
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft L.mapHomotopyCategoryPlus H.rightDerivedFunctorPlusUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.inv H.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom
  let γ := (Functor.leftUnitor G.rightDerivedFunctorPlus).inv ≫
    Functor.whiskerRight adj.derivedPlus.unit G.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft L.mapDerivedCategoryPlus
      (Functor.rightDerivedFunctorPlusCompIso' R G e).hom
  suffices h : Functor.rightDerivedDesc _ G.rightDerivedFunctorPlusUnit
      (HomotopyCategory.Plus.quasiIso _) _ β = γ by
    simpa only [γ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.leftUnitor_inv_app, Category.id_comp, Category.assoc] using
      NatTrans.congr_app h K
  apply Functor.rightDerived_ext _ G.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso _)
  rw [Functor.rightDerived_fac]
  ext M : 2
  simp only [β, γ, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Category.id_comp, Category.comp_id]
  -- Compute the derived unit before using naturality of the Leray comparison.
  have hu : adj.derivedPlus.unit.app (DerivedCategory.Plus.Qh.obj M) =
      DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app M) ≫
        R.rightDerivedFunctorPlusUnit.app (L.mapHomotopyCategoryPlus.obj M) ≫
        R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.inv.app M) := by
    rw [← Category.assoc, ← adj.derivedPlus_unit_app_fac, Category.assoc,
      ← Functor.map_comp]
    simp
  rw [hu, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  have hn := (Functor.rightDerivedFunctorPlusCompIso' R G e).hom.naturality
    (L.mapDerivedCategoryPlusFactorsh.inv.app M)
  simp only [Functor.comp_map] at hn
  dsimp only [Functor.comp_obj] at hn
  rw [hn]
  have hG := G.rightDerivedFunctorPlusUnit.naturality
    (adj.mapHomotopyCategoryPlus.unit.app M)
  simp only [Functor.comp_map] at hG
  rw [← reassoc_of% hG]
  rw [← Functor.rightDerivedFunctorPlusCompUnit_app_assoc]
  have hc := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac R G e)
    (L.mapHomotopyCategoryPlus.obj M)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hc
  rw [reassoc_of% hc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 2
  apply (HomotopyCategory.Plus.ι _).map_injective
  obtain ⟨M, hM⟩ := M
  obtain ⟨A, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  simp only [Functor.map_comp, NatTrans.ι_map_mapHomotopyCategoryPlus_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app]
  rw [(HomotopyCategory.Plus.ι _).map_id, Category.comp_id]
  change _ = (G.mapHomotopyCategory _).map
      ((HomotopyCategory.Plus.ι _).map
        (adj.mapHomotopyCategoryPlus.unit.app ⟨_, hM⟩)) ≫ _
  rw [Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app]
  change (HomotopyCategory.quotient _ _).map
      ((NatTrans.mapHomologicalComplex
        (G.leftUnitor.inv ≫ Functor.whiskerRight adj.unit G ≫
          (Functor.associator L R G).hom ≫ Functor.whiskerLeft L e.hom) _).app A) =
      (G.mapHomotopyCategory _).map
        ((adj.mapHomotopyCategory _).unit.app ((HomotopyCategory.quotient _ _).obj A)) ≫
      (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex e.hom _).app
          ((L.mapHomologicalComplex _).obj A))
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Functor.mapHomotopyCategory_map, ← Functor.map_comp]
  congr 1
  ext i
  simp



private theorem modulePullback_eq_unit (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    moduleDerivedCohomologyPullback A f K =
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).derivedPlus.unit.app K) ≫
      (moduleLerayPlus A f).hom.app
        ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.obj K) := by
  unfold moduleDerivedCohomologyPullback moduleLerayPlus
  exact derivedPullback_eq_unit _ _ _ _
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} A) f) K

private theorem relativeKummerGlobalPullback_eq_unit
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) :
    (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.map
        (relativeKummerUnit A m hm hA f hY hX) ≫
      (moduleLerayPlus A f).hom.app (relativeKummerLinePlus A m hA X) =
        relativeKummerGlobalPullback A m hm hA f hY hX := by
  unfold relativeKummerGlobalPullback relativeKummerUnit
  rw [modulePullback_eq_unit, Functor.map_comp]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun t ↦
      (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).derivedPlus.unit.app
          (relativeKummerLinePlus A m hA Y)) ≫ t)
      ((moduleLerayPlus A f).hom.naturality
        (relativeKummerLinePullback A m hm hA f hY hX).hom)



private theorem exactAdjunction_derived_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] [L.Full] [L.Faithful]
    (adj : L ⊣ R) (K : DerivedCategory.Plus C) :
    IsIso (adj.derivedPlus.unit.app K) := by
  let M := DerivedCategory.Plus.Qh.objPreimage K
  rw [← NatTrans.isIso_app_iff_of_iso adj.derivedPlus.unit
    (DerivedCategory.Plus.Qh.objObjPreimageIso K)]
  have : IsIso adj.mapHomotopyCategoryPlus.unit :=
    adj.mapHomotopyCategoryPlus.unit_isIso_of_L_fully_faithful
  have : IsIso R.rightDerivedFunctorPlusUnit :=
    Functor.isIso_rightDerivedFunctorPlusUnit R
  have : IsIso (adj.mapHomotopyCategoryPlus.unit.app M) :=
    NatIso.isIso_app_of_isIso _ _
  have hfac := adj.derivedPlus_unit_app_fac M
  have : IsIso (adj.derivedPlus.unit.app (DerivedCategory.Plus.Qh.obj M) ≫
      R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app M)) := by
    rw [hfac]
    exact IsIso.comp_isIso' (Functor.map_isIso DerivedCategory.Plus.Qh _)
      (NatIso.isIso_app_of_isIso R.rightDerivedFunctorPlusUnit _)
  exact IsIso.of_isIso_comp_right _
    (R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app M))

private theorem strictLocalBase_unit (A : Type (u + 1)) [CommRing A]
    (k : Type u) [Field k] [IsAlgClosed k]
    (H : Type u) [CommRing H] [Algebra k H] [IsStrictlyHenselianLocalRing H]
    (K : DerivedCategory.Plus
      (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (relativeKummerBaseMap k H)).derivedPlus.unit.app K) := by
  let Ck := constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} A)
  let CH := constantSheaf (Spec (.of H)).smallEtaleTopology (ModuleCat.{u + 1} A)
  let Gk := Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} A)
  let GH := Sheaf.Γ (Spec (.of H)).smallEtaleTopology (ModuleCat.{u + 1} A)
  let f := relativeKummerBaseMap k H
  let L := upperStar (ModuleCat.{u + 1} A) f
  let R := lowerStar (ModuleCat.{u + 1} A) f
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  have hCH : CH.FullyFaithful :=
    (constantSheafAdj (Spec (.of H)).smallEtaleTopology (ModuleCat.{u + 1} A)
      (Scheme.isTerminalEtaleTerminal H)).fullyFaithfulLOfIsIsoUnit
  let : CH.Full := hCH.full
  let : CH.Faithful := hCH.faithful
  have hCL : (Ck ⋙ L).FullyFaithful :=
    hCH.ofIso (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).symm
  let : (Ck ⋙ L).Full := hCL.full
  let : (Ck ⋙ L).Faithful := hCL.faithful
  let : L.Full := L.full_of_comp_essSurj Ck (fun ⦃_ _⦄ φ ↦ by
    obtain ⟨ψ, rfl⟩ := (Ck ⋙ L).map_surjective φ
    exact ⟨Ck.map ψ, rfl⟩)
  let : L.Faithful := L.faithful_of_comp_essSurj Ck (fun ⦃_ _⦄ α β h ↦ by
    obtain ⟨α, rfl⟩ := Ck.map_surjective α
    obtain ⟨β, rfl⟩ := Ck.map_surjective β
    exact congrArg Ck.map ((Ck ⋙ L).map_injective h))
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  let : Gk.IsEquivalence :=
    (constantSheafΓAdj (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} A)).isEquivalence_right_of_isEquivalence_left
  let E := (sheafSections (Spec (.of H)).smallEtaleTopology
    (ModuleCat.{u + 1} A)).obj (op (Scheme.etaleTerminal H))
  have : E.PreservesEpimorphisms := by
    refine ⟨?_⟩
    intro F G φ hφ
    exact (ModuleCat.epi_iff_surjective _).2
      (Scheme.surjective_app_of_epi_of_isStrictlyHenselianLocalRing H φ)
  let : GH.PreservesEpimorphisms := Functor.PreservesEpimorphisms.of_iso
    (Sheaf.ΓNatIsoSheafSections (Spec (.of H)).smallEtaleTopology
      (ModuleCat.{u + 1} A) (Scheme.isTerminalEtaleTerminal H)).symm
  let : GH.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels GH
  let : PreservesFiniteColimits GH := GH.preservesFiniteColimits_of_preservesHomology
  let : PreservesFiniteColimits (R ⋙ Gk) :=
    preservesFiniteColimits_of_natIso (lowerStarCompGlobalSectionsIso
      (ModuleCat.{u + 1} A) f).symm
  let : PreservesFiniteColimits R := preservesFiniteColimits_of_reflects_of_preserves R Gk
  exact exactAdjunction_derived_unit adj K

section
attribute [local instance] relativeKummerHasSheafify relativeKummerHasExt

private theorem underlyingPullback_transpose
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (c : (upperStar (ModuleCat.{u + 1} A) f).obj F ⟶ G) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
        (relativeKummerUnderlyingPullback A f c) =
      (moduleAbelianForget A Y).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _ c) := by
  unfold relativeKummerUnderlyingPullback
  dsimp only [RawModuleScalarComparison.pullbackIso, moduleAbelianUpperStarIso,
    asIso, Iso.symm_inv]
  rw [Adjunction.homEquiv_naturality_right]
  dsimp only [moduleAbelianUpperStarComparison]
  erw [Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  rfl



private theorem relativeKummerAbelianPullback_transpose
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
        (relativeKummerAbelianPullback A m hm hA f hY hX) =
      (moduleAbelianForget A Y).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
          ((Scheme.finiteEtaleTwistPullbackData A m hm hA).c f hY hX 1).hom) := by
  unfold relativeKummerAbelianPullback
  exact underlyingPullback_transpose A f _


private theorem finiteRootComparison_eq
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (m : Γ(Y, ⊤))) :
    ((Scheme.finiteEtaleTwistPullbackData A m hm hA).r f hY).hom =
      Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf m f := by
  apply (cancel_mono (kernel.ι (m • 𝟙 X.gmSheaf))).1
  rw [← (Scheme.finiteEtaleTwistPullbackData A m hm hA).laws.2.1 f hY]
  exact (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι m f).symm

private theorem ordinaryFiniteRootMap_pullback
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) :
    (upperStar AddCommGrpCat.{u + 1} f).map (ordinaryFiniteRootMap A m hA Y) ≫
        relativeKummerAbelianPullback A m hm hA f hY hX =
      Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf m f ≫
        ordinaryFiniteRootMap A m hA X := by
  apply ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    relativeKummerAbelianPullback_transpose]
  ext W z
  change ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
      ((Scheme.finiteEtaleTwistPullbackData A m hm hA).c f hY hX 1).hom).hom.app W
        (Scheme.finiteEtaleTateOneGenerator A m Y hA W 1 z) = _
  rw [(Scheme.finiteEtaleTwistPullbackData A m hm hA).laws.2.2.1 f hY hX W 1 z,
    finiteRootComparison_eq]
  rfl


private theorem gmUnits_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (v : Γ(Y, ⊤)ˣ) :
    Sheaf.H.map (Scheme.upperStarGmSheafToGmSheaf f) 0
      (cohomologyMap f Y.gmSheaf 0
        ((Sheaf.H.equiv₀ Y.gmSheaf
          (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y)).symm
            (ULift.up (Additive.ofMul v)))) =
      (Sheaf.H.equiv₀ X.gmSheaf
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)).symm
          (ULift.up (Additive.ofMul (Units.map f.appTop.hom.toMonoidHom v))) := by
  let e : Scheme.Etale.mk (𝟙 X) ⟶ f.Etale.obj (Scheme.Etale.mk (𝟙 Y)) :=
    MorphismProperty.Over.homMk (pullback.lift f (𝟙 X) (by simp))
      (pullback.lift_snd _ _ _)
  apply (Sheaf.H.equiv₀ X.gmSheaf
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)).injective
  rw [AddEquiv.apply_symm_apply]
  rw [Scheme.upperStarGmSheafToGmSheaf]
  rw [equiv₀_map_cohomologyMap f (Scheme.gmSheafToLowerStarGmSheaf f) _
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y) e,
    AddEquiv.apply_symm_apply]
  apply ULift.ext
  apply Additive.toMul.injective
  apply Units.ext
  change (pullback.lift f (𝟙 X) (by simp)).appTop
      ((pullback.fst (𝟙 Y) f).appTop (v : Γ(Y, ⊤))) = f.appTop (v : Γ(Y, ⊤))
  rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_fst]

private theorem kummerBoundary_pullback (m : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) (v : Γ(Y, ⊤)ˣ) :
    Scheme.rootsOfUnityCohomologyMap f m 1 (Y.kummerδ₀ m hY (Additive.ofMul v)) =
      X.kummerδ₀ m hX (Additive.ofMul (Units.map f.appTop.hom.toMonoidHom v)) := by
  let x := (Sheaf.H.equiv₀ Y.gmSheaf
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y)).symm
      (ULift.up (Additive.ofMul v))
  have h₁ := cohomologyMap_δSucc f (Y.kummerSequence_shortExact m hY) 0 x
  have h₂ := Sheaf.H.map_δSucc
    ((Y.kummerSequence_shortExact m hY).map_of_exact
      (upperStar AddCommGrpCat.{u + 1} f))
    (X.kummerSequence_shortExact m hX) (Scheme.kummerSequenceUpperStarMap f m) 0
      (cohomologyMap f Y.gmSheaf 0 x)
  have h := (congrArg
    (Sheaf.H.map (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf m f) 1) h₁).trans h₂
  rw [Sheaf.H.δSucc_zero (Y.kummerSequence_shortExact m hY)
      (MorphismProperty.Over.mkIdTerminal
      @AlgebraicGeometry.Etale Y),
    Sheaf.H.δSucc_zero (X.kummerSequence_shortExact m hX)
      (MorphismProperty.Over.mkIdTerminal
      @AlgebraicGeometry.Etale X)] at h
  dsimp only [x, Scheme.kummerSequence, Scheme.kummerSequenceUpperStarMap] at h
  rw [AddEquiv.apply_symm_apply] at h
  erw [gmUnits_pullback f v, AddEquiv.apply_symm_apply] at h
  exact h

private theorem relativeKummerClass_pullback
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) (v : Γ(Y, ⊤)ˣ) :
    RelativeKummerClassInvariance A m hm hA f hY hX v := by
  unfold RelativeKummerClassInvariance relativeKummerClass
    relativeKummerCohomologyPullback relativeKummerMapOnCohomology
  rw [relativeKummerPullbackOnCohomology_apply]
  rw [cohomologyMap_map, ← Sheaf.H.map_comp_apply, ordinaryFiniteRootMap_pullback,
    Sheaf.H.map_comp_apply]
  exact congrArg (Sheaf.H.map (ordinaryFiniteRootMap A m hA X) 1)
    (kummerBoundary_pullback m f hY hX v)


end

private theorem strictLocalSmooth_unit (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    (k : Type u) [Field k] [IsAlgClosed k]
    (H : Type u) [CommRing H] [Algebra k H] [IsStrictlyHenselianLocalRing H]
    (hmk : IsUnit (m : k)) {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [Smooth p]
    (K : DerivedCategory.Plus
      (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (pullback.fst p (relativeKummerBaseMap k H))).derivedPlus.unit.app
        ((upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategoryPlus.obj K)) := by
  let g := relativeKummerBaseMap k H
  let sq : IsPullback (pullback.snd p g) (pullback.fst p g) g p :=
    (IsPullback.of_hasPullback p g).flip
  let : QuasiCompact g := inferInstanceAs
    (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k H))))
  let : QuasiSeparated g := inferInstanceAs
    (QuasiSeparated (Spec.map (CommRingCat.ofHom (algebraMap k H))))
  have := strictLocalBase_unit A k H K
  have : IsIso ((baseChange (ModuleCat.{u + 1} A) sq.toCommSq).app
      ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.obj K)) :=
    isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder A p sq _
      (fun _ ↦ Scheme.IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero
        A m hm.ne' hA (relativeKummerExponentUnit m hmk (Spec (.of k)) (𝟙 _)) _)
  have hunit : IsIso ((derivedUpperStarLowerStarAdjunctionPlus
      (ModuleCat.{u + 1} A) g).unit.app K) := by
    rw [derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus]
    infer_instance
  have h := upperStar_map_unit_comp_baseChange_app A sq.toCommSq K
  have hcomp : IsIso
      ((upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategoryPlus.map
          ((derivedUpperStarLowerStarAdjunctionPlus
            (ModuleCat.{u + 1} A) g).unit.app K) ≫
        (baseChange (ModuleCat.{u + 1} A) sq.toCommSq).app
          ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.obj K)) :=
    inferInstance
  have htarget : IsIso ((derivedUpperStarLowerStarAdjunctionPlus
      (ModuleCat.{u + 1} A) (pullback.fst p g)).unit.app
        ((upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategoryPlus.obj K)) := by
    exact IsIso.of_isIso_fac_right h.symm
  rw [derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus] at htarget
  exact htarget

private theorem relativeKummerUnit_of_smooth (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    (k : Type u) [Field k] [IsAlgClosed k]
    (H : Type u) [CommRing H] [Algebra k H] [IsStrictlyHenselianLocalRing H]
    (hmk : IsUnit (m : k)) {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [Smooth p]
    (hX : IsUnit (m : Γ(X, ⊤)))
    (hXH : IsUnit (m : Γ(pullback p (relativeKummerBaseMap k H), ⊤))) :
    IsIso (relativeKummerUnit A m hm hA
      (pullback.fst p (relativeKummerBaseMap k H)) hX hXH) := by
  let hp := relativeKummerLinePullback A m hm hA p
    (relativeKummerExponentUnit m hmk (Spec (.of k)) (𝟙 _)) hX
  have := strictLocalSmooth_unit A m hm hA k H hmk p
    (relativeKummerLinePlus A m hA (Spec (.of k)))
  have := (NatTrans.isIso_app_iff_of_iso
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (pullback.fst p (relativeKummerBaseMap k H))).derivedPlus.unit hp).1 inferInstance
  unfold relativeKummerUnit
  infer_instance

private theorem kummerLine_structure_smooth (k : Type u) [Field k] (b : Bool) :
    Smooth (KummerLine.structureMap k b) := by
  have hline : Smooth (KummerLine.structureMap k false) := by
    apply HasRingHomProperty.Spec_iff.mpr
    change (algebraMap k (Polynomial k)).Smooth
    exact RingHom.smooth_algebraMap.mpr
      (show Algebra.Smooth k (Polynomial k) from ⟨inferInstance, inferInstance⟩)
  cases b
  · exact hline
  · have : IsOpenImmersion (KummerLine.inclusion k) :=
      IsOpenImmersion.of_isLocalization (S := LaurentPolynomial k) Polynomial.X
    have he : KummerLine.inclusion k ≫ KummerLine.structureMap k false =
        KummerLine.structureMap k true := by
      rw [KummerLine.inclusion, KummerLine.structureMap, KummerLine.structureMap,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      apply RingHom.ext
      intro x
      exact Polynomial.toLaurent_C x
    rw [← he]
    let := hline
    infer_instance


section
attribute [local instance] relativeKummerHasSheafify relativeKummerHasExt

private theorem finiteGenerator_naturality
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0) (T : Scheme.{u})
    {W V : T.Etaleᵒᵖ} (j : W ⟶ V) (a : A)
    (z : (T.rootsOfUnitySheaf m).obj.obj W) :
    (Scheme.finiteEtaleTateLine T m A hA).obj.map j
        (Scheme.finiteEtaleTateOneGenerator A m T hA W a z) =
      Scheme.finiteEtaleTateOneGenerator A m T hA V a
        ((T.rootsOfUnitySheaf m).obj.map j z) := by
  have h := ConcreteCategory.congr_hom
    ((toSheafify T.smallEtaleTopology (Scheme.finiteEtaleMuModulePresheaf T m ⋙
      ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar m A hA))).naturality j)
    (a ⊗ₜ[ZMod m, Scheme.finiteEtaleTwistScalar m A hA]
      (show (Scheme.finiteEtaleMuModulePresheaf T m).obj W from z))
  exact h.symm

private def rootConstantSection (m : ℕ) (hm : 0 < m)
    {k : Type u} [Field k] {ζ : k} (hζ : IsPrimitiveRoot ζ m)
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of k)) (W : T.Etaleᵒᵖ) :
    (T.rootsOfUnitySheaf m).obj.obj W := by
  let : NeZero m := ⟨hm.ne'⟩
  exact (T.constantZModIsoRootsOfUnitySheaf m aT hζ).hom.hom.app W
    ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod m))))).app W (ULift.up 1))

private theorem rootConstantSection_val (m : ℕ) (hm : 0 < m)
    {k : Type u} [Field k] {ζ : k} (hζ : IsPrimitiveRoot ζ m)
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of k)) (W : T.Etaleᵒᵖ) :
    ((Additive.toMul (((kernel.ι (m • 𝟙 T.gmSheaf)).hom.app W
        (rootConstantSection m hm hζ T aT W))).down : Γ(W.unop.left, ⊤)ˣ) :
          Γ(W.unop.left, ⊤)) =
      W.unop.hom.appTop (((Scheme.ΓSpecIso (.of k)).inv ≫ aT.appTop) ζ) := by
  let : NeZero m := ⟨hm.ne'⟩
  let hu : IsUnit (((Scheme.ΓSpecIso (.of k)).inv ≫ aT.appTop) ζ) :=
    (hζ.isUnit hm.ne').map _
  let hz : hu.unit ^ m = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← map_pow,
      hζ.pow_eq_one, map_one, Units.val_one]
  have h := congrArg (fun φ : T.constantZMod m ⟶ T.gmSheaf ↦
      φ.hom.app W ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod m))))).app W (ULift.up 1)))
    (kernel.lift_ι (m • 𝟙 T.gmSheaf) (T.constantZModToGmSheaf m hu.unit hz)
      (T.constantZModToGmSheaf_comp_nsmul m hu.unit hz))
  have hg := ConcreteCategory.congr_hom (NatTrans.congr_app
    (T.toSheafify_constantZModToGmSheaf m hu.unit hz) W) (ULift.up 1)
  change (kernel.ι (m • 𝟙 T.gmSheaf)).hom.app W
      (rootConstantSection m hm hζ T aT W) = _ at h
  change (T.constantZModToGmSheaf m hu.unit hz).hom.app W
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod m))))).app W (ULift.up 1)) =
    (T.zmodToGmPresheaf m hu.unit hz).app W (ULift.up 1) at hg
  have he := congrArg (fun z : T.gmSheaf.obj.obj W ↦
      ((Additive.toMul z.down : Γ(W.unop.left, ⊤)ˣ) : Γ(W.unop.left, ⊤))) (h.trans hg)
  exact he.trans (by
    simpa only [Nat.cast_one, pow_one, IsUnit.unit_spec] using
      T.zmodToGmPresheaf_app_natCast m hu.unit hz W 1)

private theorem rootConstantSection_pullback (m : ℕ) (hm : 0 < m)
    {k : Type u} [Field k] {ζ : k} (hζ : IsPrimitiveRoot ζ m)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ Spec (.of k))
    (e : Scheme.Etale.mk (𝟙 X) ⟶ f.Etale.obj (Scheme.Etale.mk (𝟙 Y))) :
    (X.rootsOfUnitySheaf m).obj.map e.op
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
        (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf m f)).hom.app
          (op (Scheme.Etale.mk (𝟙 Y)))
            (rootConstantSection m hm hζ Y aY (op (Scheme.Etale.mk (𝟙 Y))))) =
      rootConstantSection m hm hζ X (f ≫ aY) (op (Scheme.Etale.mk (𝟙 X))) := by
  apply X.injective_kernelι_app m (op (Scheme.Etale.mk (𝟙 X)))
  erw [NatTrans.naturality_apply (kernel.ι (m • 𝟙 X.gmSheaf)).hom]
  have h := congrArg ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _)
    (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι m f)
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_left, Scheme.upperStarGmSheafToGmSheaf,
    Equiv.apply_symm_apply] at h
  have hs := ConcreteCategory.congr_hom
    (congrArg (fun φ ↦ φ.hom.app (op (Scheme.Etale.mk (𝟙 Y)))) h)
    (rootConstantSection m hm hζ Y aY (op (Scheme.Etale.mk (𝟙 Y))))
  change (kernel.ι (m • 𝟙 X.gmSheaf)).hom.app
      (op (f.Etale.obj (Scheme.Etale.mk (𝟙 Y))))
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
          (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf m f)).hom.app
            (op (Scheme.Etale.mk (𝟙 Y)))
              (rootConstantSection m hm hζ Y aY (op (Scheme.Etale.mk (𝟙 Y))))) =
    (Scheme.gmSheafToLowerStarGmSheaf f).hom.app _ _ at hs
  erw [hs]
  apply ULift.ext
  apply Additive.toMul.injective
  apply Units.ext
  change e.left.appTop ((pullback.fst (𝟙 Y) f).appTop _) = _
  erw [rootConstantSection_val]
  have he : e.left ≫ pullback.fst (𝟙 Y) f = f := by
    rw [show pullback.fst (𝟙 Y) f = pullback.snd (𝟙 Y) f ≫ f by
      simpa using (pullback.condition (f := 𝟙 Y) (g := f))]
    have hes := e.w
    change e.left ≫ pullback.snd (𝟙 Y) f = 𝟙 X at hes
    rw [← Category.assoc, hes]
    exact Category.id_comp f
  have he' := congrArg (fun t : X ⟶ Y ↦
    t.appTop (((Scheme.ΓSpecIso (.of k)).inv ≫ aY.appTop) ζ)) he
  change e.left.appTop ((pullback.fst (𝟙 Y) f).appTop _) =
    f.appTop (((Scheme.ΓSpecIso (.of k)).inv ≫ aY.appTop) ζ) at he'
  erw [rootConstantSection_val]
  change e.left.appTop ((pullback.fst (𝟙 Y) f).appTop
      (((Scheme.ΓSpecIso (.of k)).inv ≫ aY.appTop) ζ)) =
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ aY).appTop) ζ
  rw [Scheme.Hom.comp_appTop]
  exact he'

private theorem abelianSectionClass_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (c : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ G)
    (e : Scheme.Etale.mk (𝟙 X) ⟶ f.Etale.obj (Scheme.Etale.mk (𝟙 Y)))
    (x : F.obj.obj (op (Scheme.Etale.mk (𝟙 Y)))) :
    relativeKummerPullbackOnCohomology f c 0
      ((Sheaf.H.equiv₀ F (MorphismProperty.Over.mkIdTerminal
        @AlgebraicGeometry.Etale Y)).symm x) =
    (Sheaf.H.equiv₀ G (MorphismProperty.Over.mkIdTerminal
      @AlgebraicGeometry.Etale X)).symm
      (G.obj.map e.op
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _ c).hom.app
          (op (Scheme.Etale.mk (𝟙 Y))) x)) := by
  let φ := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _ c
  have h := equiv₀_map_cohomologyMap f φ
    ((Sheaf.H.equiv₀ F (MorphismProperty.Over.mkIdTerminal
      @AlgebraicGeometry.Etale Y)).symm x)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y) e
  dsimp only [φ] at h
  rw [Equiv.symm_apply_apply, AddEquiv.apply_symm_apply, cohomologyMap_apply] at h
  apply (Sheaf.H.equiv₀ G (MorphismProperty.Over.mkIdTerminal
    @AlgebraicGeometry.Etale X)).injective
  rw [relativeKummerPullbackOnCohomology_apply, AddEquiv.apply_symm_apply,
    cohomologyMap_apply]
  exact h

private theorem moduleSectionClass_pullback
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (c : (upperStar (ModuleCat.{u + 1} A) f).obj F ⟶ G)
    (e : Scheme.Etale.mk (𝟙 X) ⟶ f.Etale.obj (Scheme.Etale.mk (𝟙 Y)))
    (x : F.obj.obj (op (Scheme.Etale.mk (𝟙 Y)))) :
    relativeKummerPullbackOnCohomology f (relativeKummerUnderlyingPullback A f c) 0
        (relativeKummerModuleSectionClass A Y F x) =
      relativeKummerModuleSectionClass A X G
        (G.obj.map e.op
          (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _ c).hom.app
            (op (Scheme.Etale.mk (𝟙 Y))) x)) := by
  have h := abelianSectionClass_pullback f (relativeKummerUnderlyingPullback A f c) e x
  rw [underlyingPullback_transpose] at h
  unfold relativeKummerModuleSectionClass
  exact h

private theorem relativeKummerConstant_pullback
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {k : Type u} [Field k] {ζ : k} (hζ : IsPrimitiveRoot ζ m)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ Spec (.of k))
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) (a : A) :
    relativeKummerCohomologyPullback A m hm hA f hY hX 0
        (relativeKummerConstant A m hm hA hζ Y aY a) =
      relativeKummerConstant A m hm hA hζ X (f ≫ aY) a := by
  let e : Scheme.Etale.mk (𝟙 X) ⟶ f.Etale.obj (Scheme.Etale.mk (𝟙 Y)) :=
    MorphismProperty.Over.homMk (pullback.lift f (𝟙 X) (by simp))
      (pullback.lift_snd _ _ _)
  unfold relativeKummerCohomologyPullback relativeKummerAbelianPullback
    relativeKummerConstant
  rw [moduleSectionClass_pullback A f _ e]
  congr 1
  change (Scheme.finiteEtaleTateLine X m A hA).obj.map e.op
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
      ((Scheme.finiteEtaleTwistPullbackData A m hm hA).c f hY hX 1).hom).hom.app _
        (Scheme.finiteEtaleTateOneGenerator A m Y hA _ a
          (rootConstantSection m hm hζ Y aY _))) =
    Scheme.finiteEtaleTateOneGenerator A m X hA _ a
      (rootConstantSection m hm hζ X (f ≫ aY) _)
  rw [(Scheme.finiteEtaleTwistPullbackData A m hm hA).laws.2.2.1,
    finiteRootComparison_eq]
  erw [finiteGenerator_naturality]
  exact congrArg (Scheme.finiteEtaleTateOneGenerator A m X hA _ a)
    (rootConstantSection_pullback m hm hζ f aY e)


end

section Statement
variable (k : Type u) [Field k] [hk : IsAlgClosed k]
  (ℓ N : ℕ) (hℓ : ℓ.Prime) (hN : 1 ≤ N) (hℓk : IsUnit (ℓ : k))
  (A : Type (u + 1)) [CommRing A] [Algebra (ZMod (ℓ ^ N)) A]
  [hfree : Module.Free (ZMod (ℓ ^ N)) A] [hfinite : Module.Finite (ZMod (ℓ ^ N)) A]
  (ζ : k) (hζ : IsPrimitiveRoot ζ (ℓ ^ N))
  (H : Type u) [CommRing H] [Algebra k H] [hH : IsStrictlyHenselianLocalRing H]

set_option linter.defProp false in
/-- The exponent is positive. This term is the existing arithmetic lemma applied to the
prime hypothesis, used only as a witness for the root-line API.
Source: blueprint r=l^N convention
(blueprint: lem-pur-relative-kummer-strict-local-invariance). -/
def relativeKummerPositive : 0 < ℓ ^ N := pow_pos hℓ.pos N

include hN hk hfree hfinite hH in
set_option linter.unusedSectionVars false in
/-- Strict-local invariance for both specified curves, the actual unit and canonical
pullback, constants, and the scalar-extended coordinate Kummer class.
Source: blueprint prop-pur-gm-relative-kummer.proof.md, Step 2; Stacks 0EYU and 03Q9
(blueprint: lem-pur-relative-kummer-strict-local-invariance).

Proof plan:
1. Factor X^r-1 using the primitive root. The Lagrange idempotents give the constant-root
   trivialization, whose scalar extension is a -> zeta tensor a, compatible with pullback.
2. For g:Spec H -> Spec k, the strict-henselization stalk formula and strictly henselian
   constant cohomology give vanishing above zero. Connectedness of Spec H identifies the
   actual constant-section unit in degree zero. Geometric-point extension, conservative
   stalks, module/abelian comparisons and the D+ cohomology criterion make eta_g invertible.
3. The structure map of either curve is smooth (restrict to D(t) for Gm), and g is affine,
   hence qcqs. Smooth base change gives an invertible canonical derived exchange; forget
   coefficients and use the comparison theorem to obtain the same assertion for A-modules.
4. Under h* adjoint Rh*, the exchange composed with f* eta_g transposes to the identity by
   the triangle identity. It is therefore the actual eta_h, which is invertible.
5. Apply derived global sections and the canonical Leray comparison. The derived-unit
   formula identifies this with the resolution-defined module pullback. In degree zero
   the section comparison sends zeta tensor a to the same constant for every a.
6. Pull back the ordinary abelian Kummer sequence. Powers and root inclusions commute
   with restriction, hence so does its boundary by the long exact ladder and naturality
   of the canonical SES triangle. The coefficient map z -> z tensor 1 commutes with
   pullback. The Laurent coordinate restricts to its base-changed coordinate, giving the
   final equality. No module structure on Gm and no finiteness assumption on H is used.
-/
theorem relativeKummer_strictLocal_invariance :
    (∀ b : Bool, RelativeKummerPullbackInvariance A (ℓ ^ N)
      (relativeKummerPositive ℓ N hℓ) (relativeKummerAnnihilator A (ℓ ^ N)) hζ
      (relativeKummerProjection k H b) (KummerLine.structureMap k b)
      (relativeKummerExponentUnit (ℓ ^ N) (relativeKummerFieldExponentUnit ℓ N hℓk)
        (KummerLine.curve k b) (KummerLine.structureMap k b))
      (relativeKummerExponentUnit (ℓ ^ N) (relativeKummerFieldExponentUnit ℓ N hℓk)
        (relativeKummerBaseCurve k H b) (relativeKummerBaseStructure k H b))) ∧
    RelativeKummerClassInvariance A (ℓ ^ N) (relativeKummerPositive ℓ N hℓ)
      (relativeKummerAnnihilator A (ℓ ^ N)) (relativeKummerProjection k H true)
      (relativeKummerExponentUnit (ℓ ^ N) (relativeKummerFieldExponentUnit ℓ N hℓk)
        (KummerLine.curve k true) (KummerLine.structureMap k true))
      (relativeKummerExponentUnit (ℓ ^ N) (relativeKummerFieldExponentUnit ℓ N hℓk)
        (relativeKummerBaseCurve k H true) (relativeKummerBaseStructure k H true))
      (KummerLine.coordinateUnit k) := by
  constructor
  · intro b
    have : Smooth (KummerLine.structureMap k b) := kummerLine_structure_smooth k b
    have : IsIso (relativeKummerUnit A (ℓ ^ N)
        (relativeKummerPositive ℓ N hℓ) (relativeKummerAnnihilator A (ℓ ^ N))
        (relativeKummerProjection k H b)
        (relativeKummerExponentUnit (ℓ ^ N) (relativeKummerFieldExponentUnit ℓ N hℓk)
          (KummerLine.curve k b) (KummerLine.structureMap k b))
        (relativeKummerExponentUnit (ℓ ^ N) (relativeKummerFieldExponentUnit ℓ N hℓk)
          (relativeKummerBaseCurve k H b) (relativeKummerBaseStructure k H b))) :=
      relativeKummerUnit_of_smooth A (ℓ ^ N)
      (relativeKummerPositive ℓ N hℓ) (relativeKummerAnnihilator A (ℓ ^ N))
      k H (relativeKummerFieldExponentUnit ℓ N hℓk) (KummerLine.structureMap k b)
      (relativeKummerExponentUnit (ℓ ^ N) (relativeKummerFieldExponentUnit ℓ N hℓk)
        (KummerLine.curve k b) (KummerLine.structureMap k b))
      (relativeKummerExponentUnit (ℓ ^ N) (relativeKummerFieldExponentUnit ℓ N hℓk)
        (relativeKummerBaseCurve k H b) (relativeKummerBaseStructure k H b))
    unfold RelativeKummerPullbackInvariance
    refine ⟨inferInstance, relativeKummerGlobalPullback_eq_unit .., ?_, ?_⟩
    · rw [← relativeKummerGlobalPullback_eq_unit]
      infer_instance
    · intro a
      exact relativeKummerConstant_pullback ..
  · exact relativeKummerClass_pullback ..

end Statement
end AlgebraicGeometry.Etale
