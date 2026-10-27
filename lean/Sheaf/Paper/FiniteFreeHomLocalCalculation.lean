module

public import Sheaf.Paper.FiniteFreeHomEvaluationCoordinates
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # Canonical finite-free Hom models and restriction square

Source: thm-coef-finite-hom proof paragraphs 2–3
(blueprint: def-sf-finite-free-hom-local-calculation).
These predicates describe specified maps; they assert no theorem about an arbitrary map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures
attribute [local instance] lisseHomModuleDerivedCategory

/-- The published Hom, uncurried only to share notation in the model calculation.
Source: internal Hom (blueprint: def-sf-finite-free-hom-local-calculation). -/
abbrev lisseHomRingHom (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  Functor.uncurry.obj (Etale.derivedHom (ModuleCat.{u + 1} A) T)

/-- The published derived inverse image, with its ring instance shared before specialization.
Source: etale restriction (blueprint: def-sf-finite-free-hom-local-calculation). -/
def lisseHomRestrictionFunctorRing (A : Type (u + 1)) [CommRing A]
    (T U : Scheme.{u}) (f : U ⟶ T) :
    Etale.DerivedCategoryModule A T ⥤ Etale.DerivedCategoryModule A U :=
  L(Etale.upperStar (ModuleCat.{u + 1} A) f)

/-- The type of a coefficient-Hom comparison; the theorem supplies its canonical arrow.
Source: comparison domain (blueprint: def-sf-finite-free-hom-local-calculation). -/
abbrev LisseHomComparisonType (A B : Type (u + 1)) [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (K N : Etale.DerivedCategoryModule A T) :=
  (Etale.scalarExtension φ T).obj ((lisseHomRingHom A T).obj (op K, N)) ⟶
    (lisseHomRingHom B T).obj
      (op ((Etale.scalarExtension φ T).obj K), (Etale.scalarExtension φ T).obj N)

/-- Reduction of vectors uses the canonical scalar unit, realized in degree zero.
Source: reduced basis (blueprint: def-sf-finite-free-hom-local-calculation). -/
def lisseHomReducedBasisRing (A B : Type (u + 1)) [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (t : ℕ) (K : Etale.DerivedCategoryModule A T)
    (basis : Fin t → ((_root_.DerivedCategory.singleFunctor _ 0).obj
      ((lisseHomConstantFunctor A T).obj (ModuleCat.of A A)) ⟶ K)) (i : Fin t) :
    (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((lisseHomConstantFunctor B T).obj (ModuleCat.of B B)) ⟶
        (Etale.scalarExtension φ T).obj K :=
  (lisseHomConstantUnitIso B T).inv ≫
    (Etale.ExceptionalCoefficients.unitIso φ T).inv ≫
      (Etale.scalarExtension φ T).map
        ((lisseHomConstantUnitIso A T).hom ≫ basis i)

/-- The scalar representative map, using the published derived counit.
Source: K-flat scalar model (blueprint: def-sf-finite-free-hom-local-calculation). -/
def lisseHomModelMapRing (A B : Type (u + 1)) [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : Etale.DerivedCategoryModule A T)
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (eP : N ≅ _root_.DerivedCategory.Q.obj P) :
    (Etale.scalarExtension φ T).obj N ⟶ _root_.DerivedCategory.Q.obj
      (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) :=
  (Etale.scalarExtension φ T).map eP.hom ≫ Etale.scalarExtensionRepresentative φ T P

/-- Source coordinates: reduced evaluation coordinates and the finite-product comparison.
Source: finite-free scalar model (blueprint: def-sf-finite-free-hom-local-calculation). -/
def lisseHomSourceCoordinatesRing (A B : Type (u + 1)) [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (t : ℕ) (K N : Etale.DerivedCategoryModule A T)
    (basis : Fin t → ((_root_.DerivedCategory.singleFunctor _ 0).obj
      ((lisseHomConstantFunctor A T).obj (ModuleCat.of A A)) ⟶ K))
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (eP : N ≅ _root_.DerivedCategory.Q.obj P) :
    (Etale.scalarExtension φ T).obj ((lisseHomRingHom A T).obj (op K, N)) ⟶
      ∏ᶜ (fun _ : Fin t ↦ _root_.DerivedCategory.Q.obj
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P)) :=
  (Etale.scalarExtension φ T).map (lisseHomCoordinatesRing A T t K N basis) ≫
    piComparison (Etale.scalarExtension φ T) (fun _ : Fin t ↦ N) ≫
      Limits.Pi.map (fun _ : Fin t ↦ lisseHomModelMapRing A B φ T N P eP)

/-- Target coordinates evaluate on the reduced standard vectors, in B-modules.
Source: finite-free scalar model (blueprint: def-sf-finite-free-hom-local-calculation). -/
def lisseHomTargetCoordinatesRing (A B : Type (u + 1)) [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (t : ℕ) (K N : Etale.DerivedCategoryModule A T)
    (basis : Fin t → ((_root_.DerivedCategory.singleFunctor _ 0).obj
      ((lisseHomConstantFunctor A T).obj (ModuleCat.of A A)) ⟶ K))
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (eP : N ≅ _root_.DerivedCategory.Q.obj P) :
    (lisseHomRingHom B T).obj
      (op ((Etale.scalarExtension φ T).obj K), (Etale.scalarExtension φ T).obj N) ⟶
      ∏ᶜ (fun _ : Fin t ↦ _root_.DerivedCategory.Q.obj
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P)) :=
  lisseHomCoordinatesRing B T t
      ((Etale.scalarExtension φ T).obj K) ((Etale.scalarExtension φ T).obj N)
      (lisseHomReducedBasisRing A B φ T t K basis) ≫
    Limits.Pi.map (fun _ : Fin t ↦ lisseHomModelMapRing A B φ T N P eP)

/-- Every bounded flat model identifies the specified comparison with the identity
in canonical evaluation coordinates, including rank zero. Linearity is in the types.
Source: local identity calculation (blueprint: def-sf-finite-free-hom-local-calculation). -/
def LisseHomLocalFreeCalculationRing (A B : Type (u + 1)) [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (K N : Etale.DerivedCategoryModule A T)
    (u : LisseHomComparisonType A B φ T K N) : Prop :=
  ∀ (t : ℕ) (e : K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((lisseHomConstantFunctor A T).obj (ModuleCat.of A (Fin t → A))))
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (c d : ℤ), Etale.IsBoundedFlatComplex A c d P →
    ∀ eP : N ≅ _root_.DerivedCategory.Q.obj P,
      IsIso (lisseHomCoordinatesRing A T t K N (lisseHomTrivializedBasis A T t K e) ≫
        Limits.Pi.map (fun _ : Fin t ↦ eP.hom)) ∧
      IsIso (lisseHomSourceCoordinatesRing A B φ T t K N
        (lisseHomTrivializedBasis A T t K e) P eP) ∧
      IsIso (lisseHomTargetCoordinatesRing A B φ T t K N
        (lisseHomTrivializedBasis A T t K e) P eP) ∧
      u ≫ lisseHomTargetCoordinatesRing A B φ T t K N
          (lisseHomTrivializedBasis A T t K e) P eP =
        lisseHomSourceCoordinatesRing A B φ T t K N
          (lisseHomTrivializedBasis A T t K e) P eP

/-- Hom restriction is the tensorator mate for derived etale inverse image.
Source: restriction and evaluation (blueprint: def-sf-finite-free-hom-local-calculation). -/
def lisseHomRestrictionGeneral
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {T U : Scheme.{u}} (f : U ⟶ T) [(Etale.upperStar A f).PreservesFlat]
    (K N : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    L(Etale.upperStar A f).obj (((Etale.derivedHom A T).obj (op K)).obj N) ⟶
      ((Etale.derivedHom A U).obj (op (L(Etale.upperStar A f).obj K))).obj
        (L(Etale.upperStar A f).obj N) :=
  letI := Etale.leftDerivedUpperStarMonoidal A f
  (Functor.LaxMonoidal.ihomComparison L(Etale.upperStar A f) K).natTrans.app N

/-- Ring-coefficient specialization of canonical Hom restriction.
Source: restriction (blueprint: def-sf-finite-free-hom-local-calculation). -/
abbrev lisseHomRestrictionRing (A : Type (u + 1)) [CommRing A]
    (T U : Scheme.{u}) (f : U ⟶ T) :=
  lisseHomRestrictionGeneral (ModuleCat.{u + 1} A) f

/-- The Hom restriction square, formed with shared functor and category data.
Source: restriction compatibility (blueprint: def-sf-finite-free-hom-local-calculation). -/
def LisseHomRestrictionSquare
    {C₁ C₂ C₃ C₄ : Type v} [Category.{w} C₁] [Category.{w} C₂]
    [Category.{w} C₃] [Category.{w} C₄]
    (H₁ : C₁ᵒᵖ × C₁ ⥤ C₁) (H₂ : C₂ᵒᵖ × C₂ ⥤ C₂)
    (H₃ : C₃ᵒᵖ × C₃ ⥤ C₃) (H₄ : C₄ᵒᵖ × C₄ ⥤ C₄)
    (F : C₁ ⥤ C₂) (G : C₃ ⥤ C₄) (R : C₁ ⥤ C₃) (S : C₂ ⥤ C₄)
    (σ : F ⋙ S ≅ R ⋙ G)
    (χ : ∀ K N : C₁, R.obj (H₁.obj (op K, N)) ⟶ H₃.obj (op (R.obj K), R.obj N))
    (ψ : ∀ K N : C₂, S.obj (H₂.obj (op K, N)) ⟶ H₄.obj (op (S.obj K), S.obj N))
    (K N : C₁)
    (uT : F.obj (H₁.obj (op K, N)) ⟶ H₂.obj (op (F.obj K), F.obj N))
    (uU : G.obj (H₃.obj (op (R.obj K), R.obj N)) ⟶
      H₄.obj (op (G.obj (R.obj K)), G.obj (R.obj N))) : Prop :=
  IsIso (χ K N) ∧ IsIso (ψ (F.obj K) (F.obj N)) ∧
  σ.hom.app (H₁.obj (op K, N)) ≫ G.map (χ K N) ≫ uU =
    S.map uT ≫ ψ (F.obj K) (F.obj N) ≫
      H₄.map (Prod.mkHom (σ.inv.app K).op (σ.hom.app N))

/-- The explicit restriction square for two specified comparison arrows, using the
canonical scalar/pullback isomorphism and canonical Hom restriction mates.
Source: restriction compatibility (blueprint: def-sf-finite-free-hom-local-calculation). -/
def LisseHomRestrictionCompatibilityRing (A B : Type (u + 1)) [CommRing A] [CommRing B]
    (φ : A →+* B) (T U : Scheme.{u}) (f : U ⟶ T) (K N : Etale.DerivedCategoryModule A T)
    (uT : LisseHomComparisonType A B φ T K N)
    (uU : LisseHomComparisonType A B φ U
      (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj K)
      (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj N)) : Prop :=
  LisseHomRestrictionSquare
    (lisseHomRingHom A T) (lisseHomRingHom B T)
    (lisseHomRingHom A U) (lisseHomRingHom B U)
    (Etale.scalarExtension φ T) (Etale.scalarExtension φ U)
    L(Etale.upperStar (ModuleCat.{u + 1} A) f)
    L(Etale.upperStar (ModuleCat.{u + 1} B) f)
    (Etale.scalarPullbackIso φ f)
    (lisseHomRestrictionRing A T U f) (lisseHomRestrictionRing B T U f)
    K N uT uU

end WeilConjectures
