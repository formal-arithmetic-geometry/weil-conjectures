/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Trace
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionConstructible
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarFlatModel
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformationOplax
public import WeilConjectures.SixFunctors.GeneralFiniteHomConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.FiniteSiteInternalHomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SmoothPurity.CoefFiniteHomIsomorphisms
public import WeilConjectures.SmoothPurity.CoefFiniteHomScalarTensorCoherence

/-! # Finite coefficient internal-Hom comparison

Source: latest blueprint, `thm-coef-finite-hom` (blueprint: thm-coef-finite-hom).
The statement is on the ordinary derived categories of constant coefficient module
sheaves on both sites.  Every comparison used below is a named canonical construction:
the fixed scalar extension, the transported ringed-derived monoidal core, the lax-monoidal
internal-Hom comparison (its evaluation transpose), and the published pro-etale/etale
site comparison.  The postponed proof is the finite-projective constructible calculation,
followed by the transpose, composition, identity, and site-transport checks.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w

open CategoryTheory Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
namespace WeilConjectures

/-- Ordinary uncompleted derived category of constant-ring module sheaves on the small
etale site. Source: thm-coef-finite-hom, statement (blueprint: thm-coef-finite-hom). -/
abbrev EtaleDerived (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :=
  DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat R))
/-- Ordinary uncompleted derived category on the small pro-etale site.
Source: thm-coef-finite-hom, statement (blueprint: thm-coef-finite-hom). -/
abbrev ProEtaleDerived (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :=
  DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat R))

/-- The original small pro-etale site has the ordinary coefficient universe size.
Source: finite coefficient size convention in thm-coef-finite-hom, statement
(blueprint: thm-coef-finite-hom). -/
local instance proEtSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1, u, u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

open AlgebraicGeometry.CoefficientScalarRepresentatives


/-- Native derived scalar extension on an ordinary module-sheaf site.
Source: Stacks 06YY, coefficient-change construction in thm-coef-finite-hom
(blueprint: thm-coef-finite-hom). -/
abbrev finiteHomScalar
    {S : Type (u + 1)} [Category.{u} S] [EssentiallySmall.{u + 1} S]
    (J : GrothendieckTopology S) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) := (ordinaryExtension J φ).leftDerivedFunctor

/-- Ordinary small-etale derived scalar extension.
Source: thm-coef-finite-hom, coefficient-change paragraph
(blueprint: thm-coef-finite-hom). -/
abbrev etaleScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (X : Scheme.{u})
    (φ : A →+* B) : EtaleDerived A X ⥤ EtaleDerived B X :=
  finiteHomScalar X.smallEtaleTopology φ

/-- Ordinary small-pro-etale derived scalar extension, canonically identified by its
scalar adjunction with the side-framework sheafExtendScalars.leftDerivedFunctor.
Source: thm-coef-finite-hom, coefficient-change paragraph
(blueprint: thm-coef-finite-hom). -/
abbrev proEtaleScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (X : Scheme.{u})
    (φ : A →+* B) : ProEtaleDerived A X ⥤ ProEtaleDerived B X :=
  finiteHomScalar (ProEt.topology X) φ

/-- The native scalar adjunction, with the actual exact derived restriction on the right.
Source: Stacks 06YY, thm-coef-finite-hom proof, scalar construction
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomScalarAdjunction
    {S : Type (u + 1)} [Category.{u} S] [EssentiallySmall.{u + 1} S]
    (J : GrothendieckTopology S) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) : finiteHomScalar J φ ⊣ Sheaf.derivedRestrictScalars J φ :=
  scalarDerivedAdjunction J φ

/-- Canonical scalar transitivity, conjugate to restriction transitivity.
Source: thm-coef-finite-hom, successive coefficient change
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomScalarComp
    {S : Type (u + 1)} [Category.{u} S] [EssentiallySmall.{u + 1} S]
    (J : GrothendieckTopology S)
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) :
    finiteHomScalar J φ ⋙ finiteHomScalar J ψ ≅ finiteHomScalar J (ψ.comp φ) :=
  Adjunction.leftAdjointCompIso (finiteHomScalarAdjunction J φ)
    (finiteHomScalarAdjunction J ψ) (finiteHomScalarAdjunction J (ψ.comp φ))
    (Sheaf.derivedRestrictScalarsCompIso J rfl)

/-- The identity restriction iso is the identity on sections.
Source: thm-coef-finite-hom, identity coefficient change
(blueprint: thm-coef-finite-hom). -/
def finiteHomRestrictionId
    {S : Type (u + 1)} [Category.{u} S] [EssentiallySmall.{u + 1} S]
    (J : GrothendieckTopology S) (A : Type (u + 1)) [CommRing A] :
    Sheaf.restrictScalars J (RingHom.id A) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun F ↦ (fullyFaithfulSheafToPresheaf J _).preimageIso
      (Functor.isoWhiskerLeft F.obj (ModuleCat.restrictScalarsId A) ≪≫
        Functor.rightUnitor F.obj))
    (by intros; apply (fullyFaithfulSheafToPresheaf J _).map_injective; ext; rfl)

/-- Canonical scalar identity iso, conjugate to identity restriction.
Source: thm-coef-finite-hom, identity coefficient change
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomScalarId
    {S : Type (u + 1)} [Category.{u} S] [EssentiallySmall.{u + 1} S]
    (J : GrothendieckTopology S) (A : Type (u + 1)) [CommRing A] :
    finiteHomScalar J (RingHom.id A) ≅ 𝟭 _ :=
  Adjunction.leftAdjointIdIso (finiteHomScalarAdjunction J (RingHom.id A))
    (Functor.mapDerivedCategoryNatIso (finiteHomRestrictionId J A) ≪≫
      Functor.mapDerivedCategoryIdIso _)

/-- Canonical ordinary scalar monoidality, conjugate to lax restriction.
Source: Stacks 03EK, thm-coef-finite-hom proof, tensor construction
(blueprint: thm-coef-finite-hom). -/
@[instance_reducible]
def finiteHomOrdinaryMonoidal
    {S : Type (u + 1)} [Category.{u} S] [EssentiallySmall.{u + 1} S]
    (J : GrothendieckTopology S) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) : (ordinaryExtension J φ).Monoidal :=
  composeAndSheafifyMonoidal J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

/-- Extract the core of the existing K-flat derived monoidal construction before
specializing its category instances. This is the same upstream oplax construction,
with its invertible tensor and unit maps; no monoidal data are chosen.
Source: Stacks 07A4, thm-coef-finite-hom proof, final paragraph
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomNativeDerivedCore
    {V : Type v} [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalPreadditive V]
    [MonoidalClosed V] [BraidedCategory V] [Abelian.HasFunctorialFlatResolution V]
    {W : Type w} [Category.{u + 1} W] [Abelian W]
    [IsGrothendieckAbelian.{u + 1} W] [MonoidalCategory W] [MonoidalPreadditive W]
    [MonoidalClosed W] [BraidedCategory W] [Abelian.HasFunctorialFlatResolution W]
    (F : V ⥤ W) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat]
    [F.IsLeftAdjoint] [F.Monoidal] : F.leftDerivedFunctor.CoreMonoidal := by
  letI := F.leftDerivedFunctorOplaxMonoidal
  letI := F.isIso_leftDerivedFunctorOplaxMonoidal_δ
  letI := F.isIso_leftDerivedFunctorOplaxMonoidal_η
  exact Functor.CoreMonoidal.ofOplaxMonoidal F.leftDerivedFunctor

/-- Ordinary etale scalar extension preserves flat sheaves, via the canonical
scalar-adjunction isomorphism with the side-framework scalar extension.
Source: Stacks 07A4, thm-coef-finite-hom proof, scalar tensor construction
(blueprint: thm-coef-finite-hom). -/
instance finiteHomEtalePreservesFlat
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (X : Scheme.{u})
    (φ : A →+* B) : (ordinaryExtension X.smallEtaleTopology φ).PreservesFlat := by
  let e := (ordinaryAdjunction X.smallEtaleTopology φ).leftAdjointUniq
    (AlgebraicGeometry.ProEtale.etaleSheafExtendScalarsAdjunction φ X)
  exact ⟨fun h ↦ ObjectProperty.prop_of_iso _ (e.app _).symm
    (AlgebraicGeometry.ProEtale.flat_etaleSheafExtendScalars_obj (φ := φ) (X := X) h)⟩

/-- The native etale scalar monoidal core, with tensor comparison obtained by
left-deriving the ordinary scalar oplax tensor map on flat resolutions.
Source: Stacks 07A4, thm-coef-finite-hom proof, final paragraph
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def etaleCore
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (X : Scheme.{u})
    (φ : A →+* B) : (etaleScalar X φ).CoreMonoidal := by
  let E := ordinaryExtension X.smallEtaleTopology φ
  letI : E.Monoidal := finiteHomOrdinaryMonoidal X.smallEtaleTopology φ
  letI : E.IsLeftAdjoint := (ordinaryAdjunction X.smallEtaleTopology φ).isLeftAdjoint
  letI : E.PreservesFlat := finiteHomEtalePreservesFlat X φ
  exact finiteHomNativeDerivedCore E

/-- The side-framework pro-etale scalar monoidal core. Adjunction uniqueness
transports leftDerivedSheafExtendScalarsMonoidal to the native ordinary scalar
representative; the normalization is fixed by the actual scalar unit.
Source: Stacks 07A4, thm-coef-finite-hom proof, final paragraph
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def proCore
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (X : Scheme.{u})
    (φ : A →+* B) : (proEtaleScalar X φ).CoreMonoidal := by
  letI : Algebra A B := φ.toAlgebra
  letI := AlgebraicGeometry.ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B X
  let adj := AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsAdjunction A B X
  let e := adj.leftAdjointUniq (finiteHomScalarAdjunction (ProEt.topology X) φ)
  letI := AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsMonoidal
    (R := A) (S := B) X
  exact Functor.Monoidal.coreMonoidalTransport e


/-- The canonical etale scalar tensor map, inverse of the normalized tensorator.
Source: thm-coef-finite-hom proof, final paragraph; Stacks 07A4
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
noncomputable def etaleTensor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (X : Scheme.{u})
    (φ : A →+* B) (K M : EtaleDerived A X) :
    (etaleScalar X φ).obj ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat A) X).obj K |>.obj M) ⟶
      ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat B) X).obj
        ((etaleScalar X φ).obj K)).obj ((etaleScalar X φ).obj M) :=
  (etaleCore X φ).μIso K M |>.inv

/-- The side-framework derived scalar tensor comparison on the pro-etale site.
Source: thm-coef-finite-hom proof, final paragraph; Stacks 07A4
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
noncomputable def proTensor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (X : Scheme.{u})
    (φ : A →+* B) (K M : ProEtaleDerived A X) :
    (proEtaleScalar X φ).obj
      ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat A) X).obj K |>.obj M) ⟶
      ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat B) X).obj
        ((proEtaleScalar X φ).obj K)).obj ((proEtaleScalar X φ).obj M) :=
  by
    change (proEtaleScalar X φ).obj (MonoidalCategoryStruct.tensorObj K M) ⟶ _
    exact (proCore X φ).μIso K M |>.inv

/-- The etale evaluation transpose using the inverse of etaleTensor.
Source: thm-coef-finite-hom proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
noncomputable def etaleHom
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (X : Scheme.{u})
    (φ : A →+* B) (K M : EtaleDerived A X) :
    (etaleScalar X φ).obj
      ((AlgebraicGeometry.Etale.derivedHom (ModuleCat A) X).obj (op K) |>.obj M) ⟶
      ((AlgebraicGeometry.Etale.derivedHom (ModuleCat B) X).obj
        (op ((etaleScalar X φ).obj K))).obj ((etaleScalar X φ).obj M) := by
  letI := (etaleCore X φ).toMonoidal
  exact (Functor.LaxMonoidal.ihomComparison (etaleScalar X φ) K).natTrans.app M

/-- The pro-etale evaluation transpose using the inverse of proTensor.
Source: thm-coef-finite-hom proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
noncomputable def proHom
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (X : Scheme.{u})
    (φ : A →+* B) (K M : ProEtaleDerived A X) :
    (proEtaleScalar X φ).obj
      ((AlgebraicGeometry.ProEtale.derivedHom (ModuleCat A) X).obj (op K) |>.obj M) ⟶
      ((AlgebraicGeometry.ProEtale.derivedHom (ModuleCat B) X).obj
        (op ((proEtaleScalar X φ).obj K))).obj ((proEtaleScalar X φ).obj M) := by
  letI : (proEtaleScalar X φ).Monoidal := (proCore X φ).toMonoidal
  exact (Functor.LaxMonoidal.ihomComparison (proEtaleScalar X φ) K).natTrans.app M

/-- Evaluation-transpose specification on the etale site.
Source: thm-coef-finite-hom proof, first paragraph (blueprint: thm-coef-finite-hom). -/
def etaleHomTranspose
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (X : Scheme.{u})
    (φ : A →+* B) (K M : EtaleDerived A X) : Prop := by
  letI := (etaleCore X φ).toMonoidal
  exact etaleHom X φ K M =
    MonoidalClosed.curry ((Functor.LaxMonoidal.μ (etaleScalar X φ) K
      (((AlgebraicGeometry.Etale.derivedHom (ModuleCat A) X).obj (op K)).obj M)) ≫
      (etaleScalar X φ).map ((ihom.ev K).app M))

/-- Evaluation-transpose specification on the pro-etale site.
Source: thm-coef-finite-hom proof, first paragraph (blueprint: thm-coef-finite-hom). -/
def proHomTranspose
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (X : Scheme.{u})
    (φ : A →+* B) (K M : ProEtaleDerived A X) : Prop := by
  letI : (proEtaleScalar X φ).Monoidal := (proCore X φ).toMonoidal
  exact proHom X φ K M =
    MonoidalClosed.curry ((Functor.LaxMonoidal.μ (proEtaleScalar X φ) K
      (((AlgebraicGeometry.ProEtale.derivedHom (ModuleCat A) X).obj (op K)).obj M)) ≫
      (proEtaleScalar X φ).map ((ihom.ev K).app M))

/-- Derived inverse image of the specified etale/pro-etale comparison morphism.
Source: thm-coef-finite-hom proof, final paragraph; Stacks 03EL
(blueprint: thm-coef-finite-hom). -/
def comparisonNu
    {R : Type (u + 1)} [CommRing R] [Finite R] (X : Scheme.{u}) :
    EtaleDerived R X ⥤ ProEtaleDerived R X :=
  (AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat R) X).mapDerivedCategory

/-- Native scalar extension is identified with the fixed scalar adjoint by its unit.
Source: Stacks 06YY, thm-coef-finite-hom proof, derived scalar construction
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomScalarFixedIso
    {S : Type (u + 1)} [Category.{u} S] [EssentiallySmall.{u + 1} S]
    (J : GrothendieckTopology S) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) : finiteHomScalar J φ ≅ extension J φ :=
  (finiteHomScalarAdjunction J φ).leftAdjointUniq (adjunction J φ)

/-- The scalar/site comparison is the derived mate of the ordinary upper-star/scalar
comparison, transported by the unique scalar adjunction isomorphisms. The recorded
comparisonIso computes exactly this mate on K-flat representatives.
Source: Stacks 03EL and 07A4, thm-coef-finite-hom proof, final paragraph
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomRhoIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (X : Scheme.{u}) (φ : A →+* B) :
    comparisonNu (R := A) X ⋙ proEtaleScalar X φ ≅
      etaleScalar X φ ⋙ comparisonNu (R := B) X :=
  Functor.isoWhiskerLeft _ (finiteHomScalarFixedIso (ProEt.topology X) φ) ≪≫
    comparisonIso X φ ≪≫
    Functor.isoWhiskerRight (finiteHomScalarFixedIso X.smallEtaleTopology φ).symm _


/-- Inverse of the node's rho: scalar after site pullback to site after scalar.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: thm-coef-finite-hom). -/
def canonicalRho
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (X : Scheme.{u}) (φ : A →+* B) (T : EtaleDerived A X) :=
  (finiteHomRhoIso X φ).hom.app T

/-- The node's rho, with source nu_B(T_B).
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: thm-coef-finite-hom). -/
def canonicalRhoInv
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (X : Scheme.{u}) (φ : A →+* B) (T : EtaleDerived A X) :=
  (finiteHomRhoIso X φ).inv.app T

/-- The specified evaluation-defined site-Hom comparison, without an isomorphism
assertion. Source: thm-coef-finite-hom proof, final paragraph
(blueprint: thm-coef-finite-hom). -/
noncomputable def comparisonBeta
    {R : Type (u + 1)} [CommRing R] [Finite R] (X : Scheme.{u})
    (K M : EtaleDerived R X) :
    (comparisonNu X).obj
      ((AlgebraicGeometry.Etale.derivedHom (ModuleCat R) X).obj (op K) |>.obj M) ⟶
      ((AlgebraicGeometry.ProEtale.derivedHom (ModuleCat R) X).obj
        (op ((comparisonNu X).obj K))).obj ((comparisonNu X).obj M) :=
  AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat R) X K M

/-- Bounded constructibility and Tor amplitude tested against every degree-zero
module sheaf. Source: thm-coef-finite-hom statement (blueprint: thm-coef-finite-hom). -/
def etaleCTF (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    ObjectProperty (EtaleDerived A X) :=
  AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible A X ⊓
    DerivedCategory.finiteTorAmplitude (Sheaf X.smallEtaleTopology (ModuleCat A))

/-- Bounded constructibility and finite Tor amplitude on the pro-etale site.
Source: thm-coef-finite-hom statement (blueprint: thm-coef-finite-hom). -/
def proEtaleCTF (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    ObjectProperty (ProEtaleDerived A X) :=
  AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} A) X

/-- The actual Koszul braiding descending from the homotopy category. This merely
specializes the upstream DerivedMonoidal.braiding' through its compact
abstract-category wrapper. Source: Stacks 07A4, thm-coef-finite-hom proof, final paragraph
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomSymmetry
    {S : Type (u + 1)} [Category.{u} S] [EssentiallySmall.{u + 1} S]
    (J : GrothendieckTopology S) (A : Type (u + 1)) [CommRing A]
    (K M : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) :
    K ⊗ M ≅ M ⊗ K := by
  letI := DerivedCategory.braidedCategory' (Sheaf J (ModuleCat.{u + 1} A))
  exact β_ K M

/-- Evaluation in the H(K,M) tensor K order used in the blueprint, obtained from
the upstream left-closed evaluation by the canonical signed symmetry.
Source: thm-coef-finite-hom statement and proof, first paragraph
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomRightEvaluation
    {S : Type (u + 1)} [Category.{u} S] [EssentiallySmall.{u + 1} S]
    (J : GrothendieckTopology S) (A : Type (u + 1)) [CommRing A]
    (K M : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) :
    (ihom K).obj M ⊗ K ⟶ M :=
  (finiteHomSymmetry J A ((ihom K).obj M) K).hom ≫ (ihom.ev K).app M

section LawPredicates

variable {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C]
  (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)

/-- The `tensorEtale_iso` clause of the finite-Hom comparison, stated as its full equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensorEtale_iso : Prop :=
  ∀ K M, IsIso (etaleTensor X φ K M)

/-- The `tensorPro_iso` clause of the finite-Hom comparison, stated as its full equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensorPro_iso : Prop :=
  ∀ K M, IsIso (proTensor X φ K M)

/-- The `vEtale_iso` clause of the finite-Hom comparison, stated as its full equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_vEtale_iso : Prop :=
  ∀ K M, etaleCTF A X K → etaleCTF A X M → IsIso (etaleHom X φ K M)

/-- The `vPro_iso` clause of the finite-Hom comparison, stated as its full equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_vPro_iso : Prop :=
  ∀ K M, proEtaleCTF A X K → proEtaleCTF A X M → IsIso (proHom X φ K M)

/-- The `tensor_associator_etale` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensor_associator_etale : Prop :=
  ∀ (K M N : EtaleDerived A X),
    MonoidalCategoryStruct.whiskerRight ((etaleCore X φ).μIso K M).hom ((etaleScalar X φ).obj N) ≫
      ((etaleCore X φ).μIso (MonoidalCategoryStruct.tensorObj K M) N).hom ≫
        (etaleScalar X φ).map (MonoidalCategoryStruct.associator K M N).hom =
    (MonoidalCategoryStruct.associator ((etaleScalar X φ).obj K)
      ((etaleScalar X φ).obj M) ((etaleScalar X φ).obj N)).hom ≫
      MonoidalCategoryStruct.whiskerLeft ((etaleScalar X φ).obj K) ((etaleCore X φ).μIso M N).hom ≫
        ((etaleCore X φ).μIso K (MonoidalCategoryStruct.tensorObj M N)).hom

/-- The `tensor_left_unit_etale` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensor_left_unit_etale : Prop :=
  ∀ (K : EtaleDerived A X),
    (MonoidalCategoryStruct.leftUnitor ((etaleScalar X φ).obj K)).hom =
      MonoidalCategoryStruct.whiskerRight (etaleCore X φ).εIso.hom ((etaleScalar X φ).obj K) ≫
        ((etaleCore X φ).μIso (MonoidalCategoryStruct.tensorUnit (EtaleDerived A X)) K).hom ≫
          (etaleScalar X φ).map (MonoidalCategoryStruct.leftUnitor K).hom

/-- The `tensor_right_unit_etale` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensor_right_unit_etale : Prop :=
  ∀ (K : EtaleDerived A X),
    (MonoidalCategoryStruct.rightUnitor ((etaleScalar X φ).obj K)).hom =
      MonoidalCategoryStruct.whiskerLeft ((etaleScalar X φ).obj K) (etaleCore X φ).εIso.hom ≫
        ((etaleCore X φ).μIso K (MonoidalCategoryStruct.tensorUnit (EtaleDerived A X))).hom ≫
          (etaleScalar X φ).map (MonoidalCategoryStruct.rightUnitor K).hom

/-- The `tensor_associator_pro` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensor_associator_pro : Prop :=
  ∀ (K M N : ProEtaleDerived A X),
    MonoidalCategoryStruct.whiskerRight ((proCore X φ).μIso K M).hom ((proEtaleScalar X φ).obj N) ≫
      ((proCore X φ).μIso (MonoidalCategoryStruct.tensorObj K M) N).hom ≫
        (proEtaleScalar X φ).map (MonoidalCategoryStruct.associator K M N).hom =
    (MonoidalCategoryStruct.associator ((proEtaleScalar X φ).obj K)
      ((proEtaleScalar X φ).obj M) ((proEtaleScalar X φ).obj N)).hom ≫
      MonoidalCategoryStruct.whiskerLeft ((proEtaleScalar X φ).obj K) ((proCore X φ).μIso M N).hom ≫
        ((proCore X φ).μIso K (MonoidalCategoryStruct.tensorObj M N)).hom

/-- The `tensor_left_unit_pro` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensor_left_unit_pro : Prop :=
  ∀ (K : ProEtaleDerived A X),
    (MonoidalCategoryStruct.leftUnitor ((proEtaleScalar X φ).obj K)).hom =
      MonoidalCategoryStruct.whiskerRight (proCore X φ).εIso.hom ((proEtaleScalar X φ).obj K) ≫
        ((proCore X φ).μIso (MonoidalCategoryStruct.tensorUnit (ProEtaleDerived A X)) K).hom ≫
          (proEtaleScalar X φ).map (MonoidalCategoryStruct.leftUnitor K).hom

/-- The `tensor_right_unit_pro` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensor_right_unit_pro : Prop :=
  ∀ (K : ProEtaleDerived A X),
    (MonoidalCategoryStruct.rightUnitor ((proEtaleScalar X φ).obj K)).hom =
      MonoidalCategoryStruct.whiskerLeft ((proEtaleScalar X φ).obj K) (proCore X φ).εIso.hom ≫
        ((proCore X φ).μIso K (MonoidalCategoryStruct.tensorUnit (ProEtaleDerived A X))).hom ≫
          (proEtaleScalar X φ).map (MonoidalCategoryStruct.rightUnitor K).hom

/-- The `tensor_symmetry_etale` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensor_symmetry_etale : Prop :=
  ∀ (K M : EtaleDerived A X),
    (finiteHomSymmetry X.smallEtaleTopology B
      ((etaleScalar X φ).obj K) ((etaleScalar X φ).obj M)).hom ≫
      ((etaleCore X φ).μIso M K).hom =
    ((etaleCore X φ).μIso K M).hom ≫
      (etaleScalar X φ).map
        (finiteHomSymmetry X.smallEtaleTopology A K M).hom

/-- The `tensor_symmetry_pro` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensor_symmetry_pro : Prop :=
  ∀ (K M : ProEtaleDerived A X),
    (finiteHomSymmetry (ProEt.topology X) B
      ((proEtaleScalar X φ).obj K) ((proEtaleScalar X φ).obj M)).hom ≫
      ((proCore X φ).μIso M K).hom =
    ((proCore X φ).μIso K M).hom ≫
      (proEtaleScalar X φ).map
        (finiteHomSymmetry (ProEt.topology X) A K M).hom

/-- The `tensor_naturality_etale` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensor_naturality_etale : Prop :=
  ∀ {K K' M M' : EtaleDerived A X} (f : K ⟶ K') (g : M ⟶ M'),
    (etaleScalar X φ).map (f ⊗ₘ g) ≫ etaleTensor X φ K' M' =
      etaleTensor X φ K M ≫ ((etaleScalar X φ).map f ⊗ₘ (etaleScalar X φ).map g)

/-- The `evaluation_transpose_etale` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_evaluation_transpose_etale : Prop :=
  ∀ (K M : EtaleDerived A X), etaleHomTranspose X φ K M

/-- The `tensor_naturality_pro` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensor_naturality_pro : Prop :=
  ∀ {K K' M M' : ProEtaleDerived A X} (f : K ⟶ K') (g : M ⟶ M'),
    (proEtaleScalar X φ).map (f ⊗ₘ g) ≫ proTensor X φ K' M' =
      proTensor X φ K M ≫ ((proEtaleScalar X φ).map f ⊗ₘ (proEtaleScalar X φ).map g)

/-- The `evaluation_transpose_pro` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_evaluation_transpose_pro : Prop :=
  ∀ (K M : ProEtaleDerived A X), proHomTranspose X φ K M

/-- The `successive_etale` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_successive_etale : Prop :=
  ∀ K M,
    (finiteHomScalarComp X.smallEtaleTopology φ ψ).hom.app ((ihom K).obj M) ≫
        etaleHom X (ψ.comp φ) K M =
      (etaleScalar X ψ).map (etaleHom X φ K M) ≫
        etaleHom X ψ ((etaleScalar X φ).obj K) ((etaleScalar X φ).obj M) ≫
        (MonoidalClosed.pre ((finiteHomScalarComp X.smallEtaleTopology φ ψ).inv.app K)).app
          ((etaleScalar X ψ).obj ((etaleScalar X φ).obj M)) ≫
        (ihom ((etaleScalar X (ψ.comp φ)).obj K)).map
          ((finiteHomScalarComp X.smallEtaleTopology φ ψ).hom.app M)

/-- The `identity_etale` clause of the finite-Hom comparison, stated as its full equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_identity_etale : Prop :=
  ∀ K M,
    (finiteHomScalarId X.smallEtaleTopology A).hom.app ((ihom K).obj M) =
      etaleHom X (RingHom.id A) K M ≫
        (MonoidalClosed.pre ((finiteHomScalarId X.smallEtaleTopology A).inv.app K)).app
          ((etaleScalar X (RingHom.id A)).obj M) ≫
        (ihom K).map ((finiteHomScalarId X.smallEtaleTopology A).hom.app M)

/-- The `evaluation_etale` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_evaluation_etale : Prop :=
  ∀ K M,
    ((etaleScalar X φ).obj K ◁ etaleHom X φ K M) ≫
        (ihom.ev ((etaleScalar X φ).obj K)).app ((etaleScalar X φ).obj M) =
      ((etaleCore X φ).μIso K ((ihom K).obj M)).hom ≫
        (etaleScalar X φ).map ((ihom.ev K).app M)

/-- The `evaluation_right_etale` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_evaluation_right_etale : Prop :=
  ∀ K M,
    (etaleHom X φ K M ⊗ₘ 𝟙 ((etaleScalar X φ).obj K)) ≫
        finiteHomRightEvaluation X.smallEtaleTopology B
          ((etaleScalar X φ).obj K) ((etaleScalar X φ).obj M) =
      ((etaleCore X φ).μIso ((ihom K).obj M) K).hom ≫
        (etaleScalar X φ).map (finiteHomRightEvaluation X.smallEtaleTopology A K M)

/-- The `unique_transpose_etale` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_unique_transpose_etale : Prop :=
  ∀ K M
      (w : (etaleScalar X φ).obj ((ihom K).obj M) ⟶
        (ihom ((etaleScalar X φ).obj K)).obj ((etaleScalar X φ).obj M)),
    ((etaleScalar X φ).obj K ◁ w) ≫
        (ihom.ev ((etaleScalar X φ).obj K)).app ((etaleScalar X φ).obj M) =
      ((etaleCore X φ).μIso K ((ihom K).obj M)).hom ≫
        (etaleScalar X φ).map ((ihom.ev K).app M) → w = etaleHom X φ K M

/-- The `naturality_etale` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_naturality_etale : Prop :=
  ∀ {K K' M M' : EtaleDerived A X} (f : K' ⟶ K) (g : M ⟶ M'),
    (etaleScalar X φ).map ((MonoidalClosed.pre f).app M ≫ (ihom K').map g) ≫
        etaleHom X φ K' M' =
      etaleHom X φ K M ≫ (MonoidalClosed.pre ((etaleScalar X φ).map f)).app
        ((etaleScalar X φ).obj M) ≫ (ihom ((etaleScalar X φ).obj K')).map
          ((etaleScalar X φ).map g)

/-- The `tensor_hom_adjunction_etale` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensor_hom_adjunction_etale : Prop :=
  ∀ (K U M : EtaleDerived A X) (f : K ⊗ U ⟶ M),
    (etaleScalar X φ).map (MonoidalClosed.curry f) ≫ etaleHom X φ K M =
      MonoidalClosed.curry (((etaleCore X φ).μIso K U).hom ≫ (etaleScalar X φ).map f)

/-- The `composition_etale` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_composition_etale : Prop :=
  ∀ K M N,
    (etaleScalar X φ).map (MonoidalClosed.comp K M N) ≫ etaleHom X φ K N =
      etaleTensor X φ ((ihom K).obj M) ((ihom M).obj N) ≫
        (etaleHom X φ K M ⊗ₘ etaleHom X φ M N) ≫
        MonoidalClosed.comp ((etaleScalar X φ).obj K) ((etaleScalar X φ).obj M)
          ((etaleScalar X φ).obj N)

/-- The `tensor_successive_etale` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensor_successive_etale : Prop :=
  ∀ K M,
    (finiteHomScalarComp X.smallEtaleTopology φ ψ).hom.app (K ⊗ M) ≫
        etaleTensor X (ψ.comp φ) K M =
      (etaleScalar X ψ).map (etaleTensor X φ K M) ≫
        etaleTensor X ψ ((etaleScalar X φ).obj K) ((etaleScalar X φ).obj M) ≫
        ((finiteHomScalarComp X.smallEtaleTopology φ ψ).hom.app K ⊗ₘ
          (finiteHomScalarComp X.smallEtaleTopology φ ψ).hom.app M)

/-- The unit component of successive scalar monoidality on the etale site.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_unit_successive_etale : Prop :=
  (finiteHomScalarComp X.smallEtaleTopology φ ψ).hom.app (𝟙_ (EtaleDerived A X)) ≫
      (etaleCore X (ψ.comp φ)).εIso.inv =
    (etaleScalar X ψ).map (etaleCore X φ).εIso.inv ≫ (etaleCore X ψ).εIso.inv

/-- The `tensor_identity_etale` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensor_identity_etale : Prop :=
  ∀ K M,
    etaleTensor X (RingHom.id A) K M ≫
        ((finiteHomScalarId X.smallEtaleTopology A).hom.app K ⊗ₘ
          (finiteHomScalarId X.smallEtaleTopology A).hom.app M) =
      (finiteHomScalarId X.smallEtaleTopology A).hom.app (K ⊗ M)

/-- The unit component of identity scalar monoidality on the etale site.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_unit_identity_etale : Prop :=
  (etaleCore X (RingHom.id A)).εIso.inv =
    (finiteHomScalarId X.smallEtaleTopology A).hom.app (𝟙_ (EtaleDerived A X))

/-- The `successive_pro` clause of the finite-Hom comparison, stated as its full equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_successive_pro : Prop :=
  ∀ K M,
    (finiteHomScalarComp (ProEt.topology X) φ ψ).hom.app ((ihom K).obj M) ≫
        proHom X (ψ.comp φ) K M =
      (proEtaleScalar X ψ).map (proHom X φ K M) ≫
        proHom X ψ ((proEtaleScalar X φ).obj K) ((proEtaleScalar X φ).obj M) ≫
        (MonoidalClosed.pre ((finiteHomScalarComp (ProEt.topology X) φ ψ).inv.app K)).app
          ((proEtaleScalar X ψ).obj ((proEtaleScalar X φ).obj M)) ≫
        (ihom ((proEtaleScalar X (ψ.comp φ)).obj K)).map
          ((finiteHomScalarComp (ProEt.topology X) φ ψ).hom.app M)

/-- The `identity_pro` clause of the finite-Hom comparison, stated as its full equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_identity_pro : Prop :=
  ∀ K M,
    (finiteHomScalarId (ProEt.topology X) A).hom.app ((ihom K).obj M) =
      proHom X (RingHom.id A) K M ≫
        (MonoidalClosed.pre ((finiteHomScalarId (ProEt.topology X) A).inv.app K)).app
          ((proEtaleScalar X (RingHom.id A)).obj M) ≫
        (ihom K).map ((finiteHomScalarId (ProEt.topology X) A).hom.app M)

/-- The `evaluation_pro` clause of the finite-Hom comparison, stated as its full equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_evaluation_pro : Prop :=
  ∀ K M,
    ((proEtaleScalar X φ).obj K ◁ proHom X φ K M) ≫
        (ihom.ev ((proEtaleScalar X φ).obj K)).app ((proEtaleScalar X φ).obj M) =
      ((proCore X φ).μIso K ((ihom K).obj M)).hom ≫
        (proEtaleScalar X φ).map ((ihom.ev K).app M)

/-- The `evaluation_right_pro` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_evaluation_right_pro : Prop :=
  ∀ K M,
    (proHom X φ K M ⊗ₘ 𝟙 ((proEtaleScalar X φ).obj K)) ≫
        finiteHomRightEvaluation (ProEt.topology X) B
          ((proEtaleScalar X φ).obj K) ((proEtaleScalar X φ).obj M) =
      ((proCore X φ).μIso ((ihom K).obj M) K).hom ≫
        (proEtaleScalar X φ).map (finiteHomRightEvaluation (ProEt.topology X) A K M)

/-- The `unique_transpose_pro` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_unique_transpose_pro : Prop :=
  ∀ K M
      (w : (proEtaleScalar X φ).obj ((ihom K).obj M) ⟶
        (ihom ((proEtaleScalar X φ).obj K)).obj ((proEtaleScalar X φ).obj M)),
    ((proEtaleScalar X φ).obj K ◁ w) ≫
        (ihom.ev ((proEtaleScalar X φ).obj K)).app ((proEtaleScalar X φ).obj M) =
      ((proCore X φ).μIso K ((ihom K).obj M)).hom ≫
        (proEtaleScalar X φ).map ((ihom.ev K).app M) → w = proHom X φ K M

/-- The `naturality_pro` clause of the finite-Hom comparison, stated as its full equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_naturality_pro : Prop :=
  ∀ {K K' M M' : ProEtaleDerived A X} (f : K' ⟶ K) (g : M ⟶ M'),
    (proEtaleScalar X φ).map ((MonoidalClosed.pre f).app M ≫ (ihom K').map g) ≫
        proHom X φ K' M' =
      proHom X φ K M ≫ (MonoidalClosed.pre ((proEtaleScalar X φ).map f)).app
        ((proEtaleScalar X φ).obj M) ≫ (ihom ((proEtaleScalar X φ).obj K')).map
          ((proEtaleScalar X φ).map g)

/-- The `tensor_hom_adjunction_pro` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensor_hom_adjunction_pro : Prop :=
  ∀ (K U M : ProEtaleDerived A X) (f : K ⊗ U ⟶ M),
    (proEtaleScalar X φ).map (MonoidalClosed.curry f) ≫ proHom X φ K M =
      MonoidalClosed.curry (((proCore X φ).μIso K U).hom ≫ (proEtaleScalar X φ).map f)

/-- The `composition_pro` clause of the finite-Hom comparison, stated as its full equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_composition_pro : Prop :=
  ∀ K M N,
    (proEtaleScalar X φ).map (MonoidalClosed.comp K M N) ≫ proHom X φ K N =
      proTensor X φ ((ihom K).obj M) ((ihom M).obj N) ≫
        (proHom X φ K M ⊗ₘ proHom X φ M N) ≫
        MonoidalClosed.comp ((proEtaleScalar X φ).obj K) ((proEtaleScalar X φ).obj M)
          ((proEtaleScalar X φ).obj N)

/-- The `tensor_successive_pro` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensor_successive_pro : Prop :=
  ∀ K M,
    (finiteHomScalarComp (ProEt.topology X) φ ψ).hom.app (K ⊗ M) ≫
        proTensor X (ψ.comp φ) K M =
      (proEtaleScalar X ψ).map (proTensor X φ K M) ≫
        proTensor X ψ ((proEtaleScalar X φ).obj K) ((proEtaleScalar X φ).obj M) ≫
        ((finiteHomScalarComp (ProEt.topology X) φ ψ).hom.app K ⊗ₘ
          (finiteHomScalarComp (ProEt.topology X) φ ψ).hom.app M)

/-- The unit component of successive scalar monoidality on the pro site.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_unit_successive_pro : Prop :=
  (finiteHomScalarComp (ProEt.topology X) φ ψ).hom.app (𝟙_ (ProEtaleDerived A X)) ≫
      (proCore X (ψ.comp φ)).εIso.inv =
    (proEtaleScalar X ψ).map (proCore X φ).εIso.inv ≫ (proCore X ψ).εIso.inv

/-- The `tensor_identity_pro` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_tensor_identity_pro : Prop :=
  ∀ K M,
    proTensor X (RingHom.id A) K M ≫
        ((finiteHomScalarId (ProEt.topology X) A).hom.app K ⊗ₘ
          (finiteHomScalarId (ProEt.topology X) A).hom.app M) =
      (finiteHomScalarId (ProEt.topology X) A).hom.app (K ⊗ M)

/-- The unit component of identity scalar monoidality on the pro site.
Source: thm-coef-finite-hom proof, final paragraph
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_unit_identity_pro : Prop :=
  (proCore X (RingHom.id A)).εIso.inv =
    (finiteHomScalarId (ProEt.topology X) A).hom.app (𝟙_ (ProEtaleDerived A X))

/-- The `homEtale_source_ctf` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_homEtale_source_ctf : Prop :=
  ∀ K M,
    etaleCTF A X K → etaleCTF A X M →
      etaleCTF B X ((etaleScalar X φ).obj ((ihom K).obj M))

/-- The `homEtale_target_ctf` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_homEtale_target_ctf : Prop :=
  ∀ K M, etaleCTF A X K → etaleCTF A X M →
    etaleCTF B X (((AlgebraicGeometry.Etale.derivedHom (ModuleCat B) X).obj
      (op ((etaleScalar X φ).obj K))).obj ((etaleScalar X φ).obj M))

/-- The `homPro_source_ctf` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_homPro_source_ctf : Prop :=
  ∀ K M,
    proEtaleCTF A X K → proEtaleCTF A X M →
      proEtaleCTF B X ((proEtaleScalar X φ).obj ((ihom K).obj M))

/-- The `homPro_target_ctf` clause of the finite-Hom comparison, stated as its full
  equation/property.
Source: thm-coef-finite-hom statement and proof, first and final paragraphs
(blueprint: thm-coef-finite-hom). -/
@[irreducible]
def finiteHomLaw_homPro_target_ctf : Prop :=
  ∀ K M, proEtaleCTF A X K → proEtaleCTF A X M →
    proEtaleCTF B X (((AlgebraicGeometry.ProEtale.derivedHom (ModuleCat B) X).obj
      (op ((proEtaleScalar X φ).obj K))).obj ((proEtaleScalar X φ).obj M))

end LawPredicates

/-- The canonical tensor/Hom comparisons on both ordinary finite-coefficient sites.
Source: latest blueprint thm-coef-finite-hom.md and its proof, first and final
paragraphs (blueprint: thm-coef-finite-hom). The scalar composition and identity
isos are the conjugates of restriction transitivity and its identity. The successive
fields compare the actual A → C transpose with the two-step A → B → C transpose;
the tensor and unit fields state monoidality of those isos. The evaluation equation
and unique-transpose implication specify v, and the CTF fields specify its endpoint. -/
structure FiniteCoefficientHomLaws
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C) where
  tensorEtale_iso : finiteHomLaw_tensorEtale_iso X φ
  tensorPro_iso : finiteHomLaw_tensorPro_iso X φ
  vEtale_iso : finiteHomLaw_vEtale_iso X φ
  vPro_iso : finiteHomLaw_vPro_iso X φ
  tensor_associator_etale : finiteHomLaw_tensor_associator_etale X φ
  tensor_left_unit_etale : finiteHomLaw_tensor_left_unit_etale X φ
  tensor_right_unit_etale : finiteHomLaw_tensor_right_unit_etale X φ
  tensor_associator_pro : finiteHomLaw_tensor_associator_pro X φ
  tensor_left_unit_pro : finiteHomLaw_tensor_left_unit_pro X φ
  tensor_right_unit_pro : finiteHomLaw_tensor_right_unit_pro X φ
  tensor_symmetry_etale : finiteHomLaw_tensor_symmetry_etale X φ
  tensor_symmetry_pro : finiteHomLaw_tensor_symmetry_pro X φ
  tensor_naturality_etale : finiteHomLaw_tensor_naturality_etale X φ
  evaluation_transpose_etale : finiteHomLaw_evaluation_transpose_etale X φ
  tensor_naturality_pro : finiteHomLaw_tensor_naturality_pro X φ
  evaluation_transpose_pro : finiteHomLaw_evaluation_transpose_pro X φ
  successive_etale : finiteHomLaw_successive_etale X φ ψ
  identity_etale : finiteHomLaw_identity_etale (A := A) X
  evaluation_etale : finiteHomLaw_evaluation_etale X φ
  evaluation_right_etale : finiteHomLaw_evaluation_right_etale X φ
  unique_transpose_etale : finiteHomLaw_unique_transpose_etale X φ
  naturality_etale : finiteHomLaw_naturality_etale X φ
  tensor_hom_adjunction_etale : finiteHomLaw_tensor_hom_adjunction_etale X φ
  composition_etale : finiteHomLaw_composition_etale X φ
  tensor_successive_etale : finiteHomLaw_tensor_successive_etale X φ ψ
  unit_successive_etale : finiteHomLaw_unit_successive_etale X φ ψ
  tensor_identity_etale : finiteHomLaw_tensor_identity_etale (A := A) X
  unit_identity_etale : finiteHomLaw_unit_identity_etale (A := A) X
  successive_pro : finiteHomLaw_successive_pro X φ ψ
  identity_pro : finiteHomLaw_identity_pro (A := A) X
  evaluation_pro : finiteHomLaw_evaluation_pro X φ
  evaluation_right_pro : finiteHomLaw_evaluation_right_pro X φ
  unique_transpose_pro : finiteHomLaw_unique_transpose_pro X φ
  naturality_pro : finiteHomLaw_naturality_pro X φ
  tensor_hom_adjunction_pro : finiteHomLaw_tensor_hom_adjunction_pro X φ
  composition_pro : finiteHomLaw_composition_pro X φ
  tensor_successive_pro : finiteHomLaw_tensor_successive_pro X φ ψ
  unit_successive_pro : finiteHomLaw_unit_successive_pro X φ ψ
  tensor_identity_pro : finiteHomLaw_tensor_identity_pro (A := A) X
  unit_identity_pro : finiteHomLaw_unit_identity_pro (A := A) X
  homEtale_source_ctf : finiteHomLaw_homEtale_source_ctf X φ
  homEtale_target_ctf : finiteHomLaw_homEtale_target_ctf X φ
  homPro_source_ctf : finiteHomLaw_homPro_source_ctf X φ
  homPro_target_ctf : finiteHomLaw_homPro_target_ctf X φ

private theorem finiteHomComparisonNaturality
    {V W : Type*} [Category V] [Category W]
    [MonoidalCategory V] [MonoidalCategory W] [MonoidalClosed V] [MonoidalClosed W]
    (F : V ⥤ W) [F.Monoidal] {K K' M M' : V} (f : K' ⟶ K) (g : M ⟶ M') :
    F.map ((MonoidalClosed.pre f).app M ≫ (ihom K').map g) ≫
        (Functor.LaxMonoidal.ihomComparison F K').natTrans.app M' =
      (Functor.LaxMonoidal.ihomComparison F K).natTrans.app M ≫
        (MonoidalClosed.pre (F.map f)).app (F.obj M) ≫
        (ihom (F.obj K')).map (F.map g) := by
  simp only [F.map_comp, Category.assoc]
  have h := (Functor.LaxMonoidal.ihomComparison F K').natTrans.naturality g
  dsimp only [Functor.comp_map] at h
  rw [h]
  simp only [← Category.assoc]
  rw [Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app]

private theorem finiteHomComparisonTranspose
    {V W : Type*} [Category V] [Category W]
    [MonoidalCategory V] [MonoidalCategory W] [MonoidalClosed V] [MonoidalClosed W]
    (F : V ⥤ W) [F.Monoidal] {T K M : V} (t : T ⟶ (ihom K).obj M) :
    F.map t ≫ (Functor.LaxMonoidal.ihomComparison F K).natTrans.app M =
      MonoidalClosed.curry
        (Functor.LaxMonoidal.μ F K T ≫ F.map (MonoidalClosed.uncurry t)) := by
  rw [Functor.LaxMonoidal.ihomComparison_app_eq_curry,
    ← MonoidalClosed.curry_natural_left, MonoidalClosed.uncurry_eq,
    F.map_comp, ← Functor.LaxMonoidal.μ_natural_right_assoc]

private theorem finiteHomComparisonComposition
    {V W : Type*} [Category V] [Category W]
    [MonoidalCategory V] [MonoidalCategory W] [MonoidalClosed V] [MonoidalClosed W]
    (F : V ⥤ W) [F.Monoidal] (K M N : V) :
    F.map (MonoidalClosed.comp K M N) ≫
        (Functor.LaxMonoidal.ihomComparison F K).natTrans.app N =
      Functor.OplaxMonoidal.δ F ((ihom K).obj M) ((ihom M).obj N) ≫
        ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app M ⊗ₘ
          (Functor.LaxMonoidal.ihomComparison F M).natTrans.app N) ≫
        MonoidalClosed.comp (F.obj K) (F.obj M) (F.obj N) := by
  rw [← cancel_epi (μ F ((ihom K).obj M) ((ihom M).obj N))]
  simp only [Functor.Monoidal.μ_δ_assoc]
  rw [finiteHomComparisonTranspose]
  apply uncurry_injective
  dsimp only [Functor.comp_obj]
  rw [← curry_natural_left, uncurry_curry, uncurry_natural_left,
    MonoidalClosed.comp_eq, uncurry_curry]
  simp only [MonoidalClosed.comp_eq, uncurry_curry, compTranspose, F.map_comp]
  rw [associativity_inv_assoc, ← μ_natural_left_assoc]
  conv_rhs =>
    simp only [tensorHom_def', whiskerLeft_comp, Category.assoc,
      associator_inv_naturality_middle_assoc, associator_inv_naturality_right_assoc]
    rw [← comp_whiskerRight_assoc, whisker_exchange_assoc]
    simp only [ihomComparison_ev, comp_whiskerRight, Category.assoc]
  dsimp only [Functor.id_obj]
  rw [ihomComparison_ev F M N]

private theorem finiteHomEtaleCTF_iff
    {R : Type (u + 1)} [CommRing R] [Finite R] (X : Scheme.{u})
    (K : EtaleDerived R X) :
    etaleCTF R X K ↔
      AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor (ModuleCat R) X K := by
  constructor
  · intro h
    obtain ⟨hc, a, b, hab, hz⟩ := h.1
    refine ⟨⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, ?_⟩, h.2⟩
    · exact (DerivedCategory.isGE_iff K a).2 fun i hi ↦ hz i (.inl hi)
    · exact (DerivedCategory.isLE_iff K b).2 fun i hi ↦ hz i (.inr hi)
    · exact fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1
        (hc i)
  · intro h
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := h.1
    refine ⟨⟨fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i),
      min a b, b, min_le_right _ _, ?_⟩, h.2⟩
    intro i hi
    exact hi.elim
      (fun hi ↦ (DerivedCategory.isGE_iff K a).1 ha i (lt_of_lt_of_le hi (min_le_left _ _)))
      (fun hi ↦ (DerivedCategory.isLE_iff K b).1 hb i hi)

private theorem finiteHomEtaleScalarCTF
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (X : Scheme.{u}) [IsNoetherian X] (φ : A →+* B) (K : EtaleDerived A X)
    (hK : etaleCTF A X K) : etaleCTF B X ((etaleScalar X φ).obj K) := by
  obtain ⟨a, b, ht⟩ := hK.2
  have ht' := DerivedCategory.torAmplitudeIn.mono (min_le_left a b) le_rfl ht
  obtain ⟨hc, c, d, hcd, hz⟩ := hK.1
  let Kb : DerivedCategory.Bounded (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨K, ⟨⟨c, (DerivedCategory.isGE_iff K c).2 fun i hi ↦ hz i (.inl hi)⟩,
      ⟨d, (DerivedCategory.isLE_iff K d).2 fun i hi ↦ hz i (.inr hi)⟩⟩⟩
  obtain ⟨-, -, ⟨L, ⟨eL⟩⟩, hcons, htor⟩ :=
    AlgebraicGeometry.Etale.exists_etaleScalarFlatModel X A B φ (min a b) b
      (min_le_right _ _) Kb hc
      (AlgebraicGeometry.Etale.hasTorAmplitudeIn_of_torAmplitudeIn ht')
  let e := (finiteHomScalarAdjunction X.smallEtaleTopology φ).leftAdjointUniq
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
  have htor' :=
    AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 htor
  have hh := DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn htor'
  have hfixed : etaleCTF B X
      ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension X.smallEtaleTopology φ).obj K) := by
    refine ⟨⟨hcons, min a b, b, min_le_right _ _, ?_⟩, _, _, htor'⟩
    intro i hi
    exact hi.elim
      (fun hi ↦ (DerivedCategory.isGE_iff _ (min a b)).1 hh.1 i hi)
      (fun hi ↦ (DerivedCategory.isLE_iff _ b).1 hh.2 i hi)
  exact (finiteHomEtaleCTF_iff X _).2
    (ObjectProperty.prop_of_iso
      (AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor (ModuleCat B) X)
      (e.app K).symm ((finiteHomEtaleCTF_iff X _).1 hfixed))

private theorem finiteHomProOrigin
    {A : Type (u + 1)} [CommRing A] [Finite A] (X : Scheme.{u})
    (K : ProEtaleDerived A X) (hK : proEtaleCTF A X K) :
    ∃ Ke : EtaleDerived A X, etaleCTF A X Ke ∧ Nonempty ((comparisonNu X).obj Ke ≅ K) := by
  obtain ⟨⟨Ke, hKe, ⟨eK⟩⟩, a, b, ht⟩ := hK
  refine ⟨Ke, (finiteHomEtaleCTF_iff X Ke).2 ⟨hKe, a, b, ?_⟩, ⟨eK⟩⟩
  exact (AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
    a b Ke).1 ((DerivedCategory.torAmplitudeIn _ a b).prop_of_iso eK.symm ht)

private theorem finiteHomProScalarCTF
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (X : Scheme.{u}) [IsNoetherian X] (φ : A →+* B) (K : ProEtaleDerived A X)
    (hK : proEtaleCTF A X K) : proEtaleCTF B X ((proEtaleScalar X φ).obj K) := by
  obtain ⟨Ke, hKe, ⟨eK⟩⟩ := finiteHomProOrigin X K hK
  have he := finiteHomEtaleScalarCTF X φ Ke hKe
  let e := (finiteHomRhoIso X φ).app Ke
  exact (AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor
    (ModuleCat B) X).prop_of_iso
      (e.symm ≪≫ (proEtaleScalar X φ).mapIso eK)
      (AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor_mapDerivedCategory B
        ((finiteHomEtaleCTF_iff X _).1 he))

private theorem finiteHomComparisonRightEvaluation
    {V W : Type*} [Category V] [Category W]
    [MonoidalCategory V] [MonoidalCategory W] [MonoidalClosed V] [MonoidalClosed W]
    [BraidedCategory V] [BraidedCategory W] (F : V ⥤ W) [F.Monoidal]
    (hF : ∀ K M, (β_ (F.obj K) (F.obj M)).hom ≫ μ F M K =
      μ F K M ≫ F.map (β_ K M).hom) (K M : V) :
    ((ihomComparison F K).natTrans.app M ⊗ₘ 𝟙 (F.obj K)) ≫
        (β_ ((ihom (F.obj K)).obj (F.obj M)) (F.obj K)).hom ≫
        (ihom.ev (F.obj K)).app (F.obj M) =
      μ F ((ihom K).obj M) K ≫ F.map
        ((β_ ((ihom K).obj M) K).hom ≫ (ihom.ev K).app M) := by
  dsimp only [Functor.comp_obj]
  simp only [tensorHom_id, F.map_comp]
  rw [BraidedCategory.braiding_naturality_left_assoc, ihomComparison_ev]
  rw [← Category.assoc, hF, Category.assoc]

private theorem finiteHomMonoidalIsoUnit
    {V W : Type*} [Category V] [Category W]
    [MonoidalCategory V] [MonoidalCategory W]
    {F G : V ⥤ W} [F.Monoidal] [G.Monoidal]
    (e : F ≅ G) [NatTrans.IsMonoidal e.hom] :
    e.hom.app (𝟙_ V) ≫ η G = η F := by
  rw [← cancel_epi (ε F), ← Category.assoc, NatTrans.IsMonoidal.unit, ε_η, ε_η]

private theorem finiteHomComparisonIso
    {V W : Type*} [Category V] [Category W]
    [MonoidalCategory V] [MonoidalCategory W] [MonoidalClosed V] [MonoidalClosed W]
    {F G : V ⥤ W} [F.Monoidal] [G.Monoidal]
    (e : F ≅ G) [NatTrans.IsMonoidal e.hom] (K M : V) :
    e.hom.app ((ihom K).obj M) ≫ (ihomComparison G K).natTrans.app M =
      (ihomComparison F K).natTrans.app M ≫
        (pre (e.inv.app K)).app (F.obj M) ≫
        (ihom (G.obj K)).map (e.hom.app M) := by
  have h := ihomComparison_app_comp_map_app e.inv K M
  have h' := congrArg (fun f ↦ e.hom.app ((ihom K).obj M) ≫ f ≫
    (ihom (G.obj K)).map (e.hom.app M)) h
  simp only [← Functor.map_comp, Iso.inv_hom_id_app,
    Category.assoc, Iso.hom_inv_id_app_assoc] at h'
  dsimp only [Functor.comp_obj] at h' ⊢
  simpa only [(ihom (G.obj K)).map_id, Category.comp_id] using h'

private theorem finiteHomComparisonIdentity
    {V : Type*} [Category V] [MonoidalCategory V] [MonoidalClosed V]
    (K M : V) : (ihomComparison (𝟭 V) K).natTrans.app M = 𝟙 _ := by
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [ihomComparison_app_eq_curry]
  simp only [Functor.LaxMonoidal.id_μ, Functor.id_map, Category.id_comp]
  simpa only [uncurry_eq, MonoidalCategory.whiskerLeft_id, Category.id_comp] using
    (curry_uncurry (𝟙 ((ihom K).obj M)))

private theorem tensorEtale_iso : finiteHomLaw_tensorEtale_iso X φ := by
  unfold finiteHomLaw_tensorEtale_iso
  intro K M
  unfold etaleTensor
  infer_instance

private theorem tensorPro_iso : finiteHomLaw_tensorPro_iso X φ := by
  letI : (proEtaleScalar X φ).Monoidal := (proCore X φ).toMonoidal
  unfold finiteHomLaw_tensorPro_iso
  intro K M
  unfold proTensor
  change IsIso ((proCore X φ).μIso K M).inv
  infer_instance

private theorem tensor_associator_etale : finiteHomLaw_tensor_associator_etale X φ :=
  by
    unfold finiteHomLaw_tensor_associator_etale
    exact (etaleCore X φ).associativity

private theorem tensor_left_unit_etale : finiteHomLaw_tensor_left_unit_etale X φ :=
  by
    unfold finiteHomLaw_tensor_left_unit_etale
    exact (etaleCore X φ).left_unitality

private theorem tensor_right_unit_etale : finiteHomLaw_tensor_right_unit_etale X φ :=
  by
    unfold finiteHomLaw_tensor_right_unit_etale
    exact (etaleCore X φ).right_unitality

private theorem tensor_associator_pro : finiteHomLaw_tensor_associator_pro X φ :=
  by
    unfold finiteHomLaw_tensor_associator_pro
    exact (proCore X φ).associativity

private theorem tensor_left_unit_pro : finiteHomLaw_tensor_left_unit_pro X φ :=
  by
    unfold finiteHomLaw_tensor_left_unit_pro
    exact (proCore X φ).left_unitality

private theorem tensor_right_unit_pro : finiteHomLaw_tensor_right_unit_pro X φ :=
  by
    unfold finiteHomLaw_tensor_right_unit_pro
    exact (proCore X φ).right_unitality

private theorem evaluation_transpose_etale : finiteHomLaw_evaluation_transpose_etale X φ := by
  letI : (etaleScalar X φ).Monoidal := (etaleCore X φ).toMonoidal
  unfold finiteHomLaw_evaluation_transpose_etale etaleHomTranspose
  intro K M
  unfold etaleHom
  exact Functor.LaxMonoidal.ihomComparison_app_eq_curry _ _ _

private theorem evaluation_transpose_pro : finiteHomLaw_evaluation_transpose_pro X φ := by
  letI : (proEtaleScalar X φ).Monoidal := (proCore X φ).toMonoidal
  unfold finiteHomLaw_evaluation_transpose_pro proHomTranspose
  intro K M
  unfold proHom
  exact Functor.LaxMonoidal.ihomComparison_app_eq_curry _ _ _

private theorem evaluation_etale : finiteHomLaw_evaluation_etale X φ := by
  unfold finiteHomLaw_evaluation_etale
  intro K M
  letI : (etaleScalar X φ).Monoidal := (etaleCore X φ).toMonoidal
  unfold etaleHom
  exact Functor.LaxMonoidal.ihomComparison_ev _ _ _

private theorem evaluation_pro : finiteHomLaw_evaluation_pro X φ := by
  unfold finiteHomLaw_evaluation_pro
  intro K M
  letI : (proEtaleScalar X φ).Monoidal := (proCore X φ).toMonoidal
  unfold proHom
  exact Functor.LaxMonoidal.ihomComparison_ev _ _ _

private theorem unique_transpose_etale : finiteHomLaw_unique_transpose_etale X φ := by
  unfold finiteHomLaw_unique_transpose_etale
  intro K M w hw
  apply MonoidalClosed.uncurry_injective
  have h := evaluation_etale X φ
  unfold finiteHomLaw_evaluation_etale at h
  exact hw.trans (h K M).symm

private theorem unique_transpose_pro : finiteHomLaw_unique_transpose_pro X φ := by
  unfold finiteHomLaw_unique_transpose_pro
  intro K M w hw
  apply MonoidalClosed.uncurry_injective
  have h := evaluation_pro X φ
  unfold finiteHomLaw_evaluation_pro at h
  exact hw.trans (h K M).symm

private theorem tensor_naturality_etale : finiteHomLaw_tensor_naturality_etale X φ := by
  letI := (etaleCore X φ).toMonoidal
  unfold finiteHomLaw_tensor_naturality_etale etaleTensor
  intro K K' M M' f g
  exact (Functor.OplaxMonoidal.δ_natural (etaleScalar X φ) f g).symm

private theorem tensor_naturality_pro : finiteHomLaw_tensor_naturality_pro X φ := by
  letI := (proCore X φ).toMonoidal
  unfold finiteHomLaw_tensor_naturality_pro proTensor
  intro K K' M M' f g
  exact (Functor.OplaxMonoidal.δ_natural (proEtaleScalar X φ) f g).symm

private theorem naturality_etale : finiteHomLaw_naturality_etale X φ := by
  letI := (etaleCore X φ).toMonoidal
  unfold finiteHomLaw_naturality_etale etaleHom
  intro K K' M M' f g
  exact finiteHomComparisonNaturality (etaleScalar X φ) f g

private theorem naturality_pro : finiteHomLaw_naturality_pro X φ := by
  letI := (proCore X φ).toMonoidal
  unfold finiteHomLaw_naturality_pro proHom
  intro K K' M M' f g
  exact finiteHomComparisonNaturality (proEtaleScalar X φ) f g

private theorem tensor_hom_adjunction_etale :
    finiteHomLaw_tensor_hom_adjunction_etale X φ := by
  letI := (etaleCore X φ).toMonoidal
  unfold finiteHomLaw_tensor_hom_adjunction_etale etaleHom
  intro K U M f
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_eq,
    Functor.LaxMonoidal.ihomComparison_ev,
    Functor.LaxMonoidal.μ_natural_right_assoc, ← Functor.map_comp,
    ← MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_curry]
  rfl

private theorem tensor_hom_adjunction_pro :
    finiteHomLaw_tensor_hom_adjunction_pro X φ := by
  letI := (proCore X φ).toMonoidal
  unfold finiteHomLaw_tensor_hom_adjunction_pro proHom
  intro K U M f
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_eq,
    Functor.LaxMonoidal.ihomComparison_ev,
    Functor.LaxMonoidal.μ_natural_right_assoc, ← Functor.map_comp,
    ← MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_curry]
  rfl

private theorem composition_etale : finiteHomLaw_composition_etale X φ := by
  letI := (etaleCore X φ).toMonoidal
  unfold finiteHomLaw_composition_etale etaleTensor etaleHom
  intro K M N
  exact finiteHomComparisonComposition (etaleScalar X φ) K M N

private theorem composition_pro : finiteHomLaw_composition_pro X φ := by
  letI := (proCore X φ).toMonoidal
  unfold finiteHomLaw_composition_pro proTensor proHom
  intro K M N
  exact finiteHomComparisonComposition (proEtaleScalar X φ) K M N

private theorem homEtale_source_ctf : finiteHomLaw_homEtale_source_ctf X φ := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  haveI : IsNoetherian X :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k)) }
  unfold finiteHomLaw_homEtale_source_ctf
  intro K M hK hM
  apply finiteHomEtaleScalarCTF X φ
  exact (finiteHomEtaleCTF_iff X _).2
    (generalFiniteHomConstructible hbase ell (isUnit_iff_ne_zero.mpr hell) A hA
      (X ↘ Spec (.of k)) ((finiteHomEtaleCTF_iff X K).1 hK)
      ((finiteHomEtaleCTF_iff X M).1 hM))

private theorem homEtale_target_ctf : finiteHomLaw_homEtale_target_ctf X φ := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  haveI : IsNoetherian X :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k)) }
  unfold finiteHomLaw_homEtale_target_ctf
  intro K M hK hM
  exact (finiteHomEtaleCTF_iff X _).2
    (generalFiniteHomConstructible hbase ell (isUnit_iff_ne_zero.mpr hell) B hB
      (X ↘ Spec (.of k))
      ((finiteHomEtaleCTF_iff X _).1 (finiteHomEtaleScalarCTF X φ K hK))
      ((finiteHomEtaleCTF_iff X _).1 (finiteHomEtaleScalarCTF X φ M hM)))

private theorem finiteHomProHomCTF
    {R : Type (u + 1)} [CommRing R] [Finite R]
    (hR : ∃ n : ℕ, (ell ^ n : R) = 0) (K M : ProEtaleDerived R X)
    (hK : proEtaleCTF R X K) (hM : proEtaleCTF R X M) :
    proEtaleCTF R X ((ihom K).obj M) := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  haveI : IsNoetherian X :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k)) }
  obtain ⟨Ke, hKe, ⟨eK⟩⟩ := finiteHomProOrigin X K hK
  obtain ⟨Me, hMe, ⟨eM⟩⟩ := finiteHomProOrigin X M hM
  have ht : ∃ a b : ℤ,
      AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn R X a b Ke := by
    obtain ⟨a, b, ht⟩ := hKe.2
    exact ⟨a, b, AlgebraicGeometry.Etale.hasTorAmplitudeIn_of_torAmplitudeIn ht⟩
  haveI : IsIso (comparisonBeta X Ke Me) := by
    change IsIso (AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat R) X Ke Me)
    exact (AlgebraicGeometry.ProEtale.DerivedCategory.isIso_finiteSiteInternalHomComparison
      R Ke Me hKe.1 ht ((finiteHomEtaleCTF_iff X Me).1 hMe).1.1.1).1
  let eH := asIso (comparisonBeta X Ke Me) ≪≫
    ((MonoidalClosed.internalHom.mapIso eK.op.symm).app ((comparisonNu X).obj Me)) ≪≫
    (ihom K).mapIso eM
  exact (AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor
    (ModuleCat R) X).prop_of_iso eH
      (AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor_mapDerivedCategory R
        (generalFiniteHomConstructible hbase ell (isUnit_iff_ne_zero.mpr hell) R hR
          (X ↘ Spec (.of k)) ((finiteHomEtaleCTF_iff X Ke).1 hKe)
          ((finiteHomEtaleCTF_iff X Me).1 hMe)))

private theorem homPro_source_ctf : finiteHomLaw_homPro_source_ctf X φ := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  haveI : IsNoetherian X :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k)) }
  unfold finiteHomLaw_homPro_source_ctf
  intro K M hK hM
  exact finiteHomProScalarCTF X φ _ (finiteHomProHomCTF X k hbase ell hell hA K M hK hM)

private theorem homPro_target_ctf : finiteHomLaw_homPro_target_ctf X φ := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  haveI : IsNoetherian X :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k)) }
  unfold finiteHomLaw_homPro_target_ctf
  intro K M hK hM
  exact finiteHomProHomCTF X k hbase ell hell hB _ _
    (finiteHomProScalarCTF X φ K hK) (finiteHomProScalarCTF X φ M hM)

private theorem successive_etale
    (ht : finiteHomLaw_tensor_successive_etale X φ ψ) :
    finiteHomLaw_unit_successive_etale X φ ψ ∧
      finiteHomLaw_successive_etale X φ ψ := by
  unfold finiteHomLaw_tensor_successive_etale etaleTensor at ht
  letI := (etaleCore X φ).toMonoidal
  letI := (etaleCore X ψ).toMonoidal
  letI := (etaleCore X (ψ.comp φ)).toMonoidal
  let e : etaleScalar X φ ⋙ etaleScalar X ψ ≅ etaleScalar X (ψ.comp φ) :=
    finiteHomScalarComp X.smallEtaleTopology φ ψ
  haveI : NatTrans.IsMonoidal e.hom := by
    apply NatTrans.IsMonoidal.of_isIso_of_δ
    simpa only [e, Functor.OplaxMonoidal.comp_δ,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
      Functor.CoreMonoidal.toOplaxMonoidal_δ, Category.assoc, id_eq] using ht
  constructor
  · unfold finiteHomLaw_unit_successive_etale
    simpa only [e, Functor.OplaxMonoidal.comp_η,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
      Functor.CoreMonoidal.toOplaxMonoidal_η] using finiteHomMonoidalIsoUnit e
  · unfold finiteHomLaw_successive_etale etaleHom
    intro K M
    simpa only [Functor.LaxMonoidal.ihomComparison_comp_app, Functor.comp_obj, Category.assoc] using
      finiteHomComparisonIso e K M

private theorem identity_etale
    (ht : finiteHomLaw_tensor_identity_etale (A := A) X) :
    finiteHomLaw_unit_identity_etale (A := A) X ∧
      finiteHomLaw_identity_etale (A := A) X := by
  unfold finiteHomLaw_tensor_identity_etale etaleTensor at ht
  letI := (etaleCore X (RingHom.id A)).toMonoidal
  let e : etaleScalar X (RingHom.id A) ≅ 𝟭 (EtaleDerived A X) :=
    finiteHomScalarId X.smallEtaleTopology A
  haveI : NatTrans.IsMonoidal e.hom := by
    apply NatTrans.IsMonoidal.of_isIso_of_δ
    intro K M
    simpa only [e, Functor.OplaxMonoidal.id_δ,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
      Functor.CoreMonoidal.toOplaxMonoidal_δ, Category.comp_id, id_eq] using (ht K M).symm
  constructor
  · unfold finiteHomLaw_unit_identity_etale
    simpa only [e, Functor.OplaxMonoidal.id_η,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
      Functor.CoreMonoidal.toOplaxMonoidal_η, Category.comp_id] using
      (finiteHomMonoidalIsoUnit e).symm
  · unfold finiteHomLaw_identity_etale etaleHom
    intro K M
    have h := finiteHomComparisonIso e K M
    rw [finiteHomComparisonIdentity] at h
    dsimp only [Functor.comp_obj, Functor.id_obj] at h
    simpa only [e, Category.comp_id] using h

private theorem successive_pro
    (ht : finiteHomLaw_tensor_successive_pro X φ ψ) :
    finiteHomLaw_unit_successive_pro X φ ψ ∧
      finiteHomLaw_successive_pro X φ ψ := by
  unfold finiteHomLaw_tensor_successive_pro proTensor at ht
  letI := (proCore X φ).toMonoidal
  letI := (proCore X ψ).toMonoidal
  letI := (proCore X (ψ.comp φ)).toMonoidal
  let e : proEtaleScalar X φ ⋙ proEtaleScalar X ψ ≅ proEtaleScalar X (ψ.comp φ) :=
    finiteHomScalarComp (ProEt.topology X) φ ψ
  haveI : NatTrans.IsMonoidal e.hom := by
    apply NatTrans.IsMonoidal.of_isIso_of_δ
    simpa only [e, Functor.OplaxMonoidal.comp_δ,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
      Functor.CoreMonoidal.toOplaxMonoidal_δ, Category.assoc, id_eq] using ht
  constructor
  · unfold finiteHomLaw_unit_successive_pro
    simpa only [e, Functor.OplaxMonoidal.comp_η,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
      Functor.CoreMonoidal.toOplaxMonoidal_η] using finiteHomMonoidalIsoUnit e
  · unfold finiteHomLaw_successive_pro proHom
    intro K M
    simpa only [Functor.LaxMonoidal.ihomComparison_comp_app, Functor.comp_obj, Category.assoc] using
      finiteHomComparisonIso e K M

private theorem identity_pro
    (ht : finiteHomLaw_tensor_identity_pro (A := A) X) :
    finiteHomLaw_unit_identity_pro (A := A) X ∧
      finiteHomLaw_identity_pro (A := A) X := by
  unfold finiteHomLaw_tensor_identity_pro proTensor at ht
  letI := (proCore X (RingHom.id A)).toMonoidal
  let e : proEtaleScalar X (RingHom.id A) ≅ 𝟭 (ProEtaleDerived A X) :=
    finiteHomScalarId (ProEt.topology X) A
  haveI : NatTrans.IsMonoidal e.hom := by
    apply NatTrans.IsMonoidal.of_isIso_of_δ
    intro K M
    simpa only [e, Functor.OplaxMonoidal.id_δ,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
      Functor.CoreMonoidal.toOplaxMonoidal_δ, Category.comp_id, id_eq] using (ht K M).symm
  constructor
  · unfold finiteHomLaw_unit_identity_pro
    simpa only [e, Functor.OplaxMonoidal.id_η,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
      Functor.CoreMonoidal.toOplaxMonoidal_η, Category.comp_id] using
      (finiteHomMonoidalIsoUnit e).symm
  · unfold finiteHomLaw_identity_pro proHom
    intro K M
    have h := finiteHomComparisonIso e K M
    rw [finiteHomComparisonIdentity] at h
    dsimp only [Functor.comp_obj, Functor.id_obj] at h
    simpa only [e, Category.comp_id] using h

/-- The etale half of the finite-Hom law package.

This is the devissage and closed-Hom comparison on the ordinary etale site.  It
is separated from the pro-etale half so that the two site arguments can be
proved independently and then assembled by the main theorem.
(blueprint: thm-coef-finite-hom)
-/
structure FiniteCoefficientHomEtaleLaws
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C) where
  tensorEtale_iso : finiteHomLaw_tensorEtale_iso X φ
  vEtale_iso : finiteHomLaw_vEtale_iso X φ
  tensor_associator_etale : finiteHomLaw_tensor_associator_etale X φ
  tensor_left_unit_etale : finiteHomLaw_tensor_left_unit_etale X φ
  tensor_right_unit_etale : finiteHomLaw_tensor_right_unit_etale X φ
  tensor_symmetry_etale : finiteHomLaw_tensor_symmetry_etale X φ
  tensor_naturality_etale : finiteHomLaw_tensor_naturality_etale X φ
  evaluation_transpose_etale : finiteHomLaw_evaluation_transpose_etale X φ
  successive_etale : finiteHomLaw_successive_etale X φ ψ
  identity_etale : finiteHomLaw_identity_etale (A := A) X
  evaluation_etale : finiteHomLaw_evaluation_etale X φ
  evaluation_right_etale : finiteHomLaw_evaluation_right_etale X φ
  unique_transpose_etale : finiteHomLaw_unique_transpose_etale X φ
  naturality_etale : finiteHomLaw_naturality_etale X φ
  tensor_hom_adjunction_etale : finiteHomLaw_tensor_hom_adjunction_etale X φ
  composition_etale : finiteHomLaw_composition_etale X φ
  tensor_successive_etale : finiteHomLaw_tensor_successive_etale X φ ψ
  unit_successive_etale : finiteHomLaw_unit_successive_etale X φ ψ
  tensor_identity_etale : finiteHomLaw_tensor_identity_etale (A := A) X
  unit_identity_etale : finiteHomLaw_unit_identity_etale (A := A) X
  homEtale_source_ctf : finiteHomLaw_homEtale_source_ctf X φ
  homEtale_target_ctf : finiteHomLaw_homEtale_target_ctf X φ

/-- The pro-etale half of the finite-Hom law package.

This is the finite-duality transport and coherence argument on the pro-etale
site.  It is an independent sub-conclusion of `thmCoefFiniteHom`.
(blueprint: thm-coef-finite-hom)
-/
structure FiniteCoefficientHomProLaws
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C) where
  tensorPro_iso : finiteHomLaw_tensorPro_iso X φ
  vPro_iso : finiteHomLaw_vPro_iso X φ
  tensor_associator_pro : finiteHomLaw_tensor_associator_pro X φ
  tensor_left_unit_pro : finiteHomLaw_tensor_left_unit_pro X φ
  tensor_right_unit_pro : finiteHomLaw_tensor_right_unit_pro X φ
  tensor_symmetry_pro : finiteHomLaw_tensor_symmetry_pro X φ
  tensor_naturality_pro : finiteHomLaw_tensor_naturality_pro X φ
  evaluation_transpose_pro : finiteHomLaw_evaluation_transpose_pro X φ
  successive_pro : finiteHomLaw_successive_pro X φ ψ
  identity_pro : finiteHomLaw_identity_pro (A := A) X
  evaluation_pro : finiteHomLaw_evaluation_pro X φ
  evaluation_right_pro : finiteHomLaw_evaluation_right_pro X φ
  unique_transpose_pro : finiteHomLaw_unique_transpose_pro X φ
  naturality_pro : finiteHomLaw_naturality_pro X φ
  tensor_hom_adjunction_pro : finiteHomLaw_tensor_hom_adjunction_pro X φ
  composition_pro : finiteHomLaw_composition_pro X φ
  tensor_successive_pro : finiteHomLaw_tensor_successive_pro X φ ψ
  unit_successive_pro : finiteHomLaw_unit_successive_pro X φ ψ
  tensor_identity_pro : finiteHomLaw_tensor_identity_pro (A := A) X
  unit_identity_pro : finiteHomLaw_unit_identity_pro (A := A) X
  homPro_source_ctf : finiteHomLaw_homPro_source_ctf X φ
  homPro_target_ctf : finiteHomLaw_homPro_target_ctf X φ

private theorem finiteHomEtaleLawsOfComparison
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (hell : (ell : k) ≠ 0)
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C)
    (hA : ∃ n : ℕ, (ell ^ n : A) = 0)
    (hB : ∃ n : ℕ, (ell ^ n : B) = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (hi : finiteHomLaw_vEtale_iso X φ)
    (hbraid : finiteHomLaw_tensor_symmetry_etale X φ)
    (heval : finiteHomLaw_evaluation_right_etale X φ)
    (hs : finiteHomLaw_tensor_successive_etale X φ ψ)
    (hid : finiteHomLaw_tensor_identity_etale (A := A) X) :
    Nonempty (FiniteCoefficientHomEtaleLaws X φ ψ) := by
  have hc := successive_etale X φ ψ hs
  have hci := identity_etale X hid
  exact ⟨{
    tensorEtale_iso := tensorEtale_iso X φ
    vEtale_iso := hi
    tensor_associator_etale := tensor_associator_etale X φ
    tensor_left_unit_etale := tensor_left_unit_etale X φ
    tensor_right_unit_etale := tensor_right_unit_etale X φ
    tensor_symmetry_etale := hbraid
    tensor_naturality_etale := tensor_naturality_etale X φ
    evaluation_transpose_etale := evaluation_transpose_etale X φ
    evaluation_etale := evaluation_etale X φ
    evaluation_right_etale := heval
    unique_transpose_etale := unique_transpose_etale X φ
    naturality_etale := naturality_etale X φ
    tensor_hom_adjunction_etale := tensor_hom_adjunction_etale X φ
    composition_etale := composition_etale X φ
    successive_etale := hc.2
    identity_etale := hci.2
    tensor_successive_etale := hs
    unit_successive_etale := hc.1
    tensor_identity_etale := hid
    unit_identity_etale := hci.1
    homEtale_source_ctf := homEtale_source_ctf X φ k hbase ell hell hA
    homEtale_target_ctf := homEtale_target_ctf X φ k hbase ell hell hB }⟩

private theorem finiteHomProLawsOfComparison
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (hell : (ell : k) ≠ 0)
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C)
    (hA : ∃ n : ℕ, (ell ^ n : A) = 0)
    (hB : ∃ n : ℕ, (ell ^ n : B) = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (hi : finiteHomLaw_vPro_iso X φ)
    (hbraid : finiteHomLaw_tensor_symmetry_pro X φ)
    (heval : finiteHomLaw_evaluation_right_pro X φ)
    (hs : finiteHomLaw_tensor_successive_pro X φ ψ)
    (hid : finiteHomLaw_tensor_identity_pro (A := A) X) :
    Nonempty (FiniteCoefficientHomProLaws X φ ψ) := by
  have hc := successive_pro X φ ψ hs
  have hci := identity_pro X hid
  exact ⟨{
    tensorPro_iso := tensorPro_iso X φ
    vPro_iso := hi
    tensor_associator_pro := tensor_associator_pro X φ
    tensor_left_unit_pro := tensor_left_unit_pro X φ
    tensor_right_unit_pro := tensor_right_unit_pro X φ
    tensor_symmetry_pro := hbraid
    tensor_naturality_pro := tensor_naturality_pro X φ
    evaluation_transpose_pro := evaluation_transpose_pro X φ
    evaluation_pro := evaluation_pro X φ
    evaluation_right_pro := heval
    unique_transpose_pro := unique_transpose_pro X φ
    naturality_pro := naturality_pro X φ
    tensor_hom_adjunction_pro := tensor_hom_adjunction_pro X φ
    composition_pro := composition_pro X φ
    successive_pro := hc.2
    identity_pro := hci.2
    tensor_successive_pro := hs
    unit_successive_pro := hc.1
    tensor_identity_pro := hid
    unit_identity_pro := hci.1
    homPro_source_ctf := homPro_source_ctf X φ k hbase ell hell hA
    homPro_target_ctf := homPro_target_ctf X φ k hbase ell hell hB }⟩

/-- Etale finite-Hom devissage and endpoint constructibility.

The proof follows the constructible-stratum filtration, perfect replacement,
localization triangles, and the finite projective scalar calculation from the
proof of `thm-coef-finite-hom`; this is the ordinary-site subproblem.
(blueprint: thm-coef-finite-hom)
-/
theorem finiteCoefficientHomEtaleLaws
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (hell : (ell : k) ≠ 0)
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C)
    (hA : ∃ n : ℕ, (ell ^ n : A) = 0)
    (hB : ∃ n : ℕ, (ell ^ n : B) = 0)
    (hC : ∃ n : ℕ, (ell ^ n : C) = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    Nonempty (FiniteCoefficientHomEtaleLaws X φ ψ) := by
  have hiso := finiteCoefficientHomIsomorphisms k hbase ell hell φ hA hB X
  have htensor := finiteCoefficientHomScalarTensorCoherence k hbase ell hell φ ψ hA hB hC X
  exact finiteHomEtaleLawsOfComparison k hbase ell hell φ ψ hA hB X
    hiso.1 htensor.2.2.2.2.1 htensor.2.2.2.2.2.2.1 htensor.1 htensor.2.1

/-- Pro-etale finite-Hom transport and coherence.

The proof transports the finite-duality comparison through the pro-etale
scalar extension, then verifies the successive and identity coherence maps.
This is the pro-etale subproblem of `thmCoefFiniteHom`.
(blueprint: thm-coef-finite-hom)
-/
theorem finiteCoefficientHomProLaws
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (hell : (ell : k) ≠ 0)
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C)
    (hA : ∃ n : ℕ, (ell ^ n : A) = 0)
    (hB : ∃ n : ℕ, (ell ^ n : B) = 0)
    (hC : ∃ n : ℕ, (ell ^ n : C) = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    Nonempty (FiniteCoefficientHomProLaws X φ ψ) := by
  have hiso := finiteCoefficientHomIsomorphisms k hbase ell hell φ hA hB X
  have htensor := finiteCoefficientHomScalarTensorCoherence k hbase ell hell φ ψ hA hB hC X
  exact finiteHomProLawsOfComparison k hbase ell hell φ ψ hA hB X
    hiso.2 htensor.2.2.2.2.2.1 htensor.2.2.2.2.2.2.2 htensor.2.2.1 htensor.2.2.2.1

/-- Arbitrary finite-primary coefficient change for the ordinary derived Hom.
Source: latest blueprint thm-coef-finite-hom.md, statement, and
thm-coef-finite-hom.proof.md, all paragraphs (blueprint: thm-coef-finite-hom).
Proof: define v by tensoring evaluation, applying the canonical tensor reassociation,
and transposing; finite constructibility and finite Tor amplitude give the CTF
endpoints. Stratify K so each cohomology sheaf is finite locally constant. On a
stratum its bounded finite-Tor restriction has finite free truncations and is
site-perfect. Localization triangles and exactness in K reduce to K = Rs_!P for a
stratum immersion and site-perfect P. Identify ambient Hom with
Rs_* RHom(P, Rs^!M). For P perfect, Hom is its dual tensor Rs^!M; scalar change
commutes by the finite projective calculation, the finite-direct-image comparison,
and the closed-shriek comparison. The extension-by-zero comparison and evaluation
counits show the resulting isomorphism is the specified v. Reassemble through the
localization triangles. Apply the finite-duality site comparison for the pro-etale
case. Finally uncurry: evaluation, naturality, tensor-Hom adjunction and composition
follow from the defining transpose. Associativity and the unit for scalar pullback
give the actual successive and identity equations, including monoidality of the
canonical scalar compositor and scalar unit. -/
theorem thmCoefFiniteHom
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (hell : (ell : k) ≠ 0)
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C)
    (hA : ∃ n : ℕ, (ell ^ n : A) = 0)
    (hB : ∃ n : ℕ, (ell ^ n : B) = 0)
    (hC : ∃ n : ℕ, (ell ^ n : C) = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    Nonempty (FiniteCoefficientHomLaws X φ ψ) := by
  let e := Classical.choice (finiteCoefficientHomEtaleLaws k hbase ell hell φ ψ hA hB hC X)
  let p := Classical.choice (finiteCoefficientHomProLaws k hbase ell hell φ ψ hA hB hC X)
  exact ⟨{
    tensorEtale_iso := e.tensorEtale_iso
    tensorPro_iso := p.tensorPro_iso
    vEtale_iso := e.vEtale_iso
    vPro_iso := p.vPro_iso
    tensor_associator_etale := e.tensor_associator_etale
    tensor_left_unit_etale := e.tensor_left_unit_etale
    tensor_right_unit_etale := e.tensor_right_unit_etale
    tensor_associator_pro := p.tensor_associator_pro
    tensor_left_unit_pro := p.tensor_left_unit_pro
    tensor_right_unit_pro := p.tensor_right_unit_pro
    tensor_symmetry_etale := e.tensor_symmetry_etale
    tensor_symmetry_pro := p.tensor_symmetry_pro
    tensor_naturality_etale := e.tensor_naturality_etale
    evaluation_transpose_etale := e.evaluation_transpose_etale
    tensor_naturality_pro := p.tensor_naturality_pro
    evaluation_transpose_pro := p.evaluation_transpose_pro
    successive_etale := e.successive_etale
    identity_etale := e.identity_etale
    evaluation_etale := e.evaluation_etale
    evaluation_right_etale := e.evaluation_right_etale
    unique_transpose_etale := e.unique_transpose_etale
    naturality_etale := e.naturality_etale
    tensor_hom_adjunction_etale := e.tensor_hom_adjunction_etale
    composition_etale := e.composition_etale
    tensor_successive_etale := e.tensor_successive_etale
    unit_successive_etale := e.unit_successive_etale
    tensor_identity_etale := e.tensor_identity_etale
    unit_identity_etale := e.unit_identity_etale
    successive_pro := p.successive_pro
    identity_pro := p.identity_pro
    evaluation_pro := p.evaluation_pro
    evaluation_right_pro := p.evaluation_right_pro
    unique_transpose_pro := p.unique_transpose_pro
    naturality_pro := p.naturality_pro
    tensor_hom_adjunction_pro := p.tensor_hom_adjunction_pro
    composition_pro := p.composition_pro
    tensor_successive_pro := p.tensor_successive_pro
    unit_successive_pro := p.unit_successive_pro
    tensor_identity_pro := p.tensor_identity_pro
    unit_identity_pro := p.unit_identity_pro
    homEtale_source_ctf := e.homEtale_source_ctf
    homEtale_target_ctf := e.homEtale_target_ctf
    homPro_source_ctf := p.homPro_source_ctf
    homPro_target_ctf := p.homPro_target_ctf }⟩

end WeilConjectures
