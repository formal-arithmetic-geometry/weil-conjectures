module

public import Sheaf.Paper.ProEtaleVectorIntegrationArrows
public import Sheaf.Paper.BoundedSiteAdjunctionTranspose
public import Sheaf.Paper.VectorPurityNormalization

/-! # Canonical equations for tensor integration site comparison
Source: Stacks 099R, 0944 and 0B65; vector-bundle integration
(blueprint: def-pur-vector-tensor-site-equations).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- Generic compact-support source before specializing the finite ring.
Source: vector integration (blueprint: def-pur-vector-tensor-site-equations). -/
abbrev genericVectorSource (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (Etale.vectorBundlePurityCompactification S d F)).obj
      ((comparison A _).obj (Etale.vectorIntegrationCoefficient A N hA S d F))

/-- Generic ordinary integration Hom type.
Source: vector integration (blueprint: def-pur-vector-tensor-site-equations). -/
@[implicit_reducible]
def GenericOrdinaryIntegrationHom (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (K : Etale.DerivedCategoryModule A S) :=
  (Etale.vectorBundlePurityLower A S d F).obj
    (Etale.vectorBundlePurityTwistedPullback A N hA S d F K) ⟶ K

/-- Generic pro-etale integration Hom type.
Source: vector integration (blueprint: def-pur-vector-tensor-site-equations). -/
@[implicit_reducible]
def GenericProIntegrationHom (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (K : Etale.DerivedCategoryModule A S) :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (Etale.vectorBundlePurityCompactification S d F)).obj
      ((comparison A _).obj (Etale.vectorBundlePurityTwistedPullback A N hA S d F K)) ⟶
        (comparison A S).obj K

/-- The recorded ordinary exceptional functor before coefficient specialization.
Source: ordinary compact-support adjunction
(blueprint: def-pur-vector-tensor-site-equations). -/
abbrev genericVectorExceptional (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :=
  letI := (Etale.vectorIntegration_geometry S d F).1
  letI := (Etale.vectorIntegration_geometry S d F).2.1
  Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) (VectorBundleZeroSection.π S d F)

/-- Witnesses and equations defining canonical tensor integration compatibility.
Source: Stacks 099R, 0944 and 0B65; vector-bundle integration
(blueprint: def-pur-vector-tensor-site-equations). -/
structure TensorCompatibilityData (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (K : Etale.DerivedCategoryModule A S)
    (t : genericVectorSource A N hA S d F ⟶ unit A S)
    (e : genericVectorSource A N hA S d F ≅
      (comparison A S).obj (Etale.vectorIntegrationSource A N hA S d F)) where
  hM : DerivedCategory.TStructure.t.plus (Etale.vectorBundlePurityTwistedPullback A N hA S d F K)
  pe : (Etale.vectorBundlePurityLower A S d F).obj
        (Etale.vectorBundlePurityTwistedPullback A N hA S d F K) ≅
        ((Etale.derivedTensor (ModuleCat.{u + 1} A) S).obj
           K).obj (Etale.vectorIntegrationSource A N hA S d F)
  pp : (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A)
        (Etale.vectorBundlePurityCompactification S d F)).obj
          ((comparison A _).obj
            (Etale.vectorBundlePurityTwistedPullback A N hA S d F K)) ≅
        ((derivedTensor (ModuleCat.{u + 1} A) S).obj
           ((comparison A S).obj K)).obj
            (genericVectorSource A N hA S d F)
  ae : GenericOrdinaryIntegrationHom A N hA S d F K
  ap : GenericProIntegrationHom A N hA S d F K
  ordinary_formula :
    HEq ae
      (ordinaryTensorIntegrate A S K
        (Etale.vectorIntegrationSource A N hA S d F)
        ((Etale.vectorBundlePurityLower A S d F).obj
          (Etale.vectorBundlePurityTwistedPullback A N hA S d F K)) pe
        (Etale.vectorBundleIntegration N
          hN A hA S hS d F))
  pro_formula :
    HEq ap
      (proTensorIntegrate A S K
        (genericVectorSource A N hA S d F)
        ((rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A)
          (Etale.vectorBundlePurityCompactification S d F)).obj
            ((comparison A _).obj
              (Etale.vectorBundlePurityTwistedPullback A N hA S d F K))) pp
        t)
  ordinary_projection :
    pe.inv = Etale.vectorBundlePurityProjectionMap
      A N hA S d F K
  pro_projection :
    HEq pp.inv
      (comparedModuleProjection A
        (Etale.vectorBundlePurityCompactification S d F)
        (Etale.vectorIntegrationCoefficient A N hA S d F) K)
  projection_square :
    HEq ((tensorComparison A S K
        (Etale.vectorIntegrationSource A N hA S d F)).hom ≫
      ((derivedTensor (ModuleCat.{u + 1} A) S).obj
         ((comparison A S).obj K)).map
          e.inv ≫ pp.inv)
      ((comparison A S).map pe.inv ≫
        (compactSupportSiteComparison A
          (Etale.vectorBundlePurityCompactification S d F)).inv.app ⟨_, hM⟩)
  integration_square :
    HEq ((compactSupportSiteComparison A
        (Etale.vectorBundlePurityCompactification S d F)).inv.app ⟨_, hM⟩ ≫
      ap)
      ((comparison A S).map
        ae)
  transpose_square :
    HEq (boundedSiteTranspose A
      (Etale.vectorBundlePurityCompactification S d F) (genericVectorExceptional A S d F)
      (Etale.vectorBundlePurityAdjunction A S d F)
      ⟨_, hM⟩ ((comparison A S).obj K)
      ap)
      ((comparison A _).map
        ((Etale.vectorBundlePurityAdjunction A S d F).homEquiv
           _ K ae) ≫
      boundedSiteRho A
        (genericVectorExceptional A S d F) K)
  ordinary_purity :
    IsIso ((Etale.vectorBundlePurityAdjunction
      A S d F).homEquiv
       _ K ae)
  ordinary_normalization :
    letI : IsAffineHom (VectorBundleZeroSection.π S d F) :=
      (Etale.vectorIntegration_geometry S d F).1
    letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
      (Etale.vectorIntegration_geometry S d F).2.1
    ∃ γ : WeilConjectures.PurityFiniteSetting.VectorPurityGamma A N hA S d F,
      WeilConjectures.PurityFiniteSetting.VectorPurityGammaNormalized
        A N hN hA S hS d F γ ∧
      HEq ((Etale.vectorBundlePurityAdjunction A S d F).homEquiv _ K ae)
        ((((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A)
          (VectorBundleZeroSection.scheme S d F)).hom.app
            ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).obj K)).app
              (Etale.vectorIntegrationCoefficient A N hA S d F)) ≫ γ.app K)

set_option linter.unusedVariables false in
/-- The canonical tensor comparison equations have witnesses.
Source: Stacks 099R, 0944 and 0B65; vector-bundle integration
(blueprint: def-pur-vector-tensor-site-equations). -/
def TensorCompatibility (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) S)
    (hK : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) S K) : Prop :=
  Nonempty (TensorCompatibilityData (Scheme.finiteTateCoefficient l E n)
    (l ^ (r + 1)) (pow_pos (Fact.out : l.Prime).pos _) hA S
    (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F K
    (vectorIntegration l E n S r hA d F hS) (vectorSite l E n S r hA d F hS))

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
