module

public import Sheaf.CategoryTheory.RingedSiteGlobalDerivedAdjunction
public import Mathlib.Algebra.Module.TransferInstance

/-! # Global and relative module cup products

Source: Stacks Project, Tags 0B6C, 0FPJ and 03FD
(blueprint: def-sfb-ringed-site-module-cup-product).

## Main definitions
- `global`: the adjoint of the tensor comparison followed by the two counits.
- `globalModuleCup`: the induced scalar-module cohomology product.
- `globalAbelianComparison`: the canonical comparison with additive sheaf cohomology.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace SheafOfModules.RingedSiteCup

/-- The relative derived cup product, with exactly the adjoint prescribed in Stacks 0B6C.
Source: Stacks Project, Tag 0B6C
(blueprint: def-sfb-ringed-site-module-cup-product). -/
def relative {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X) (K L : X.mateDerived) :
    Y.tensor.obj (e.right.obj K, e.right.obj L) ⟶
      e.right.obj (X.tensor.obj (K, L)) :=
  (e.derivedAdjunction.homEquiv _ _)
    ((e.tensorComparison a b).hom.app (e.right.obj K, e.right.obj L) ≫
      X.tensor.map (Prod.mkHom (e.derivedAdjunction.counit.app K)
        (e.derivedAdjunction.counit.app L)))

/-- The module-sheaf cup product in nonnegative degrees, in the specified order:
κ, cohomology of the relative derived cup, then the derived ordinary-tensor augmentation.
Source: Stacks Project, Tags 0B6C and 0FPJ
(blueprint: def-sfb-ringed-site-module-cup-product). -/
def moduleCup {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X) (F G : X.mateModules) (p q : ℕ) :
    (cohomology Y (p : ℤ)).obj (e.right.obj ((degreeZero X).obj F)) ⊗
      (cohomology Y (q : ℤ)).obj (e.right.obj ((degreeZero X).obj G)) ⟶
        (cohomology Y ((p : ℤ) + (q : ℤ))).obj
          (e.right.obj ((degreeZero X).obj (F ⊗ G))) :=
  cohomologyPairing Y a _ _ (p : ℤ) (q : ℤ) ≫
    (cohomology Y ((p : ℤ) + (q : ℤ))).map
      (relative e a b ((degreeZero X).obj F) ((degreeZero X).obj G) ≫
        e.right.map (tensorAugmentation X b F G))

/-- Cup product with a specified module multiplication F tensor G to H.
Source: Stacks Project, Tags 0B6C and 0FPJ
(blueprint: def-sfb-ringed-site-module-cup-product). -/
def moduleCupWith {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X)
    (F G H : X.mateModules) (m : F ⊗ G ⟶ H) (p q : ℕ) :
    (cohomology Y (p : ℤ)).obj (e.right.obj ((degreeZero X).obj F)) ⊗
      (cohomology Y (q : ℤ)).obj (e.right.obj ((degreeZero X).obj G)) ⟶
        (cohomology Y ((p : ℤ) + (q : ℤ))).obj (e.right.obj ((degreeZero X).obj H)) :=
  moduleCup e a b F G p q ≫
    (cohomology Y ((p : ℤ) + (q : ℤ))).map (e.right.map ((degreeZero X).map m))

/-- The global derived cup product in D(A) is the same adjoint-of-two-counits
construction for the canonical morphism to the ringed point with A=Γ(O).
Source: Stacks Project, Tag 0FPJ, applying Tag 0B6C
(blueprint: def-sfb-ringed-site-module-cup-product). -/
def global (X : RingedTensorCorner.{u, w}) (b : RingedTensorModel X)
    (K L : X.mateDerived) :
    (derivedGlobalSections X).obj K ⊗ (derivedGlobalSections X).obj L ⟶
      (derivedGlobalSections X).obj (X.tensor.obj (K, L)) :=
  ((globalDerivedAdjunction X).homEquiv _ _)
    ((globalLeftTensor X b).app
        ((derivedGlobalSections X).obj K, (derivedGlobalSections X).obj L) ≫
      X.tensor.map (Prod.mkHom ((globalDerivedAdjunction X).counit.app K)
        ((globalDerivedAdjunction X).counit.app L)))

/-- Scalar-module cohomology, with its actual A-module structure.
Source: Stacks Project, Tag 0FPJ
(blueprint: def-sfb-ringed-site-module-cup-product). -/
abbrev scalarCohomology (X : RingedTensorCorner.{u, w}) (n : ℤ) :=
  DerivedCategory.homologyFunctor (ModuleCat.{u} (scalars X)) n

/-- The cocycle-normalized κ in D(A), using the existing native derived tensor.
This is the coefficient-module version of the sheafified pairing above.
Source: Stacks Project, Tag 0FPJ
(blueprint: def-sfb-ringed-site-module-cup-product). -/
def ScalarPairingSpec (X : RingedTensorCorner.{u, w}) (U V : scalarDerived X) (p q : ℤ)
    (c : (scalarCohomology X p).obj U ⊗ (scalarCohomology X q).obj V ⟶
      (scalarCohomology X (p + q)).obj (U ⊗ V)) : Prop :=
  ∀ (P Q : CochainComplex (ModuleCat.{u} (scalars X)) ℤ)
    (_hP : ScalarFlatModel X P) (_hQ : ScalarFlatModel X Q)
    (i : DerivedCategory.Q.obj P ≅ U) (j : DerivedCategory.Q.obj Q ≅ V),
    ∃ z : P.cycles p ⊗ Q.cycles q ⟶ (P ⊗ Q).cycles (p + q),
      z ≫ (P ⊗ Q).iCycles (p + q) =
        (P.iCycles p ⊗ₘ Q.iCycles q) ≫
          HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ)
            p q (p + q) rfl ∧
      ((P.homologyπ p ≫
          (DerivedCategory.homologyFunctorFactors _ p).inv.app P ≫
          (scalarCohomology X p).map i.hom) ⊗ₘ
        (Q.homologyπ q ≫
          (DerivedCategory.homologyFunctorFactors _ q).inv.app Q ≫
          (scalarCohomology X q).map j.hom)) ≫ c ≫
          (scalarCohomology X (p + q)).map
            ((i.inv ⊗ₘ j.inv) ≫ Functor.LaxMonoidal.μ DerivedCategory.Q P Q) =
        z ≫ (P ⊗ Q).homologyπ (p + q) ≫
          (DerivedCategory.homologyFunctorFactors _ (p + q)).inv.app (P ⊗ Q)

/-- Scalar κ is uniquely determined by tensors of cocycles on flat K-flat models.
Source: Stacks Project, Tag 0FPJ
(blueprint: def-sfb-ringed-site-module-cup-product).

Proof: the signed Leibniz identity makes the tensor of cycles a cycle and sends
a boundary in either factor to a total boundary. Descend through both homology
quotients using the right exactness of tensor. The quotient maps tensor to an
epimorphism, giving uniqueness. Naturality and K-flat localization extend the
pairing to the derived objects; the native Q tensor comparison supplies exactly
the resolution identifications in the displayed normalization. -/
theorem scalarPairing_existsUnique (X : RingedTensorCorner.{u, w})
    (U V : scalarDerived X) (p q : ℤ) :
    ∃! c : (scalarCohomology X p).obj U ⊗ (scalarCohomology X q).obj V ⟶
        (scalarCohomology X (p + q)).obj (U ⊗ V),
      ScalarPairingSpec X U V p q c := by
  sorry

/-- The canonical κ on coefficient-module cohomology.
Source: Stacks Project, Tag 0FPJ
(blueprint: def-sfb-ringed-site-module-cup-product). -/
def scalarPairing (X : RingedTensorCorner.{u, w}) (U V : scalarDerived X) (p q : ℤ) :
    (scalarCohomology X p).obj U ⊗ (scalarCohomology X q).obj V ⟶
      (scalarCohomology X (p + q)).obj (U ⊗ V) :=
  Classical.choose (scalarPairing_existsUnique X U V p q)

/-- Global cup on H(RΓ), as an A-linear map from the ordinary tensor of cohomology modules.
Source: Stacks Project, Tag 0FPJ
(blueprint: def-sfb-ringed-site-module-cup-product). -/
def globalModuleCup (X : RingedTensorCorner.{u, w}) (b : RingedTensorModel X)
    (F G : X.mateModules) (p q : ℕ) :
    (scalarCohomology X (p : ℤ)).obj ((derivedGlobalSections X).obj ((degreeZero X).obj F)) ⊗
      (scalarCohomology X (q : ℤ)).obj
        ((derivedGlobalSections X).obj ((degreeZero X).obj G)) ⟶
      (scalarCohomology X ((p + q : ℕ) : ℤ)).obj
        ((derivedGlobalSections X).obj ((degreeZero X).obj (F ⊗ G))) := by
  simpa only [Nat.cast_add] using (scalarPairing X _ _ (p : ℤ) (q : ℤ) ≫
    (scalarCohomology X ((p : ℤ) + (q : ℤ))).map
      (global X b ((degreeZero X).obj F) ((degreeZero X).obj G) ≫
        (derivedGlobalSections X).map (tensorAugmentation X b F G)))

/-- Forgetting A from Γ gives the recorded compatible-family abelian global sections.
The projections of Γ, expressed by ΓNatIsoLim, identify a homomorphism O to F
with the compatible family of the images of 1.
Source: Stacks Project, Tag 0FPJ and the global-sections definition
(blueprint: def-sfb-ringed-site-module-cup-product).

Proof: unitHomEquiv identifies O-linear maps O to F with compatible sections
by evaluation at 1, with inverse s maps to (a maps to a*s). Both directions are
additive, and the scalar action becomes pointwise multiplication. The global
sections limit has these families as its universal cone, giving a natural
isomorphism. Its projections determine it uniquely. -/
theorem globalUnderlyingSections_existsUnique (X : RingedTensorCorner.{u, w}) :
    ∃! e : globalSections X ⋙ forget₂ (ModuleCat.{u} (scalars X)) AddCommGrpCat.{u} ≅
        CoefficientDerivedSections.coefficientSections X.ring,
      ∀ (F : X.mateModules) (s : (globalSections X).obj F) (U : X.siteᵒᵖ),
        (limit.π ((SheafOfModules.toSheaf _).obj F).obj U)
            ((Sheaf.ΓNatIsoLim X.topology AddCommGrpCat.{u}).hom.app
              ((SheafOfModules.toSheaf _).obj F) (e.hom.app F s)) =
          s.val.app U (1 : X.ring.obj.obj U) := by
  sorry

/-- The unit-normalized identification of the two global-sections encodings.
Source: Stacks Project, Tag 0FPJ
(blueprint: def-sfb-ringed-site-module-cup-product). -/
def globalUnderlyingSections (X : RingedTensorCorner.{u, w}) :
    globalSections X ⋙ forget₂ (ModuleCat.{u} (scalars X)) AddCommGrpCat.{u} ≅
      CoefficientDerivedSections.coefficientSections X.ring :=
  Classical.choose (globalUnderlyingSections_existsUnique X)

/-- The canonical right-derived unit, expressed at the complex localization Q.
Source: Stacks Project, Tags 0FPJ and 07A5
(blueprint: def-sfb-ringed-site-module-cup-product). -/
def globalDerivedUnit (X : RingedTensorCorner.{u, w}) :
    (globalSections X).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedGlobalSections X where
  app I := (globalSections X).rightDerivedFunctorUnitQ I
  naturality {_ _} f := (globalSections X).rightDerivedFunctorUnitQ_naturality f

/-- The same RΓ with scalars forgotten in its target derived category.
Source: Stacks Project, Tags 0FPJ and 03FD
(blueprint: def-sfb-ringed-site-module-cup-product). -/
def globalAbelianDerived (X : RingedTensorCorner.{u, w}) :
    X.mateDerived ⥤ DerivedCategory.{u} AddCommGrpCat.{u} :=
  derivedGlobalSections X ⋙
    (forget₂ (ModuleCat.{u} (scalars X)) AddCommGrpCat.{u}).mapDerivedCategory

/-- The right-derived unit for compatible-family sections, transported by evaluation at 1.
Source: Stacks Project, Tags 0FPJ and 03FD
(blueprint: def-sfb-ringed-site-module-cup-product). -/
def globalAbelianUnit (X : RingedTensorCorner.{u, w}) :
    CoefficientDerivedSections.coefficientComplexSections X.ring ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ globalAbelianDerived X :=
  (Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso
      (globalUnderlyingSections X) (.up ℤ)) DerivedCategory.Q).inv ≫
    Functor.whiskerLeft ((globalSections X).mapHomologicalComplex (.up ℤ))
      (forget₂ (ModuleCat.{u} (scalars X)) AddCommGrpCat.{u}).mapDerivedCategoryFactors.inv ≫
    Functor.whiskerRight (globalDerivedUnit X)
      (forget₂ (ModuleCat.{u} (scalars X)) AddCommGrpCat.{u}).mapDerivedCategory

/-- The transported unit still computes the right derived functor of module sections.
Source: Stacks Project, Tags 0FPJ and 03FD
(blueprint: def-sfb-ringed-site-module-cup-product).

Proof: on a K-injective source the module-derived unit is an isomorphism.
Forgetting scalars is exact and preserves that isomorphism, while the other
transport factors are natural isomorphisms. The K-injective criterion for
right derivation therefore applies. No flatness of A over the integers is used. -/
@[instance] theorem globalAbelianUnit_isRightDerived (X : RingedTensorCorner.{u, w}) :
    (globalAbelianDerived X).IsRightDerivedFunctor (globalAbelianUnit X)
      (HomologicalComplex.quasiIso X.mateModules (.up ℤ)) := by
  sorry

/-- The canonical comparison with cohomology of the underlying abelian sheaf.
Its choice is fixed by the recorded theorem's degree-zero identity, scalar
naturality, and formula for every comparison between the two injective resolutions.
Source: Stacks Project, Tag 03FD, as used in Tag 0FPJ
(blueprint: def-sfb-ringed-site-module-cup-product). -/
def globalAbelianComparison (X : RingedTensorCorner.{u, w}) (n : ℕ) :
    degreeZero X ⋙ globalAbelianDerived X ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} (n : ℤ) ≅
      SheafOfModules.toSheaf _ ⋙ (Sheaf.Γ X.topology AddCommGrpCat.{u}).rightDerived n :=
  (Classical.choose (CoefficientDerivedSections.global_module_abelian_cohomology
    X.topology X.ring (globalAbelianDerived X) (globalAbelianUnit X))) n

/-- Forgetting coefficients commutes canonically with homology, followed by the
recorded normalized module-to-abelian comparison.
Source: Stacks Project, Tags 03FD and 0FPJ
(blueprint: def-sfb-ringed-site-module-cup-product). -/
def globalCohomologyComparison (X : RingedTensorCorner.{u, w}) (F : X.mateModules)
    (n : ℕ) :
    (forget₂ (ModuleCat.{u} (scalars X)) AddCommGrpCat.{u}).obj
        ((scalarCohomology X (n : ℤ)).obj
          ((derivedGlobalSections X).obj ((degreeZero X).obj F))) ≅
      ((Sheaf.Γ X.topology AddCommGrpCat.{u}).rightDerived n).obj
        ((SheafOfModules.toSheaf _).obj F) :=
  ((forget₂ (ModuleCat.{u} (scalars X)) AddCommGrpCat.{u}).mapDerivedCategoryHomologyFunctorIso
    (n : ℤ)).app ((derivedGlobalSections X).obj ((degreeZero X).obj F)) ≪≫
    (globalAbelianComparison X n).app F

/-- The A-module action on additive sheaf cohomology, transported along the canonical
comparison. The dependency's scalar-naturality equation identifies it with the action
induced by multiplication on the coefficient sheaf.
Source: Stacks Project, Tags 03FD and 0FPJ
(blueprint: def-sfb-ringed-site-module-cup-product). -/
instance globalCohomologyModule (X : RingedTensorCorner.{u, w}) (F : X.mateModules) (n : ℕ) :
    Module (scalars X)
      (((Sheaf.Γ X.topology AddCommGrpCat.{u}).rightDerived n).obj
        ((SheafOfModules.toSheaf _).obj F)) :=
  letI : Module (scalars X)
      ((forget₂ (ModuleCat.{u} (scalars X)) AddCommGrpCat.{u}).obj
        ((scalarCohomology X (n : ℤ)).obj
          ((derivedGlobalSections X).obj ((degreeZero X).obj F)))) :=
    inferInstanceAs (Module (scalars X)
      ((scalarCohomology X (n : ℤ)).obj
        ((derivedGlobalSections X).obj ((degreeZero X).obj F))))
  AddEquiv.module (scalars X)
    (Iso.addCommGroupIsoToAddEquiv (globalCohomologyComparison X F n).symm)

/-- The canonical comparison is A-linear for the transported action.
Source: Stacks Project, Tags 03FD and 0FPJ
(blueprint: def-sfb-ringed-site-module-cup-product). -/
def globalCohomologyLinearEquiv (X : RingedTensorCorner.{u, w}) (F : X.mateModules)
    (n : ℕ) :
    ((Sheaf.Γ X.topology AddCommGrpCat.{u}).rightDerived n).obj
        ((SheafOfModules.toSheaf _).obj F) ≃ₗ[scalars X]
      (scalarCohomology X (n : ℤ)).obj
        ((derivedGlobalSections X).obj ((degreeZero X).obj F)) :=
  letI : Module (scalars X)
      ((forget₂ (ModuleCat.{u} (scalars X)) AddCommGrpCat.{u}).obj
        ((scalarCohomology X (n : ℤ)).obj
          ((derivedGlobalSections X).obj ((degreeZero X).obj F)))) :=
    inferInstanceAs (Module (scalars X)
      ((scalarCohomology X (n : ℤ)).obj
        ((derivedGlobalSections X).obj ((degreeZero X).obj F))))
  AddEquiv.linearEquiv (scalars X)
    (Iso.addCommGroupIsoToAddEquiv (globalCohomologyComparison X F n).symm)

/-- The global cup product as an A-linear map on the tensor of the actual additive
sheaf cohomology groups; thus its evaluation on pure tensors is A-bilinear.
Source: Stacks Project, Tags 0B6C, 0FPJ and 03FD
(blueprint: def-sfb-ringed-site-module-cup-product). -/
def globalCupLinear (X : RingedTensorCorner.{u, w}) (b : RingedTensorModel X)
    (F G : X.mateModules) (p q : ℕ) :
    TensorProduct (scalars X)
      (((Sheaf.Γ X.topology AddCommGrpCat.{u}).rightDerived p).obj
        ((SheafOfModules.toSheaf _).obj F))
      (((Sheaf.Γ X.topology AddCommGrpCat.{u}).rightDerived q).obj
        ((SheafOfModules.toSheaf _).obj G)) →ₗ[scalars X]
      ((Sheaf.Γ X.topology AddCommGrpCat.{u}).rightDerived (p + q)).obj
        ((SheafOfModules.toSheaf _).obj (F ⊗ G)) :=
  (globalCohomologyLinearEquiv X (F ⊗ G) (p + q)).symm.toLinearMap.comp
    ((globalModuleCup X b F G p q).hom.comp
      (TensorProduct.map (globalCohomologyLinearEquiv X F p).toLinearMap
        (globalCohomologyLinearEquiv X G q).toLinearMap))

/-- The binary global cup product on the actual right-derived additive sheaf groups.
Source: Stacks Project, Tags 0B6C, 0FPJ and 03FD
(blueprint: def-sfb-ringed-site-module-cup-product). -/
def globalCup (X : RingedTensorCorner.{u, w}) (b : RingedTensorModel X)
    (F G : X.mateModules) (p q : ℕ)
    (x : ((Sheaf.Γ X.topology AddCommGrpCat.{u}).rightDerived p).obj
      ((SheafOfModules.toSheaf _).obj F))
    (y : ((Sheaf.Γ X.topology AddCommGrpCat.{u}).rightDerived q).obj
      ((SheafOfModules.toSheaf _).obj G)) :
    ((Sheaf.Γ X.topology AddCommGrpCat.{u}).rightDerived (p + q)).obj
      ((SheafOfModules.toSheaf _).obj (F ⊗ G)) :=
  globalCupLinear X b F G p q (TensorProduct.tmul (scalars X) x y)

/-- Multiplication in the coefficients is composed after the cup product.
Source: Stacks Project, Tags 0B6C and 0FPJ
(blueprint: def-sfb-ringed-site-module-cup-product). -/
def globalCupWith (X : RingedTensorCorner.{u, w}) (b : RingedTensorModel X)
    (F G H : X.mateModules) (m : F ⊗ G ⟶ H) (p q : ℕ)
    (x : ((Sheaf.Γ X.topology AddCommGrpCat.{u}).rightDerived p).obj
      ((SheafOfModules.toSheaf _).obj F))
    (y : ((Sheaf.Γ X.topology AddCommGrpCat.{u}).rightDerived q).obj
      ((SheafOfModules.toSheaf _).obj G)) :
    ((Sheaf.Γ X.topology AddCommGrpCat.{u}).rightDerived (p + q)).obj
      ((SheafOfModules.toSheaf _).obj H) :=
  (((Sheaf.Γ X.topology AddCommGrpCat.{u}).rightDerived (p + q)).map
    ((SheafOfModules.toSheaf _).map m)) (globalCup X b F G p q x y)

end SheafOfModules.RingedSiteCup
