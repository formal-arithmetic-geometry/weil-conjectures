module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.Paper.RingedTopoiTensorSections
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Scalar global sections on the small étale model

Source: Stacks, Spaces Duality, Tag 0E58; Cohomology on Sites, Tags 0B6C and 08JA
(blueprint: def-sfb-space-affine-global-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pull back a scalar to each affine chart.
Source: Stacks 0B6C (blueprint: def-sfb-space-affine-global-sections). -/
def affineChartScalar {S : Scheme.{u}} (A : Type u) [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
    (T : X.SmallEtaleModelᵒᵖ) : A →+* X.smallStructureSheaf.obj.obj T :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫
    Scheme.Γ.map ((chartToScheme Y f (X.smallEtaleInclusion.obj T.unop) ≫ e.hom).op)).hom

/-- Pullback of scalars is compatible with every chart restriction.
Source: Stacks 0B6C (blueprint: def-sfb-space-affine-global-sections).
Proof: the chart maps to Y commute with their transition morphisms by the
costructured-arrow relation. Apply contravariant regular functions, then compose
with the same inverse Gamma-Spec map on both sides. -/
theorem affineChartScalar_naturality {S : Scheme.{u}} (A : Type u) [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
    {T U : X.SmallEtaleModelᵒᵖ} (i : T ⟶ U) (a : A) :
    X.smallStructureSheaf.obj.map i (affineChartScalar A Y e X f T a) =
      affineChartScalar A Y e X f U a := by
  sorry

/-- The scalar ring map into compatible global functions.
Source: Stacks 0B6C (blueprint: def-sfb-space-affine-global-sections). -/
def affineGlobalScalar {S : Scheme.{u}} (A : Type u) [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y) :
    A →+* RingCat.sectionsSubring X.smallStructureRings.obj where
  toFun a := ⟨fun T ↦ affineChartScalar A Y e X f T a,
    fun i ↦ affineChartScalar_naturality A Y e X f i a⟩
  map_one' := by ext T; exact map_one _
  map_mul' a b := by ext T; exact map_mul _ a b
  map_zero' := by ext T; exact map_zero _
  map_add' a b := by ext T; exact map_add _ a b

/-- Hom from O, with its actual A-action, is the ordinary scalar sections functor.
Source: Stacks 0B6C, 08JA (blueprint: def-sfb-space-affine-global-sections). -/
def affineScalarSections {S : Scheme.{u}} (A : Type u) [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y) :
    X.SmallModules ⥤ ModuleCat.{u} A :=
  letI : Linear (RingCat.sectionsSubring X.smallStructureRings.obj) X.SmallModules :=
    SheafOfModules.homLinear X.smallStructureSheaf.obj X.smallStructureRings.property
  (linearCoyoneda (RingCat.sectionsSubring X.smallStructureRings.obj)
    X.SmallModules).obj (op (SheafOfModules.unit X.smallStructureRings)) ⋙
      ModuleCat.restrictScalars (affineGlobalScalar A Y e X f)

/-- Scalar sections preserve sums of morphisms.
Source: Stacks 08JA (blueprint: def-sfb-space-affine-global-sections).
Proof: postcomposition on Hom(O,-) preserves sums; restriction of scalars preserves
those very same linear maps and their sums. -/
@[instance] theorem affineScalarSections_additive {S : Scheme.{u}} (A : Type u) [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y) :
    (affineScalarSections A Y e X f).Additive := by
  sorry

/-- Unbounded A-valued sections, computed by the canonical K-injective derived functor.
Source: Stacks 08JA (blueprint: def-sfb-space-affine-global-sections). -/
abbrev affineDerivedSections {S : Scheme.{u}} (A : Type u) [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
    [HasDerivedCategory.{w} X.SmallModules] :
    X.DerivedModules ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (affineScalarSections A Y e X f).rightDerivedFunctor

section ScalarPullback

variable {S : Scheme.{u}} (A : Type u) [CommRing A]
  (Y : Over S) (e : Y.left ≅ Spec (.of A))
  (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)

/-- Scalar sections have a left adjoint: sheafify the chartwise modules O(T) tensor_A M.
Source: Stacks 03EL (blueprint: def-sfb-space-affine-global-sections).
Proof: before sheafification, send M to the presheaf with value O(T) tensor_A M.
A map from this presheaf to N is equivalently an A-linear map from M to compatible
sections of N; the correspondence sends a tensor b tensor m to b times s(m).
Module sheafification gives the same bijection for module sheaves. -/
@[instance] theorem affineScalarSections_isRightAdjoint :
    (affineScalarSections A Y e X f).IsRightAdjoint := by
  sorry

/-- The universal scalar pullback; its objects are determined up to the adjunction isomorphism.
Source: Stacks 03EL (blueprint: def-sfb-space-affine-global-sections). -/
def affineScalarPullback : ModuleCat.{u} A ⥤ X.SmallModules :=
  (affineScalarSections A Y e X f).leftAdjoint

/-- The universal pullback/global-sections adjunction fixes both unit and counit.
Source: Stacks 03EL (blueprint: def-sfb-space-affine-global-sections). -/
def affineScalarAdjunction : affineScalarPullback A Y e X f ⊣ affineScalarSections A Y e X f :=
  Adjunction.ofIsRightAdjoint _

/-- The canonical pure section of scalar pullback, supplied by the adjunction unit.
Source: Stacks 03EL (blueprint: def-sfb-space-affine-global-sections). -/
def affinePullbackSection (M : ModuleCat.{u} A) (m : M) (T : X.SmallEtaleModelᵒᵖ) :
    ((affineScalarPullback A Y e X f).obj M).val.obj T :=
  (((affineScalarAdjunction A Y e X f).unit.app M m).val.app T)
    (1 : X.smallStructureRings.obj.obj T)

/-- Pullback is additive since its right adjoint is additive.
Source: Stacks 03EL (blueprint: def-sfb-space-affine-global-sections).
Proof: the adjunction identifies sums of maps with sums under sections. The Yoneda
criterion therefore identifies pullback of a sum with the sum of pullbacks. -/
@[instance] theorem affineScalarPullback_additive :
    (affineScalarPullback A Y e X f).Additive := by
  sorry

/-- The ordinary scalar tensor is uniquely determined on pure pulled-back sections.
Source: Stacks 03EL (blueprint: def-sfb-space-affine-global-sections). -/
def AffineScalarTensorNormalization
    (d : ∀ M N : ModuleCat.{u} A,
      (affineScalarPullback A Y e X f).obj
        ((MonoidalCategory.tensor (ModuleCat.{u} A)).obj (M, N)) ≅
      (SheafOfModules.monoidalCategory X.smallStructureSheaf).tensorObj
        ((affineScalarPullback A Y e X f).obj M)
        ((affineScalarPullback A Y e X f).obj N)) : Prop :=
  ∀ (M N : ModuleCat.{u} A) (T : X.SmallEtaleModelᵒᵖ) (m : M) (n : N),
    (d M N).hom.val.app T
      (affinePullbackSection A Y e X f _ (m ⊗ₜ[A] n) T) =
    SheafOfModules.RingedTensor.pure X.smallStructureSheaf _ _ T
      (affinePullbackSection A Y e X f M m T)
      (affinePullbackSection A Y e X f N n T)

/-- The pure-section normalization uniquely specifies the ordinary tensor comparison.
Source: Stacks 03EL (blueprint: def-sfb-space-affine-global-sections).
Proof: locally the pullback is O tensor_A M. Send b tensor (m tensor n) to
(b tensor m) tensor (1 tensor n), and reverse by multiplying the coefficients.
Balancedness gives inverse maps; sheafification glues them. Pure sections generate
locally, so the specified formula determines the map and its inverse uniquely. -/
theorem affineScalarTensor_existsUnique :
    ∃! d, AffineScalarTensorNormalization A Y e X f d := by
  sorry

/-- The universal pure-section tensor comparison.
Source: Stacks 03EL (blueprint: def-sfb-space-affine-global-sections). -/
def affineScalarTensor :=
  Classical.choose (affineScalarTensor_existsUnique A Y e X f)

/-- Tensor comparison commutes with both module maps.
Source: Stacks 03EL (blueprint: def-sfb-space-affine-global-sections).
Proof: both composites take each pulled-back m tensor n to the tensor of the two
pulled-back images. Local generation by pure sections gives the equality. -/
theorem affineScalarTensor_naturality {M M' N N' : ModuleCat.{u} A}
    (g : M ⟶ M') (h : N ⟶ N') :
    letI := SheafOfModules.monoidalCategory X.smallStructureSheaf
    (affineScalarPullback A Y e X f).map (MonoidalCategory.tensorHom g h) ≫
      (affineScalarTensor A Y e X f M' N').hom =
    (affineScalarTensor A Y e X f M N).hom ≫ MonoidalCategory.tensorHom
      ((affineScalarPullback A Y e X f).map g)
      ((affineScalarPullback A Y e X f).map h) := by
  sorry

/-- Scalar pullback preserves quasi-isomorphisms between K-flat module complexes.
Source: Stacks 06YY, 07A4 (blueprint: def-sfb-space-affine-global-sections).
Proof: on each chart it is extension of scalars followed by sheafification. The cone
of a quasi-isomorphism between K-flat complexes is K-flat acyclic; tensoring with
the chart ring is acyclic. Exact sheafification and descent preserve this assertion. -/
@[instance] theorem affineScalarPullback_preservesKFlatQuasiIso :
    (affineScalarPullback A Y e X f).PreservesKFlatQuasiIso := by
  sorry

variable [HasDerivedCategory.{w} X.SmallModules]

/-- The universal K-flat scalar pullback on unbounded derived categories.
Source: Stacks 07A4 (blueprint: def-sfb-space-affine-global-sections). -/
abbrev affineDerivedScalarPullback :
    DerivedCategory (ModuleCat.{u} A) ⥤ X.DerivedModules :=
  (affineScalarPullback A Y e X f).leftDerivedFunctor

/-- Postcomposition of this K-flat left derived functor is still left derived.
Source: Stacks 06YY (blueprint: def-sfb-space-affine-global-sections).
Proof: its comparison is invertible on K-flat complexes, and remains so after any
functor. The K-flat left derivability structure gives the asserted universal property. -/
@[instance] theorem affineDerivedScalarPullback_absolute :
    ((affineDerivedScalarPullback A Y e X f) ⋙
      affineDerivedSections A Y e X f).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
        (affineScalarPullback A Y e X f).leftDerivedFunctorCounit
        (affineDerivedSections A Y e X f))
      (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ)) := by
  sorry

/-- Postcomposition of K-injective scalar sections is still right derived.
Source: Stacks 070K (blueprint: def-sfb-space-affine-global-sections).
Proof: the derived unit is invertible on K-injectives, also after postcomposition.
The K-injective right derivability structure gives the universal property. -/
@[instance] theorem affineDerivedSections_absolute :
    ((affineDerivedSections A Y e X f) ⋙
      affineDerivedScalarPullback A Y e X f).IsRightDerivedFunctor
      (Functor.whiskerRight (affineScalarSections A Y e X f).rightDerivedFunctorUnit
        (affineDerivedScalarPullback A Y e X f) ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso X.SmallModules (.up ℤ)) := by
  sorry

/-- Derived scalar adjunction with the actual universal derived unit and counit.
Source: Stacks 07A4 (blueprint: def-sfb-space-affine-global-sections). -/
def affineDerivedScalarAdjunction :
    affineDerivedScalarPullback A Y e X f ⊣ affineDerivedSections A Y e X f :=
  ((affineScalarAdjunction A Y e X f).mapHomotopyCategory (.up ℤ)).derived
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ))
    (HomotopyCategory.quasiIso X.SmallModules (.up ℤ))
    (affineScalarPullback A Y e X f).leftDerivedFunctorCounit
    (affineScalarSections A Y e X f).rightDerivedFunctorUnit


/-- The comparison on complexes induced by the universal left-derived counit.
Source: Stacks 06YY (blueprint: def-sfb-space-affine-global-sections). -/
def affineScalarComplexComparison (P : CochainComplex (ModuleCat.{u} A) ℤ) :=
  derivedPullbackComplexComparison (affineScalarPullback A Y e X f)
    (affineDerivedScalarPullback A Y e X f)
    (affineScalarPullback A Y e X f).leftDerivedFunctorCounit P

/-- The signed total of the ordinary tensor comparison, before localization.
Source: Stacks 07A4 (blueprint: def-sfb-space-affine-global-sections). -/
def affineScalarTensorTotal (P Q : CochainComplex (ModuleCat.{u} A) ℤ) :=
  letI := SheafOfModules.monoidalCategory X.smallStructureSheaf
  letI := SheafOfModules.ringedTensorPreadditive X.smallStructureSheaf
  tensorPullbackTotal (affineScalarPullback A Y e X f)
    (affineScalarTensor A Y e X f) (affineScalarTensor_naturality A Y e X f) P Q

/-- Characterization on K-flat representatives with flat terms of the derived tensor map.
Its ordinary tensor map is already fixed by pulled-back pure sections.
Source: Stacks 07A4 (blueprint: def-sfb-space-affine-global-sections). -/
def AffineDerivedScalarTensorNormalization
    (d : MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u} A)) ⋙
        affineDerivedScalarPullback A Y e X f ≅
      ((affineDerivedScalarPullback A Y e X f).prod
        (affineDerivedScalarPullback A Y e X f)) ⋙ X.derivedDualityModel.closed.tensor) : Prop :=
  ∀ (P Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (_ : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P)
    (_ : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat Q)
    (_ : ∀ n : ℤ, Module.Flat A (P.X n)) (_ : ∀ n : ℤ, Module.Flat A (Q.X n)),
    ∃ hP : CochainComplex.IsKFlatIndependentCoefficients
        (J := X.smallEtaleModelTopology) (R := X.smallStructureSheaf)
        (((affineScalarPullback A Y e X f).mapHomologicalComplex (.up ℤ)).obj P),
    ∃ hQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := X.smallEtaleModelTopology) (R := X.smallStructureSheaf)
        (((affineScalarPullback A Y e X f).mapHomologicalComplex (.up ℤ)).obj Q),
    (affineDerivedScalarPullback A Y e X f).map
        (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      affineScalarComplexComparison A Y e X f
        (CochainComplex.mapBifunctor P Q (MonoidalCategory.curriedTensor _)) =
    (d.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      X.derivedDualityModel.closed.tensor.map
        (X := ((affineDerivedScalarPullback A Y e X f).obj (DerivedCategory.Q.obj P),
          (affineDerivedScalarPullback A Y e X f).obj (DerivedCategory.Q.obj Q)))
        (Y := (DerivedCategory.Q.obj
          (((affineScalarPullback A Y e X f).mapHomologicalComplex (.up ℤ)).obj P),
          DerivedCategory.Q.obj
          (((affineScalarPullback A Y e X f).mapHomologicalComplex (.up ℤ)).obj Q)))
        (affineScalarComplexComparison A Y e X f P,
          affineScalarComplexComparison A Y e X f Q) ≫
      (X.derivedDualityModel.models.iso X.smallEtaleModelTopology X.smallStructureSheaf
        X.derivedDualityModel.closed _ _ hP hQ).inv ≫
      DerivedCategory.Q.map (affineScalarTensorTotal A Y e X f P Q)

/-- Existence and uniqueness of the tensor comparison with its representative formula.
Source: Stacks 07A4 (blueprint: def-sfb-space-affine-global-sections).
Proof: scalar pullback preserves flat modules and K-flat complexes. On simultaneous
K-flat resolutions with flat terms use the signed total of the ordinary tensor map.
All three comparison maps are isomorphisms on these representatives. Naturality and
localization descend the isomorphisms; full faithfulness of whiskering by the resolving
K-flat subcategory proves uniqueness. The displayed formula is the descent square. -/
theorem affineDerivedScalarTensor_existsUnique :
    ∃! d, AffineDerivedScalarTensorNormalization A Y e X f d := by
  sorry

/-- The uniquely normalized derived scalar tensor comparison.
Source: Stacks 07A4 (blueprint: def-sfb-space-affine-global-sections). -/
def affineDerivedScalarTensor :=
  Classical.choose (affineDerivedScalarTensor_existsUnique A Y e X f)

/-- The canonical cup product is the adjoint of the tensor of the derived counits.
Source: Stacks 0B6C (blueprint: def-sfb-space-affine-global-sections). -/
def affineDerivedCup (K L : X.DerivedModules) :
    (MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u} A))).obj
        ((affineDerivedSections A Y e X f).obj K,
          (affineDerivedSections A Y e X f).obj L) ⟶
      (affineDerivedSections A Y e X f).obj (X.derivedDualityModel.closed.tensor.obj (K, L)) :=
  (affineDerivedScalarAdjunction A Y e X f).homEquiv _ _
    ((affineDerivedScalarTensor A Y e X f).hom.app _ ≫
      X.derivedDualityModel.closed.tensor.map
        ((affineDerivedScalarAdjunction A Y e X f).counit.app K,
          (affineDerivedScalarAdjunction A Y e X f).counit.app L))

end ScalarPullback

end AlgebraicGeometry.AlgebraicSpace

