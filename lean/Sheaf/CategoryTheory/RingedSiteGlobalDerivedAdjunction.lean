module

public import Sheaf.CategoryTheory.RingedSiteCohomologyTensorMaps

/-! # Derived adjunction for the ringed point

Source: Stacks Project, Tags 0FPJ, 06YU and 07A5
(blueprint: def-sfb-ringed-site-global-derived-adjunction).

## Main definitions
- `globalSections`: module-valued compatible sections, via Hom(O,-).
- `globalPullback`: its universal left adjoint.
- `globalDerivedAdjunction`: the normalized unbounded derived adjunction.
- `globalLeftTensor`: the tensor comparison normalized on flat K-flat representatives.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace SheafOfModules.RingedSiteCup

/-- The coefficient ring A is the ring of compatible families, with pointwise operations.
Source: Stacks Project, Tag 0FPJ
(blueprint: def-sfb-ringed-site-global-derived-adjunction). -/
abbrev scalars (X : RingedTensorCorner.{u, w}) :=
  RingCat.sectionsSubring (X.ring.obj ⋙ forget₂ CommRingCat RingCat)

/-- The existing linear structure on module maps over the ring of global sections.
Source: Stacks Project, Tag 0FPJ
(blueprint: def-sfb-ringed-site-global-derived-adjunction). -/
instance globalLinear (X : RingedTensorCorner.{u, w}) : Linear (scalars X) X.mateModules :=
  SheafOfModules.homLinear X.ring.obj
    ((sheafCompose X.topology (forget₂ CommRingCat RingCat)).obj X.ring).property

/-- The existing Grothendieck structure supplies the K-injective resolutions for RΓ.
Source: Stacks Project, Tags 0FPJ and 07A5
(blueprint: def-sfb-ringed-site-global-derived-adjunction). -/
instance globalGrothendieck (X : RingedTensorCorner.{u, w}) :
    IsGrothendieckAbelian.{u} X.mateModules :=
  SheafOfModules.isGrothendieckAbelian _

/-- Module-valued global sections, equivalently compatible families via unitHomEquiv.
The scalar action is pointwise multiplication by a compatible family of ring sections.
Source: Stacks Project, Tag 0FPJ
(blueprint: def-sfb-ringed-site-global-derived-adjunction). -/
def globalSections (X : RingedTensorCorner.{u, w}) :
    X.mateModules ⥤ ModuleCat.{u} (scalars X) :=
  (linearCoyoneda (scalars X) X.mateModules).obj
    (op (SheafOfModules.unit
      ((sheafCompose X.topology (forget₂ CommRingCat RingCat)).obj X.ring)))

/-- Additivity of the module-valued global sections functor.
Source: Stacks Project, Tag 0FPJ
(blueprint: def-sfb-ringed-site-global-derived-adjunction).
Proof: Γ is the linear covariant Hom functor at O, hence addition of maps is pointwise. -/
@[instance] theorem globalSections_additive (X : RingedTensorCorner.{u, w}) :
    (globalSections X).Additive := by
  sorry

/-- The global-sections module functor has the canonical extension-of-scalars left adjoint.
Source: Stacks Project, Tag 0FPJ, the morphism to (Sh(pt),Γ(O))
(blueprint: def-sfb-ringed-site-global-derived-adjunction).

Proof: for an A-module M form the presheaf U maps to O(U) tensor_A M, with
restrictions induced by those of O, and sheafify it. A map from this sheaf to N
is the same as an A-linear map from M to compatible families of sections of N,
by tensor adjunction followed by sheafification adjunction. This bijection is
natural and constructs the required left adjoint. It is uniquely determined
with its unit by this universal property, not by arbitrary existence data. -/
@[instance] theorem globalSections_isRightAdjoint (X : RingedTensorCorner.{u, w}) :
    (globalSections X).IsRightAdjoint := by
  sorry

/-- Pullback from the point, selected by the global-sections adjunction universal property.
Its sections construction is sheafification of U maps to O(U) tensor_A M.
Source: Stacks Project, Tag 0FPJ
(blueprint: def-sfb-ringed-site-global-derived-adjunction). -/
def globalPullback (X : RingedTensorCorner.{u, w}) :
    ModuleCat.{u} (scalars X) ⥤ X.mateModules :=
  Functor.leftAdjoint (globalSections X)

/-- The universal adjunction defining pullback from the ringed point.
Source: Stacks Project, Tag 0FPJ
(blueprint: def-sfb-ringed-site-global-derived-adjunction). -/
def globalModuleAdjunction (X : RingedTensorCorner.{u, w}) :
    globalPullback X ⊣ globalSections X :=
  Adjunction.ofIsRightAdjoint (globalSections X)

/-- The defining left adjunction supplies all colimit preservation needed by total tensor.
Source: Stacks Project, Tag 0FPJ
(blueprint: def-sfb-ringed-site-global-derived-adjunction). -/
instance globalPullback_isLeftAdjoint (X : RingedTensorCorner.{u, w}) :
    (globalPullback X).IsLeftAdjoint :=
  (globalModuleAdjunction X).isLeftAdjoint

/-- Additivity of extension of scalars from global coefficients.
Source: Stacks Project, Tag 0FPJ
(blueprint: def-sfb-ringed-site-global-derived-adjunction).
Proof: the tensor and sheafification construction of the left adjoint is additive. -/
@[instance] theorem globalPullback_additive (X : RingedTensorCorner.{u, w}) :
    (globalPullback X).Additive := by
  sorry

/-- The ordinary tensor comparison is uniquely specified by the units on pure tensors.
The unit components are O-linear maps O to the indicated pullback modules, so the
right side is the map 1 maps to the tensor of their unit sections.
Source: Stacks Project, Tags 0B6C and 0FPJ
(blueprint: def-sfb-ringed-site-global-derived-adjunction).

Proof: the tensor universal property makes the tensor of the two unit maps an
A-bilinear map in x,y. Its adjunct gives the comparison. The unit formula fixes
it uniquely because pure tensors generate M tensor_A N and adjunction is a
bijection. Under the explicit sheafified tensor construction it is the usual
map a tensor (x tensor y) maps to (a tensor x) tensor (1 tensor y). -/
theorem globalPullbackTensor_existsUnique (X : RingedTensorCorner.{u, w}) :
    ∃! μ : (Functor.postcompose₂.obj (globalPullback X)).obj
          (curriedTensor (ModuleCat.{u} (scalars X))) ⟶
        (((Functor.whiskeringLeft₂ _).obj (globalPullback X)).obj
          (globalPullback X)).obj X.mateTensor,
      ∀ (M N : ModuleCat.{u} (scalars X)) (x : M) (y : N),
        (globalModuleAdjunction X).unit.app (M ⊗ N)
            (TensorProduct.tmul (scalars X) x y) ≫ (μ.app M).app N =
          (λ_ (SheafOfModules.unit
            ((sheafCompose X.topology (forget₂ CommRingCat RingCat)).obj X.ring))).inv ≫
              ((globalModuleAdjunction X).unit.app M x ⊗ₘ
                (globalModuleAdjunction X).unit.app N y) := by
  sorry

/-- The pure-tensor-normalized ordinary pullback comparison.
Source: Stacks Project, Tags 0B6C and 0FPJ
(blueprint: def-sfb-ringed-site-global-derived-adjunction). -/
def globalPullbackTensor (X : RingedTensorCorner.{u, w}) :
    (Functor.postcompose₂.obj (globalPullback X)).obj
        (curriedTensor (ModuleCat.{u} (scalars X))) ⟶
      (((Functor.whiskeringLeft₂ _).obj (globalPullback X)).obj
        (globalPullback X)).obj X.mateTensor :=
  Classical.choose (globalPullbackTensor_existsUnique X)

/-- Pullback from the point preserves the quasi-isomorphisms used in K-flat derivation.
Source: Stacks Project, Tags 0FPJ and 06YU
(blueprint: def-sfb-ringed-site-global-derived-adjunction).

Proof: on flat K-flat models the pullback is tensoring over A with O followed by
exact sheafification. The cone of a quasi-isomorphism of K-flat complexes is
acyclic K-flat; tensor with O preserves its acyclicity. This proves the claim. -/
@[instance] theorem globalPullback_preservesKFlatQuasiIso (X : RingedTensorCorner.{u, w}) :
    (globalPullback X).PreservesKFlatQuasiIso := by
  sorry

/-- The source module category has the existing native derived tensor structure.
Source: Stacks Project, Tag 0FPJ
(blueprint: def-sfb-ringed-site-global-derived-adjunction). -/
abbrev scalarDerived (X : RingedTensorCorner.{u, w}) :=
  DerivedCategory.{u} (ModuleCat.{u} (scalars X))

/-- Derived pullback from the point, using the existing K-flat left-derived construction.
Source: Stacks Project, Tags 0FPJ and 06YU
(blueprint: def-sfb-ringed-site-global-derived-adjunction). -/
def globalLeft (X : RingedTensorCorner.{u, w}) : scalarDerived X ⥤ X.mateDerived :=
  (globalPullback X).leftDerivedFunctor

/-- Derived global sections with values in D(A), computed by the existing K-injective functor.
Source: Stacks Project, Tags 0FPJ and 07A5
(blueprint: def-sfb-ringed-site-global-derived-adjunction). -/
def derivedGlobalSections (X : RingedTensorCorner.{u, w}) : X.mateDerived ⥤ scalarDerived X :=
  (globalSections X).rightDerivedFunctor

/-- The canonical left-derived comparison on complexes.
Source: Stacks Project, Tag 0FPJ
(blueprint: def-sfb-ringed-site-global-derived-adjunction). -/
def globalLeftComparison (X : RingedTensorCorner.{u, w})
    (P : CochainComplex (ModuleCat.{u} (scalars X)) ℤ) :
    (globalLeft X).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((globalPullback X).mapHomologicalComplex (.up ℤ)).obj P) :=
  derivedPullbackComplexComparison (globalPullback X) (globalLeft X)
    (globalPullback X).leftDerivedFunctorCounit P

/-- The canonical derived adjunction is fixed by its underived adjunction on complexes.
Source: Stacks Project, Tags 0B6C and 0FPJ
(blueprint: def-sfb-ringed-site-global-derived-adjunction).

Proof: apply the complex adjunction to K-flat source and K-injective target
representatives. Both derived comparison maps are isomorphisms there, so the
complex Hom bijection transfers to the derived categories. It is natural and
therefore gives an adjunction. The displayed formula follows before localization
and extends to all complexes by naturality. Such representatives cover every
pair of derived objects and determine every Hom bijection, proving uniqueness. -/
theorem globalDerivedAdjunction_existsUnique (X : RingedTensorCorner.{u, w}) :
    ∃! d : globalLeft X ⊣ derivedGlobalSections X,
      ∀ (P : CochainComplex (ModuleCat.{u} (scalars X)) ℤ)
        (I : CochainComplex X.mateModules ℤ)
        (f : ((globalPullback X).mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
        d.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
            (globalLeftComparison X P ≫ DerivedCategory.Q.map f) =
          DerivedCategory.Q.map
              (((globalModuleAdjunction X).mapHomologicalComplex (.up ℤ)).homEquiv P I f) ≫
            (globalSections X).rightDerivedFunctorUnitQ I := by
  sorry

/-- The uniquely normalized derived adjunction for global sections.
Source: Stacks Project, Tags 0B6C and 0FPJ
(blueprint: def-sfb-ringed-site-global-derived-adjunction). -/
def globalDerivedAdjunction (X : RingedTensorCorner.{u, w}) :
    globalLeft X ⊣ derivedGlobalSections X :=
  Classical.choose (globalDerivedAdjunction_existsUnique X)

/-- Flat-term K-flat coefficient complexes, used only to pin down the tensor comparison.
Source: Stacks Project, Tags 0FPJ and 06YU
(blueprint: def-sfb-ringed-site-global-derived-adjunction). -/
def ScalarFlatModel (X : RingedTensorCorner.{u, w})
    (P : CochainComplex (ModuleCat.{u} (scalars X)) ℤ) : Prop :=
  (HomologicalComplex.quasiIso (ModuleCat.{u} (scalars X)) (.up ℤ)).kFlat P ∧
    ∀ n : ℤ, ObjectProperty.flat (P.X n)

/-- Pullback from the point takes the flat models to flat K-flat module-sheaf models.
Source: Stacks Project, Tags 0FPJ and 06YU
(blueprint: def-sfb-ringed-site-global-derived-adjunction).

Proof: extension of scalars carries a flat A-module to a flat O-module, since
its tensor functor is tensor over A with that module. The same identity on
total complexes carries K-flat complexes to K-flat complexes: a test acyclic
O-complex stays acyclic after forgetting to A, and tensoring with P preserves
that acyclicity. Sheafification is exact. Apply the termwise assertion in every degree. -/
theorem globalPullback_flatModel (X : RingedTensorCorner.{u, w})
    (P : CochainComplex (ModuleCat.{u} (scalars X)) ℤ) (hP : ScalarFlatModel X P) :
    X.mateFlat (((globalPullback X).mapHomologicalComplex (.up ℤ)).obj P) := by
  sorry

/-- The derived tensor comparison from the point is uniquely normalized on flat models.
Source: Stacks Project, Tags 0B6C and 0FPJ
(blueprint: def-sfb-ringed-site-global-derived-adjunction).

Proof: apply the pure-tensor-normalized ordinary comparison in each bidegree and
sum over p+q=n, with the standard total signs. Pullback preserves sums, so this
is a chain isomorphism. On flat K-flat representatives both left-derived
counits are isomorphisms; conjugate this chain map by those counits and the two
recorded tensor comparisons. Naturality in both complexes descends through
quasi-isomorphisms. Flat K-flat descent proves existence and uniqueness of the
natural transformation with the displayed representative equation. -/
theorem globalLeftTensor_existsUnique (X : RingedTensorCorner.{u, w})
    (b : RingedTensorModel X) :
    ∃! μ : Functor.uncurry.obj (curriedTensor (scalarDerived X)) ⋙ globalLeft X ⟶
        ((globalLeft X).prod (globalLeft X)) ⋙ X.tensor,
      ∀ (P Q : CochainComplex (ModuleCat.{u} (scalars X)) ℤ)
        (hP : ScalarFlatModel X P) (hQ : ScalarFlatModel X Q),
        μ.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            X.tensor.map (Prod.mkHom (globalLeftComparison X P)
              (globalLeftComparison X Q)) =
          (globalLeft X).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
            globalLeftComparison X (P ⊗ Q) ≫
            DerivedCategory.Q.map
              (HomologicalComplex.mapBifunctorComparison
                (globalPullbackTensor X) (.up ℤ) P Q) ≫
            b.mateRepresentative.hom.app
              (⟨((globalPullback X).mapHomologicalComplex (.up ℤ)).obj P,
                  globalPullback_flatModel X P hP⟩,
                ⟨((globalPullback X).mapHomologicalComplex (.up ℤ)).obj Q,
                  globalPullback_flatModel X Q hQ⟩) := by
  sorry

/-- The canonical derived pullback tensor map from the point.
Source: Stacks Project, Tags 0B6C and 0FPJ
(blueprint: def-sfb-ringed-site-global-derived-adjunction). -/
def globalLeftTensor (X : RingedTensorCorner.{u, w}) (b : RingedTensorModel X) :
    Functor.uncurry.obj (curriedTensor (scalarDerived X)) ⋙ globalLeft X ⟶
      ((globalLeft X).prod (globalLeft X)) ⋙ X.tensor :=
  Classical.choose (globalLeftTensor_existsUnique X b)

/-- The prescribed pullback comparison is an isomorphism.
Source: Stacks Project, Tags 0B6C and 0FPJ
(blueprint: def-sfb-ringed-site-global-derived-adjunction).
Proof: the ordinary comparison has inverse (a tensor x) tensor (b tensor y)
maps to ab tensor (x tensor y). The corresponding total comparison and the
K-flat resolution comparisons are isomorphisms, hence so is every derived component. -/
@[instance] theorem globalLeftTensor_isIso (X : RingedTensorCorner.{u, w})
    (b : RingedTensorModel X) : IsIso (globalLeftTensor X b) := by
  sorry


end SheafOfModules.RingedSiteCup
