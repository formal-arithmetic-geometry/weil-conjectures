module

public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackRecordedComposition
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel
public import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
public import WeilConjectures.AlgebraicGeometry.Modules.AffineTildeTensor
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-! # Affine algebra classes and evaluation

Source: Stacks Project, perfect.tex, Tag 0A6H(3)(a); sites-cohomology.tex,
Tag 08J9; duality.tex, Tag 0E2U.
(blueprint: def-trf-affine-algebra-class-comparison-data).

The comparison is specified by evaluation. The auxiliary records package the
canonical tensor and restriction identifications together with their equations on
representatives. No arbitrary derived-Hom isomorphism is used in place of that map.

## Main definitions

- `Realizations` and `Normalized`: the affine realization and its representative equations.
- `gamma`, `localization`, `openHom`: the evaluation-defined comparison arrows.
- `classMap`, `algebraMultiplication`: the module algebra-class transpose and multiplication.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.AffineClassComparison

/-- Ordinary module derived category, with its existing small-Hom localization.
Source: Stacks 05RU (blueprint: def-trf-affine-algebra-class-comparison-data). -/
abbrev DMod (B : Type u) [CommRing B] := DerivedCategory (ModuleCat.{u} B)

/-- The termwise associated-sheaf functor, with the shared sheaf-of-modules carrier.
Source: Stacks 06Z0 (blueprint: def-trf-affine-algebra-class-comparison-data). -/
abbrev tildeComplex (B : Type u) [CommRing B] :=
  @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} B ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))
      (tilde.functor (.of B))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)

/-- A module placed in degree zero, then localized.
Source: Stacks 0E2U (blueprint: def-trf-affine-algebra-class-comparison-data). -/
abbrev zeroComplex (B : Type u) [CommRing B] (M : ModuleCat.{u} B) : DMod B :=
  DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M)

/-- The already recorded ordinary-module RHom, without a new Hom construction.
Source: Stacks 08J9 (blueprint: def-trf-affine-algebra-class-comparison-data). -/
abbrev hom (B : Type u) [CommRing B] (E T : DMod B) : DMod B :=
  (ordinaryModuleDerivedInternalHom B).obj (op E, T)

/-- Evaluation in the order RHom(E,T) tensor E used by the node.
Source: Stacks 08J9 (blueprint: def-trf-affine-algebra-class-comparison-data). -/
@[irreducible] def evaluation (B : Type u) [CommRing B] (E T : DMod B) : hom B E T ⊗ E ⟶ T :=
  (@BraidedCategory.braiding _ _ _
    (DerivedCategory.braidedCategory' (ModuleCat.{u} B)) (hom B E T) E).hom ≫ (ihom.ev E).app T

/-- Transpose with that same tensor order. Mathlib's curry uses E tensor V.
Source: Stacks 08J9 (blueprint: def-trf-affine-algebra-class-comparison-data). -/
@[irreducible] def transpose (B : Type u) [CommRing B] (E V T : DMod B) (f : V ⊗ E ⟶ T) :
    V ⟶ hom B E T :=
  MonoidalClosed.curry ((@BraidedCategory.braiding _ _ _
    (DerivedCategory.braidedCategory' (ModuleCat.{u} B)) E V).hom ≫ f)

/-- The evaluation-defined change-of-rings map, for the normalized monoidal
scalar extension already recorded by lem-pur-derived-change-of-rings.
Source: Stacks 08J9, 06YY (blueprint: def-trf-affine-algebra-class-comparison-data). -/
@[irreducible] def localization {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D)
    (E T : DMod B) :
    (ModuleCat.ordinaryDerivedExtendScalars φ).obj (hom B E T) ⟶
      hom D ((ModuleCat.ordinaryDerivedExtendScalars φ).obj E)
        ((ModuleCat.ordinaryDerivedExtendScalars φ).obj T) :=
  transpose D _ _ _
    (Functor.LaxMonoidal.μ (ModuleCat.ordinaryDerivedExtendScalars φ) _ _ ≫
      (ModuleCat.ordinaryDerivedExtendScalars φ).map (evaluation B E T))

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The existing internal Hom of sheaves on Spec B.
Source: Stacks 08J9 (blueprint: def-trf-affine-algebra-class-comparison-data). -/
abbrev sheafHom (B : Type u) [CommRing B]
    (E T : schemeDerivedCategory (Spec (.of B))) :=
  (derivedInternalHom (Opens.grothendieckTopology (Spec (.of B)))
    (Spec (.of B)).sheaf).obj (op E, T)

/-- The ordinary tilde tensor arrow is the unique arrow specified on canonical
pure tensor sections by the recorded affine tilde tensor theorem.
Source: Stacks 01I8 (blueprint: def-trf-affine-algebra-class-comparison-data). -/
@[irreducible] def ordinaryTensor (B : Type u) [CommRing B] (M N : ModuleCat.{u} B) :
    tilde (R := .of B) (M ⊗ N) ⟶ tilde (R := .of B) M ⊗ tilde (R := .of B) N :=
  (affine_tilde_tensor (.of B) M N).choose_spec.2.2.choose

/-- The original pullback complex functor, retaining its recorded additive witness.
Source: Stacks 06YJ (blueprint: def-trf-affine-algebra-class-comparison-data). -/
def pullbackComplex {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D) :
    CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) ℤ ⥤
    CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace)) ℤ :=
  letI := (recordedPullbackData (Spec.map (CommRingCat.ofHom φ))).additive
  (recordedPullbackData (Spec.map (CommRingCat.ofHom φ))).E.mapHomologicalComplex (.up ℤ)

/-- The cochain component of the original derived-pullback counit. All arrows
are retained localization comparisons, rather than a fresh choice of a counit.
Source: Stacks 06YJ (blueprint: def-trf-affine-algebra-class-comparison-data). -/
@[irreducible] def pullbackCounit {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D)
    (P : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) ℤ) :
    (derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((pullbackComplex φ).obj P) :=
  letI := (recordedPullbackData (Spec.map (CommRingCat.ofHom φ))).additive
  (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map
      (DerivedCategory.quotientCompQhIso _ |>.inv.app P) ≫
    (recordedPullbackData (Spec.map (CommRingCat.ofHom φ))).ε.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((recordedPullbackData (Spec.map (CommRingCat.ofHom φ))).E.mapHomotopyCategoryFactors
         (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app ((pullbackComplex φ).obj P)

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- A concrete affine realization system. The factorization is the one supplied
by lem-pc-affine-qcoh-derived-equivalence. Tensor arrows are pinned on every
summand of the ordinary total tensor and then on K-flat representatives.
The restriction arrows use the original pullback counit and the ordinary
unit-normalized tilde/pullback map of Tag 01I9.
Source: Stacks 06Z0, 08DX, 08DW, 01I8, 01I9
(blueprint: def-trf-affine-algebra-class-comparison-data). -/
structure Realizations where
  F : ∀ (B : Type u) [CommRing B], DMod B ⥤ schemeDerivedCategory (Spec (.of B))

  factor : ∀ (B : Type u) [CommRing B],
    DerivedCategory.Q ⋙ F B ≅ tildeComplex B ⋙ DerivedCategory.Q

  tensor : ∀ (B : Type u) [CommRing B] (P Q : DMod B),
    (F B).obj P ⊗ (F B).obj Q ≅ (F B).obj (P ⊗ Q)

  totalTensor : ∀ (B : Type u) [CommRing B]
    (P Q : CochainComplex (ModuleCat.{u} B) ℤ),
    (tildeComplex B).obj (P ⊗ Q) ≅
      pullbackTensorTotal (Spec (.of B)) ((tildeComplex B).obj P) ((tildeComplex B).obj Q)

  rho : ∀ {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) →
      ((F B ⋙ derivedPullback (Spec.map (CommRingCat.ofHom φ))) ≅
        (ModuleCat.ordinaryDerivedExtendScalars φ ⋙ F D))

  pullbackTotal : ∀ {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D)
    (P : CochainComplex (ModuleCat.{u} B) ℤ),
    (pullbackComplex φ).obj ((tildeComplex B).obj P) ≅
      (tildeComplex D).obj (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P)

  pullbackMonoidal : ∀ {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D),
    (derivedPullback (Spec.map (CommRingCat.ofHom φ))).CoreMonoidal

  extensionComp : ∀ {B D A : Type u} [CommRing B] [CommRing D] [CommRing A]
    (φ : B →+* D) (ψ : D →+* A),
    ModuleCat.ordinaryDerivedExtendScalars (ψ.comp φ) ≅
      (ModuleCat.ordinaryDerivedExtendScalars φ ⋙ ModuleCat.ordinaryDerivedExtendScalars ψ)

/-- Representative equations specifying the canonical realization data. Keeping
these equations in a conjunction avoids unnecessary recursors for proof fields.
Source: Stacks 06Z0, 08DW, 01I8, 01I9
(blueprint: def-trf-affine-algebra-class-comparison-data). -/
def Normalized (s : Realizations.{u, w}) : Prop :=
  -- tensor_natural
  (∀ (B : Type u) [CommRing B] (P P' Q Q' : DMod B)
    (p : P ⟶ P') (q : Q ⟶ Q'),
    ((s.F B).map p ⊗ₘ (s.F B).map q) ≫ (s.tensor B P' Q').hom =
      (s.tensor B P Q).hom ≫ (s.F B).map (p ⊗ₘ q)) ∧
  -- totalTensor_normalized
  (∀ (B : Type u) [CommRing B]
    (P Q : CochainComplex (ModuleCat.{u} B) ℤ) (p q n : ℤ) (h : p + q = n),
    letI := SheafOfModules.isMonoidal_W (Spec (.of B)).sheaf
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor (Spec (.of B)).sheaf
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj (Spec (.of B)).sheaf
    (tilde.functor (.of B)).map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
        (s.totalTensor B P Q).hom.f n =
      ordinaryTensor B (P.X p) (Q.X q) ≫
        HomologicalComplex.ιMapBifunctor ((tildeComplex B).obj P)
          ((tildeComplex B).obj Q)
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory (Spec (.of B)).sheaf))
          (.up ℤ) p q n h) ∧
  -- tensor_normalized
  (∀ (B : Type u) [CommRing B]
    (P Q : CochainComplex (ModuleCat.{u} B) ℤ),
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)).kFlat P →
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)).kFlat Q →
    (s.tensor B (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        (s.F B).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        (s.factor B).hom.app (P ⊗ Q) ≫ DerivedCategory.Q.map (s.totalTensor B P Q).hom =
      ((s.factor B).hom.app P ⊗ₘ (s.factor B).hom.app Q) ≫
        pullbackTensorModelMap (Spec (.of B)) ((tildeComplex B).obj P) ((tildeComplex B).obj Q)) ∧
  -- pullbackTotal_normalized
  (∀ {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D)
    (P : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ),
    (s.pullbackTotal φ P).hom.f n =
      eqToHom ((recordedPullbackData (Spec.map (CommRingCat.ofHom φ))).obj_eq
        ((tilde.functor (.of B)).obj (P.X n))) ≫
      (Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
        (CommRingCat.ofHom φ))).hom.app (P.X n)) ∧
  -- rho_normalized
  (∀ {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D)
    (hj : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)))
    (P : CochainComplex (ModuleCat.{u} B) ℤ),
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)).kFlat P →
    (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map ((s.factor B).hom.app P) ≫
        pullbackCounit φ ((tildeComplex B).obj P) ≫
        DerivedCategory.Q.map (s.pullbackTotal φ P).hom =
      (s.rho φ hj).hom.app (DerivedCategory.Q.obj P) ≫
        (s.F D).map ((ModuleCat.ordinaryDerivedChangeOfRings φ).counit.app P) ≫
        (s.factor D).hom.app (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P)) ∧
  -- pullbackMonoidal_normalized
  (∀ {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D),
    IsDerivedPullbackMonoidalModel (Spec.map (CommRingCat.ofHom φ)) (s.pullbackMonoidal φ)) ∧
  -- rho_tensor
  (∀ {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D)
    (hj : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))) (P Q : DMod B),
    ((s.pullbackMonoidal φ).μIso ((s.F B).obj P) ((s.F B).obj Q)).hom ≫
        (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map (s.tensor B P Q).hom ≫
        (s.rho φ hj).hom.app (P ⊗ Q) =
      ((s.rho φ hj).hom.app P ⊗ₘ (s.rho φ hj).hom.app Q) ≫
        (s.tensor D ((ModuleCat.ordinaryDerivedExtendScalars φ).obj P)
          ((ModuleCat.ordinaryDerivedExtendScalars φ).obj Q)).hom ≫
        (s.F D).map (Functor.LaxMonoidal.μ (ModuleCat.ordinaryDerivedExtendScalars φ) P Q)) ∧
  -- extensionComp_normalized
  (∀ {B D A : Type u} [CommRing B] [CommRing D] [CommRing A]
    (φ : B →+* D) (ψ : D →+* A) (P : CochainComplex (ModuleCat.{u} B) ℤ),
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)).kFlat P →
    (s.extensionComp φ ψ).hom.app (DerivedCategory.Q.obj P) ≫
        (ModuleCat.ordinaryDerivedExtendScalars ψ).map
          ((ModuleCat.ordinaryDerivedChangeOfRings φ).counit.app P) ≫
        (ModuleCat.ordinaryDerivedChangeOfRings ψ).counit.app
          (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P) =
      (ModuleCat.ordinaryDerivedChangeOfRings (ψ.comp φ)).counit.app P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp φ ψ) (.up ℤ)).hom.app P)) ∧
  -- rho_comp
  (∀ {B D A : Type u} [CommRing B] [CommRing D] [CommRing A]
    (φ : B →+* D) (ψ : D →+* A)
    (hj : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)))
    (hk : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ)))
    (hjk : IsOpenImmersion (Spec.map (CommRingCat.ofHom (ψ.comp φ)))) (P : DMod B),
    (derivedPullback (Spec.map (CommRingCat.ofHom ψ))).map ((s.rho φ hj).hom.app P) ≫
        (s.rho ψ hk).hom.app ((ModuleCat.ordinaryDerivedExtendScalars φ).obj P) =
      (recordedDerivedPullbackComposition (Spec.map (CommRingCat.ofHom ψ))
        (Spec.map (CommRingCat.ofHom φ))).hom.app ((s.F B).obj P) ≫
        (eqToHom (congrArg (fun f : Spec (.of A) ⟶ Spec (.of B) ↦ derivedPullback f)
          (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)).symm)).app
            ((s.F B).obj P) ≫
        (s.rho (ψ.comp φ) hjk).hom.app P ≫ (s.F A).map ((s.extensionComp φ ψ).hom.app P))

/-- The actual comparison is the transpose of realized evaluation. This defines
it for every pair of derived modules before imposing the hypotheses for invertibility.
Source: Stacks 08J9, 0A6H (blueprint: def-trf-affine-algebra-class-comparison-data). -/
@[irreducible] def gamma (s : Realizations.{u, w}) (B : Type u) [CommRing B] (E T : DMod B) :
    (s.F B).obj (hom B E T) ⟶ sheafHom B ((s.F B).obj E) ((s.F B).obj T) :=
  (schemeDerivedTensorHomEquiv (Spec (.of B)) _ _ _).symm
    ((s.tensor B (hom B E T) E).hom ≫ (s.F B).map (evaluation B E T))

/-- The multiplication-class transpose for an arbitrary derived multiplication.
The algebra specialization in the final theorem pins that multiplication to
ordinary multiplication in degree zero; this helper adds no algebra hypothesis.
Source: Stacks 0E2U, 08J9 (blueprint: def-trf-affine-algebra-class-comparison-data). -/
@[irreducible] def classMap (B : Type u) [CommRing B] (E T : DMod B)
    (μ : E ⊗ E ⟶ E) (ξ : E ⟶ T) : E ⟶ hom B E T :=
  transpose B E E T (μ ≫ ξ)

/-- Open restriction of RHom, defined by transposing restricted evaluation.
Source: Stacks 08DL, 08J9 (blueprint: def-trf-affine-algebra-class-comparison-data). -/
@[irreducible] def openHom (s : Realizations.{u, w}) {B D : Type u} [CommRing B] [CommRing D]
    (φ : B →+* D) (K L : schemeDerivedCategory (Spec (.of B))) :
    (derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj (sheafHom B K L) ⟶
      sheafHom D ((derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj K)
        ((derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj L) :=
  (schemeDerivedTensorHomEquiv (Spec (.of D)) _ _ _).symm
    (((s.pullbackMonoidal φ).μIso (sheafHom B K L) K).hom ≫
      (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map
        (schemeDerivedTensorHomEquiv (Spec (.of B)) _ _ _ (𝟙 (sheafHom B K L))))

/-- Ordinary algebra multiplication followed by the localization tensorator.
Thus the multiplication is fixed even when C is not flat over B.
Source: Stacks 0E2U (blueprint: def-trf-affine-algebra-class-comparison-data). -/
@[irreducible] def algebraMultiplication (B C : Type u) [CommRing B] [CommRing C] [Algebra B C] :
    zeroComplex B (ModuleCat.of B C) ⊗ zeroComplex B (ModuleCat.of B C) ⟶
      zeroComplex B (ModuleCat.of B C) :=
  Functor.LaxMonoidal.μ DerivedCategory.Q _ _ ≫
    DerivedCategory.Q.map
      ((CochainComplex.mapBifunctorSingle₁Iso (curriedTensor (ModuleCat.{u} B))
        (ModuleCat.of B C)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (ModuleCat.of B C))).hom ≫
      (HomologicalComplex.singleMapHomologicalComplex (tensorLeft (ModuleCat.of B C))
        (.up ℤ) 0).hom.app (ModuleCat.of B C) ≫
      (HomologicalComplex.single _ (.up ℤ) 0).map (ModuleCat.ofHom (LinearMap.mul' B C)))

/-- The canonical degree-zero scalar-extension arrow. For an affine open map it
is an isomorphism because scalar extension is exact.
Source: Stacks 06YY, 08DW (blueprint: def-trf-affine-algebra-class-comparison-data). -/
@[irreducible] def zeroComparison {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D)
    (M : ModuleCat.{u} B) :
    (ModuleCat.ordinaryDerivedExtendScalars φ).obj (zeroComplex B M) ⟶
      zeroComplex D ((ModuleCat.extendScalars φ).obj M) :=
  (ModuleCat.ordinaryDerivedChangeOfRings φ).counit.app
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars φ)
        (.up ℤ) 0).hom.app M)

/-- Multiplication of D tensor_B C in its ordinary degree-zero complex.
The B-algebra structure on D here is the one induced by the specified ring map.
Source: Stacks 0E2U (blueprint: def-trf-affine-algebra-class-comparison-data). -/
@[irreducible] def baseChangedMultiplication {B D : Type u} [CommRing B] [CommRing D] (φ : B →+* D)
    (C : Type u) [CommRing C] [Algebra B C] :
    zeroComplex D ((ModuleCat.extendScalars φ).obj (ModuleCat.of B C)) ⊗
      zeroComplex D ((ModuleCat.extendScalars φ).obj (ModuleCat.of B C)) ⟶
        zeroComplex D ((ModuleCat.extendScalars φ).obj (ModuleCat.of B C)) :=
  letI := φ.toAlgebra
  algebraMultiplication D (D ⊗[B] C)

/-- Multiplication by a scalar of the ordinary algebra, then placed in degree zero.
Source: Stacks 0E2U (blueprint: def-trf-affine-algebra-class-comparison-data). -/
@[irreducible] def algebraScalar (B C : Type u) [CommRing B] [CommRing C] [Algebra B C] (c : C) :
    zeroComplex B (ModuleCat.of B C) ⟶ zeroComplex B (ModuleCat.of B C) :=
  DerivedCategory.Q.map ((HomologicalComplex.single _ (.up ℤ) 0).map
    (ModuleCat.ofHom (Algebra.lmul B C c)))

end AlgebraicGeometry.AffineClassComparison
