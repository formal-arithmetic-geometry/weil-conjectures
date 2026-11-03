/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteClopenTensor.ProEtaleFiniteClopenDerivedCalculus
public import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenMonoidalNormalization
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.CategoryTheory.FiniteProductDerived.FiniteProductDerivedLocalization
import WeilConjectures.CategoryTheory.FiniteProductCoordinates.AdditiveFiniteProductCoordinates
import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleFiniteClopenNormalizedTensorModels
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenArbitraryScalarNormalizedWitnesses
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenScalarHomotopyRepresentative

/-!
# Tensor and unbounded derived calculus for a finite clopen partition

Source: Stacks Project, derived.tex, Tags 015F and 05RU; sites-modules.tex, Tag 0GMW;
sites-cohomology.tex, Tags 06YN, 06YS, 0G7D and 06YU; finite-component application
(blueprint: lem-pur-finite-product-derived-tensor-calculus).

All restrictions are the sectionwise functors of the module-gluing node. Tensor products
and their constraints are the existing sheafification and K-flat localization constructions.
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenScalar.derived
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenScalar.sheafify
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenScalar.locallyBijective

-- The canonical public wrappers below provide these instances to consumers.
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.hasDerived
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.monoidal
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.symmetric
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.restrictionLimits
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.restrictionColimits

set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe t u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory
  DerivedCategory.Q Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard DerivedCategory.Qh DerivedCategory.quotientCompQhIso
  Functor.mapDerivedCategoryFactorsh Functor.mapHomotopyCategoryFactors
  RingedDerivedNative.monoidal RingedDerivedNative.symmetric
  coefficientTotalTensor
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.ModelNormalization

namespace AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor

private local instance piPreadditive {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] : Preadditive (∀ i, D i) :=
  CategoryTheory.FiniteProductCoordinates.piPreadditive D

private theorem equivalenceCoordinateDecomposition
    {C : Type*} [Category C] [Preadditive C] {J : Type*} [Finite J]
    (D : J → Type*) [∀ i, Category (D i)] [∀ i, Preadditive (D i)]
    [∀ i, HasZeroObject (D i)] (E : C ≌ ∀ i, D i) [E.inverse.Additive] :
    ∃ e : ∀ i, D i ⥤ C,
      (∀ i, Nonempty (e i ⋙ (E.functor ⋙ Pi.eval D i) ≅ 𝟭 _)) ∧
      (∀ i k, i ≠ k → ∀ M, IsZero ((e k ⋙ (E.functor ⋙ Pi.eval D i)).obj M)) ∧
      (∃ s : ∀ i, D i ⥤ ∀ k, D k,
        ∀ i, e i = s i ⋙ E.inverse ∧
          Nonempty (s i ⋙ Pi.eval D i ≅ 𝟭 _) ∧
          (∀ k, k ≠ i → ∀ M, IsZero ((s i).obj M k))) ∧
      (∃ b : Bicone (fun i ↦ (E.functor ⋙ Pi.eval D i) ⋙ e i),
        b.pt = 𝟭 _ ∧ Nonempty b.IsBilimit) ∧
      (∃ b : Bicone (fun i ↦ Pi.eval D i ⋙ e i),
        b.pt = E.inverse ∧ Nonempty b.IsBilimit) := by
  exact CategoryTheory.FiniteProductCoordinates.equivalenceCoordinateDecomposition D E

section DerivedPi

universe a b c d z
variable {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory A]
  {I : Type z} [Finite I] {B : I → Type c} [∀ i, Category.{d} (B i)]
  [∀ i, Abelian (B i)] [∀ i, HasDerivedCategory (B i)]
  (r : ∀ i, A ⥤ B i) [∀ i, (r i).Additive]
  [∀ i, PreservesFiniteLimits (r i)] [∀ i, PreservesFiniteColimits (r i)]
  (G : (∀ i, B i) ⥤ A)
  (hzero : ∀ (M N : ∀ i, B i), G.map (fun i ↦ (0 : M i ⟶ N i)) = 0)
  (η : 𝟭 A ≅ Functor.pi' r ⋙ G) (ε : G ⋙ Functor.pi' r ≅ 𝟭 _)

end DerivedPi

set_option maxHeartbeats 800000 in
-- The normalized comparison types carry several dependent localization instances.
/-- Ordinary and total tensor comparisons, flatness and K-flatness, and the normalized
symmetric monoidal derived restriction. Each `Braided` structure contains invertible
tensorators and unit comparison, their naturality, associativity, both unit diagrams,
and the symmetry diagram; the tensor products are the existing ones on both sides.
Source: Stacks 0GMW, 06YN, 06YS, 0G7D, 06YU and 0FPT
(blueprint: lem-pur-finite-product-derived-tensor-calculus).

Proof (node steps 4-9): the bilinear universal property constructs the restriction
tensorator. Its inverse is obtained by gluing the component bilinear maps. Both
composites fix pure tensors, so they are identities. Reassociation, exchange and unit
multiplication agree on generators. Restriction is left adjoint to zero insertion,
hence preserves the sums over p+q=n. Apply the tensorator on each summand: both
differentials send x tensor y to dx tensor y + (-1)^p x tensor dy. This gives the natural
chain isomorphism below. Test exact tensoring first by restriction and then by exact
zero insertion to obtain both directions of flatness. Test K-flatness against arbitrary
acyclic complexes, using restriction in one direction and insertion in the other.
Choose flat-term K-flat resolutions. Their restrictions are again such resolutions.
The K-flat localization equivalence and its unique natural-transformation extension
clause descend the chain tensorator and its inverse to all derived morphisms. The
representative square below fixes this descent to the native K-flat tensor models.
Associativity, units and Koszul symmetry descend because their diagrams agree on pure
triple tensors and degree (p,q) generators, with the same sign (-1)^(pq). Empty and zero
categories have unique maps and satisfy all these formulas. -/
theorem finite_clopen_tensor_calculus
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    (∀ F : Modules.{t, u} R,
      SheafOfModules.IsFlatOnSite (J := topology X) (R := R) F ↔
        ∀ i, SheafOfModules.IsFlatOnSite (J := topology (Y i))
          (R := (rings.{t, u} (j i)).obj R)
          ((restriction.{t, u} (j i) R).obj F)) ∧
    (∀ P : CochainComplex (Modules.{t, u} R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P ↔
        ∀ i, CochainComplex.IsKFlatIndependentCoefficients (J := topology (Y i))
          (R := (rings.{t, u} (j i)).obj R)
          (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj P)) ∧
    ∀ i, ∃ (h : (restriction.{t, u} (j i) R).Braided)
      (c : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
          (restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ) ≅
        (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).prod
          ((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ))) ⋙
            coefficientTotalTensor.{u, t + 1, t} (topology (Y i)) ((rings.{t, u} (j i)).obj R))
      (d : (derivedRestriction.{t, u} (j i) R).Braided),
      (∀ (F H : Modules.{t, u} R) (U : (Y i).ProEt) (x : F.val.obj
          (op ((MorphismProperty.Over.map ⊤
            (inferInstance : WeaklyEtale (j i))).obj U)))
        (y : H.val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U))),
        ((tensorComparison (j i) R h F H).hom.val.app (op U))
          (pure R F H _ x y) =
        pure ((rings.{t, u} (j i)).obj R) ((restriction.{t, u} (j i) R).obj F)
          ((restriction.{t, u} (j i) R).obj H) (op U) x y) ∧
      (∀ (P Q : CochainComplex (Modules.{t, u} R) ℤ) (p q n : ℤ) (hpq : p + q = n)
        (U : (Y i).ProEt)
        (x : (P.X p).val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U)))
        (y : (Q.X q).val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U))),
        (((c.hom.app (P, Q)).f n).val.app (op U))
          (coefficientTensorGenerator.{u, t + 1, t} (topology X) R P Q p q n hpq _ x y) =
        coefficientTensorGenerator.{u, t + 1, t} (topology (Y i)) ((rings.{t, u} (j i)).obj R)
          (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj P)
          (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj Q)
          p q n hpq (op U) x y) ∧
      (∀ (P Q : CochainComplex (Modules.{t, u} R) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P)
        (_hQ : CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) Q)
        (hiP : CochainComplex.IsKFlatIndependentCoefficients (J := topology (Y i))
          (R := (rings.{t, u} (j i)).obj R)
          (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj P))
        (_hiQ : CochainComplex.IsKFlatIndependentCoefficients (J := topology (Y i))
          (R := (rings.{t, u} (j i)).obj R)
          (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj Q)),
        (derivedRestriction.{t, u} (j i) R).map
            (RingedDerivedNative.tensorIso.{t + 1, t, u} (topology X) R P Q
              (Or.inl hP)).hom ≫
          (derivedTensorComparison (j i) R d (DerivedCategory.Q.obj P)
            (DerivedCategory.Q.obj Q)).hom ≫
          ((restriction.{t, u} (j i) R).mapDerivedCategoryFactors.hom.app P ⊗ₘ
            (restriction.{t, u} (j i) R).mapDerivedCategoryFactors.hom.app Q) =
        (restriction.{t, u} (j i) R).mapDerivedCategoryFactors.hom.app
            ((coefficientTotalTensor.{u, t + 1, t} (topology X) R).obj (P, Q)) ≫
          DerivedCategory.Q.map (c.hom.app (P, Q)) ≫
          (RingedDerivedNative.tensorIso.{t + 1, t, u} (topology (Y i))
            ((rings.{t, u} (j i)).obj R)
            (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj P)
            (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj Q)
            (Or.inl hiP)).hom) := by
  have h := clopen_total_tensor_kflat_detection X I Y j hdisjoint hcover R
  exact ⟨h.1, h.2.1,
    ClopenMonoidalDescent.finite_clopen_normalized_tensor_models
      X I Y j hdisjoint hcover R⟩

open SheafOfModules.SuccessiveDerivedQuotient

/-- The already defined universal coefficient-extension presentations on this site.
Source: Stacks 06YY (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
abbrev Presentations (X : Scheme.{t}) :=
  ∀ {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S),
    Presentation.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (J := topology X) a

/-- Apply the existing normalized scalar compositor to the restricted ring maps.
The final equality transport is only functoriality of ring restriction.
Source: Stacks 0D6D (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
def scalarComposite {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (p : Presentations.{t, u} Y) (N : Normalization (J := topology Y) p)
    {R S T : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S) (b : S ⟶ T) :
    (p ((rings.{t, u} j).map a)).derived ⋙ (p ((rings.{t, u} j).map b)).derived ≅
      (p ((rings.{t, u} j).map (a ≫ b))).derived :=
  N.derived ((rings.{t, u} j).map a) ((rings.{t, u} j).map b) ≪≫
    eqToIso (congrArg (fun f ↦ (p f).derived) ((rings.{t, u} j).map_comp a b).symm)

-- The normalized comparison types carry several dependent localization instances.

/-- Lift an ordinary coefficient/restriction comparison degreewise to homotopy categories.
Source: Stacks 015F and 06YY (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
def scalarHomotopyComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (p : Presentations.{t, u} X) (q : Presentations.{t, u} Y)
    {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
    (c : (p a).ordinary ⋙ restriction.{t, u} j S ≅
      restriction.{t, u} j R ⋙ (q ((rings.{t, u} j).map a)).ordinary) :
    (p a).ordinary.mapHomotopyCategory (.up ℤ) ⋙
        (restriction.{t, u} j S).mapHomotopyCategory (.up ℤ) ≅
      (restriction.{t, u} j R).mapHomotopyCategory (.up ℤ) ⋙
        (q ((rings.{t, u} j).map a)).ordinary.mapHomotopyCategory (.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso c (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).symm

/-- Coefficient extension is identified componentwise as an S_i-linear natural
isomorphism, with its canonical K-flat normalization and compatibility with composites.
The conclusion quantifies over arbitrary presentations of the existing universal
left-derived functors and their normalized compositors; their existence is the recorded
successive-derived-quotient theorem. Thus no scalar-extension data is assumed beyond
what those dependency theorems already construct.

Source: Stacks 06YT, 06YY, 0G7D, 05V4 and 0D6D
(blueprint: lem-pur-finite-product-derived-tensor-calculus).

Proof (node steps 10-12): on a K-flat flat-term representative P, ordinary extension
computes derived extension by lem-pur-derived-change-of-rings. Restriction commutes with
ordinary extension by the sheafified formula p tensor s maps to r(p) tensor r(s);
in the scalar-first convention this is s tensor p. The restricted complex is K-flat
with flat terms by the tensor calculus. Descend this natural chain isomorphism and its
inverse along the K-flat localization equivalence. The universal counits give exactly
the representative square below; uniqueness extends it to every derived morphism.
For R to S to T, tensor cancellation shows P tensor_R S is still flat-term K-flat.
The existing normalized compositor is represented by (p tensor s) tensor t mapping
to p tensor psi(s)t. Restricting before or after this formula gives the same section;
descent proves the displayed composition square. Identity maps are included, with the
unit formula p tensor a mapping to a p. No flatness of the ring maps is needed. Thus
finite quotient reductions and every completed-to-finite projection are special cases,
using the coefficient identifications of the module-gluing node. For empty and zero
components every comparison is the unique morphism, and the same formulas apply. -/
theorem finite_clopen_scalar_calculus
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i)) :
    ∀ (p : Presentations.{t, u} X) (N : Normalization (J := topology X) p)
      (q : ∀ i, Presentations.{t, u} (Y i)) (Ni : ∀ i, Normalization (J := topology (Y i)) (q i)),
    ∃ (c : ∀ i {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S),
        (p a).ordinary ⋙ restriction.{t, u} (j i) S ≅
          restriction.{t, u} (j i) R ⋙ (q i ((rings.{t, u} (j i)).map a)).ordinary)
      (γ : ∀ i {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S),
        (p a).derived ⋙ derivedRestriction.{t, u} (j i) S ≅
          derivedRestriction.{t, u} (j i) R ⋙ (q i ((rings.{t, u} (j i)).map a)).derived),
      (∀ i {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
        (M : Modules.{t, u} R) (U : (Y i).ProEt)
        (s : S.obj.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U)))
        (x : M.val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U))),
        ((c i a).hom.app M).val.app (op U)
          (sectionTensor (p a) M _ s x) =
        sectionTensor (q i ((rings.{t, u} (j i)).map a))
          ((restriction.{t, u} (j i) R).obj M) (op U) s x) ∧
      (∀ i {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
        (P : CochainComplex (Modules.{t, u} R) ℤ)
        (_hP : CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P)
        (_hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := topology X) (R := R) (P.X n)),
        (derivedRestriction.{t, u} (j i) S).map
            ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
          (restriction.{t, u} (j i) S).mapDerivedCategoryFactorsh.hom.app
            (((p a).ordinary.mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ _).obj P)) ≫
          DerivedCategory.Qh.map
            ((scalarHomotopyComparison (j i) p (q i) a (c i a)).hom.app
              ((HomotopyCategory.quotient _ _).obj P)) =
        (γ i a).hom.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
          (q i ((rings.{t, u} (j i)).map a)).derived.map
            ((restriction.{t, u} (j i) R).mapDerivedCategoryFactorsh.hom.app
              ((HomotopyCategory.quotient _ _).obj P)) ≫
          (q i ((rings.{t, u} (j i)).map a)).counit.app
            (((restriction.{t, u} (j i) R).mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ _).obj P))) ∧
      (∀ i {R S T : Sheaf (topology X) CommRingCat.{max u (t + 1)}}
        (a : R ⟶ S) (b : S ⟶ T) (K : DerivedCategory (Modules.{t, u} R)),
        (derivedRestriction.{t, u} (j i) T).map ((N.derived a b).hom.app K) ≫
          (γ i (a ≫ b)).hom.app K =
        (γ i b).hom.app ((p a).derived.obj K) ≫
          (q i ((rings.{t, u} (j i)).map b)).derived.map ((γ i a).hom.app K) ≫
          (scalarComposite (j i) (q i) (Ni i) a b).hom.app
            ((derivedRestriction.{t, u} (j i) R).obj K)) := by
  intro p N q Ni
  obtain ⟨U, V, d, hd⟩ := ClopenScalar.clopen_arbitrary_scalar_normalized_witnesses
    X I Y j hdisjoint hcover p N q Ni
  refine ⟨(fun i ↦ (d i).ordinary), (fun i ↦ (d i).derived), ?_, ?_, ?_⟩
  · intro i R S a M W s x
    exact (hd i).1 a M (op W) s x
  · intro i R S a P hP hf
    have hchain : (d i).chain a =
        NatIso.mapHomologicalComplex ((d i).ordinary a) (.up ℤ) := by
      apply Iso.ext
      apply NatTrans.ext
      funext K
      apply HomologicalComplex.Hom.ext
      funext n
      exact (hd i).2.1 a K n
    apply ClopenScalar.clopen_scalar_homotopy_representative
      (ClopenScalar.res (j i) R) (ClopenScalar.res (j i) S)
      (p a).ordinary (q i ((rings (j i)).map a)).ordinary
      (p a).derived (q i ((rings (j i)).map a)).derived
      (p a).counit (q i ((rings (j i)).map a)).counit
      ((d i).ordinary a) ((d i).derived a) P
    simpa only [hchain, ClopenScalar.computation, ClopenScalar.cochainComputation,
      ClopenScalar.ext, ClopenScalar.extD, ClopenScalar.resD] using
        (hd i).2.2.1 a P hP hf
  · intro i R S T a b K
    simpa only [scalarComposite, Iso.trans_hom, eqToIso.hom, NatTrans.comp_app,
      eqToHom_app, Category.assoc, ClopenScalar.extD] using (hd i).2.2.2.composition a b K

end AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor
