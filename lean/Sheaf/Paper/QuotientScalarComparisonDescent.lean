/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Sheaf.CategoryTheory.StrictRoosHomotopyFunctor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Sheaf.Algebra.Homology.RoosCoordinatesQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Scalar augmentation and its derived descent

Source: Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1, pp. 22,24;
Stacks Project, Tags 03EK, 014E, 08TC, 06YS, 06YT, 06XN and 05S9.
(blueprint: lem-pur-quotient-scalar-comparison-descent)

The tensor factors in the change-of-rings API are written scalar first. Natural index
`n` denotes positive level `n + 1`. Presentation isomorphisms fix the actual sheafified
tensors and their maps; they are not additional hypotheses in the existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  {R S : Sheaf J CommRingCat.{u}} {B : ℕ → Sheaf J CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡" T => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T

/-- Presentations of the two ordinary tensor functors, with their maps fixed on tensors.
Source: Stacks 03EK and the strict tower construction of Stacks 08TC
(blueprint: lem-pur-quotient-scalar-comparison-descent).
These fields package the specified functors, including their canonical transition maps. -/
structure ScalarTowerTensorModel (φ : R ⟶ S) (c : ∀ n, S ⟶ B n)
    (b : ∀ n, B (n + 1) ⟶ B n) where
  E : ringedSiteModules.{u} (𝓡 R) ⥤
    ringedSiteModules.{u} (𝓡 S)
  V : ringedSiteModules.{u} (𝓡 R) ⥤
    (ℕᵒᵖ ⥤ ringedSiteModules.{u} (𝓡 S))
  E_add : E.Additive
  V_add : V.Additive
  eE : ∀ M, E.obj M ≅ changeOfRings φ M
  eV : ∀ M n, (V.obj M).obj (op n) ≅
    (restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map (c n))).obj
        (changeOfRings (φ ≫ c n) M)
  E_map : ∀ {M N} (f : M ⟶ N),
    (eE M).inv ≫ E.map f ≫ (eE N).hom = changeOfRingsHom φ M f
  V_map : ∀ {M N} (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ)
    (x : M.val.obj U) (z : (B n).obj.obj U),
    (((eV M n).inv ≫ (V.map f).app (op n) ≫ (eV N n).hom).val.app U)
      ((toSheafify J (changeOfRingsPresheaf (φ ≫ c n) M).presheaf).app U
        (z ⊗ₜ[R.obj.obj U, ((φ ≫ c n).hom.app U).hom] x)) =
        (toSheafify J (changeOfRingsPresheaf (φ ≫ c n) N).presheaf).app U
          (z ⊗ₜ[R.obj.obj U, ((φ ≫ c n).hom.app U).hom] f.val.app U x)
  transition : ∀ M (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj U)
    (z : (B (n + 1)).obj.obj U),
    (((eV M (n + 1)).inv ≫ (V.obj M).map (homOfLE (Nat.le_succ n)).op ≫
        (eV M n).hom).val.app U)
      ((toSheafify J (changeOfRingsPresheaf (φ ≫ c (n + 1)) M).presheaf).app U
        (z ⊗ₜ[R.obj.obj U, ((φ ≫ c (n + 1)).hom.app U).hom] x)) =
        (toSheafify J (changeOfRingsPresheaf (φ ≫ c n) M).presheaf).app U
          ((((b n).hom.app U) z) ⊗ₜ[R.obj.obj U, ((φ ≫ c n).hom.app U).hom] x)

attribute [instance] ScalarTowerTensorModel.E_add ScalarTowerTensorModel.V_add

namespace ScalarTowerTensorModel

variable {φ : R ⟶ S} {c : ∀ n, S ⟶ B n} {b : ∀ n, B (n + 1) ⟶ B n}
  (M : ScalarTowerTensorModel φ c b)

/-- Ordinary extension of scalars, applied termwise to complexes.
Source: Stacks 03EK (blueprint: lem-pur-quotient-scalar-comparison-descent). -/
abbrev F := M.E.mapHomologicalComplex (ComplexShape.up ℤ)

variable [HasCountableProducts (ringedSiteModules.{u} (𝓡 S))]

/-- The actual shifted product cone of the strict coefficient tensor tower.
Source: Stacks 014E and 08TC (blueprint: lem-pur-quotient-scalar-comparison-descent). -/
abbrev G := M.V.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ roosF

/-- The zero shifted-product component and all scalar-augmentation product projections.
Generators are images of presheaf tensors under the sheafification unit, so this
condition specifies sheaf maps even when global sections are not pure tensors.
Source: Stacks 03EK, 014E and 08TC
(blueprint: lem-pur-quotient-scalar-comparison-descent). -/
def AugmentationCoordinates (β : M.F ⟶ M.G) : Prop :=
  (∀ (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ) (i : ℤ),
    (β.app P).f (i + 1) ≫
      (roosχ ((M.V.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) i).hom ≫
        biprod.fst = 0) ∧
  ∀ (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ)
    (i : ℤ) (n : ℕ) (U : Cᵒᵖ) (x : (P.X i).val.obj U) (s : S.obj.obj U),
    ((((M.eE (P.X i)).inv ≫
        (β.app P ≫ roosEval
          ((M.V.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) n).f i ≫
        (M.eV (P.X i) n).hom).val.app U)
      ((toSheafify J (changeOfRingsPresheaf φ (P.X i)).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) =
      (toSheafify J (changeOfRingsPresheaf (φ ≫ c n) (P.X i)).presheaf).app U
        (((c n).hom.app U s) ⊗ₜ[R.obj.obj U, ((φ ≫ c n).hom.app U).hom] x)

variable [HasDerivedCategory.{w} (ringedSiteModules.{u} (𝓡 R))]
  [HasDerivedCategory.{w} (ringedSiteModules.{u} (𝓡 S))]

/-- Everywhere-defined universal left derived functors, computed on every flat-term
K-flat complex, and the unique natural descent normalized on all such complexes.
The full comparison equation gives independence of every resolution; uniqueness is
required already from its restriction to the resolving class.
Source: Stacks 06YS, 06XN and 05S9
(blueprint: lem-pur-quotient-scalar-comparison-descent). -/
def DerivedDescent (β : M.F ⟶ M.G) : Prop :=
  ∃ (LF LG : DerivedCategory.{w} (ringedSiteModules.{u} (𝓡 R)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u} (𝓡 S)))
    (εF : DerivedCategory.Q ⋙ LF ⟶ M.F ⋙ DerivedCategory.Q)
    (εG : DerivedCategory.Q ⋙ LG ⟶ M.G ⋙ DerivedCategory.Q),
    LF.IsLeftDerivedFunctor εF
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) ∧
    LG.IsLeftDerivedFunctor εG
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) ∧
    (∀ X, Nonempty ((Functor.RightExtension.mk LF εF).IsPointwiseRightKanExtensionAt X)) ∧
    (∀ X, Nonempty ((Functor.RightExtension.mk LG εG).IsPointwiseRightKanExtensionAt X)) ∧
    (∀ (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ),
      P.IsKFlatIndependentCoefficients → (∀ i : ℤ, IsFlatOnSite (P.X i)) →
        IsIso (εF.app P) ∧ IsIso (εG.app P)) ∧
    ∃ χ : LF ⟶ LG,
      (∀ P, χ.app (DerivedCategory.Q.obj P) ≫ εG.app P =
        εF.app P ≫ DerivedCategory.Q.map (β.app P)) ∧
      ∀ χ' : LF ⟶ LG,
        (∀ (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ),
          P.IsKFlatIndependentCoefficients → (∀ i : ℤ, IsFlatOnSite (P.X i)) →
            χ'.app (DerivedCategory.Q.obj P) ≫ εG.app P =
              εF.app P ≫ DerivedCategory.Q.map (β.app P)) → χ' = χ

end ScalarTowerTensorModel

/-- The canonical scalar augmentation exists uniquely and descends to universal derived
functors, independently of flat-term K-flat representatives.

Source: Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1, pp. 22,24;
Stacks 03EK, 014E, 08TC, 06YS, 06YT, 06XN and 05S9.
(blueprint: lem-pur-quotient-scalar-comparison-descent)

Proof plan:
1. The balanced maps send p tensor s to p tensor c_n(s), and sheafify (03EK).
   Strict compatibility gives a map alpha to the product killed by 1 minus shift.
2. In the fixed roosχ coordinates use (0, alpha), as in roosAugment. The cone
   differential proves it is a chain map. Pure tensors and product projections give
   naturality and uniqueness, without any surjectivity of c_n.
3. Tensor preserves chain homotopies. The strict Roos homotopy functor sends the
   compatible tensor homotopies to (-h_V, h_V), so both functors pass to K(R).
4. Use the flat-term K-flat resolutions of 06YS. Quasi-isomorphisms in K(R) have
   saturated right fractions by lem-pur-quasi-isos-saturated-triangulated.
5. Apply lem-pur-change-of-rings-kflat-quasi-iso to R to S and each R to B_n.
   Restriction changes no underlying abelian sheaf and preserves quasi-isomorphisms.
6. Exact countable products commute with cohomology, so the product map is a
   quasi-isomorphism. It commutes with 1 minus shift by the strict tower equations.
7. Reorder Roos coordinates and apply lem-pe-roos-coordinates-quasi-iso with
   endomorphism minus (1 minus shift). Thus G preserves these quasi-isomorphisms.
8. Apply resolvingClass_essentialConstancy, leftDerived_defined_pointwiseKan_bridge,
   then the total-left-derived-localization theorem. The identity legs are invertible
   on flat-term K-flat complexes. The cochain version is the same universal extension:
   target localization identifies homotopic maps, so it factors through K(R).
9. The right Kan universal property descends εF followed by beta to χ on all D(R),
   with χ followed by εG equal to εF followed by Q(beta).
10. For any resolution q:P to X, Q(q) is invertible. Naturality forces the value at X
    from the normalized value at P. Hence the normalization determines χ uniquely,
    independently of the resolution and of comparison-preserving derived models.
11. For S=R the multiplication isomorphism sends p tensor r to rp; its inverse
    sends p to p tensor 1. The quotient specialization is stated below.
-/
theorem quotient_scalar_comparison_descent
    (φ : R ⟶ S) (c : ∀ n, S ⟶ B n) (b : ∀ n, B (n + 1) ⟶ B n)
    (hc : ∀ n, c (n + 1) ≫ b n = c n)
    [HasCountableProducts (ringedSiteModules.{u} (𝓡 S))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (𝓡 R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (𝓡 S))]
    (hexact : exactFunctor _ _
      (Pi.functor ℕ : (ℕ → ringedSiteModules.{u} (𝓡 S)) ⥤ _)) :
    ∃ M : ScalarTowerTensorModel φ c b,
      (∃! β : M.F ⟶ M.G, M.AugmentationCoordinates β) ∧
      ∀ β : M.F ⟶ M.G, M.AugmentationCoordinates β → M.DerivedDescent β := by
  sorry

/-- Multiplication identifies the scalar augmentation with the strict quotient unit.
Source: Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1, pp. 22,24;
Stacks 03EK and 08TC (blueprint: lem-pur-quotient-scalar-comparison-descent).

Proof: specialize the scalar formula to the identity of R and the canonical
projections R to R/a^(n+1). Multiplication on sheafified tensors sends p tensor r
to rp, with inverse p to p tensor 1. It commutes with restrictions and differentials.
After precomposing beta with this inverse, every product projection sends p to
p tensor 1 and the shifted-product component is zero. Product extensionality and
the fixed Roos coordinates identify the map with roosAugment of that compatible
family. This includes a=0, when the tower is constant R, and invertible a, when
all positive quotient levels vanish. This is Step 11 of the node's proof. -/
theorem quotient_scalar_comparison_unit
    [HasSheafify J CommRingCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (a : (R.obj ⋙ CategoryTheory.forget CommRingCat.{u}).sections)
    (b : ∀ n : ℕ, principalPowerRingQuotient R a ((n + 1) + 1) ⟶
      principalPowerRingQuotient R a (n + 1))
    (hc : ∀ n : ℕ, principalPowerRingProjection R a ((n + 1) + 1) ≫ b n =
      principalPowerRingProjection R a (n + 1))
    [HasCountableProducts (ringedSiteModules.{u} (𝓡 R))]
    (M : ScalarTowerTensorModel (𝟙 R)
      (fun n : ℕ ↦ principalPowerRingProjection R a (n + 1)) b)
    (β : M.F ⟶ M.G) (hβ : M.AugmentationCoordinates β)
    (P : CochainComplex (ringedSiteModules.{u} (𝓡 R)) ℤ) :
    ∃ m : M.F.obj P ≅ P,
      (∀ (i : ℤ) (U : Cᵒᵖ) (x : (P.X i).val.obj U) (r : R.obj.obj U),
        (((M.eE (P.X i)).inv ≫ m.hom.f i).val.app U)
          ((toSheafify J (changeOfRingsPresheaf (𝟙 R) (P.X i)).presheaf).app U
            (r ⊗ₜ[R.obj.obj U, ((𝟙 R : R ⟶ R).hom.app U).hom] x)) = r • x) ∧
      ∃ (γ : ∀ n : ℕ, P ⟶
          ((M.V.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).asFunctor.obj (op n))
        (hγ : ∀ n : ℕ, γ (n + 1) ≫
          ((M.V.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).asFunctor.map
            (homOfLE (Nat.le_succ n)).op = γ n),
        (∀ (n : ℕ) (i : ℤ) (U : Cᵒᵖ) (x : (P.X i).val.obj U),
          (((γ n).f i ≫ (M.eV (P.X i) n).hom).val.app U) x =
            (toSheafify J
              (changeOfRingsPresheaf (𝟙 R ≫ principalPowerRingProjection R a (n + 1))
                (P.X i)).presheaf).app U
              ((1 : (principalPowerRingQuotient R a (n + 1)).obj.obj U)
                ⊗ₜ[R.obj.obj U, ((𝟙 R ≫ principalPowerRingProjection R a (n + 1)).hom.app U).hom]
                  x)) ∧
        m.inv ≫ β.app P = roosAugment γ hγ := by
  sorry

end SheafOfModules
