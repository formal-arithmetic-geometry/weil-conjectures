/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
import Sheaf.TraceFormula.IntegralConeCounitRealization
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.StrictRoosComparison
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Sheaf.Paper.IntegralPullbackResolutionMatching

/-!
# Composition of the integral inverse-image comparison

Source: blueprint `sec-trace-formula/sk-thm-trace-transport/`
`thm-trf-l-function-euler-product.proof.md`, Step 1, Global powers; Stacks Project,
Tags 03D6, 0D6D and 0941
(blueprint: lem-trf-integral-inverse-image-comparison-composition).

The auxiliary compositor is fixed on sections, then applied termwise and localized.
The pullback compositor is exactly the recorded normalized realization, and kappa
is the recorded cone comparison evaluated on a derived object.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical inverse-image compositor is linear for the transported completed
coefficient actions and is uniquely determined by the canonical restriction on sections.
Source: Stacks 03D6; blueprint Global powers
(blueprint: lem-trf-integral-inverse-image-comparison-composition).
Proof: the site compositor is identity on the underlying schemes. Constant-section
maps respect it at every finite quotient. The limit projection equations then give
compatibility for the completed coefficient maps. Transporting actions through their
inverses makes the displayed section map linear. Its inverse comes from the inverse
site compositor. Restriction and module maps commute with both maps, giving a natural
isomorphism. Evaluation on every section determines its hom, hence the isomorphism,
uniquely. This is the linearity assertion for d in the node's statement. -/
theorem integralInverseImageComposition_existsUnique
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k] :
    ∃! d : inverseImageIntegralModules l E k ⋙ inverseImageIntegralModules l E h ≅
        inverseImageIntegralModules l E (h ≫ k),
      ∀ (M : integralTowerModules l E V) (U : Z.ProEt)
        (x : M.val.obj (op ((proEtaleIsoPostcompose k).obj
          ((proEtaleIsoPostcompose h).obj U)))),
        (d.hom.app M).val.app (op U) x =
          M.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
            (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)).hom.app U).op x := by
  sorry

/-- The section-normalized linear compositor on completed-coefficient module sheaves.
Source: Stacks 03D6; blueprint Global powers
(blueprint: lem-trf-integral-inverse-image-comparison-composition). -/
def integralInverseImageComposition
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k] :=
  (integralInverseImageComposition_existsUnique l E h k).exists.choose

/-- The same canonical compositor, applied termwise and localized at quasi-isomorphisms.
Source: Stacks 03D6 and 05RU; blueprint Global powers
(blueprint: lem-trf-integral-inverse-image-comparison-composition). -/
def integralInverseImageDerivedComposition
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k] :
    inverseImageIntegralDerived l E k ⋙ inverseImageIntegralDerived l E h ≅
      inverseImageIntegralDerived l E (h ≫ k) :=
  (Functor.mapDerivedCategoryCompIso (inverseImageIntegralModules l E k)
    (inverseImageIntegralModules l E h)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (integralInverseImageComposition l E h k)

/-- The specified integral inverse-image comparison respects composition, as an
actual equality in the ambient completed-coefficient derived category.
Source: blueprint Global powers; Stacks 03D6, 0D6D and 0941
(blueprint: lem-trf-integral-inverse-image-comparison-composition).

Proof:
1. Integral pullback preserves the recorded bounded constructible, derived-complete
category. The coefficient projection equations make d linear, as stated above.
2. At every finite level the canonical pullback compositor and the two tensor units
send a local section x to x tensor 1 tensor 1. Constant coefficient composition and
lem-weil-pbc-proetale-derived-pullback-composition identify these maps.
3. Choose a flat-term K-flat representative P of N. The maps theta_(g,m) define a
strict augmentation of the quotient tower. Kappa is its zero-shifted-component cone
map, conjugated by the inverse-image resolution. Exact countable products and the
normalized strict Roos comparison identify this with Rlim of that augmentation.
The counit identity of lem-trf-integral-cone-counit-realization computes its entire
tower image, before any reduction detection.
4. Write M=Lk*N and D_tower=h* C_k. The realization eta identifies Lh*M with
Rlim D_tower. The derived constant-tower/limit adjunction, obtained from
lem-pc-pre-derived-adjoint-functors-general and K-injective tower resolutions,
makes postcomposition with its counit injective on Hom. On the left, naturality
and the definition of integralComparisonComposition give c_(h,k,tower) theta_(kh) d.
On the right, lem-trf-integral-pullback-resolution-matching gives u_h h-inverse(theta_k).
Step 2 identifies these strict tower maps, including their resolution denominators.
Injectivity gives equality after eta; cancel eta. This proves the displayed derived
morphism equality, without rationalization or finite-level detection. -/
theorem integralInverseImageComparison_composition
    (D : IntegralComparisonSystem.{u} l)
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ v : V, Invertible (l : V.residueField v)]
    (N : sfIntegralConstructibleCategory l E V) :
    sfIntegralConstructible l E W ((integralDerivedPullback l E k).obj N.obj) ∧
      (integralInverseImageDerivedComposition l E h k).hom.app N.obj ≫
          inverseImagePullbackComparisonDerived l E (h ≫ k)
            (fun z ↦ isUnit_of_map_unit (IsLocalRing.residue (Z.presheaf.stalk z)) _
              ((map_natCast (IsLocalRing.residue (Z.presheaf.stalk z)) l).symm ▸
                isUnit_of_invertible (l : Z.residueField z)))
            (fun v ↦ isUnit_of_map_unit (IsLocalRing.residue (V.presheaf.stalk v)) _
              ((map_natCast (IsLocalRing.residue (V.presheaf.stalk v)) l).symm ▸
                isUnit_of_invertible (l : V.residueField v))) N.obj ≫
          (integralComparisonComposition l E D h k N).hom =
        (inverseImageIntegralDerived l E h).map
            (inverseImagePullbackComparisonDerived l E k
              (fun w ↦ isUnit_of_map_unit (IsLocalRing.residue (W.presheaf.stalk w)) _
                ((map_natCast (IsLocalRing.residue (W.presheaf.stalk w)) l).symm ▸
                  isUnit_of_invertible (l : W.residueField w)))
              (fun v ↦ isUnit_of_map_unit (IsLocalRing.residue (V.presheaf.stalk v)) _
                ((map_natCast (IsLocalRing.residue (V.presheaf.stalk v)) l).symm ▸
                  isUnit_of_invertible (l : V.residueField v))) N.obj) ≫
          inverseImagePullbackComparisonDerived l E h
            (fun z ↦ isUnit_of_map_unit (IsLocalRing.residue (Z.presheaf.stalk z)) _
              ((map_natCast (IsLocalRing.residue (Z.presheaf.stalk z)) l).symm ▸
                isUnit_of_invertible (l : Z.residueField z)))
            (fun w ↦ isUnit_of_map_unit (IsLocalRing.residue (W.presheaf.stalk w)) _
              ((map_natCast (IsLocalRing.residue (W.presheaf.stalk w)) l).symm ▸
                isUnit_of_invertible (l : W.residueField w)))
            ((integralDerivedPullback l E k).obj N.obj) := by
  sorry

end AlgebraicGeometry.ProEtale
