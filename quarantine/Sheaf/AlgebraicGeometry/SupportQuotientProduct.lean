/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.SupportQuotientFlat
public import Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.ConstructibleSheaf.ConstantModuleLocallyConstant
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Normalized multiplication of support quotients

Source: blueprint main-20261015, `lem-pur-kunneth-supported`, support-quotient
refinement (blueprint: lem-pur-support-quotient-product).

The coefficient ring and the base field are independent. The generator equations
specify multiplication, including zero coefficients. The derived map is the actual
localization comparison followed by the degree-zero multiplication. Naturality is
expressed by its quotient-generator test: every pullback square preserving the
constant generators commutes. In particular this applies to the maps induced by
morphisms of pairs and their product.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- Pull back the recorded cokernel, without choosing a new support object.
Source: blueprint support-quotient refinement
(blueprint: lem-pur-support-quotient-product). -/
def etaleSupportQuotientPullback (A : Type u) [CommRing A] [Finite A]
    {C T V : Scheme.{u}} (a : C ⟶ T) [IsClosedImmersion a] (h : V ⟶ T) :=
  (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).obj (etaleSupportQuotient A a)

/-- The tensor of the two quotient generators, with constant one sent to one tensor one.
Source: blueprint support-quotient refinement
(blueprint: lem-pur-support-quotient-product). -/
def etaleSupportQuotientProductGenerator (A : Type u) [CommRing A] [Finite A]
    {B X Y Z W : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] :
    (constantSheaf (pullback f g).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶
      etaleSupportQuotientPullback A i (pullback.fst f g) ⊗
        etaleSupportQuotientPullback A j (pullback.snd f g) :=
  (constantSheaf (pullback f g).smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).map
      (λ_ (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))).inv ≫
    Etale.constantExteriorTensor (ULift.{u + 1, u} A) f g
      (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
      (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ≫
    ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.fst f g)).map (etaleSupportQuotientMap A i) ⊗ₘ
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.snd f g)).map (etaleSupportQuotientMap A j))

/-- The canonical derived-to-ordinary tensor comparison for the two degree-zero
factors. Composing with the canonical single-complex collapse and the ordinary
multiplication gives the derived multiplication. Both latter arrows are isomorphisms,
so invertibility of this arrow is exactly invertibility of that multiplication.
Source: blueprint support-quotient refinement
(blueprint: lem-pur-support-quotient-product). -/
def etaleSupportQuotientDerivedComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u})
    (F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  Etale.supportedDerivedTensorLocalizationGeneric
    (ModuleCat.{u + 1} A) T
    ((HomologicalComplex.single _ (.up ℤ) 0).obj F)
    ((HomologicalComplex.single _ (.up ℤ) 0).obj G)

/-- Naturality tested on the quotient generators. Here `s` is the induced map on the
pulled-back tensor and `c` the induced map on the product support quotient. Requiring
commutation with the generators describes those maps without choosing replacements.
The quantification also includes identity and composite maps of pairs.
Source: blueprint support-quotient refinement
(blueprint: lem-pur-support-quotient-product). -/
def etaleSupportQuotientProductNatural (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u})
    {F H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (m : (constantSheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶ F)
    (r : (constantSheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶ H)
    (e : F ⟶ H) : Prop :=
  ∀ (T' : Scheme.{u}) (h : T' ⟶ T)
    (F' H' : Sheaf T'.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (m' : (constantSheaf T'.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶ F')
    (r' : (constantSheaf T'.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶ H')
    (e' : F' ⟶ H')
    (s : (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).obj F ⟶ F')
    (c : (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).obj H ⟶ H'),
    m' ≫ e' = r' →
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).map m ≫ s =
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).hom.app
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ≫ m' →
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).map r ≫ c =
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).hom.app
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ≫ r' →
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).map e ≫ c = s ≫ e'

/-- Pull back the recorded cokernel, without choosing a new support object.
Source: blueprint support-quotient refinement
(blueprint: lem-pur-support-quotient-product). -/
def proEtaleSupportQuotientPullback (A : Type u) [CommRing A] [Finite A]
    {C T V : Scheme.{u}} (a : C ⟶ T) [IsClosedImmersion a] (h : V ⟶ T) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).obj (proEtaleSupportQuotient A a)

/-- The tensor of the two quotient generators, with constant one sent to one tensor one.
Source: blueprint support-quotient refinement
(blueprint: lem-pur-support-quotient-product). -/
def proEtaleSupportQuotientProductGenerator (A : Type u) [CommRing A] [Finite A]
    {B X Y Z W : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] :
    (constantSheaf (ProEt.topology (pullback f g))
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶
      proEtaleSupportQuotientPullback A i (pullback.fst f g) ⊗
        proEtaleSupportQuotientPullback A j (pullback.snd f g) :=
  (constantSheaf (ProEt.topology (pullback f g))
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).map
      (λ_ (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))).inv ≫
    ProEtale.constantExteriorTensor (ULift.{u + 1, u} A) f g
      (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
      (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ≫
    ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.fst f g)).map (proEtaleSupportQuotientMap A i) ⊗ₘ
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.snd f g)).map (proEtaleSupportQuotientMap A j))

/-- The canonical derived-to-ordinary tensor comparison for the two degree-zero
factors. Composing with the canonical single-complex collapse and the ordinary
multiplication gives the derived multiplication. Both latter arrows are isomorphisms,
so invertibility of this arrow is exactly invertibility of that multiplication.
Source: blueprint support-quotient refinement
(blueprint: lem-pur-support-quotient-product). -/
def proEtaleSupportQuotientDerivedComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u})
    (F G : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) :=
  ProEtale.supportedDerivedTensorLocalizationGeneric
    (ModuleCat.{u + 1} A) T
    ((HomologicalComplex.single _ (.up ℤ) 0).obj F)
    ((HomologicalComplex.single _ (.up ℤ) 0).obj G)

/-- Naturality tested on the quotient generators. Here `s` is the induced map on the
pulled-back tensor and `c` the induced map on the product support quotient. Requiring
commutation with the generators describes those maps without choosing replacements.
The quantification also includes identity and composite maps of pairs.
Source: blueprint support-quotient refinement
(blueprint: lem-pur-support-quotient-product). -/
def proEtaleSupportQuotientProductNatural (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u})
    {F H : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (m : (constantSheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶ F)
    (r : (constantSheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶ H)
    (e : F ⟶ H) : Prop :=
  ∀ (T' : Scheme.{u}) (h : T' ⟶ T)
    (F' H' : Sheaf (ProEt.topology T')
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (m' : (constantSheaf (ProEt.topology T')
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶ F')
    (r' : (constantSheaf (ProEt.topology T')
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶ H')
    (e' : F' ⟶ H')
    (s : (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).obj F ⟶ F')
    (c : (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).obj H ⟶ H'),
    m' ≫ e' = r' →
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).map m ≫ s =
      (ProEtale.constantSheafCompUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).hom.app
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ≫ m' →
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).map r ≫ c =
      (ProEtale.constantSheafCompUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).hom.app
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ≫ r' →
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).map e ≫ c = s ≫ e'

/-- The normalized product multiplication in both topologies, also for derived tensor.
Source: blueprint main-20261015, support-quotient refinement of
`lem-pur-kunneth-supported` (blueprint: lem-pur-support-quotient-product).

Proof:
1. Finite type over the field makes X, Y and their product Noetherian. Thus the open
complements are quasi-compact and the quotient-flat lemma applies. Geometric stalks
of each pulled-back quotient are A on its support and zero elsewhere.
2. Write the two quotient kernels as I and J. Multiplication A tensor A to A descends
through (A/I) tensor (A/J) to A/(I+J): both kernels vanish in the product-support
quotient. On each geometric stalk this sends a tensor b to ab, and is an isomorphism.
The generator map is epic, proving uniqueness and all generator-preserving naturality
squares, including those induced by morphisms of the pairs and their products.
3. Both quotient complexes are K-flat in degree zero. The lax-monoidal localization
comparison is therefore invertible. Collapse the tensor of the two single complexes;
the resulting map is exactly the degree-zero ordinary multiplication specified here.
4. Exact etale-to-pro-etale comparison preserves the quotient generators, projection
pullbacks and tensor. It transports the normalized multiplication and its derived
map, giving the same assertions and naturality on the pro-etale site. -/
theorem supportQuotient_product
    (A : Type u) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Z W : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] :
    (∃! e :
      etaleSupportQuotientPullback A i (pullback.fst f g) ⊗
        etaleSupportQuotientPullback A j (pullback.snd f g) ≅
          etaleSupportQuotient A (Etale.supportedProductImmersion f g i j),
      etaleSupportQuotientProductGenerator A f g i j ≫ e.hom =
        etaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j) ∧
      IsIso (etaleSupportQuotientDerivedComparison (ULift.{u + 1, u} A) (pullback f g)
        (etaleSupportQuotientPullback A i (pullback.fst f g))
        (etaleSupportQuotientPullback A j (pullback.snd f g))) ∧
      etaleSupportQuotientProductNatural A (pullback f g)
        (etaleSupportQuotientProductGenerator A f g i j)
        (etaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j)) e.hom) ∧
    (∃! e :
      proEtaleSupportQuotientPullback A i (pullback.fst f g) ⊗
        proEtaleSupportQuotientPullback A j (pullback.snd f g) ≅
          proEtaleSupportQuotient A (Etale.supportedProductImmersion f g i j),
      proEtaleSupportQuotientProductGenerator A f g i j ≫ e.hom =
        proEtaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j) ∧
      IsIso (proEtaleSupportQuotientDerivedComparison (ULift.{u + 1, u} A) (pullback f g)
        (proEtaleSupportQuotientPullback A i (pullback.fst f g))
        (proEtaleSupportQuotientPullback A j (pullback.snd f g))) ∧
      proEtaleSupportQuotientProductNatural A (pullback f g)
        (proEtaleSupportQuotientProductGenerator A f g i j)
        (proEtaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j)) e.hom) := by
  sorry

end AlgebraicGeometry.Scheme
