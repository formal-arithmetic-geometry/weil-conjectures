/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange
public import Sheaf.AlgebraicGeometry.EtaleSupportedSections
public import Sheaf.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.Flat.Rank
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import Mathlib.CategoryTheory.Sites.Point.Monoidal

public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import Sheaf.RingTheory.StrictHenselizationNoetherian
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Prime-power geometric costalk reduction

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII, Definitions 1.1.1,
1.1.2 and 1.4.1, and section 1.3, printed pp. 258--262
(blueprint: lem-per-prime-power-costalk-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w c₁ c₂ c₃ d₁ d₂ d₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- The geometric costalk, using the local scheme, its closed support right adjoint,
and the geometric fibre over the residue field. Source: Gabber XVII, Definition 1.1.1
(blueprint: lem-per-prime-power-costalk-reduction). -/
abbrev geometricCostalkPlus (A : Type (u + 1)) [CommRing A] [Finite A]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory.Plus (ModuleCat.{u + 1} A) :=
  letI : ((Scheme.pointSmallEtale (Spec.map (X.SpecToEquivOfField Ω s).2)).sheafFiber
      (A := ModuleCat.{u + 1} A)).Additive :=
    (Scheme.pointSmallEtale (Spec.map (X.SpecToEquivOfField Ω s).2)).sheafFiber_additive
  (upperStar (ModuleCat.{u + 1} A)
      (X.fromSpecStalk (X.SpecToEquivOfField Ω s).1)).mapDerivedCategoryPlus ⋙
    closedSupportPlus A (Spec.map (X.residue (X.SpecToEquivOfField Ω s).1)) ⋙
    ((Scheme.pointSmallEtale (Spec.map (X.SpecToEquivOfField Ω s).2)).sheafFiber
      (A := ModuleCat.{u + 1} A)).rightDerivedFunctorPlus

/-- The strict-local expression for a geometric costalk. Source: Gabber XVII,
Definition 1.1.1 and its footnote (blueprint: lem-per-prime-power-costalk-reduction). -/
abbrev strictLocalCostalk (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory (ModuleCat.{u + 1} A) :=
  (upperStar (ModuleCat.{u + 1} A) (Scheme.strictLocalizationToBase s)).mapDerivedCategoryPlus ⋙
    derivedSupportedEtaleSections A (Scheme.strictLocalization s)
      ⟨{IsLocalRing.closedPoint (Scheme.strictHenselization s)}ᶜ,
        (IsLocalRing.isClosed_singleton_closedPoint _).isOpen_compl⟩

/-- The bounded-below geometric stalk with its exact additive module fibre.
Source: Gabber XVII, Definition 1.1.1
(blueprint: lem-per-prime-power-costalk-reduction). -/
abbrev costalkGeometricFiberPlus (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory.Plus (ModuleCat.{u + 1} A) :=
  letI := (Scheme.pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} A)
  (Scheme.pointSmallEtale s).sheafFiber.rightDerivedFunctorPlus

/-- Geometric stalk on D+, with its exact module-valued fibre functor.
Source: Gabber XVII, Definition 1.1.1
(blueprint: lem-per-prime-power-costalk-reduction). -/
abbrev geometricFiberPlus (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory (ModuleCat.{u + 1} A) :=
  letI := (Scheme.pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} A)
  (Scheme.pointSmallEtale s).sheafFiber.rightDerivedFunctorPlus ⋙
    _root_.DerivedCategory.Plus.ι



/-- Restrict an endofunctor preserving an object property to its full subcategory.
This is the actual object-property lift, used to restrict the derived Tate tensor.
Source: Gabber XVII, Definition 1.4.1, bounded-below tensor compatibility
(blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkLiftEndofunctor {C : Type v} [Category.{w} C] (P : ObjectProperty C)
    (F : C ⥤ C) (h : ∀ K : P.FullSubcategory, P (F.obj K.obj)) :
    P.FullSubcategory ⥤ P.FullSubcategory :=
  P.lift (P.ι ⋙ F) h

/-- The recorded derived tensor with the signed Tate sheaf in degree zero.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateTensor (A : Type (u + 1)) [CommRing A] (m : ℕ) (T : Scheme.{u})
    (hA : (m : A) = 0) (a : ℤ) :
    _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  tensorRight ((_root_.DerivedCategory.singleFunctor
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
      (T.finiteEtaleTateSheaf A m hA a))

/-- A signed Tate line is flat, including negative powers and prime-power coefficients.
Source: lem-asd-etale-finite-twist-pullback, Step 6 of the node
(blueprint: lem-per-prime-power-costalk-reduction).
Proof: use the normalized signed multiplication with the opposite exponent. Its
product is the coefficient unit; tensoring by the line is an equivalence with inverse
its dual. Hence it preserves finite limits. No basis is selected. -/
theorem costalkTateTensor_exact (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤)))
    (hA : (m : A) = 0) (a : ℤ) :
    PreservesFiniteLimits (tensorRight (T.finiteEtaleTateSheaf A m hA a)) := by
  sorry

/-- The actual exact tensor functor on D+. Its realization as the recorded derived
monoidal tensor is fixed by the K-flat counit below.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateTensorPlus (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤)))
    (hA : (m : A) = 0) (a : ℤ) :
    _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  letI := costalkTateTensor_exact A m hm T hT hA a
  (tensorRight (T.finiteEtaleTateSheaf A m hA a)).mapDerivedCategoryPlus

/-- The fibre Tate line is flat over the same coefficient ring.
Source: lem-asd-etale-finite-twist-pullback, Step 6 of the node
(blueprint: lem-per-prime-power-costalk-reduction).
Proof: the exact monoidal geometric fibre preserves the line and its normalized dual
and evaluation; its tensor functor is therefore an equivalence, hence exact. -/
theorem costalkTateFiber_exact (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) {T : Scheme.{u}} (hT : IsUnit (m : Γ(T, ⊤)))
    (hA : (m : A) = 0) (a : ℤ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    PreservesFiniteLimits (tensorRight
      ((Scheme.pointSmallEtale t).sheafFiber.obj (T.finiteEtaleTateSheaf A m hA a))) := by
  sorry

/-- Exact tensor with the actual geometric fibre of the Tate line, on D+.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateFiberTensorPlus (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) {T : Scheme.{u}} (hT : IsUnit (m : Γ(T, ⊤)))
    (hA : (m : A) = 0) (a : ℤ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    _root_.DerivedCategory.Plus (ModuleCat.{u + 1} A) ⥤ _root_.DerivedCategory.Plus (ModuleCat.{u
      + 1} A) :=
  letI := costalkTateFiber_exact A m hm hT hA a t
  letI : PreservesColimitsOfSize.{0, 0} (tensorRight
    ((Scheme.pointSmallEtale t).sheafFiber.obj (T.finiteEtaleTateSheaf A m hA a))) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)
  (tensorRight ((Scheme.pointSmallEtale t).sheafFiber.obj
    (T.finiteEtaleTateSheaf A m hA a))).mapDerivedCategoryPlus

/-- Exact tensor with the actual fibre line, on the coefficient derived category.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateFiberTensor (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) {T : Scheme.{u}} (hT : IsUnit (m : Γ(T, ⊤)))
    (hA : (m : A) = 0) (a : ℤ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    _root_.DerivedCategory (ModuleCat.{u + 1} A) ⥤ _root_.DerivedCategory (ModuleCat.{u + 1} A) :=
  letI := costalkTateFiber_exact A m hm hT hA a t
  letI : PreservesColimitsOfSize.{0, 0} (tensorRight
    ((Scheme.pointSmallEtale t).sheafFiber.obj (T.finiteEtaleTateSheaf A m hA a))) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)
  (tensorRight ((Scheme.pointSmallEtale t).sheafFiber.obj
    (T.finiteEtaleTateSheaf A m hA a))).mapDerivedCategory

section FlatTensorRealization
universe c d e
variable {C : Type c} [Category.{d} C] [Abelian C]
  [IsGrothendieckAbelian.{d} C] [HasDerivedCategory.{e} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  (L : C) [PreservesFiniteLimits (tensorRight L)]
  [PreservesFiniteColimits (tensorRight L)]

/-- The K-flat counit characterizes exact tensor as the recorded derived tensor.
Source: def-kun-derived-tensor, Step 6 of the node
(blueprint: lem-per-prime-power-costalk-reduction). -/
def CostalkTensorRealization
    (e : (tensorRight L).mapDerivedCategory ≅
      tensorRight ((_root_.DerivedCategory.singleFunctor C 0).obj L)) : Prop :=
  ∀ (P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P),
    e.app (_root_.DerivedCategory.Q.obj P) ≪≫
      _root_.DerivedCategory.QObjTensorSingleFunctorObjIso P hP L =
        (tensorRight L).mapDerivedCategoryFactors.app P

/-- Exact tensor has a unique realization satisfying the full K-flat counit equation.
Source: def-kun-derived-tensor, Step 6 of the node
(blueprint: lem-per-prime-power-costalk-reduction).
Proof: tensor by the flat degree-zero line preserves quasi-isomorphisms. On K-flat
representatives compose the exact localization factorization with the inverse of
QObjTensorSingleFunctorObjIso. Localization descends this natural isomorphism; all
objects have K-flat resolutions, and localization is fully faithful on natural
transformations, proving uniqueness. This includes unbounded representatives. -/
theorem costalkTensorRealization_existsUnique :
    ∃! e : (tensorRight L).mapDerivedCategory ≅
      tensorRight ((_root_.DerivedCategory.singleFunctor C 0).obj L),
      CostalkTensorRealization L e := by
  sorry

/-- The uniquely normalized realization, with no choice of a basis or an arbitrary iso.
Source: def-kun-derived-tensor (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTensorRealization :
    (tensorRight L).mapDerivedCategory ≅
      tensorRight ((_root_.DerivedCategory.singleFunctor C 0).obj L) :=
  (costalkTensorRealization_existsUnique L).choose
end FlatTensorRealization

/-- Invertibility of the coefficient integer is preserved under every scheme pullback.
Source: Gabber XVII 1.1.1 (blueprint: lem-per-prime-power-costalk-reduction).
Proof: apply the global-section ring homomorphism to the inverse of ell, take its nth
power, and use preservation of natural-number casts. -/
theorem costalkTateUnit (ℓ n : ℕ) {X T : Scheme.{u}}
    (hℓ : IsUnit (ℓ : Γ(X, ⊤))) (f : T ⟶ X) :
    IsUnit ((ℓ ^ n : ℕ) : Γ(T, ⊤)) := by
  sorry

/-- The signed Tate pullback is uniquely determined by its roots-of-unity generator,
unit, positive-power tensorator and negative-power evaluation normalizations.
Source: lem-asd-etale-finite-twist-pullback, the r and c witnesses and their laws
(blueprint: lem-per-prime-power-costalk-reduction).
Proof: the recorded theorem supplies r and c with all four displayed laws. The
roots map is unique because its inclusion into G_m is monic. The degree-one map is
then determined by the scalar-extended roots generators. The zero comparison is
specified, positive powers are determined recursively by the monoidal tensorator,
and the negative powers are determined by the perfect evaluation pairing. Thus
there is exactly one entire signed family c, independently of any basis. -/
theorem costalkTateLinePullback_existsUnique (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) {T S : Scheme.{u}} (f : S ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hS : IsUnit (m : Γ(S, ⊤)))
    (hA : (m : A) = 0) :
    ∃! c : ∀ a : ℤ,
      (upperStar (ModuleCat.{u + 1} A) f).obj (T.finiteEtaleTateSheaf A m hA a) ≅
        S.finiteEtaleTateSheaf A m hA a,
      (∃ r : (upperStar AddCommGrpCat.{u + 1} f).obj (T.rootsOfUnitySheaf m) ≅
          S.rootsOfUnitySheaf m,
        (upperStar AddCommGrpCat.{u + 1} f).map (kernel.ι (m • 𝟙 T.gmSheaf)) ≫
            Scheme.upperStarGmSheafToGmSheaf f = r.hom ≫ kernel.ι (m • 𝟙 S.gmSheaf) ∧
        ∀ (W : T.Etaleᵒᵖ) (b : A) (z : (T.rootsOfUnitySheaf m).obj.obj W),
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
            (c 1).hom).hom.app W (Scheme.finiteEtaleTateOneGenerator A m T hA W b z) =
          Scheme.finiteEtaleTateOneGenerator A m S hA
            ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj W) b
            (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
              r.hom).hom.app W z)) ∧
      c 0 = (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app (ModuleCat.of A A) ∧
      (∀ n : ℕ, c (.ofNat (n + 2)) =
        asIso (Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) f)
          (T.finiteEtaleTateSheaf A m hA (.ofNat (n + 1))) (T.finiteEtaleTateLine m A hA)) ≪≫
          tensorIso (c (.ofNat (n + 1))) (c 1)) ∧
      ∀ n : ℕ,
        (upperStar (ModuleCat.{u + 1} A) f).map
          ((ihom.ev (T.finiteEtaleTateSheaf A m hA (.ofNat (n + 1)))).app
            (T.finiteEtaleTateSheaf A m hA 0)) ≫ (c 0).hom =
        Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) f)
          (T.finiteEtaleTateSheaf A m hA (.ofNat (n + 1)))
          (T.finiteEtaleTateSheaf A m hA (.negSucc n)) ≫
        tensorHom (c (.ofNat (n + 1))).hom (c (.negSucc n)).hom ≫
          (ihom.ev (S.finiteEtaleTateSheaf A m hA (.ofNat (n + 1)))).app
            (S.finiteEtaleTateSheaf A m hA 0) := by
  sorry

/-- The normalized signed pullback supplied by the recorded Tate-line theorem.
The choice is of the unique generator-normalized entire signed family above.
Source: lem-asd-etale-finite-twist-pullback, signed inverse-image witness
(blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateLinePullback (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) {T S : Scheme.{u}} (f : S ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hS : IsUnit (m : Γ(S, ⊤)))
    (hA : (m : A) = 0) (a : ℤ) :
    (upperStar (ModuleCat.{u + 1} A) f).obj (T.finiteEtaleTateSheaf A m hA a) ≅
      S.finiteEtaleTateSheaf A m hA a :=
  (costalkTateLinePullback_existsUnique A m hm f hT hS hA).choose a

/-- The canonical ordinary tensor-pullback comparison, using the normalized signed
roots-of-unity pullback of lem-asd-etale-finite-twist-pullback.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTatePullbackObj (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) {T S : Scheme.{u}} (f : S ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hS : IsUnit (m : Γ(S, ⊤)))
    (hA : (m : A) = 0) (a : ℤ)
    (K : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  asIso (Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) f)
    K (T.finiteEtaleTateSheaf A m hA a)) ≪≫
      tensorIso (Iso.refl _) (costalkTateLinePullback A m hm f hT hS hA a)

/-- Naturality of the canonical tensor-pullback comparison.
Source: lem-asd-etale-finite-twist-pullback (blueprint: lem-per-prime-power-costalk-reduction).
Proof: naturality of the monoidal tensorator followed by functoriality of tensoring
the normalized Tate pullback isomorphism. -/
theorem costalkTatePullbackObj_naturality (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) {T S : Scheme.{u}} (f : S ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hS : IsUnit (m : Γ(S, ⊤)))
    (hA : (m : A) = 0) (a : ℤ)
    {K K' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)} (g : K ⟶ K') :
    (upperStar (ModuleCat.{u + 1} A) f).map
        ((tensorRight (T.finiteEtaleTateSheaf A m hA a)).map g) ≫
      (costalkTatePullbackObj A m hm f hT hS hA a K').hom =
    (costalkTatePullbackObj A m hm f hT hS hA a K).hom ≫
      (tensorRight (S.finiteEtaleTateSheaf A m hA a)).map
        ((upperStar (ModuleCat.{u + 1} A) f).map g) := by
  sorry

/-- Exact localization of the ordinary canonical tensor-pullback square.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTatePullback (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) {T S : Scheme.{u}} (f : S ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hS : IsUnit (m : Γ(S, ⊤)))
    (hA : (m : A) = 0) (a : ℤ) :
    costalkTateTensorPlus A m hm T hT hA a ⋙
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus ≅
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus ⋙
        costalkTateTensorPlus A m hm S hS hA a :=
  letI := costalkTateTensor_exact A m hm T hT hA a
  letI := costalkTateTensor_exact A m hm S hS hA a
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (NatIso.ofComponents
        (F := tensorRight (T.finiteEtaleTateSheaf A m hA a) ⋙
          upperStar (ModuleCat.{u + 1} A) f)
        (G := upperStar (ModuleCat.{u + 1} A) f ⋙
          tensorRight (S.finiteEtaleTateSheaf A m hA a))
        (costalkTatePullbackObj A m hm f hT hS hA a)
        (costalkTatePullbackObj_naturality A m hm f hT hS hA a)) ≪≫
      Functor.mapDerivedCategoryPlusCompIso _ _

/-- The canonical closed direct-image projection: the mate of the Tate-pullback tensorator.
Source: Gabber XVII 1.4.1, supported-kernel adjunction
(blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateClosedProjection (A : Type (u + 1)) [CommRing A] [Finite A]
    (m : ℕ) (hm : 0 < m) {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (hT : IsUnit (m : Γ(T, ⊤))) (hZ : IsUnit (m : Γ(Z, ⊤)))
    (hA : (m : A) = 0) (a : ℤ) :
    (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus ⋙
      costalkTateTensorPlus A m hm T hT hA a ⟶
    costalkTateTensorPlus A m hm Z hZ hA a ⋙
      (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus :=
  (mateEquiv
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).derivedAdjunctionPlus
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).derivedAdjunctionPlus
    (TwoSquare.mk _ _ _ _ (costalkTatePullback A m hm i hT hZ hA a).hom)).natTrans

/-- The projection at a Tate line is invertible.
Source: Step 6 of the node, lem-asd-etale-finite-twist-pullback
(blueprint: lem-per-prime-power-costalk-reduction).
Proof: the line is dualizable by its normalized signed product and evaluation.
The adjunction projection formula for a dualizable object is invertible; its inverse
is obtained by inserting coevaluation and contracting evaluation. This is exactly
costalkTateClosedProjection, by the adjunction homEquiv, without any basis. -/
@[instance] theorem costalkTateClosedProjection_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (m : ℕ) (hm : 0 < m) {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (hT : IsUnit (m : Γ(T, ⊤))) (hZ : IsUnit (m : Γ(Z, ⊤)))
    (hA : (m : A) = 0) (a : ℤ) :
    IsIso (costalkTateClosedProjection A m hm i hT hZ hA a) := by
  sorry

/-- The closed-support tensor map is the counit mate of the inverse projection.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateClosedMap (A : Type (u + 1)) [CommRing A] [Finite A]
    (m : ℕ) (hm : 0 < m) {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (hT : IsUnit (m : Γ(T, ⊤))) (hZ : IsUnit (m : Γ(Z, ⊤)))
    (hA : (m : A) = 0) (a : ℤ) :
    closedSupportPlus A i ⋙ costalkTateTensorPlus A m hm Z hZ hA a ⟶
      costalkTateTensorPlus A m hm T hT hA a ⋙ closedSupportPlus A i :=
  (mateEquiv (closedSupportPlusAdjunction A i) (closedSupportPlusAdjunction A i)
    (TwoSquare.mk _ _ _ _ (inv (costalkTateClosedProjection A m hm i hT hZ hA a)))).natTrans

/-- The counit mate is invertible at every signed Tate line.
Source: Step 6 of the node (blueprint: lem-per-prime-power-costalk-reduction).
Proof: apply the same dual-line evaluation and coevaluation to the closed-support
adjunction. The triangle identities give inverse mates. This argument applies to
the supported-kernel right adjoint, without purity or constructibility. -/
@[instance] theorem costalkTateClosedMap_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (m : ℕ) (hm : 0 < m) {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (hT : IsUnit (m : Γ(T, ⊤))) (hZ : IsUnit (m : Γ(Z, ⊤)))
    (hA : (m : A) = 0) (a : ℤ) :
    IsIso (costalkTateClosedMap A m hm i hT hZ hA a) := by
  sorry

/-- The canonical exceptional tensor comparison, from the fixed support counit.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateClosed (A : Type (u + 1)) [CommRing A] [Finite A]
    (m : ℕ) (hm : 0 < m) {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (hT : IsUnit (m : Γ(T, ⊤))) (hZ : IsUnit (m : Γ(Z, ⊤)))
    (hA : (m : A) = 0) (a : ℤ) :
    costalkTateTensorPlus A m hm T hT hA a ⋙ closedSupportPlus A i ≅
      closedSupportPlus A i ⋙ costalkTateTensorPlus A m hm Z hZ hA a :=
  (asIso (costalkTateClosedMap A m hm i hT hZ hA a)).symm

section DerivedInterchange
variable {C : Type c₁} {D : Type c₂} [Category.{d₁} C] [Category.{d₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives C] [EnoughInjectives D]
  (T : C ⥤ C) (V : D ⥤ D) (F : C ⥤ D)
  [T.Additive] [V.Additive] [F.Additive]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [T.PreservesInjectiveObjects]

/-- Unit normalization for the derived interchange of exact tensor with a right derived
functor. This fixes the comparison on every bounded-below homotopy representative.
Source: Gabber XVII 1.4.1, Step 6 (blueprint: lem-per-prime-power-costalk-reduction). -/
def CostalkDerivedInterchangeLaw (c : T ⋙ F ≅ F ⋙ V)
    (e : T.mapDerivedCategoryPlus ⋙ F.rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus) : Prop :=
  ∀ H : HomotopyCategory.Plus C,
    F.rightDerivedFunctorPlusUnit.app (T.mapHomotopyCategoryPlus.obj H) ≫
      F.rightDerivedFunctorPlus.map (T.mapDerivedCategoryPlusFactorsh.inv.app H) ≫
      e.hom.app (_root_.DerivedCategory.Plus.Qh.obj H) =
    _root_.DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus c.hom).app H) ≫
      V.mapDerivedCategoryPlusFactorsh.inv.app (F.mapHomotopyCategoryPlus.obj H) ≫
      V.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnit.app H)

/-- The ordinary tensor comparison uniquely determines its derived interchange.
Source: Gabber XVII 1.4.1, Step 6 (blueprint: lem-per-prime-power-costalk-reduction).
Proof: exact tensor by a line and its dual preserve injectives. Derive the ordinary
isomorphism, using the composition isomorphism for the first tensor and exactness for
the second. The right-derived units give the displayed equality. Right-derived
uniqueness gives uniqueness of the transformation, and deriving the inverse makes it
an isomorphism. No basis or costalk-reduction isomorphism enters this construction. -/
theorem costalkDerivedInterchange_existsUnique (c : T ⋙ F ≅ F ⋙ V) :
    ∃! e : T.mapDerivedCategoryPlus ⋙ F.rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus,
      CostalkDerivedInterchangeLaw T V F c e := by
  sorry

/-- The uniquely unit-normalized derived comparison.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkDerivedInterchange (c : T ⋙ F ≅ F ⋙ V) :
    T.mapDerivedCategoryPlus ⋙ F.rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus :=
  (costalkDerivedInterchange_existsUnique T V F c).choose
end DerivedInterchange

/-- Tensor by a signed Tate line preserves injectives, since its inverse is tensor
by the dual line. Source: lem-asd-etale-finite-twist-pullback, signed multiplication
(blueprint: lem-per-prime-power-costalk-reduction).
Proof: normalized multiplication and evaluation identify tensor by opposite exponents
as inverse equivalences. Equivalences preserve injective objects. -/
theorem costalkTateTensor_preservesInjectives (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤)))
    (hA : (m : A) = 0) (a : ℤ) :
    (tensorRight (T.finiteEtaleTateSheaf A m hA a)).PreservesInjectiveObjects := by
  sorry

/-- The ordinary fibre tensorator, before taking any costalk comparisons.
Source: Gabber XVII 1.4.1; monoidality of the geometric fibre
(blueprint: lem-per-prime-power-costalk-reduction).
Proof: the oplax monoidal naturality square in the first tensor variable is precisely
the required naturality equation. Its components are isomorphisms by monoidality. -/
theorem costalkTateFiberObj_naturality (A : Type (u + 1)) [CommRing A]
    (m : ℕ) {T : Scheme.{u}} (hA : (m : A) = 0) (a : ℤ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    {K K' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)} (g : K ⟶ K') :
    (Scheme.pointSmallEtale t).sheafFiber.map
        ((tensorRight (T.finiteEtaleTateSheaf A m hA a)).map g) ≫
      Functor.OplaxMonoidal.δ (Scheme.pointSmallEtale t).sheafFiber K'
        (T.finiteEtaleTateSheaf A m hA a) =
    Functor.OplaxMonoidal.δ (Scheme.pointSmallEtale t).sheafFiber K
        (T.finiteEtaleTateSheaf A m hA a) ≫
      (tensorRight ((Scheme.pointSmallEtale t).sheafFiber.obj
        (T.finiteEtaleTateSheaf A m hA a))).map
          ((Scheme.pointSmallEtale t).sheafFiber.map g) := by
  sorry

/-- The canonical Tate tensor comparison for the geometric fibre on D+.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateFiber (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) {T : Scheme.{u}} (hT : IsUnit (m : Γ(T, ⊤)))
    (hA : (m : A) = 0) (a : ℤ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    costalkTateTensorPlus A m hm T hT hA a ⋙ costalkGeometricFiberPlus A t ≅
      costalkGeometricFiberPlus A t ⋙ costalkTateFiberTensorPlus A m hm hT hA a t :=
  letI := costalkTateTensor_exact A m hm T hT hA a
  letI := costalkTateFiber_exact A m hm hT hA a t
  letI := costalkTateTensor_preservesInjectives A m hm T hT hA a
  letI := (Scheme.pointSmallEtale t).sheafFiber_additive (A := ModuleCat.{u + 1} A)
  letI : PreservesColimitsOfSize.{0, 0} (tensorRight
    ((Scheme.pointSmallEtale t).sheafFiber.obj (T.finiteEtaleTateSheaf A m hA a))) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)
  costalkDerivedInterchange
    (tensorRight (T.finiteEtaleTateSheaf A m hA a))
    (tensorRight ((Scheme.pointSmallEtale t).sheafFiber.obj
      (T.finiteEtaleTateSheaf A m hA a))) (Scheme.pointSmallEtale t).sheafFiber
    (NatIso.ofComponents
      (F := tensorRight (T.finiteEtaleTateSheaf A m hA a) ⋙
        (Scheme.pointSmallEtale t).sheafFiber)
      (G := (Scheme.pointSmallEtale t).sheafFiber ⋙
        tensorRight ((Scheme.pointSmallEtale t).sheafFiber.obj
          (T.finiteEtaleTateSheaf A m hA a)))
      (fun K ↦ asIso (Functor.OplaxMonoidal.δ (Scheme.pointSmallEtale t).sheafFiber K
        (T.finiteEtaleTateSheaf A m hA a)))
      (fun g ↦ costalkTateFiberObj_naturality A m hA a t g))

/-- The canonical global germ at a geometric point, from the global-section limit cone.
Source: Gabber XVII 1.1.1; Stacks 03QO
(blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkGlobalGerm (A : Type (u + 1)) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj F ⟶
      (Scheme.pointSmallEtale t).sheafFiber.obj F :=
  F.ΓRes (Opposite.op (Scheme.Etale.mk (𝟙 T))) ≫
      (Scheme.pointSmallEtale t).toPresheafFiber (Scheme.Etale.mk (𝟙 T))
        (Over.homMk t (Category.comp_id t)) F.obj

/-- The supported germ is the support-kernel inclusion followed by the global germ.
Source: Gabber XVII 1.1.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkSupportedGerm (A : Type (u + 1)) [CommRing A]
    {T : Scheme.{u}} (W : T.Opens) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (supportedEtaleSections A T W).obj F ⟶ (Scheme.pointSmallEtale t).sheafFiber.obj F :=
  (supportedEtaleSectionsι A T W).app F ≫ costalkGlobalGerm A t F

/-- The germ equation determines the ordinary supported tensor comparison uniquely.
Source: Gabber XVII 1.4.1; Stacks 03QO
(blueprint: lem-per-prime-power-costalk-reduction).
Proof: global sections identify with the closed geometric fibre. Under this
identification the supported functor is the kernel of restriction, embedded in that
fibre. The canonical tensorator preserves this kernel because the Tate line is flat.
The restriction square commutes by the normalized Tate pullback. This constructs the
isomorphism and its inverse; the monic supported germ gives uniqueness. -/
theorem costalkTateSupportedObj_existsUnique (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) {T : Scheme.{u}} (hT : IsUnit (m : Γ(T, ⊤)))
    (hA : (m : A) = 0) (a : ℤ) (W : T.Opens)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (hΓ : ∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
      IsIso (costalkGlobalGerm A t F)) :
    ∃! e : tensorRight (T.finiteEtaleTateSheaf A m hA a) ⋙ supportedEtaleSections A T W ≅
      supportedEtaleSections A T W ⋙ tensorRight
        ((Scheme.pointSmallEtale t).sheafFiber.obj (T.finiteEtaleTateSheaf A m hA a)),
      ∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
        e.hom.app F ≫ (costalkSupportedGerm A W t F ▷
          (Scheme.pointSmallEtale t).sheafFiber.obj (T.finiteEtaleTateSheaf A m hA a)) =
        costalkSupportedGerm A W t (F ⊗ T.finiteEtaleTateSheaf A m hA a) ≫
          Functor.OplaxMonoidal.δ (Scheme.pointSmallEtale t).sheafFiber F
            (T.finiteEtaleTateSheaf A m hA a) := by
  sorry

/-- The unique supported tensorator characterized by the canonical germ, without a basis.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateSupportedObj (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) {T : Scheme.{u}} (hT : IsUnit (m : Γ(T, ⊤)))
    (hA : (m : A) = 0) (a : ℤ) (W : T.Opens)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (hΓ : ∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
      IsIso (costalkGlobalGerm A t F)) :
    tensorRight (T.finiteEtaleTateSheaf A m hA a) ⋙ supportedEtaleSections A T W ≅
      supportedEtaleSections A T W ⋙ tensorRight
        ((Scheme.pointSmallEtale t).sheafFiber.obj (T.finiteEtaleTateSheaf A m hA a)) :=
  (costalkTateSupportedObj_existsUnique A m hm hT hA a W t hΓ).choose

/-- Derive the uniquely germ-normalized supported tensor comparison using the fixed
right-derived unit. Source: Gabber XVII 1.4.1
(blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateSupportedPlus (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) {T : Scheme.{u}} (hT : IsUnit (m : Γ(T, ⊤)))
    (hA : (m : A) = 0) (a : ℤ) (W : T.Opens)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (hΓ : ∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
      IsIso (costalkGlobalGerm A t F)) :
    costalkTateTensorPlus A m hm T hT hA a ⋙
      (supportedEtaleSections A T W).rightDerivedFunctorPlus ≅
    (supportedEtaleSections A T W).rightDerivedFunctorPlus ⋙
      costalkTateFiberTensorPlus A m hm hT hA a t :=
  letI := costalkTateTensor_exact A m hm T hT hA a
  letI := costalkTateFiber_exact A m hm hT hA a t
  letI := costalkTateTensor_preservesInjectives A m hm T hT hA a
  letI : PreservesColimitsOfSize.{0, 0} (tensorRight
    ((Scheme.pointSmallEtale t).sheafFiber.obj (T.finiteEtaleTateSheaf A m hA a))) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)
  costalkDerivedInterchange
    (tensorRight (T.finiteEtaleTateSheaf A m hA a))
    (tensorRight ((Scheme.pointSmallEtale t).sheafFiber.obj
      (T.finiteEtaleTateSheaf A m hA a))) (supportedEtaleSections A T W)
    (costalkTateSupportedObj A m hm hT hA a W t hΓ)

/-- On a strictly henselian local affine scheme the canonical global germ at the
closed geometric point is invertible for module sheaves.
Source: Stacks 03QO; Gabber XVII 1.1.1
(blueprint: lem-per-prime-power-costalk-reduction).
Proof: identify the affine scheme with the spectrum of its global ring. Every
pointed etale neighbourhood of the closed point admits a pointed section over a
strictly henselian local ring. Surjectivity and injectivity of the germ follow by
pulling representatives and equalities along such sections. The construction is
linear in every scalar, so the abelian-group result applies to module sheaves. -/
theorem costalkGlobalGerm_isIso (A : Type (u + 1)) [CommRing A]
    {T : Scheme.{u}} [IsAffine T]
    (hlocal : IsStrictlyHenselianLocalRing Γ(T, ⊤))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (ht : IsClosed ({t default} : Set T))
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    IsIso (costalkGlobalGerm A t F) := by
  sorry

/-- The closed geometric point on a strict localization has invertible global germ.
Source: Gabber XVII 1.1.1; Stacks 03QO
(blueprint: lem-per-prime-power-costalk-reduction).
Proof: the strict localization is the spectrum of the strictly henselian local
strict-henselization ring; its evaluation geometric point lies at the closed point.
Apply the preceding module-valued global-germ theorem. -/
theorem costalkStrictLocalGerm_isIso (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X)
    (F : Sheaf (Scheme.strictLocalization s).smallEtaleTopology (ModuleCat.{u + 1} A)) :
    IsIso (costalkGlobalGerm A (Spec.map (Scheme.strictHenselizationEval s)) F) := by
  sorry

/-- Pasting of canonical tensor interchanges along a functor chain.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTatePaste {C : Type c₁} {D : Type c₂} {E : Type c₃}
    [Category.{d₁} C] [Category.{d₂} D] [Category.{d₃} E]
    {T : C ⥤ C} {U : D ⥤ D} {V : E ⥤ E} {F : C ⥤ D} {G : D ⥤ E}
    (q : T ⋙ F ≅ F ⋙ U) (r : U ⋙ G ≅ G ⋙ V) :
    T ⋙ (F ⋙ G) ≅ (F ⋙ G) ⋙ V :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight q G ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F r ≪≫
      (Functor.associator _ _ _).symm

/-- Invertible integers remain invertible on global sections after scheme pullback.
Source: Gabber XVII 1.1.1 (blueprint: lem-per-prime-power-costalk-reduction).
Proof: the ring map on global sections preserves units and the natural-number cast. -/
theorem costalkTateUnitMap (m : ℕ) {T S : Scheme.{u}}
    (hT : IsUnit (m : Γ(T, ⊤))) (f : S ⟶ T) : IsUnit (m : Γ(S, ⊤)) := by
  sorry

/-- Pullback of a Tate line followed by the geometric fibre, with the normalized
signed Tate-line comparison. Source: lem-asd-etale-finite-twist-pullback
(blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateFiberLine (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) {T S : Scheme.{u}} (f : S ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hS : IsUnit (m : Γ(S, ⊤)))
    (hA : (m : A) = 0) (a : ℤ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S) :
    (Scheme.pointSmallEtale (t ≫ f)).sheafFiber.obj (T.finiteEtaleTateSheaf A m hA a) ≅
      (Scheme.pointSmallEtale t).sheafFiber.obj (S.finiteEtaleTateSheaf A m hA a) :=
  ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) f t).app
    (T.finiteEtaleTateSheaf A m hA a)).symm ≪≫
      (Scheme.pointSmallEtale t).sheafFiber.mapIso
        (costalkTateLinePullback A m hm f hT hS hA a)

/-- A fibre-line isomorphism induces the exact coefficient tensor isomorphism.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateFiberChange (A : Type (u + 1)) [CommRing A]
    (L M : ModuleCat.{u + 1} A)
    [PreservesFiniteLimits (tensorRight L)] [PreservesFiniteLimits (tensorRight M)]
    (e : L ≅ M) :
    (tensorRight L).mapDerivedCategoryPlus ≅ (tensorRight M).mapDerivedCategoryPlus :=
  letI : PreservesColimitsOfSize.{0, 0} (tensorRight L) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)
  letI : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)
  Functor.mapDerivedCategoryPlusNatIso ((curriedTensor _).flip.mapIso e)

/-- The residue geometric point followed by its local closed immersion is the
original point. Source: Gabber XVII 1.1.1
(blueprint: lem-per-prime-power-costalk-reduction).
Proof: this is the inverse equation of SpecToEquivOfField, followed by the defining
residue-field factorization through the stalk spectrum. -/
theorem costalkPointFactorization {T : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    Spec.map (T.SpecToEquivOfField Ω t).2 ≫
      (Spec.map (T.residue (T.SpecToEquivOfField Ω t).1) ≫
        T.fromSpecStalk (T.SpecToEquivOfField Ω t).1) = t := by
  sorry

/-- The canonical costalk tensorator: restrict to the local ring, apply the
exceptional tensor counit mate, then the monoidal geometric fibre. The final fibre
line is transported from the original scheme by the normalized pullback comparison.
Source: Gabber XVII 1.1.1 and 1.4.1
(blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateCostalkPlus (A : Type (u + 1)) [CommRing A] [Finite A]
    (m : ℕ) (hm : 0 < m) {T : Scheme.{u}} (hT : IsUnit (m : Γ(T, ⊤)))
    (hA : (m : A) = 0) (a : ℤ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    costalkTateTensorPlus A m hm T hT hA a ⋙ geometricCostalkPlus A t ≅
      geometricCostalkPlus A t ⋙ costalkTateFiberTensorPlus A m hm hT hA a t :=
  let z := (T.SpecToEquivOfField Ω t).1
  let f := T.fromSpecStalk z
  let i := Spec.map (T.residue z)
  let q := Spec.map (T.SpecToEquivOfField Ω t).2
  let hV := costalkTateUnitMap m hT f
  let hZ := costalkTateUnitMap m hV i
  letI := costalkTateFiber_exact A m hm hT hA a t
  letI := costalkTateFiber_exact A m hm hZ hA a q
  costalkTatePaste
    (costalkTatePullback A m hm f hT hV hA a)
    (costalkTatePaste (costalkTateClosed A m hm i hV hZ hA a)
      (costalkTateFiber A m hm hZ hA a q)) ≪≫
      Functor.isoWhiskerLeft (geometricCostalkPlus A t)
        (costalkTateFiberChange A _ _
          ((costalkTateFiberLine A m hm (i ≫ f) hT hZ hA a q).symm ≪≫
            eqToIso (congrArg
              (fun s ↦ (Scheme.pointSmallEtale s).sheafFiber.obj
                (T.finiteEtaleTateSheaf A m hA a))
              (costalkPointFactorization t))))

/-- Transport the coefficient fibre line through a scheme map and a specified
geometric-point factorization. Source: lem-asd-etale-finite-twist-pullback
(blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateFiberTransport (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) {T S : Scheme.{u}} (f : S ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hS : IsUnit (m : Γ(S, ⊤)))
    (hA : (m : A) = 0) (a : ℤ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ S) (s : Spec (.of Ω) ⟶ T) (hs : t ≫ f = s) :
    (Scheme.pointSmallEtale t).sheafFiber.obj (S.finiteEtaleTateSheaf A m hA a) ≅
      (Scheme.pointSmallEtale s).sheafFiber.obj (T.finiteEtaleTateSheaf A m hA a) :=
  (costalkTateFiberLine A m hm f hT hS hA a t).symm ≪≫
    eqToIso (congrArg (fun v ↦ (Scheme.pointSmallEtale v).sheafFiber.obj
      (T.finiteEtaleTateSheaf A m hA a)) hs)

/-- Extend an interchange to unbounded coefficient output, using the uniquely
K-flat-normalized realization of exact tensor as derived tensor.
Source: def-kun-derived-tensor; Gabber XVII 1.4.1
(blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateInclude {C : Type c₁} [Category.{d₁} C] (T : C ⥤ C)
    (A : Type (u + 1)) [CommRing A] (L : ModuleCat.{u + 1} A)
    [PreservesFiniteLimits (tensorRight L)]
    (F : C ⥤ _root_.DerivedCategory.Plus (ModuleCat.{u + 1} A))
    (q : T ⋙ F ≅ F ⋙ (tensorRight L).mapDerivedCategoryPlus) :
    T ⋙ (F ⋙ _root_.DerivedCategory.Plus.ι) ≅
      (F ⋙ _root_.DerivedCategory.Plus.ι) ⋙
        tensorRight ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj L) :=
  letI : PreservesColimitsOfSize.{0, 0} (tensorRight L) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)
  costalkTatePaste (F := F) (G := _root_.DerivedCategory.Plus.ι)
    q ((tensorRight L).mapDerivedCategoryPlusCompatibility ≪≫
    Functor.isoWhiskerLeft _root_.DerivedCategory.Plus.ι (costalkTensorRealization (C :=
      ModuleCat.{u + 1} A) L))

/-- Transport a chain interchange to the fixed geometric fibre of its initial Tate line.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateRebase {C : Type c₁} [Category.{d₁} C] (T : C ⥤ C)
    (A : Type (u + 1)) [CommRing A] (L M : ModuleCat.{u + 1} A)
    [PreservesFiniteLimits (tensorRight L)] [PreservesFiniteLimits (tensorRight M)]
    (F : C ⥤ _root_.DerivedCategory.Plus (ModuleCat.{u + 1} A))
    (q : T ⋙ F ≅ F ⋙ (tensorRight L).mapDerivedCategoryPlus) (e : L ≅ M) :
    T ⋙ F ≅ F ⋙ (tensorRight M).mapDerivedCategoryPlus :=
  q ≪≫ Functor.isoWhiskerLeft F (costalkTateFiberChange A L M e)

/-- Exact Tate tensor on sheaves realizes the actual recorded derived tensor on D+.
Source: def-kun-derived-tensor (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateRealization (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤)))
    (hA : (m : A) = 0) (a : ℤ) :
    costalkTateTensorPlus A m hm T hT hA a ⋙ _root_.DerivedCategory.Plus.ι ≅
      _root_.DerivedCategory.Plus.ι ⋙ costalkTateTensor A m T hA a :=
  letI := costalkTateTensor_exact A m hm T hT hA a
  (tensorRight (T.finiteEtaleTateSheaf A m hA a)).mapDerivedCategoryPlusCompatibility ≪≫
    Functor.isoWhiskerLeft _root_.DerivedCategory.Plus.ι
      (costalkTensorRealization
        (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
        (T.finiteEtaleTateSheaf A m hA a))

/-- The geometric costalk comparison with the actual derived coefficient tensor.
Source: Gabber XVII 1.1.1 and 1.4.1
(blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateCostalk (A : Type (u + 1)) [CommRing A] [Finite A]
    (m : ℕ) (hm : 0 < m) {T : Scheme.{u}} (hT : IsUnit (m : Γ(T, ⊤)))
    (hA : (m : A) = 0) (a : ℤ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    costalkTateTensorPlus A m hm T hT hA a ⋙
      (geometricCostalkPlus A t ⋙ _root_.DerivedCategory.Plus.ι) ≅
    (geometricCostalkPlus A t ⋙ _root_.DerivedCategory.Plus.ι) ⋙
      tensorRight ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
        ((Scheme.pointSmallEtale t).sheafFiber.obj (T.finiteEtaleTateSheaf A m hA a))) :=
  letI := costalkTateFiber_exact A m hm hT hA a t
  costalkTateInclude (costalkTateTensorPlus A m hm T hT hA a) A
    ((Scheme.pointSmallEtale t).sheafFiber.obj (T.finiteEtaleTateSheaf A m hA a))
    (geometricCostalkPlus A t) (costalkTateCostalkPlus A m hm hT hA a t)

/-- The two strict-local functors in the geometric costalk formula.
Source: Gabber XVII, Definition 1.1.1 and its footnote
(blueprint: lem-per-prime-power-costalk-reduction). -/
abbrev costalkStrictLocalTerms (A : Type (u + 1)) [CommRing A] [Finite A]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    Fin 2 → (_root_.DerivedCategory.Plus
      (Sheaf (Scheme.strictLocalization s).smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
        _root_.DerivedCategory (ModuleCat.{u + 1} A))
  | 0 => geometricCostalkPlus A (Spec.map (Scheme.strictHenselizationEval s)) ⋙
      _root_.DerivedCategory.Plus.ι
  | 1 => derivedSupportedEtaleSections A (Scheme.strictLocalization s)
      ⟨{IsLocalRing.closedPoint (Scheme.strictHenselization s)}ᶜ,
        (IsLocalRing.isClosed_singleton_closedPoint _).isOpen_compl⟩

/-- A comparison commutes with the canonical derived Tate interchange maps.
The two maps are the normalized comparisons supplied by `costalkDerivedInterchange`,
whose unit equation fixes them on K-flat representatives; this predicate records the
resulting square without choosing a basis.
Source: Gabber XVII 1.4.1, Step 6
(blueprint: lem-per-prime-power-costalk-reduction). -/
def CostalkTateCompatibility {C : Type c₁} {D : Type c₂}
    [Category.{d₁} C] [Category.{d₂} D]
    (T : C ⥤ C) (U : D ⥤ D) (F G : C ⥤ D)
    (qF : T ⋙ F ≅ F ⋙ U) (qG : T ⋙ G ≅ G ⋙ U) (e : F ≅ G) : Prop :=
  Functor.whiskerLeft T e.hom ≫ qG.hom = qF.hom ≫ Functor.whiskerRight e.hom U

/-- Canonical tensor comparison after restriction, rebased to the original geometric
fibre using its specified factorization. Source: Gabber XVII 1.4.1
(blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateAfterPullback (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) {T S : Scheme.{u}} (f : S ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hS : IsUnit (m : Γ(S, ⊤)))
    (hA : (m : A) = 0) (a : ℤ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ S) (s : Spec (.of Ω) ⟶ T) (hs : t ≫ f = s)
    (F : _root_.DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory.Plus (ModuleCat.{u + 1} A))
    (q : costalkTateTensorPlus A m hm S hS hA a ⋙ F ≅
      F ⋙ costalkTateFiberTensorPlus A m hm hS hA a t) :
    costalkTateTensorPlus A m hm T hT hA a ⋙ ((upperStar (ModuleCat.{u + 1} A)
      f).mapDerivedCategoryPlus ⋙ F) ≅
      ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus ⋙ F) ⋙
        costalkTateFiberTensorPlus A m hm hT hA a s :=
  letI := costalkTateFiber_exact A m hm hT hA a s
  letI := costalkTateFiber_exact A m hm hS hA a t
  costalkTateRebase (costalkTateTensorPlus A m hm T hT hA a) A _ _
    ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus ⋙ F)
    (costalkTatePaste (costalkTatePullback A m hm f hT hS hA a) q)
    (costalkTateFiberTransport A m hm f hT hS hA a t s hs)

/-- The coefficient derived Tate tensor with the actual geometric fibre line.
Source: def-kun-derived-tensor (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateDerivedFiber (A : Type (u + 1)) [CommRing A]
    (m : ℕ) {T : Scheme.{u}} (hA : (m : A) = 0) (a : ℤ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T) :
    _root_.DerivedCategory (ModuleCat.{u + 1} A) ⥤ _root_.DerivedCategory (ModuleCat.{u + 1} A) :=
  tensorRight ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
    ((Scheme.pointSmallEtale s).sheafFiber.obj (T.finiteEtaleTateSheaf A m hA a)))

/-- The strict-local supported-sections interchange at its canonical closed point.
Source: Gabber XVII 1.1.1 and 1.4.1
(blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateStrictSupportedPlus (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) {X : Scheme.{u}} (hX : IsUnit (m : Γ(X, ⊤)))
    (hA : (m : A) = 0) (a : ℤ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :=
  costalkTateSupportedPlus A m hm
    (costalkTateUnitMap m hX (Scheme.strictLocalizationToBase s)) hA a
    ⟨{IsLocalRing.closedPoint (Scheme.strictHenselization s)}ᶜ,
      (IsLocalRing.isClosed_singleton_closedPoint _).isOpen_compl⟩
    (Spec.map (Scheme.strictHenselizationEval s)) (costalkStrictLocalGerm_isIso A s)

/-- The two strict-local canonical interchanges, before any comparison is selected.
Source: Gabber XVII 1.1.1 and 1.4.1
(blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateStrictTerms (A : Type (u + 1)) [CommRing A] [Finite A]
    (m : ℕ) (hm : 0 < m) {X : Scheme.{u}} (hX : IsUnit (m : Γ(X, ⊤)))
    (hA : (m : A) = 0) (a : ℤ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) (j : Fin 2) :
    costalkTateTensorPlus A m hm (Scheme.strictLocalization s)
        (costalkTateUnitMap m hX (Scheme.strictLocalizationToBase s)) hA a ⋙
      costalkStrictLocalTerms A s j ≅
    costalkStrictLocalTerms A s j ⋙
      costalkTateDerivedFiber A m hA a (Spec.map (Scheme.strictHenselizationEval s)) :=
  match j with
  | 0 => costalkTateCostalk A m hm
      (costalkTateUnitMap m hX (Scheme.strictLocalizationToBase s)) hA a
      (Spec.map (Scheme.strictHenselizationEval s))
  | 1 =>
    letI := costalkTateFiber_exact A m hm
      (costalkTateUnitMap m hX (Scheme.strictLocalizationToBase s)) hA a
      (Spec.map (Scheme.strictHenselizationEval s))
    costalkTateInclude _ A _ _ (costalkTateStrictSupportedPlus A m hm hX hA a s)

/-- The evaluation point of a strict localization lies above its defining point.
Source: Gabber XVII 1.1.1 (blueprint: lem-per-prime-power-costalk-reduction).
Proof: the defining evaluation on the strict-henselization colimit restricts to the
original local evaluation, giving the displayed equality of spectrum morphisms. -/
theorem costalkStrictPointFactorization {X : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Spec.map (Scheme.strictHenselizationEval s) ≫ Scheme.strictLocalizationToBase s = s := by
  sorry

/-- The restriction arrow's target interchange starts with the actual Tate line on X.
Source: Gabber XVII 1.1.1 and 1.4.1
(blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateStrictRestriction (A : Type (u + 1)) [CommRing A] [Finite A]
    (m : ℕ) (hm : 0 < m) {X : Scheme.{u}} (hX : IsUnit (m : Γ(X, ⊤)))
    (hA : (m : A) = 0) (a : ℤ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :=
  let hS := costalkTateUnitMap m hX (Scheme.strictLocalizationToBase s)
  let t := Spec.map (Scheme.strictHenselizationEval s)
  letI := costalkTateFiber_exact A m hm hX hA a s
  costalkTateInclude _ A _ _
    (costalkTateAfterPullback A m hm (Scheme.strictLocalizationToBase s) hX hS hA a
      t s (costalkStrictPointFactorization s) (geometricCostalkPlus A t)
      (costalkTateCostalkPlus A m hm hS hA a t))

/-- Geometric costalks are strict-local supported cohomology, naturally in K.
Source: Gabber XVII, Definition 1.1.1 and footnote, printed pp. 258--259
(blueprint: lem-per-prime-power-costalk-reduction).
Proof: derive the supported-kernel adjunction on module injectives, whose sections
are the kernel of restriction to the complementary open (Step 1). Strict henselization
is ind-etale over the local ring, with closed fibre the separable residue closure;
apply ind-etale closed-support base change. On that closed fibre sections are the
exact geometric stalk, so derived supported sections compute the costalk (Step 2).
Scalar actions are preserved by each restriction and each kernel. -/
theorem primePower_costalk_strictLocal
    (ℓ n : ℕ) [Fact ℓ.Prime] (hn : 1 ≤ n)
    {X : Scheme.{u}} [IsNoetherian X]
    (hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hℓ : IsUnit (ℓ : Γ(X, ⊤)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    ∃ r : (geometricCostalkPlus (ULift.{u + 1} (ZMod (ℓ ^ n))) s ⋙
      _root_.DerivedCategory.Plus.ι) ≅
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))
        (Scheme.strictLocalizationToBase s)).mapDerivedCategoryPlus ⋙
          costalkStrictLocalTerms (ULift.{u + 1} (ZMod (ℓ ^ n))) s 0,
    ∃ d : costalkStrictLocalTerms (ULift.{u + 1} (ZMod (ℓ ^ n))) s 0 ≅
      costalkStrictLocalTerms (ULift.{u + 1} (ZMod (ℓ ^ n))) s 1,
    NatTrans.CommShift r.hom ℤ ∧ NatTrans.CommShift d.hom ℤ ∧
    ∀ a : ℤ,
      CostalkTateCompatibility
        (costalkTateTensorPlus (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n) X (costalkTateUnit ℓ n hℓ (𝟙 X)) (CharP.cast_eq_zero _ (ℓ ^ n)) a)
        (costalkTateDerivedFiber (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (CharP.cast_eq_zero _ (ℓ ^
          n)) a s) _ _
        (costalkTateCostalk (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (costalkTateUnit ℓ n hℓ (𝟙 X)) (CharP.cast_eq_zero _ (ℓ ^ n)) a s)
        (costalkTateStrictRestriction (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (costalkTateUnit ℓ n hℓ (𝟙 X)) (CharP.cast_eq_zero _ (ℓ ^ n)) a s) r ∧
      CostalkTateCompatibility
        (costalkTateTensorPlus (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n) (Scheme.strictLocalization s)
        (costalkTateUnitMap (ℓ ^ n) (costalkTateUnit ℓ n hℓ (𝟙 X))
          (Scheme.strictLocalizationToBase s)) (CharP.cast_eq_zero _ (ℓ ^ n)) a)
        (costalkTateDerivedFiber (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (CharP.cast_eq_zero _ (ℓ ^
          n)) a
          (Spec.map (Scheme.strictHenselizationEval s))) _ _
        (costalkTateStrictTerms (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (costalkTateUnit ℓ n hℓ (𝟙 X)) (CharP.cast_eq_zero _ (ℓ ^ n)) a s 0)
        (costalkTateStrictTerms (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (costalkTateUnit ℓ n hℓ (𝟙 X)) (CharP.cast_eq_zero _ (ℓ ^ n)) a s 1) d := by
  sorry

/-- Restriction to the reduced specialization curve, followed by its closed support.
Source: Gabber XVII, Definition 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
abbrev specializationSupportPlus (A : Type (u + 1)) [CommRing A] [Finite A]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) {Z : Scheme.{u}}
    (i : Z ⟶ Scheme.strictLocalization x) [IsClosedImmersion i] :
    _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (upperStar (ModuleCat.{u + 1} A) (Scheme.strictLocalizationToBase x)).mapDerivedCategoryPlus ⋙
    closedSupportPlus A i

/-- The reduced closure of an immediate geometric generization is a strictly henselian
excellent local integral curve.
Source: Gabber XVII, Definitions 1.1.2 and 1.4.1, printed pp. 259, 262
(blueprint: lem-per-prime-power-costalk-reduction).
Proof (Step 3): strict henselization preserves Noetherianity and excellence. The
reduced closure of a point is integral, and a closed subscheme of a strictly henselian
local scheme is affine, local and strictly henselian. Its dimension is one by the
immediacy assumption. These assertions do not depend on the coefficient complex. -/
theorem primePower_costalk_closure_geometry
    (ℓ n : ℕ) [Fact ℓ.Prime] (hn : 1 ≤ n)
    {X : Scheme.{u}} [IsNoetherian X]
    (hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hℓ : IsUnit (ℓ : Γ(X, ⊤)))
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    (x : Spec (.of Ωx) ⟶ X) (y : Spec (.of Ωy) ⟶ X)
    (σ : Scheme.strictLocalization y ⟶ Scheme.strictLocalization x)
    (hσ : σ ≫ Scheme.strictLocalizationToBase x = Scheme.strictLocalizationToBase y)
    {Z : Scheme.{u}} (i : Z ⟶ Scheme.strictLocalization x)
    [IsClosedImmersion i] [IsReduced Z]
    (hZ : Set.range i = closure (Set.range (Spec.map (Scheme.strictHenselizationEval y) ≫ σ)))
    (hdim : topologicalKrullDim Z = 1) :
    IsIntegral Z ∧ IsAffine Z ∧ IsNoetherian Z ∧
      (∀ U : Z.affineOpens, IsExcellent Γ(Z, U)) ∧
      IsStrictlyHenselianLocalRing Γ(Z, ⊤) := by
  sorry

/-- The normalization of that curve is a finite universal homeomorphism from a strictly
henselian trait, with the same generic point and function field; inverse image is an
etale-topos equivalence.
Source: Gabber XVII, section 1.3 and Definition 1.4.1, printed p. 262
(blueprint: lem-per-prime-power-costalk-reduction).
Proof (Steps 3 and 5): excellence makes normalization finite. A finite algebra over a
henselian local ring is a product of local rings; its integral normalization is a domain,
so there is just one factor. Its residue extension is purely inseparable since the
base residue field is separably closed. The normal Noetherian local domain of dimension
one is a DVR, and finite henselian permanence makes it strictly henselian. The generic
field is unchanged by normalization. Thus the map is universally bijective and integral,
hence a universal homeomorphism. Topological invariance gives the etale equivalence. -/
theorem primePower_costalk_normalization_geometry
    (ℓ n : ℕ) [Fact ℓ.Prime] (hn : 1 ≤ n)
    {X : Scheme.{u}} [IsNoetherian X]
    (hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hℓ : IsUnit (ℓ : Γ(X, ⊤)))
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    (x : Spec (.of Ωx) ⟶ X) (y : Spec (.of Ωy) ⟶ X)
    (σ : Scheme.strictLocalization y ⟶ Scheme.strictLocalization x)
    (hσ : σ ≫ Scheme.strictLocalizationToBase x = Scheme.strictLocalizationToBase y)
    {Z : Scheme.{u}} (i : Z ⟶ Scheme.strictLocalization x)
    [IsClosedImmersion i] [IsIntegral Z]
    (hZ : Set.range i = closure (Set.range (Spec.map (Scheme.strictHenselizationEval y) ≫ σ)))
    (hdim : topologicalKrullDim Z = 1) :
    IsFinite Z.fromNormalization ∧
      (topologically IsHomeomorph).universally Z.fromNormalization ∧
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))
        Z.fromNormalization).IsEquivalence ∧
      (∃ (R : CommRingCat.{u}) (_ : IsDomain R) (_ : IsDiscreteValuationRing R),
        IsStrictlyHenselianLocalRing R ∧ Nonempty (Z.normalization ≅ Spec R)) ∧
      ∀ (η : Z.normalization) (z : Z),
        IsGenericPoint η Set.univ → IsGenericPoint z Set.univ →
          Z.fromNormalization η = z ∧ IsIso (Z.fromNormalization.residueFieldMap η) := by
  sorry

/-- The normalized closed residue degree is finite purely inseparable, a power of the
positive residue characteristic (one in characteristic zero), and a unit in Z/ell^n.
Source: Gabber XVII, section 1.3, printed p. 262
(blueprint: lem-per-prime-power-costalk-reduction).
Proof (Step 3): the finite local normalization has purely inseparable closed residue
extension. Its degree is a power of the residue characteristic, or one in characteristic
zero. Since ell is invertible on X, that prime differs from ell. Bezout for this degree
and ell^n produces its inverse modulo ell^n, also for n=1 and degree one. -/
theorem primePower_costalk_residue_degree
    (ℓ n : ℕ) [Fact ℓ.Prime] (hn : 1 ≤ n)
    {X : Scheme.{u}} [IsNoetherian X]
    (hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hℓ : IsUnit (ℓ : Γ(X, ⊤)))
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    (x : Spec (.of Ωx) ⟶ X) (y : Spec (.of Ωy) ⟶ X)
    (σ : Scheme.strictLocalization y ⟶ Scheme.strictLocalization x)
    (hσ : σ ≫ Scheme.strictLocalizationToBase x = Scheme.strictLocalizationToBase y)
    {Z : Scheme.{u}} (i : Z ⟶ Scheme.strictLocalization x)
    [IsClosedImmersion i] [IsIntegral Z]
    (hZ : Set.range i = closure (Set.range (Spec.map (Scheme.strictHenselizationEval y) ≫ σ)))
    (hdim : topologicalKrullDim Z = 1)
    (c : Z.normalization) (hc : IsClosed ({c} : Set Z.normalization)) :
    (Z.fromNormalization.residueFieldMap c).hom.Finite ∧
      @IsPurelyInseparable (Z.residueField (Z.fromNormalization c))
        (Z.normalization.residueField c) _ _
        (Z.fromNormalization.residueFieldMap c).hom.toAlgebra ∧
      (ringChar (Z.residueField (Z.fromNormalization c)) = 0 →
        (Z.fromNormalization.residueFieldMap c).hom.finrank ⊥ = 1) ∧
      (ringChar (Z.residueField (Z.fromNormalization c)) ≠ 0 →
        ∃ r : ℕ, (Z.fromNormalization.residueFieldMap c).hom.finrank ⊥ =
          ringChar (Z.residueField (Z.fromNormalization c)) ^ r) ∧
      IsUnit (((Z.fromNormalization.residueFieldMap c).hom.finrank ⊥ : ℕ) :
        ULift.{u + 1} (ZMod (ℓ ^ n))) := by
  sorry

/-- Both geometric points on the specialization curve lift uniquely through normalization.
Source: Gabber XVII, section 1.3 and Definition 1.4.1
(blueprint: lem-per-prime-power-costalk-reduction).
Proof (Steps 3--5): the geometric generization and closed geometric point factor through
the reduced closed curve because their maps kill its radical defining ideal. A universal
homeomorphism has exactly one lift of each algebraically closed geometric point: its
residue extension is purely inseparable. This also fixes the points in the comparisons. -/
theorem primePower_costalk_point_lifts
    (ℓ n : ℕ) [Fact ℓ.Prime] (hn : 1 ≤ n)
    {X : Scheme.{u}} [IsNoetherian X]
    (hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hℓ : IsUnit (ℓ : Γ(X, ⊤)))
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    (x : Spec (.of Ωx) ⟶ X) (y : Spec (.of Ωy) ⟶ X)
    (σ : Scheme.strictLocalization y ⟶ Scheme.strictLocalization x)
    (hσ : σ ≫ Scheme.strictLocalizationToBase x = Scheme.strictLocalizationToBase y)
    {Z : Scheme.{u}} (i : Z ⟶ Scheme.strictLocalization x)
    [IsClosedImmersion i] [IsIntegral Z]
    (hZ : Set.range i = closure (Set.range (Spec.map (Scheme.strictHenselizationEval y) ≫ σ)))
    (hdim : topologicalKrullDim Z = 1) :
    (∃! yZ : Spec (.of Ωy) ⟶ Z,
      yZ ≫ i = Spec.map (Scheme.strictHenselizationEval y) ≫ σ) ∧
      (∃! xZ : Spec (.of Ωx) ⟶ Z,
        xZ ≫ i = Spec.map (Scheme.strictHenselizationEval x)) ∧
      (∀ yZ : Spec (.of Ωy) ⟶ Z, ∃! yN : Spec (.of Ωy) ⟶ Z.normalization,
        yN ≫ Z.fromNormalization = yZ) ∧
      (∀ xZ : Spec (.of Ωx) ⟶ Z, ∃! xN : Spec (.of Ωx) ⟶ Z.normalization,
        xN ≫ Z.fromNormalization = xZ) := by
  sorry

/-- The six terms of the two comparison chains, on the common strict localization.
Indices 0,1,2 are the generic chain and 3,4,5 the closed chain. The geometric points
are the ones induced by the given specialization and normalization, as in the theorem.
Source: Gabber XVII, Definition 1.4.1 comparison square
(blueprint: lem-per-prime-power-costalk-reduction). -/
abbrev costalkReductionLocalTerms
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X : Scheme.{u}} {Ωx Ωy : Type u}
    [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    (x : Spec (.of Ωx) ⟶ X)
    {y : Spec (.of Ωy) ⟶ X}
    (σ : Scheme.strictLocalization y ⟶ Scheme.strictLocalization x)
    {Z : Scheme.{u}} (i : Z ⟶ Scheme.strictLocalization x)
    [IsClosedImmersion i] [IsIntegral Z]
    (yZ : Spec (.of Ωy) ⟶ Z) (xZ : Spec (.of Ωx) ⟶ Z)
    (yN : Spec (.of Ωy) ⟶ Z.normalization)
    (W : Z.normalization.Opens) :
    Fin 6 → (_root_.DerivedCategory.Plus
      (Sheaf (Scheme.strictLocalization x).smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
        _root_.DerivedCategory (ModuleCat.{u + 1} A))
  | 0 => geometricCostalkPlus A
      (Spec.map (Scheme.strictHenselizationEval y) ≫ σ) ⋙ _root_.DerivedCategory.Plus.ι
  | 1 => closedSupportPlus A i ⋙ geometricCostalkPlus A yZ ⋙ _root_.DerivedCategory.Plus.ι
  | 2 => closedSupportPlus A i ⋙
      (upperStar (ModuleCat.{u + 1} A) Z.fromNormalization).mapDerivedCategoryPlus ⋙
        geometricFiberPlus A yN
  | 3 => geometricCostalkPlus A
      (Spec.map (Scheme.strictHenselizationEval x)) ⋙ _root_.DerivedCategory.Plus.ι
  | 4 => closedSupportPlus A i ⋙ geometricCostalkPlus A xZ ⋙ _root_.DerivedCategory.Plus.ι
  | 5 => closedSupportPlus A i ⋙
      (upperStar (ModuleCat.{u + 1} A) Z.fromNormalization).mapDerivedCategoryPlus ⋙
        derivedSupportedEtaleSections A Z.normalization W

/-- Canonical interchange after exceptional inverse image, with the fibre line
transported along the closed immersion. Source: Gabber XVII 1.4.1
(blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateAfterClosed (A : Type (u + 1)) [CommRing A] [Finite A]
    (m : ℕ) (hm : 0 < m) {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (hT : IsUnit (m : Γ(T, ⊤))) (hZ : IsUnit (m : Γ(Z, ⊤)))
    (hA : (m : A) = 0) (a : ℤ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (z : Spec (.of Ω) ⟶ Z) (t : Spec (.of Ω) ⟶ T) (ht : z ≫ i = t)
    (F : _root_.DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory.Plus (ModuleCat.{u + 1} A))
    (q : costalkTateTensorPlus A m hm Z hZ hA a ⋙ F ≅
      F ⋙ costalkTateFiberTensorPlus A m hm hZ hA a z) :
    costalkTateTensorPlus A m hm T hT hA a ⋙ (closedSupportPlus A i ⋙ F) ≅
      (closedSupportPlus A i ⋙ F) ⋙ costalkTateFiberTensorPlus A m hm hT hA a t :=
  letI := costalkTateFiber_exact A m hm hT hA a t
  letI := costalkTateFiber_exact A m hm hZ hA a z
  costalkTateRebase (costalkTateTensorPlus A m hm T hT hA a) A _ _
    (closedSupportPlus A i ⋙ F)
    (costalkTatePaste (costalkTateClosed A m hm i hT hZ hA a) q)
    (costalkTateFiberTransport A m hm i hT hZ hA a z t ht)

/-- The six chain functors before inclusion of bounded-below coefficient complexes.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
abbrev costalkReductionLocalTermsPlus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X : Scheme.{u}} {Ωx Ωy : Type u}
    [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    (x : Spec (.of Ωx) ⟶ X) {y : Spec (.of Ωy) ⟶ X}
    (σ : Scheme.strictLocalization y ⟶ Scheme.strictLocalization x)
    {Z : Scheme.{u}} (i : Z ⟶ Scheme.strictLocalization x)
    [IsClosedImmersion i] [IsIntegral Z]
    (yZ : Spec (.of Ωy) ⟶ Z) (xZ : Spec (.of Ωx) ⟶ Z)
    (yN : Spec (.of Ωy) ⟶ Z.normalization) (W : Z.normalization.Opens) :
    Fin 6 → (_root_.DerivedCategory.Plus
      (Sheaf (Scheme.strictLocalization x).smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
        _root_.DerivedCategory.Plus (ModuleCat.{u + 1} A))
  | 0 => geometricCostalkPlus A (Spec.map (Scheme.strictHenselizationEval y) ≫ σ)
  | 1 => closedSupportPlus A i ⋙ geometricCostalkPlus A yZ
  | 2 =>
    letI := (Scheme.pointSmallEtale yN).sheafFiber_additive (A := ModuleCat.{u + 1} A)
    closedSupportPlus A i ⋙
      (upperStar (ModuleCat.{u + 1} A) Z.fromNormalization).mapDerivedCategoryPlus ⋙
        (Scheme.pointSmallEtale yN).sheafFiber.rightDerivedFunctorPlus
  | 3 => geometricCostalkPlus A (Spec.map (Scheme.strictHenselizationEval x))
  | 4 => closedSupportPlus A i ⋙ geometricCostalkPlus A xZ
  | 5 => closedSupportPlus A i ⋙
      (upperStar (ModuleCat.{u + 1} A) Z.fromNormalization).mapDerivedCategoryPlus ⋙
        (supportedEtaleSections A Z.normalization W).rightDerivedFunctorPlus

/-- Actual geometric fibre line for each of the two chains, without a trivialization.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
abbrev costalkReductionFiberLine (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (a : ℤ)
    {X : Scheme.{u}} {Ωx Ωy : Type u}
    [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    (x : Spec (.of Ωx) ⟶ X) {y : Spec (.of Ωy) ⟶ X}
    (σ : Scheme.strictLocalization y ⟶ Scheme.strictLocalization x) :
    Fin 6 → ModuleCat.{u + 1} A
  | 0 | 1 | 2 => (Scheme.pointSmallEtale
      (Spec.map (Scheme.strictHenselizationEval y) ≫ σ)).sheafFiber.obj
        ((Scheme.strictLocalization x).finiteEtaleTateSheaf A m hA a)
  | 3 | 4 | 5 => (Scheme.pointSmallEtale
      (Spec.map (Scheme.strictHenselizationEval x))).sheafFiber.obj
        ((Scheme.strictLocalization x).finiteEtaleTateSheaf A m hA a)

/-- Exact fibre Tate tensor for each comparison chain.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkReductionFiberTensorPlus (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) {X : Scheme.{u}} (hX : IsUnit (m : Γ(X, ⊤)))
    (hA : (m : A) = 0) (a : ℤ)
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    (x : Spec (.of Ωx) ⟶ X) {y : Spec (.of Ωy) ⟶ X}
    (σ : Scheme.strictLocalization y ⟶ Scheme.strictLocalization x) :
    Fin 6 → (_root_.DerivedCategory.Plus (ModuleCat.{u + 1} A) ⥤
      _root_.DerivedCategory.Plus (ModuleCat.{u + 1} A))
  | 0 | 1 | 2 => costalkTateFiberTensorPlus A m hm
      (costalkTateUnitMap m hX (Scheme.strictLocalizationToBase x)) hA a
      (Spec.map (Scheme.strictHenselizationEval y) ≫ σ)
  | 3 | 4 | 5 => costalkTateFiberTensorPlus A m hm
      (costalkTateUnitMap m hX (Scheme.strictLocalizationToBase x)) hA a
      (Spec.map (Scheme.strictHenselizationEval x))

/-- The canonical Tate interchanges for all six local chain functors, built by pasting
pullback, exceptional counit mates, and the fibre or supported-section tensorator.
Source: Gabber XVII 1.4.1 (blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateReductionLocalPlus (A : Type (u + 1)) [CommRing A] [Finite A]
    (m : ℕ) (hm : 0 < m) {X : Scheme.{u}}
    (hX : IsUnit (m : Γ(X, ⊤))) (hA : (m : A) = 0) (a : ℤ)
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    (x : Spec (.of Ωx) ⟶ X) {y : Spec (.of Ωy) ⟶ X}
    (σ : Scheme.strictLocalization y ⟶ Scheme.strictLocalization x)
    {Z : Scheme.{u}} (i : Z ⟶ Scheme.strictLocalization x)
    [IsClosedImmersion i] [IsIntegral Z]
    (yZ : Spec (.of Ωy) ⟶ Z) (xZ : Spec (.of Ωx) ⟶ Z)
    (hyZ : yZ ≫ i = Spec.map (Scheme.strictHenselizationEval y) ≫ σ)
    (hxZ : xZ ≫ i = Spec.map (Scheme.strictHenselizationEval x))
    (yN : Spec (.of Ωy) ⟶ Z.normalization) (xN : Spec (.of Ωx) ⟶ Z.normalization)
    (hyN : yN ≫ Z.fromNormalization = yZ) (hxN : xN ≫ Z.fromNormalization = xZ)
    (W : Z.normalization.Opens)
    (hΓ : ∀ F : Sheaf Z.normalization.smallEtaleTopology (ModuleCat.{u + 1} A),
      IsIso (costalkGlobalGerm A xN F))
    (j : Fin 6) :
    costalkTateTensorPlus A m hm (Scheme.strictLocalization x)
        (costalkTateUnitMap m hX (Scheme.strictLocalizationToBase x)) hA a ⋙
      costalkReductionLocalTermsPlus A x σ i yZ xZ yN W j ≅
    costalkReductionLocalTermsPlus A x σ i yZ xZ yN W j ⋙
      costalkReductionFiberTensorPlus A m hm hX hA a x σ j :=
  let hT := costalkTateUnitMap m hX (Scheme.strictLocalizationToBase x)
  let hZ := costalkTateUnitMap m hT i
  let hN := costalkTateUnitMap m hZ Z.fromNormalization
  match j with
  | 0 => costalkTateCostalkPlus A m hm hT hA a
      (Spec.map (Scheme.strictHenselizationEval y) ≫ σ)
  | 1 => costalkTateAfterClosed A m hm i hT hZ hA a yZ _ hyZ _
      (costalkTateCostalkPlus A m hm hZ hA a yZ)
  | 2 =>
    letI := (Scheme.pointSmallEtale yN).sheafFiber_additive (A := ModuleCat.{u + 1} A)
    costalkTateAfterClosed A m hm i hT hZ hA a yZ _ hyZ _
      (costalkTateAfterPullback A m hm Z.fromNormalization hZ hN hA a yN yZ hyN _
        (costalkTateFiber A m hm hN hA a yN))
  | 3 => costalkTateCostalkPlus A m hm hT hA a
      (Spec.map (Scheme.strictHenselizationEval x))
  | 4 => costalkTateAfterClosed A m hm i hT hZ hA a xZ _ hxZ _
      (costalkTateCostalkPlus A m hm hZ hA a xZ)
  | 5 => costalkTateAfterClosed A m hm i hT hZ hA a xZ _ hxZ _
      (costalkTateAfterPullback A m hm Z.fromNormalization hZ hN hA a xN xZ hxN _
        (costalkTateSupportedPlus A m hm hN hA a W xN hΓ))

/-- The six canonical interchanges with the actual derived tensor at the geometric fibre.
Source: Gabber XVII 1.4.1; def-kun-derived-tensor
(blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateReductionLocal (A : Type (u + 1)) [CommRing A] [Finite A]
    (m : ℕ) (hm : 0 < m) {X : Scheme.{u}}
    (hX : IsUnit (m : Γ(X, ⊤))) (hA : (m : A) = 0) (a : ℤ)
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    (x : Spec (.of Ωx) ⟶ X) {y : Spec (.of Ωy) ⟶ X}
    (σ : Scheme.strictLocalization y ⟶ Scheme.strictLocalization x)
    {Z : Scheme.{u}} (i : Z ⟶ Scheme.strictLocalization x)
    [IsClosedImmersion i] [IsIntegral Z]
    (yZ : Spec (.of Ωy) ⟶ Z) (xZ : Spec (.of Ωx) ⟶ Z)
    (hyZ : yZ ≫ i = Spec.map (Scheme.strictHenselizationEval y) ≫ σ)
    (hxZ : xZ ≫ i = Spec.map (Scheme.strictHenselizationEval x))
    (yN : Spec (.of Ωy) ⟶ Z.normalization) (xN : Spec (.of Ωx) ⟶ Z.normalization)
    (hyN : yN ≫ Z.fromNormalization = yZ) (hxN : xN ≫ Z.fromNormalization = xZ)
    (W : Z.normalization.Opens)
    (hΓ : ∀ F : Sheaf Z.normalization.smallEtaleTopology (ModuleCat.{u + 1} A),
      IsIso (costalkGlobalGerm A xN F))
    (j : Fin 6) :
    costalkTateTensorPlus A m hm (Scheme.strictLocalization x)
        (costalkTateUnitMap m hX (Scheme.strictLocalizationToBase x)) hA a ⋙
      costalkReductionLocalTerms A x σ i yZ xZ yN W j ≅
    costalkReductionLocalTerms A x σ i yZ xZ yN W j ⋙
      tensorRight ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
        (costalkReductionFiberLine A m hA a x σ j)) :=
  match j with
  | 0 =>
    letI := costalkTateFiber_exact A m hm
      (costalkTateUnitMap m hX (Scheme.strictLocalizationToBase x)) hA a (Spec.map
        (Scheme.strictHenselizationEval y) ≫ σ)
    costalkTateInclude _ A _ _
      (costalkTateReductionLocalPlus A m hm hX hA a x σ i yZ xZ hyZ hxZ
        yN xN hyN hxN W hΓ 0)
  | 1 =>
    letI := costalkTateFiber_exact A m hm
      (costalkTateUnitMap m hX (Scheme.strictLocalizationToBase x)) hA a (Spec.map
        (Scheme.strictHenselizationEval y) ≫ σ)
    costalkTateInclude _ A _ _
      (costalkTateReductionLocalPlus A m hm hX hA a x σ i yZ xZ hyZ hxZ
        yN xN hyN hxN W hΓ 1)
  | 2 =>
    letI := costalkTateFiber_exact A m hm
      (costalkTateUnitMap m hX (Scheme.strictLocalizationToBase x)) hA a (Spec.map
        (Scheme.strictHenselizationEval y) ≫ σ)
    costalkTateInclude _ A _ _
      (costalkTateReductionLocalPlus A m hm hX hA a x σ i yZ xZ hyZ hxZ
        yN xN hyN hxN W hΓ 2)
  | 3 =>
    letI := costalkTateFiber_exact A m hm
      (costalkTateUnitMap m hX (Scheme.strictLocalizationToBase x)) hA a (Spec.map
        (Scheme.strictHenselizationEval x))
    costalkTateInclude _ A _ _
      (costalkTateReductionLocalPlus A m hm hX hA a x σ i yZ xZ hyZ hxZ
        yN xN hyN hxN W hΓ 3)
  | 4 =>
    letI := costalkTateFiber_exact A m hm
      (costalkTateUnitMap m hX (Scheme.strictLocalizationToBase x)) hA a (Spec.map
        (Scheme.strictHenselizationEval x))
    costalkTateInclude _ A _ _
      (costalkTateReductionLocalPlus A m hm hX hA a x σ i yZ xZ hyZ hxZ
        yN xN hyN hxN W hΓ 4)
  | 5 =>
    letI := costalkTateFiber_exact A m hm
      (costalkTateUnitMap m hX (Scheme.strictLocalizationToBase x)) hA a (Spec.map
        (Scheme.strictHenselizationEval x))
    costalkTateInclude _ A _ _
      (costalkTateReductionLocalPlus A m hm hX hA a x σ i yZ xZ hyZ hxZ
        yN xN hyN hxN W hΓ 5)

/-- Canonical costalk interchange after arbitrary restriction, with its original
geometric fibre on the initial scheme. Source: Gabber XVII 1.4.1
(blueprint: lem-per-prime-power-costalk-reduction). -/
def costalkTateRestrictionCostalk (A : Type (u + 1)) [CommRing A] [Finite A]
    (m : ℕ) (hm : 0 < m) {T S : Scheme.{u}} (f : S ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hS : IsUnit (m : Γ(S, ⊤)))
    (hA : (m : A) = 0) (a : ℤ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ S) (s : Spec (.of Ω) ⟶ T) (hs : t ≫ f = s) :=
  letI := costalkTateFiber_exact A m hm hT hA a s
  costalkTateInclude _ A _ _
    (costalkTateAfterPullback A m hm f hT hS hA a t s hs (geometricCostalkPlus A t)
      (costalkTateCostalkPlus A m hm hS hA a t))

/-- The specialization's generic geometric point has the original image on X.
Source: Gabber XVII 1.1.2 (blueprint: lem-per-prime-power-costalk-reduction).
Proof: compose the X-map equation for the specialization with the evaluation point;
associativity and the strict-local evaluation factorization give the original y. -/
theorem costalkSpecializationPointFactorization {X : Scheme.{u}} {Ωx Ωy : Type u}
    [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    (x : Spec (.of Ωx) ⟶ X) (y : Spec (.of Ωy) ⟶ X)
    (σ : Scheme.strictLocalization y ⟶ Scheme.strictLocalization x)
    (hσ : σ ≫ Scheme.strictLocalizationToBase x = Scheme.strictLocalizationToBase y) :
    (Spec.map (Scheme.strictHenselizationEval y) ≫ σ) ≫
      Scheme.strictLocalizationToBase x = y := by
  sorry

/-- The two natural costalk comparison chains through Z and its normalized trait.
Here the parameterized closed reduced immersion presents exactly the reduced closure,
and the equations specify the induced geometric points, not arbitrary replacements.
Source: Gabber XVII, Definition 1.4.1 comparison square and section 1.3, printed p. 262
(blueprint: lem-per-prime-power-costalk-reduction).
Proof: Step 1 derives supported restriction and its transitivity from the module support
adjunction. Step 2 computes geometric costalks on strict localizations. Step 3 supplies
the normalization geometry and unit residue degree, independently of coefficients.
Step 4 uses ind-etale strict-local invariance and closed-support base change after
localization at each of the two points, then transitivity of closed support. This gives
the comparisons from X to Z. Step 5 uses topological invariance to preserve the kernel
of restriction to the generic open of Z. At the closed point this kernel computes the
supported sections on the normalized trait; at the generic point support is the whole
local field, so the costalk is the geometric stalk. All these operations act on module
injective resolutions and are natural in K, giving the four displayed functor isomorphisms.
Step 6 gives compatibility with shifts and all signed roots-of-unity twists. -/
theorem primePower_costalk_reduction
    (ℓ n : ℕ) [Fact ℓ.Prime] (hn : 1 ≤ n)
    {X : Scheme.{u}} [IsNoetherian X]
    (hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hℓ : IsUnit (ℓ : Γ(X, ⊤)))
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    (x : Spec (.of Ωx) ⟶ X) (y : Spec (.of Ωy) ⟶ X)
    (σ : Scheme.strictLocalization y ⟶ Scheme.strictLocalization x)
    (hσ : σ ≫ Scheme.strictLocalizationToBase x = Scheme.strictLocalizationToBase y)
    {Z : Scheme.{u}} (i : Z ⟶ Scheme.strictLocalization x)
    [IsClosedImmersion i] [IsIntegral Z]
    (hZ : Set.range i = closure (Set.range (Spec.map (Scheme.strictHenselizationEval y) ≫ σ)))
    (hdim : topologicalKrullDim Z = 1)
    (yZ : Spec (.of Ωy) ⟶ Z) (xZ : Spec (.of Ωx) ⟶ Z)
    (hyZ : yZ ≫ i = Spec.map (Scheme.strictHenselizationEval y) ≫ σ)
    (hxZ : xZ ≫ i = Spec.map (Scheme.strictHenselizationEval x))
    (yN : Spec (.of Ωy) ⟶ Z.normalization) (xN : Spec (.of Ωx) ⟶ Z.normalization)
    (hyN : yN ≫ Z.fromNormalization = yZ) (hxN : xN ≫ Z.fromNormalization = xZ)
    (W : Z.normalization.Opens)
    (hW : (W : Set Z.normalization) = ({(Z.normalization.SpecToEquivOfField Ωx xN).1} :
      Set Z.normalization)ᶜ) :
    ∃ rᵧ : (geometricCostalkPlus (ULift.{u + 1} (ZMod (ℓ ^ n))) y ⋙
      _root_.DerivedCategory.Plus.ι) ≅
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))
        (Scheme.strictLocalizationToBase x)).mapDerivedCategoryPlus ⋙
          costalkReductionLocalTerms (ULift.{u + 1} (ZMod (ℓ ^ n))) x σ i yZ xZ yN W 0,
    ∃ rₓ : (geometricCostalkPlus (ULift.{u + 1} (ZMod (ℓ ^ n))) x ⋙
      _root_.DerivedCategory.Plus.ι) ≅
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))
        (Scheme.strictLocalizationToBase x)).mapDerivedCategoryPlus ⋙
          costalkReductionLocalTerms (ULift.{u + 1} (ZMod (ℓ ^ n))) x σ i yZ xZ yN W 3,
    ∃ d₁ : costalkReductionLocalTerms (ULift.{u + 1} (ZMod (ℓ ^ n))) x σ i yZ xZ yN W 0 ≅
      costalkReductionLocalTerms (ULift.{u + 1} (ZMod (ℓ ^ n))) x σ i yZ xZ yN W 1,
    ∃ d₂ : costalkReductionLocalTerms (ULift.{u + 1} (ZMod (ℓ ^ n))) x σ i yZ xZ yN W 1 ≅
      costalkReductionLocalTerms (ULift.{u + 1} (ZMod (ℓ ^ n))) x σ i yZ xZ yN W 2,
    ∃ d₃ : costalkReductionLocalTerms (ULift.{u + 1} (ZMod (ℓ ^ n))) x σ i yZ xZ yN W 3 ≅
      costalkReductionLocalTerms (ULift.{u + 1} (ZMod (ℓ ^ n))) x σ i yZ xZ yN W 4,
    ∃ d₄ : costalkReductionLocalTerms (ULift.{u + 1} (ZMod (ℓ ^ n))) x σ i yZ xZ yN W 4 ≅
      costalkReductionLocalTerms (ULift.{u + 1} (ZMod (ℓ ^ n))) x σ i yZ xZ yN W 5,
    ∃ hΓ : ∀ F : Sheaf Z.normalization.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod
      (ℓ ^ n)))),
      IsIso (costalkGlobalGerm (ULift.{u + 1} (ZMod (ℓ ^ n))) xN F),
    NatTrans.CommShift rᵧ.hom ℤ ∧ NatTrans.CommShift rₓ.hom ℤ ∧
    NatTrans.CommShift d₁.hom ℤ ∧ NatTrans.CommShift d₂.hom ℤ ∧
    NatTrans.CommShift d₃.hom ℤ ∧ NatTrans.CommShift d₄.hom ℤ ∧
    ∀ a : ℤ,
      CostalkTateCompatibility
        (costalkTateTensorPlus (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n) X
          (costalkTateUnit ℓ n hℓ (𝟙 X)) (CharP.cast_eq_zero _ (ℓ ^ n)) a)
        (costalkTateDerivedFiber (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (CharP.cast_eq_zero _ (ℓ ^
          n)) a y) _ _
        (costalkTateCostalk (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (costalkTateUnit ℓ n hℓ (𝟙 X)) (CharP.cast_eq_zero _ (ℓ ^ n)) a y)
        (costalkTateRestrictionCostalk (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (Scheme.strictLocalizationToBase x) (costalkTateUnit ℓ n hℓ (𝟙 X))
          (costalkTateUnitMap (ℓ ^ n) (costalkTateUnit ℓ n hℓ (𝟙 X))
            (Scheme.strictLocalizationToBase x))
          (CharP.cast_eq_zero _ (ℓ ^ n)) a (Spec.map (Scheme.strictHenselizationEval y) ≫ σ) y
          (costalkSpecializationPointFactorization x y σ hσ)) rᵧ ∧
      CostalkTateCompatibility
        (costalkTateTensorPlus (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n) X
          (costalkTateUnit ℓ n hℓ (𝟙 X)) (CharP.cast_eq_zero _ (ℓ ^ n)) a)
        (costalkTateDerivedFiber (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (CharP.cast_eq_zero _ (ℓ ^
          n)) a x) _ _
        (costalkTateCostalk (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (costalkTateUnit ℓ n hℓ (𝟙 X)) (CharP.cast_eq_zero _ (ℓ ^ n)) a x)
        (costalkTateRestrictionCostalk (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (Scheme.strictLocalizationToBase x) (costalkTateUnit ℓ n hℓ (𝟙 X))
          (costalkTateUnitMap (ℓ ^ n) (costalkTateUnit ℓ n hℓ (𝟙 X))
            (Scheme.strictLocalizationToBase x))
          (CharP.cast_eq_zero _ (ℓ ^ n)) a (Spec.map (Scheme.strictHenselizationEval x)) x
          (costalkStrictPointFactorization x)) rₓ ∧
      CostalkTateCompatibility
        (costalkTateTensorPlus (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (Scheme.strictLocalization x)
          (costalkTateUnitMap (ℓ ^ n) (costalkTateUnit ℓ n hℓ (𝟙 X))
            (Scheme.strictLocalizationToBase x))
          (CharP.cast_eq_zero _ (ℓ ^ n)) a)
        (tensorRight ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} (ULift.{u + 1}
          (ZMod (ℓ ^ n)))) 0).obj
          (costalkReductionFiberLine (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (CharP.cast_eq_zero _
            (ℓ ^ n)) a x σ 0))) _ _
        (costalkTateReductionLocal (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (costalkTateUnit ℓ n hℓ (𝟙 X)) (CharP.cast_eq_zero _ (ℓ ^ n)) a x σ i yZ xZ hyZ hxZ yN
            xN hyN hxN W hΓ 0)
        (costalkTateReductionLocal (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (costalkTateUnit ℓ n hℓ (𝟙 X)) (CharP.cast_eq_zero _ (ℓ ^ n)) a x σ i yZ xZ hyZ hxZ yN
            xN hyN hxN W hΓ 1) d₁ ∧
      CostalkTateCompatibility
        (costalkTateTensorPlus (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (Scheme.strictLocalization x)
          (costalkTateUnitMap (ℓ ^ n) (costalkTateUnit ℓ n hℓ (𝟙 X))
            (Scheme.strictLocalizationToBase x))
          (CharP.cast_eq_zero _ (ℓ ^ n)) a)
        (tensorRight ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} (ULift.{u + 1}
          (ZMod (ℓ ^ n)))) 0).obj
          (costalkReductionFiberLine (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (CharP.cast_eq_zero _
            (ℓ ^ n)) a x σ 1))) _ _
        (costalkTateReductionLocal (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (costalkTateUnit ℓ n hℓ (𝟙 X)) (CharP.cast_eq_zero _ (ℓ ^ n)) a x σ i yZ xZ hyZ hxZ yN
            xN hyN hxN W hΓ 1)
        (costalkTateReductionLocal (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (costalkTateUnit ℓ n hℓ (𝟙 X)) (CharP.cast_eq_zero _ (ℓ ^ n)) a x σ i yZ xZ hyZ hxZ yN
            xN hyN hxN W hΓ 2) d₂ ∧
      CostalkTateCompatibility
        (costalkTateTensorPlus (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (Scheme.strictLocalization x)
          (costalkTateUnitMap (ℓ ^ n) (costalkTateUnit ℓ n hℓ (𝟙 X))
            (Scheme.strictLocalizationToBase x))
          (CharP.cast_eq_zero _ (ℓ ^ n)) a)
        (tensorRight ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} (ULift.{u + 1}
          (ZMod (ℓ ^ n)))) 0).obj
          (costalkReductionFiberLine (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (CharP.cast_eq_zero _
            (ℓ ^ n)) a x σ 3))) _ _
        (costalkTateReductionLocal (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (costalkTateUnit ℓ n hℓ (𝟙 X)) (CharP.cast_eq_zero _ (ℓ ^ n)) a x σ i yZ xZ hyZ hxZ yN
            xN hyN hxN W hΓ 3)
        (costalkTateReductionLocal (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (costalkTateUnit ℓ n hℓ (𝟙 X)) (CharP.cast_eq_zero _ (ℓ ^ n)) a x σ i yZ xZ hyZ hxZ yN
            xN hyN hxN W hΓ 4) d₃ ∧
      CostalkTateCompatibility
        (costalkTateTensorPlus (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (Scheme.strictLocalization x)
          (costalkTateUnitMap (ℓ ^ n) (costalkTateUnit ℓ n hℓ (𝟙 X))
            (Scheme.strictLocalizationToBase x))
          (CharP.cast_eq_zero _ (ℓ ^ n)) a)
        (tensorRight ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} (ULift.{u + 1}
          (ZMod (ℓ ^ n)))) 0).obj
          (costalkReductionFiberLine (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (CharP.cast_eq_zero _
            (ℓ ^ n)) a x σ 4))) _ _
        (costalkTateReductionLocal (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (costalkTateUnit ℓ n hℓ (𝟙 X)) (CharP.cast_eq_zero _ (ℓ ^ n)) a x σ i yZ xZ hyZ hxZ yN
            xN hyN hxN W hΓ 4)
        (costalkTateReductionLocal (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n) (pow_pos (Fact.out :
          ℓ.Prime).pos n)
          (costalkTateUnit ℓ n hℓ (𝟙 X)) (CharP.cast_eq_zero _ (ℓ ^ n)) a x σ i yZ xZ hyZ hxZ yN
            xN hyN hxN W hΓ 5) d₄ := by
  sorry

end AlgebraicGeometry.Etale
