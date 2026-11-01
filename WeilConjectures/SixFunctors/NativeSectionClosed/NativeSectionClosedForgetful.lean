/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedForgetful
public import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalForgetful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # The native closed forgetful comparison in the section-module presentation

Source: current blueprint, cor-coef-verdier-weil-equivariance, internal Hom,
evaluation and transposition (blueprint: lem-sf-weil-native-closed-forgetful).
The existing native comparison is retained. This interface transports it along
the specified algebraic-closure isomorphism and the section-module equivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u a b c d
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open WeilConjectures WeilConjectures.AdicQbarRealization
open WeilConjectures.NativeExceptionalForgetful
open AlgebraicGeometry.ProEtaleWeilSheaf

namespace WeilConjectures.NativeSectionClosed

/-- Evaluation transpose with independent source and target category universes.
Source: Stacks 08J9, transported native evaluation
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def sectionHomComparison {C : Type a} [Category.{b} C]
    {E : Type c} [Category.{d} E] {HC : Cᵒᵖ × C ⥤ C} {HE : Eᵒᵖ × E ⥤ E}
    (SC : CoefficientClosedStructure HC) (SE : CoefficientClosedStructure HE)
    (V : C ⥤ E) (t : SC.tensor ⋙ V ≅ V.prod V ⋙ SE.tensor) (K L : C) :=
  SE.transpose _ (V.obj K) (V.obj L)
    ((t.app (HC.obj (op K, L), K)).inv ≫ V.map (SC.evaluation K L))

/-- Signed symmetry compatibility with independent category sizes.
Source: Stacks 0FPT, transported native symmetry
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def SectionSymmetryCompatibility {C : Type a} [Category.{b} C]
    {E : Type c} [Category.{d} E] {HC : Cᵒᵖ × C ⥤ C} {HE : Eᵒᵖ × E ⥤ E}
    (SC : CoefficientClosedStructure HC) (SE : CoefficientClosedStructure HE)
    (sC : @SymmetricCategory C _ SC.monoidal)
    (sE : @SymmetricCategory E _ SE.monoidal)
    (V : C ⥤ E) (t : SC.tensor ⋙ V ≅ V.prod V ⋙ SE.tensor) : Prop :=
  ∀ K L, V.map (sC.braiding K L).hom ≫ (t.app (L, K)).hom =
    (t.app (K, L)).hom ≫ (sE.braiding (V.obj K) (V.obj L)).hom

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
  (R : Family l D) (X : Space D)

/-- Ordinary forgetting on the ambient native derived category, with the actual
closure and section-module transports. Its restriction is NativeExceptionalForgetful.U.
Source: current blueprint, cor-coef-verdier-weil-equivariance, forgetful functor
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def ambientForget :=
  nativeForget D.k₀ l X.base.left ⋙
    (ProEtale.adicLowerStar l (closureMap D X)).rightDerivedFunctor ⋙
      sectionDerived l (geometric D X).base.left (R.data (geometric D X)).realization

/-- The ordinary closed structure with the realization's own invertibility witnesses.
Source: BS 6.8.15, evaluation comparison
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def ordinaryClosed :=
  letI := (R.data (geometric D X)).units
  (R.data (geometric D X)).tensor.closed

/-- The signed ordinary symmetry of the same realization.
Source: BS 6.8.15, symmetric tensor comparison
(blueprint: lem-sf-weil-native-closed-forgetful). -/
@[instance_reducible] def ordinarySymmetry :
    @SymmetricCategory _ _ (ordinaryClosed D l R X).monoidal := by
  letI := (R.data (geometric D X)).units
  exact (R.data (geometric D X)).tensor.symmetry

/-- The actual closure direct image followed by the section presentation.
Source: the closure and section transports in the evaluation paragraph
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def ordinaryTransport :=
  (ProEtale.adicLowerStar l (closureMap D X)).rightDerivedFunctor ⋙
    sectionDerived l (geometric D X).base.left (R.data (geometric D X)).realization

/-- The same transport on complexes, before localization.
Source: BS 6.8.8 and Stacks 05RU
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def complexTransport :=
  letI := (R.data (geometric D X)).realization.commutative
  letI : (sectionFunctor l (geometric D X).base.left
      (R.data (geometric D X)).realization).Additive :=
    (R.data (geometric D X)).realization.sectionsAdditive
  (ProEtale.adicLowerStar l (closureMap D X)).mapHomologicalComplex (.up ℤ) ⋙
    (sectionFunctor l (geometric D X).base.left
      (R.data (geometric D X)).realization).mapHomologicalComplex (.up ℤ)

/-- The inverse localization factor is the actual right-derived unit, followed
by the fixed section-module localization factor. Thus it cannot be rescaled.
Source: Stacks 05RU, exact equivalence transport
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def transportLocalization (P : CochainComplex
    (ProEtale.AdicSheaf l X.base.hom.geometricFiber) ℤ) :
    DerivedCategory.Q.obj ((complexTransport D l R X).obj P) ⟶
      (ordinaryTransport D l R X).obj (DerivedCategory.Q.obj P) :=
  letI := (R.data (geometric D X)).realization.commutative
  letI : (sectionFunctor l (geometric D X).base.left
      (R.data (geometric D X)).realization).Additive :=
    (R.data (geometric D X)).realization.sectionsAdditive
  letI : PreservesFiniteLimits (sectionFunctor l (geometric D X).base.left
      (R.data (geometric D X)).realization) :=
    (R.data (geometric D X)).realization.sectionsLimits
  letI : PreservesFiniteColimits (sectionFunctor l (geometric D X).base.left
      (R.data (geometric D X)).realization) :=
    (R.data (geometric D X)).realization.sectionsColimits
  (sectionFunctor l (geometric D X).base.left
      (R.data (geometric D X)).realization).mapDerivedCategoryFactors.inv.app
        (((ProEtale.adicLowerStar l (closureMap D X)).mapHomologicalComplex (.up ℤ)).obj P) ≫
    (sectionDerived l (geometric D X).base.left
      (R.data (geometric D X)).realization).map
        ((ProEtale.adicLowerStar l (closureMap D X)).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- The homogeneous pure tensor in the ordinary source total, read after closure
transport. The order is Q then P because ordinaryTensorBifunctor curries P first.
Source: Stacks 03EK and 06YS, identity on tensor summands
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def transportedGenerator
    (P Q : CochainComplex (ProEtale.AdicSheaf l X.base.hom.geometricFiber) ℤ)
    (p q n : ℤ) (hpq : p + q = n) (V : (geometric D X).base.left.ProEtᵒᵖ)
    (x : (((complexTransport D l R X).obj Q).X q).val.obj V)
    (y : (((complexTransport D l R X).obj P).X p).val.obj V) :=
  let V' := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (closureMap D X)).op.obj V
  (((HomologicalComplex.ιMapBifunctor P Q
      (ordinaryTensorBifunctor l X.base.hom.geometricFiber) (.up ℤ) p q n hpq).hom).hom.app V')
    (((Mod.tensorπ (Q.X q) (P.X p)).hom.app V')
      (((Functor.LaxMonoidal.μ
        (sheafToPresheaf (ProEt.topology X.base.hom.geometricFiber) (WeilCoefficients l))
        (Q.X q).X (P.X p).X).app V') (x ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] y)))

/-- A tensor transport is fixed by its actual homogeneous pure-section formula
and the localization square on all ordinary K-flat representatives. The inverse
factor is the canonical right-derived unit, so the equations fix every map.
Source: Stacks 03EK, 06YS, 07A4, transported native comparison
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def TransportNormalized (N : NativeClosedComparison D.k₀ l X.base.left)
    (v : N.ordinaryClosed.tensor ⋙ ordinaryTransport D l R X ≅
      (ordinaryTransport D l R X).prod (ordinaryTransport D l R X) ⋙
        (ordinaryClosed D l R X).tensor) : Prop :=
  letI := (R.data (geometric D X)).units
  let S := (R.data (geometric D X)).tensor
  let model := N.ordinaryTensorModels.choose
  ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l X.base.hom.geometricFiber) ℤ)
      (hP : NativeOrdinaryKFlat l X.base.hom.geometricFiber P)
      (_hQ : NativeOrdinaryKFlat l X.base.hom.geometricFiber Q),
    ∃ hFP : CochainComplex.IsKFlatIndependentCoefficients
        (J := ProEt.topology (geometric D X).base.left)
        (R := ring l (geometric D X).base.left (R.data (geometric D X)).realization)
        ((complexTransport D l R X).obj P),
    ∃ hFQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := ProEt.topology (geometric D X).base.left)
        (R := ring l (geometric D X).base.left (R.data (geometric D X)).realization)
        ((complexTransport D l R X).obj Q),
    ∃ factor : ∀ T : CochainComplex
        (ProEtale.AdicSheaf l X.base.hom.geometricFiber) ℤ,
      (ordinaryTransport D l R X).obj (DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((complexTransport D l R X).obj T),
    (∀ T, (factor T).inv = transportLocalization D l R X T) ∧
    ∃ c : (complexTransport D l R X).obj
          (ordinaryTensorTotal l X.base.hom.geometricFiber P Q) ≅
        (coefficientTotalTensor.{u + 1, u + 1, u}
          (ProEt.topology (geometric D X).base.left)
          (ring l (geometric D X).base.left (R.data (geometric D X)).realization)).obj
          ((complexTransport D l R X).obj Q, (complexTransport D l R X).obj P),
      (∀ (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n)
          (V : (geometric D X).base.left.ProEtᵒᵖ)
          (x : (((complexTransport D l R X).obj Q).X q).val.obj V)
          (y : (((complexTransport D l R X).obj P).X p).val.obj V),
        (c.hom.f n).val.app V (transportedGenerator D l R X P Q p q n hpq V x y) =
          coefficientTensorGenerator.{u + 1, u + 1, u}
            (ProEt.topology (geometric D X).base.left)
            (ring l (geometric D X).base.left (R.data (geometric D X)).realization)
            ((complexTransport D l R X).obj Q) ((complexTransport D l R X).obj P)
            q p n hqp V x y) ∧
      (ordinaryTransport D l R X).map (model P Q hP).inv ≫
          v.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) =
        (factor (ordinaryTensorTotal l X.base.hom.geometricFiber P Q)).hom ≫
          DerivedCategory.Q.map c.hom ≫
          (S.models.iso _ _ _ _ _ hFQ hFP).hom ≫
          (ordinaryClosed D l R X).tensor.map
            (Prod.mkHom (transportLocalization D l R X Q)
              (transportLocalization D l R X P))

/-- Associator and both unit equations for independent source and target sizes.
Source: Stacks 07A4, monoidal exact-equivalence transport
(blueprint: lem-sf-weil-native-closed-forgetful). -/
def SectionTensorCoherence {C : Type a} [Category.{b} C]
    {E : Type c} [Category.{d} E] {HC : Cᵒᵖ × C ⥤ C} {HE : Eᵒᵖ × E ⥤ E}
    (SC : CoefficientClosedStructure HC) (SE : CoefficientClosedStructure HE)
    (V : C ⥤ E) (t : SC.tensor ⋙ V ≅ V.prod V ⋙ SE.tensor)
    (e : V.obj SC.monoidal.tensorUnit ≅ SE.monoidal.tensorUnit) : Prop :=
  (∀ K L M, V.map (SC.monoidal.associator K L M).hom ≫
      (t.app (K, SC.tensor.obj (L, M))).hom ≫
        SE.tensor.map (Prod.mkHom (𝟙 _) (t.app (L, M)).hom) =
    (t.app (SC.tensor.obj (K, L), M)).hom ≫
      SE.tensor.map (Prod.mkHom (t.app (K, L)).hom (𝟙 _)) ≫
        (SE.monoidal.associator (V.obj K) (V.obj L) (V.obj M)).hom) ∧
  (∀ K, V.map (SC.monoidal.leftUnitor K).hom =
    (t.app (SC.monoidal.tensorUnit, K)).hom ≫
      SE.tensor.map (Prod.mkHom e.hom (𝟙 _)) ≫
        (SE.monoidal.leftUnitor (V.obj K)).hom) ∧
  (∀ K, V.map (SC.monoidal.rightUnitor K).hom =
    (t.app (K, SC.monoidal.tensorUnit)).hom ≫
      SE.tensor.map (Prod.mkHom (𝟙 _) e.hom) ≫
        (SE.monoidal.rightUnitor (V.obj K)).hom)

/-- The existing native closed structure and its section-module tensor comparison.
The Hom comparison is, by definition, the transpose of mapped native evaluation.
Source: current blueprint, cor-coef-verdier-weil-equivariance, evaluation paragraph
(blueprint: lem-sf-weil-native-closed-forgetful). -/
structure Comparison where
  native : NativeClosedComparison D.k₀ l X.base.left
  compatible : native.Compatible
  tensor : native.weilClosed.tensor ⋙ ambientForget D l R X ≅
    (ambientForget D l R X).prod (ambientForget D l R X) ⋙
      (ordinaryClosed D l R X).tensor
  transportTensor : native.ordinaryClosed.tensor ⋙ ordinaryTransport D l R X ≅
    (ordinaryTransport D l R X).prod (ordinaryTransport D l R X) ⋙
      (ordinaryClosed D l R X).tensor
  transport_normalized : TransportNormalized D l R X native transportTensor
  tensor_transport : ∀ K L, tensor.hom.app (K, L) =
    (ordinaryTransport D l R X).map (native.tensorComparison.hom.app (K, L)) ≫
      transportTensor.hom.app
        ((nativeForget D.k₀ l X.base.left).obj K, (nativeForget D.k₀ l X.base.left).obj L)
  unit : (ambientForget D l R X).obj native.weilClosed.monoidal.tensorUnit ≅
    (ordinaryClosed D l R X).monoidal.tensorUnit
  coherent : SectionTensorCoherence native.weilClosed (ordinaryClosed D l R X)
    (ambientForget D l R X) tensor unit
  symmetric : SectionSymmetryCompatibility native.weilClosed
    (ordinaryClosed D l R X) native.weilSymmetry
    (ordinarySymmetry D l R X) (ambientForget D l R X) tensor
  hom_isIso : ∀ K L, IsIso (sectionHomComparison native.weilClosed
    (ordinaryClosed D l R X) (ambientForget D l R X) tensor K L)

/-- The evaluation-normalized native closed comparison remains valid after changing
from the chosen closure to D.k and from internal modules to section modules.
Source: current blueprint, cor-coef-verdier-weil-equivariance, first-map paragraph
(blueprint: lem-sf-weil-native-closed-forgetful).

Proof: apply native_closed_forgetful to X. The closure map is the base change of
an algebraic-closure equivalence; its direct image is an exact equivalence.
The section-module functor is the exact module equivalence of the realization.
Both send the coefficient module to itself and tensor pure sections pointwise,
so transport the K-flat total-tensor comparison along these equivalences.
The pure-section formula fixes every homogeneous summand. The right-derived
unit and section localization factor give the specified representative square,
and the transported native.tensorComparison gives tensor_transport. The same
calculation on three factors and the coefficient unit proves all coherence laws.
Their signed swaps are the same (-1)^(pq) swaps; hence symmetry is preserved.
On K-injective targets they preserve the product-total internal Hom. The
representative evaluation is application of a section to a section, so this
comparison is precisely nativeHomComparison, rather than an arbitrary Hom map.
Localization gives its invertibility and naturality in both variables. The
original native closed structure, representative models and compatibility
laws are retained by the field native and compatible. No assertion of
invertibility of nativeBidual is involved. -/
theorem native_section_closed_forgetful : Nonempty (NativeSectionClosed.Comparison D l R X) := by
  sorry

end WeilConjectures.NativeSectionClosed
