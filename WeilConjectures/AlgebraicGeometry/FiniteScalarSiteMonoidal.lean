/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingedComparisonInjectiveAcyclicity
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import all WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import all WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.RestrictionRingedToposModuleDirectImageSupplement

/-! # The monoidal finite scalar/site comparison

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md, final paragraph; Stacks 07A4 and 0D6D.
(blueprint: lem-coef-finite-hom-site-equation-descent).

Only finite constant coefficients occur. The site models are the existing AsSmall
transports of the original sites. The witnesses below retain the geometric morphisms,
structural ring maps, K-flat normalization and all-object monoidal diagrams. Both
composite ringed morphisms are presented by their common inverse image and quotient
ring map. Thus their geometric two-isomorphism is the identity on this common
presentation, and h is exactly the inverse first compositor followed by the second.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.RingedDerivedComparisons

namespace WeilConjectures.FiniteScalarSite

/-- The quotient at any pair of ordered levels, induced by the identity on integers.
Source: blueprint finite coefficient convention
(blueprint: lem-coef-finite-hom-site-equation-descent). -/
def quotient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {n m : ℕ} (h : m ≤ n) :
    ULift.{u + 1} (Padic.coefficientExtensionRing l E n) →+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E m) :=
  (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E))) h)).ulift

/-- The canonical constant-section ring map along a continuous site functor.
It is constructed by the sheafification adjunction, sending a coefficient to its
constant section after the given coefficient homomorphism.
Source: Stacks 00WX and blueprint final site-comparison sentence
(blueprint: lem-coef-finite-hom-site-equation-descent). -/
def constantDirectMap {C D : Type v} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : D ⥤ C) [F.IsContinuous K J]
    {A B : Type v} [CommRing A] [CommRing B] (φ : A →+* B) :
    (constantSheaf K CommRingCat.{v}).obj (.of A) ⟶
      (F.sheafPushforwardContinuous CommRingCat.{v} K J).obj
        ((constantSheaf J CommRingCat.{v}).obj (.of B)) :=
  ((sheafificationAdjunction K CommRingCat.{v}).homEquiv _ _).symm
    ((Functor.const Dᵒᵖ).map (CommRingCat.ofHom φ) ≫
      Functor.whiskerLeft F.op
        (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))))

/-- A tensor presentation of this precise ringed site, with the existing normalized
signed tensor model. Equalities of presentations retain the site and ring, rather
than replacing either by unspecified categories or coefficients.
Source: Stacks 0FPT, 06YN and blueprint final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent). -/
structure Corner {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Sheaf J CommRingCat.{v}) where
  site : Site.{v, v + 1}
  objects_eq : site.C = C
  category_eq : HEq site.category (inferInstance : SmallCategory C)
  topology_eq : HEq site.J J
  coefficient_eq : HEq site.A A

/-- A normalized geometric ringed morphism in the specified presentations.
The structural map is specified as the transpose of the constant-section map;
the RingedToposMorphism interface itself fixes the induced module direct image.
Source: Stacks 01D3, 03D6 and blueprint final site-comparison sentence
(blueprint: lem-coef-finite-hom-site-equation-descent). -/
structure Geometric {C D : Type v} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{v}} {B : Sheaf K CommRingCat.{v}}
    (x : Corner J A) (y : Corner K B)
    (L : Sheaf K (Type v) ⥤ Sheaf J (Type v))
    (R : Sheaf J (Type v) ⥤ Sheaf K (Type v)) (adj : L ⊣ R)
    (ρ : (sheafCompose K (forget CommRingCat.{v})).obj B ⟶
      R.obj ((sheafCompose J (forget CommRingCat.{v})).obj A)) where
  morphism : Morphism x.site y.site
  inverse_eq : HEq morphism.inverse L
  direct_eq : HEq morphism.direct R
  adjunction_eq : HEq morphism.adj adj
  ringMap_eq : HEq morphism.ringMap ((adj.homEquiv _ _).symm ρ)

/-- Tensor and symmetry diagrams for the common-composite presentation. The two
Composition records include their ordinary insertion and K-flat representative
formulas, tensor diagrams and unit diagrams. Their common source lift makes the
middle two-isomorphism the identity, so no arbitrary natural isomorphism is supplied.
Source: Stacks 07A4, 0D6D and blueprint final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent). -/
structure Square {etA etB proA proB : Site.{v, v + 1}}
    (sEt : Morphism etB etA) (sPro : Morphism proB proA)
    (nuA : Morphism proA etA) (nuB : Morphism proB etB)
    (k : Morphism proB etA)
    (θEt : k.inverse ≅ sEt.inverse ⋙ nuB.inverse)
    (θPro : k.inverse ≅ nuA.inverse ⋙ sPro.inverse) where
  scalarEt : Lift sEt
  scalarPro : Lift sPro
  siteA : Lift nuA
  siteB : Lift nuB
  common : Lift k
  compEt : Composition siteB scalarEt common θEt
  compPro : Composition scalarPro siteA common θPro
  tensor : ∀ T S : etA.D,
    siteB.edge.left.map (scalarEt.tensor T S).hom ≫
        (siteB.tensor (scalarEt.edge.left.obj T) (scalarEt.edge.left.obj S)).hom ≫
        proB.closed.tensor.map
          (Prod.mkHom ((compEt.pullback.symm ≪≫ compPro.pullback).hom.app T)
            ((compEt.pullback.symm ≪≫ compPro.pullback).hom.app S)) =
      (compEt.pullback.symm ≪≫ compPro.pullback).hom.app
          (etA.closed.tensor.obj (T, S)) ≫
        scalarPro.edge.left.map (siteA.tensor T S).hom ≫
        (scalarPro.tensor (siteA.edge.left.obj T) (siteA.edge.left.obj S)).hom
  symmetry : ∀ T S : etA.D,
    siteB.edge.left.map
          (scalarEt.edge.left.map (etA.symmetry.toBraidedCategory.braiding T S).hom) ≫
        siteB.edge.left.map (scalarEt.tensor S T).hom ≫
        (siteB.tensor (scalarEt.edge.left.obj S) (scalarEt.edge.left.obj T)).hom ≫
        proB.closed.tensor.map
          (Prod.mkHom ((compEt.pullback.symm ≪≫ compPro.pullback).hom.app S)
            ((compEt.pullback.symm ≪≫ compPro.pullback).hom.app T)) =
      (compEt.pullback.symm ≪≫ compPro.pullback).hom.app
          (etA.closed.tensor.obj (T, S)) ≫
        scalarPro.edge.left.map (siteA.tensor T S).hom ≫
        (scalarPro.tensor (siteA.edge.left.obj T) (siteA.edge.left.obj S)).hom ≫
        (proB.symmetry.toBraidedCategory.braiding
          (scalarPro.edge.left.obj (siteA.edge.left.obj T))
          (scalarPro.edge.left.obj (siteA.edge.left.obj S))).hom
  unit : (compEt.pullback.symm ≪≫ compPro.pullback).hom.app
        etA.closed.monoidal.tensorUnit ≫
      scalarPro.edge.left.map siteA.unit.hom ≫ scalarPro.unit.hom =
    siteB.edge.left.map scalarEt.unit.hom ≫ siteB.unit.hom

section ConstantMapNaturality
variable {C D : Type v} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (F : D ⥤ C) [F.IsContinuous K J]
  {A B Cc : Type v} [CommRing A] [CommRing B] [CommRing Cc]
/-- Naturality of constant sections in the source coefficient ring.
Source: naturality of the sheafification adjunction
(blueprint: lem-coef-finite-hom-site-equation-descent). -/
private theorem constantDirectMap_pre (φ : A →+* B) (ψ : B →+* Cc) :
    (constantSheaf K CommRingCat.{v}).map (CommRingCat.ofHom φ) ≫
        constantDirectMap J K F ψ = constantDirectMap J K F (ψ.comp φ) := by
  unfold constantDirectMap
  change (presheafToSheaf K CommRingCat.{v}).map
    ((Functor.const Dᵒᵖ).map (CommRingCat.ofHom φ)) ≫ _ = _
  rw [← Adjunction.homEquiv_naturality_left_symm]
  congr 1

/-- Naturality of constant sections in the target coefficient ring.
Source: naturality of sheafification and its adjunction
(blueprint: lem-coef-finite-hom-site-equation-descent). -/
private theorem constantDirectMap_post (φ : A →+* B) (ψ : B →+* Cc) :
    constantDirectMap J K F φ ≫
        (F.sheafPushforwardContinuous CommRingCat.{v} K J).map
          ((constantSheaf J CommRingCat.{v}).map (CommRingCat.ofHom ψ)) =
      constantDirectMap J K F (ψ.comp φ) := by
  unfold constantDirectMap
  rw [← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  change ((Functor.const Dᵒᵖ).map (CommRingCat.ofHom φ) ≫
    Functor.whiskerLeft F.op
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))) ≫
    Functor.whiskerLeft F.op
      (sheafifyMap J ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom ψ))) = _
  rw [Category.assoc, ← Functor.whiskerLeft_comp, ← toSheafify_naturality]
  rw [Functor.whiskerLeft_comp, ← Category.assoc]
  congr 1
end ConstantMapNaturality

/-- Package the existing signed tensor presentation of this exact ringed site.
Source: ringedDerived_closed_symmetric_monoidal
(blueprint: lem-coef-finite-hom-site-equation-descent). -/
private def cornerOf {C : Type v} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Sheaf J CommRingCat.{v})
    [HasDerivedCategory.{v + 1} (RingedTensorModules.{v, v, v} J A)]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{v, v, v, v + 1} J A))
    (T : CoefficientTensorModels.{v, v, v, v + 1} J A S)
    (β : @SymmetricCategory _ _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{v, v, v, v + 1} J A S T β) : Corner J A where
  site := {
    C := C
    J := J
    A := A
    closed := S
    model := T
    symmetry := β
    coherence := hc }
  objects_eq := rfl
  category_eq := HEq.rfl
  topology_eq := HEq.rfl
  coefficient_eq := HEq.rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The complete finite scalar/site assertion, using only the actual constant
coefficient rings, existing site models, geometric comparison and normalized lifts.
The level arguments are the exponents themselves, including n=m=1.
Source: blueprint thm-coef-finite-hom.proof.md, final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent). -/
structure Comparison (n m : ℕ) (h : m ≤ n) where
  etA : Corner (smallModelComparisonEtaleTopology.{u, u} X)
    ((constantSheaf (smallModelComparisonEtaleTopology.{u, u} X)
      CommRingCat.{u + 1}).obj (.of (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E n))))
  etB : Corner (smallModelComparisonEtaleTopology.{u, u} X)
    ((constantSheaf (smallModelComparisonEtaleTopology.{u, u} X)
      CommRingCat.{u + 1}).obj (.of (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E m))))
  proA : Corner (coefficientProEtaleModelTopology.{u, u} X)
    ((constantSheaf (coefficientProEtaleModelTopology.{u, u} X)
      CommRingCat.{u + 1}).obj (.of (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E n))))
  proB : Corner (coefficientProEtaleModelTopology.{u, u} X)
    ((constantSheaf (coefficientProEtaleModelTopology.{u, u} X)
      CommRingCat.{u + 1}).obj (.of (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E m))))
  sEt : Geometric etB etA (𝟭 _) (𝟭 _) Adjunction.id
    ((sheafCompose _ (forget CommRingCat.{u + 1})).map
      ((constantSheaf _ CommRingCat.{u + 1}).map (CommRingCat.ofHom (quotient l E h))))
  sPro : Geometric proB proA (𝟭 _) (𝟭 _) Adjunction.id
    ((sheafCompose _ (forget CommRingCat.{u + 1})).map
      ((constantSheaf _ CommRingCat.{u + 1}).map (CommRingCat.ofHom (quotient l E h))))
  nuA : Geometric proA etA (smallModelComparisonPullback.{u, u} X)
    (smallModelComparisonPushforward.{u, u} X) (smallModelProEtaleComparison.{u, u} X)
    ((sheafCompose _ (forget CommRingCat.{u + 1})).map
      (constantDirectMap _ _ (smallModelComparisonInclusion.{u, u} X)
        (RingHom.id (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))))
  nuB : Geometric proB etB (smallModelComparisonPullback.{u, u} X)
    (smallModelComparisonPushforward.{u, u} X) (smallModelProEtaleComparison.{u, u} X)
    ((sheafCompose _ (forget CommRingCat.{u + 1})).map
      (constantDirectMap _ _ (smallModelComparisonInclusion.{u, u} X)
        (RingHom.id (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)))))
  common : Geometric proB etA (smallModelComparisonPullback.{u, u} X)
    (smallModelComparisonPushforward.{u, u} X) (smallModelProEtaleComparison.{u, u} X)
    ((sheafCompose _ (forget CommRingCat.{u + 1})).map
      (constantDirectMap _ _ (smallModelComparisonInclusion.{u, u} X) (quotient l E h)))
  thetaEt : common.morphism.inverse ≅ sEt.morphism.inverse ⋙ nuB.morphism.inverse
  thetaEt_eq : HEq thetaEt (Functor.leftUnitor (smallModelComparisonPullback.{u, u} X)).symm
  thetaPro : common.morphism.inverse ≅ nuA.morphism.inverse ⋙ sPro.morphism.inverse
  thetaPro_eq : HEq thetaPro (Functor.rightUnitor (smallModelComparisonPullback.{u, u} X)).symm
  square : Square sEt.morphism sPro.morphism nuA.morphism nuB.morphism
    common.morphism thetaEt thetaPro

section
attribute [local implicit_reducible] Site.corner CoefficientClosedStructure.tensor

set_option maxHeartbeats 3000000 in
-- Four derived tensor presentations and the pasted diagrams require extra elaboration.
/-- The finite quotient scalar/site comparison is strongly symmetric monoidal on
ordinary unbounded derived categories. The witness specifies all four functors by
geometric adjunctions and quotient ring maps, all tensorators by K-flat models, the
compositors by ordinary pullback composition, and h by c_Et⁻¹ followed by c_Pro.
Its tensor, signed symmetry and coefficient-unit equations are Square.tensor,
Square.symmetry and Square.unit; no Hom square or other coefficient case is asserted.

Source: current blueprint thm-coef-finite-hom.proof.md, final paragraph; Stacks 07A4,
0D6D (blueprint: lem-coef-finite-hom-site-equation-descent).

Proof: form the constant coefficient ring sheaves on the two existing small models.
The identity geometric morphisms and the quotient map give sEt and sPro. Transport
nu_X along the existing site equivalences, with its constant-section coefficient
map, to give nuA and nuB. The two composites have this same inverse image and the
same structural quotient map, so present them by the single common ringed morphism.
Apply lem-sfb-ringed-derived-monoidal-comparisons to obtain the four normalized
symmetric strong monoidal lifts and their normalized composition comparisons. The
identity two-isomorphism of the common presentation induces the identity derived
comparison. Hence h is c_Et⁻¹ followed by c_Pro. Paste the two compositor tensor
squares and their unit squares to give Square.tensor and Square.unit. Naturality
of h at the signed symmetry, together with the two symmetric monoidal functor
laws, gives Square.symmetry, with the siteB(scalarEt.tensor S T) factor retained.
All formulas are on arbitrary unbounded inputs and require no flatness of the
quotient map. The positive identity quotient and the empty scheme are included. -/
theorem finiteHomSiteEquationDescent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (n m : ℕ) (_hm : 1 ≤ m) (h : m ≤ n) :
    Nonempty (Comparison l E X n m h) := by
  classical
  let J := smallModelComparisonEtaleTopology.{u, u} X
  let K := coefficientProEtaleModelTopology.{u, u} X
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E n)
  let B := ULift.{u + 1} (Padic.coefficientExtensionRing l E m)
  let eA := (constantSheaf J CommRingCat.{u + 1}).obj (.of A)
  let eB := (constantSheaf J CommRingCat.{u + 1}).obj (.of B)
  let pA := (constantSheaf K CommRingCat.{u + 1}).obj (.of A)
  let pB := (constantSheaf K CommRingCat.{u + 1}).obj (.of B)
  let := HasDerivedCategory.standard (RingedTensorModules.{u + 1, u + 1, u + 1} J eA)
  let := HasDerivedCategory.standard (RingedTensorModules.{u + 1, u + 1, u + 1} J eB)
  let := HasDerivedCategory.standard (RingedTensorModules.{u + 1, u + 1, u + 1} K pA)
  let := HasDerivedCategory.standard (RingedTensorModules.{u + 1, u + 1, u + 1} K pB)
  obtain ⟨SeA, TeA, βeA, ⟨heA⟩⟩ :=
    ringedDerived_closed_symmetric_monoidal.{u + 1, u + 1, u + 1, u + 2} J eA
  obtain ⟨SeB, TeB, βeB, ⟨heB⟩⟩ :=
    ringedDerived_closed_symmetric_monoidal.{u + 1, u + 1, u + 1, u + 2} J eB
  obtain ⟨SpA, TpA, βpA, ⟨hpA⟩⟩ :=
    ringedDerived_closed_symmetric_monoidal.{u + 1, u + 1, u + 1, u + 2} K pA
  obtain ⟨SpB, TpB, βpB, ⟨hpB⟩⟩ :=
    ringedDerived_closed_symmetric_monoidal.{u + 1, u + 1, u + 1, u + 2} K pB
  let etA := cornerOf.{u + 1} J eA SeA TeA βeA heA
  let etB := cornerOf.{u + 1} J eB SeB TeB βeB heB
  let proA := cornerOf.{u + 1} K pA SpA TpA βpA hpA
  let proB := cornerOf.{u + 1} K pB SpB TpB βpB hpB
  let φ := quotient l E h
  let ce := (constantSheaf J CommRingCat.{u + 1}).map (CommRingCat.ofHom φ)
  let cp := (constantSheaf K CommRingCat.{u + 1}).map (CommRingCat.ofHom φ)
  let F := smallModelComparisonInclusion.{u, u} X
  let L := smallModelComparisonPullback.{u, u} X
  let R := smallModelComparisonPushforward.{u, u} X
  let adj := smallModelProEtaleComparison.{u, u} X
  let fe := sheafCompose J (forget CommRingCat.{u + 1})
  let fp := sheafCompose K (forget CommRingCat.{u + 1})
  let da := constantDirectMap K J F (RingHom.id A)
  let db := constantDirectMap K J F (RingHom.id B)
  let dq := constantDirectMap K J F φ
  let se := siteRestrictionRingedTopos.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ce)
  let sp := siteRestrictionRingedTopos.{u + 1}
    ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map cp)
  let na := siteContinuousRingedTopos.{u + 1} F L adj pA eA da
  let nb := siteContinuousRingedTopos.{u + 1} F L adj pB eB db
  let kk := siteContinuousRingedTopos.{u + 1} F L adj pB eA dq
  let sEt : Geometric etB etA (𝟭 _) (𝟭 _) Adjunction.id
      ((sheafCompose J (forget CommRingCat.{u + 1})).map ce) :=
    ⟨se, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  let sPro : Geometric proB proA (𝟭 _) (𝟭 _) Adjunction.id
      ((sheafCompose K (forget CommRingCat.{u + 1})).map cp) :=
    ⟨sp, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  let nuA : Geometric proA etA L R adj
      ((sheafCompose J (forget CommRingCat.{u + 1})).map da) :=
    ⟨na, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  let nuB : Geometric proB etB L R adj
      ((sheafCompose J (forget CommRingCat.{u + 1})).map db) :=
    ⟨nb, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  let common : Geometric proB etA L R adj
      ((sheafCompose J (forget CommRingCat.{u + 1})).map dq) :=
    ⟨kk, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  let θEt : kk.inverse ≅ se.inverse ⋙ nb.inverse := (Functor.leftUnitor L).symm
  let θPro : kk.inverse ≅ na.inverse ⋙ sp.inverse := (Functor.rightUnitor L).symm
  have hEt : kk.ringMap = θEt.hom.app
      ((sheafCompose etA.site.J (forget CommRingCat.{u + 1})).obj etA.site.A) ≫
        nb.inverse.map se.ringMap ≫ nb.ringMap := by
    change (adj.homEquiv (fe.obj eA) (fp.obj pB)).symm (fe.map dq) =
      𝟙 _ ≫ L.map (fe.map ce) ≫
        (adj.homEquiv (fe.obj eB) (fp.obj pB)).symm (fe.map db)
    rw [Category.id_comp, ← adj.homEquiv_naturality_left_symm]
    congr 1
    rw [← Functor.map_comp]
    exact congrArg ((sheafCompose J (forget CommRingCat.{u + 1})).map)
      (constantDirectMap_pre K J F φ (RingHom.id B)).symm
  have hPro : kk.ringMap = θPro.hom.app
      ((sheafCompose etA.site.J (forget CommRingCat.{u + 1})).obj etA.site.A) ≫
        sp.inverse.map na.ringMap ≫ sp.ringMap := by
    change (adj.homEquiv (fe.obj eA) (fp.obj pB)).symm (fe.map dq) =
      𝟙 _ ≫ (adj.homEquiv (fe.obj eA) (fp.obj pA)).symm (fe.map da) ≫
        fp.map cp
    rw [Category.id_comp, ← adj.homEquiv_naturality_right_symm]
    congr 1
    exact congrArg ((sheafCompose J (forget CommRingCat.{u + 1})).map)
      (constantDirectMap_post K J F (RingHom.id A) φ).symm
  obtain ⟨sys⟩ := ringedDerivedMonoidalComparisons.{u + 1, u + 2}
  obtain ⟨c⟩ := sys.composition
    (X := proB.site) (Y := etB.site) (Z := etA.site) nb se kk θEt hEt
  obtain ⟨d⟩ := sys.composition
    (X := proB.site) (Y := proA.site) (Z := etA.site) sp na kk θPro hPro
  have hs : Nonempty (Square (etA := etA.site) (etB := etB.site)
      (proA := proA.site) (proB := proB.site) se sp na nb kk θEt θPro) := by
    let scalarEt := sys.lift (X := etB.site) (Y := etA.site) se
    let scalarPro := sys.lift (X := proB.site) (Y := proA.site) sp
    let siteA := sys.lift (X := proA.site) (Y := etA.site) na
    let siteB := sys.lift (X := proB.site) (Y := etB.site) nb
    let commonLift := sys.lift (X := proB.site) (Y := etA.site) kk
    have ht (T S : etA.site.D) :
        siteB.edge.left.map (scalarEt.tensor T S).hom ≫
            (siteB.tensor (scalarEt.edge.left.obj T) (scalarEt.edge.left.obj S)).hom ≫
            proB.site.closed.tensor.map
              (Prod.mkHom ((c.pullback.symm ≪≫ d.pullback).hom.app T)
                ((c.pullback.symm ≪≫ d.pullback).hom.app S)) =
          (c.pullback.symm ≪≫ d.pullback).hom.app (etA.site.closed.tensor.obj (T, S)) ≫
            scalarPro.edge.left.map (siteA.tensor T S).hom ≫
            (scalarPro.tensor (siteA.edge.left.obj T) (siteA.edge.left.obj S)).hom := by
      apply (cancel_epi (c.pullback.hom.app (etA.site.closed.tensor.obj (T, S)))).1
      simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_app_assoc]
      have hc := c.tensor T S
      simp only [Lift.tensor, Iso.symm_hom] at hc
      rw [reassoc_of% hc]
      rw [← proB.site.closed.tensor.map_comp]
      simpa only [prod_comp, Prod.mkHom, Iso.hom_inv_id_app_assoc, Lift.tensor, Iso.symm_hom]
        using (d.tensor T S).symm
    refine ⟨{
      scalarEt := scalarEt
      scalarPro := scalarPro
      siteA := siteA
      siteB := siteB
      common := commonLift
      compEt := c
      compPro := d
      tensor := ht
      symmetry := ?_
      unit := ?_ }⟩
    · intro T S
      rw [ht S T]
      have hn := (c.pullback.symm ≪≫ d.pullback).hom.naturality
        (etA.site.symmetry.toBraidedCategory.braiding T S).hom
      change siteB.edge.left.map (scalarEt.edge.left.map
        (etA.site.symmetry.toBraidedCategory.braiding T S).hom) ≫
        (c.pullback.symm ≪≫ d.pullback).hom.app (etA.site.closed.tensor.obj (S, T)) =
        (c.pullback.symm ≪≫ d.pullback).hom.app (etA.site.closed.tensor.obj (T, S)) ≫
        scalarPro.edge.left.map (siteA.edge.left.map
          (etA.site.symmetry.toBraidedCategory.braiding T S).hom) at hn
      rw [reassoc_of% hn]
      rw [← scalarPro.edge.left.map_comp_assoc]
      dsimp only [Lift.tensor, Iso.symm_hom]
      rw [← siteA.symmetric T S, scalarPro.edge.left.map_comp]
      simp only [Category.assoc]
      rw [scalarPro.symmetric (siteA.edge.left.obj T) (siteA.edge.left.obj S)]
    · apply (cancel_epi (c.pullback.hom.app etA.site.closed.monoidal.tensorUnit)).1
      simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_app_assoc]
      simpa only [Lift.unit, Iso.symm_hom, Category.assoc] using d.unit.trans c.unit.symm
  exact ⟨{
    etA := etA
    etB := etB
    proA := proA
    proB := proB
    sEt := sEt
    sPro := sPro
    nuA := nuA
    nuB := nuB
    common := common
    thetaEt := θEt
    thetaEt_eq := HEq.rfl
    thetaPro := θPro
    thetaPro_eq := HEq.rfl
    square := Classical.choice hs }⟩

end

end WeilConjectures.FiniteScalarSite
