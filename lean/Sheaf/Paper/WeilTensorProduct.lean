/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.PbcWeilCategory
public import Sheaf.Paper.WeilCompletedTensorReflector
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-!
# Completed adic tensor and its geometric Frobenius

Source: blueprint, sec-six-functors/sk-rem-sf-pf-done, order 2107
(blueprint: def-wf-tensor-product).
Derived tensor means K-flat tensor, then the explicit intrinsic Koszul completion,
then raw scalar localization. No preservation or exactness on Weil pairs is assumed.

The finite coefficient stages use `pbcStageDatum` and `pbcStageUniformizer`:
these are the valuation-ring data transported along `Shrink.algEquiv`, with the
actual field inclusions conjugated by that canonical equivalence.

## Main definitions

- `SheafOfModules.wfSiteDerivedTensor`: the localized K-flat tensor bifunctor.
- `wfIntegralTensor`, `wfRationalTensor`: completed integral and rational tensor.
- `wfRationalTensorPullback`: the normalized Frobenius/tensor comparison.
- `WeilConjectures.wfTensorFrobenius`: tensor of the given Weil structures.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
namespace SheafOfModules

/-- The derived tensor supplied by localization of the flat-term K-flat subcategory.
The representative comparison in site_derived_tensor_descent determines this functor
up to the unique compatible natural isomorphism; no functorial representatives are chosen.
Source: Stacks 06YS and 06YT (blueprint: def-wf-tensor-product). -/
def wfSiteDerivedTensor {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))] :
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ×
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ⥤
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) :=
  (wf_site_derived_tensor_descent.{u, v, w, 0, 0} J R).choose_spec.2.2.1.choose_spec.2.choose

/-- A flat-term K-flat first argument computes tensor against every second complex.
Source: Stacks 06YS and 06YT (blueprint: def-wf-tensor-product).
Proof: choose a flat-term K-flat resolution V→D of the second complex. K-flatness
of P and signed symmetry make Tot(P⊗V)→Tot(P⊗D) a quasi-isomorphism. The descent
comparison computes tensor on P,V. Localize the quasi-isomorphism V→D and use
functoriality in the second variable. Compose these three isomorphisms. Replacing
P by any flat-term K-flat resolution of a representative of M gives the stated
first-variable formula, with no functorial choice of representatives.
-/
theorem wfSiteDerivedTensor_first {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))]
    (P D : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (_hP : CochainComplex.IsAcyclicTensorKFlat (J := J) (R := R) P)
    (_hflat : ∀ n : ℤ, CategoryTheory.exactFunctor _ _
      ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) _
          (SheafOfModules.monoidalCategory.{v, u, max u v} R)).flip.obj (P.X n))) :
    Nonempty (DerivedCategory.Q.obj
        (CochainComplex.mapBifunctor P D
          (@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{max u v}
            ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) _
              (SheafOfModules.monoidalCategory.{v, u, max u v} R))) ≅
      (wfSiteDerivedTensor J R).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj D)) := by
  sorry

end SheafOfModules
namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)

/-- Ordinary uncompleted derived tensor over the actual completed coefficient sheaf.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev wfOrdinaryDerivedTensor :
    PbcCompletedDerived X d × PbcCompletedDerived X d ⥤ PbcCompletedDerived X d :=
  SheafOfModules.wfSiteDerivedTensor (ProEt.topology X) (pbcAdicCompletion X d)

/-- The localization model's natural comparison on flat-term K-flat representatives.
Source: Stacks 06YT; blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: take the natural representative comparison from site-derived-tensor descent.
The homotopy quotient comparison identifies its source with total tensor of complexes.
Flatness means exactness of sheaf tensor, so the two flat-term subcategories coincide.
Their localization comparisons give the displayed natural isomorphism. Restriction
of transformations to the resolving subcategory is bijective by descent, so the
compatible comparison with any other model exists uniquely. Thus the chosen model
is determined up to its unique compatible natural isomorphism. -/
theorem wfTensorRepresentative_exists :
    ∃ i :
      (((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι.prod
          (proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι) ⋙
        Functor.uncurry.obj
          ((proEtaleOrdinaryTensor X (pbcAdicCompletion X d)).map₂HomologicalComplex
           (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ DerivedCategory.Q) ≅
      ((((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι ⋙ DerivedCategory.Q).prod
        ((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι ⋙ DerivedCategory.Q)) ⋙
          wfOrdinaryDerivedTensor X d),
      ∀ b : ProEtaleTensorModel X (pbcAdicCompletion X d),
        ∃! e : wfOrdinaryDerivedTensor X d ≅ b.tensor,
          i.hom ≫ Functor.whiskerLeft
            ((((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι ⋙
                DerivedCategory.Q).prod
              ((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι ⋙
                DerivedCategory.Q))) e.hom = b.representative.hom := by
  sorry

/-- The existing pullback-comparison interface with this very localized tensor.
Source: Stacks 06YT; blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfTensorModel : ProEtaleTensorModel X (pbcAdicCompletion X d) where
  tensor := wfOrdinaryDerivedTensor X d
  representative := (wfTensorRepresentative_exists X d).choose

/-- Integral completed tensor is ordinary derived tensor followed by the Koszul reflector.
Source: blueprint order 2107; Bhatt--Scholze Definition 3.4.10
(blueprint: def-wf-tensor-product). -/
def wfIntegralTensor : WfCompleteCategory X d r a ha × WfCompleteCategory X d r a ha ⥤
    WfCompleteCategory X d r a ha :=
  ((ObjectProperty.ι (WfIsComplete X d r a ha)).prod
    (ObjectProperty.ι (WfIsComplete X d r a ha))) ⋙
      wfOrdinaryDerivedTensor X d ⋙ wfCompletion X d r a ha

/-- The ambient rational category keeps all integral complete objects, without boundedness.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev WfAmbientRationalCategory (p : A) :=
  ScalarLocalization A (WfCompleteCategory X d r a ha) p

/-- The underlying object of rational tensor, before specifying its localized Hom action.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfRationalTensorObj (p : A)
    (M N : WfAmbientRationalCategory X d r a ha p) :
    WfAmbientRationalCategory X d r a ha p :=
  ⟨(wfIntegralTensor X d r a ha).obj (M.obj, N.obj)⟩

/-- Bilinear scalar extension is uniquely determined on pure tensors, including denominators.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: sheaf tensor is linear in each variable. Its K-flat localization is linear by
extension of transformations from K-flat representatives; the reflector is linear by its
unit and the Hom bijection. Extend this bilinear map along A→A[1/p] in both variables.
The tensor-product universal property gives the displayed pure-tensor formula and uniqueness.
Writing coefficients as inverse powers gives precisely denominator p^(r+s). -/
theorem wfRationalTensorHom_exists (p : A)
    (M M' N N' : WfAmbientRationalCategory X d r a ha p) :
    ∃! b : (M ⟶ M') →ₗ[Localization.Away p] (N ⟶ N') →ₗ[Localization.Away p]
        (wfRationalTensorObj X d r a ha p M N ⟶ wfRationalTensorObj X d r a ha p M' N'),
      ∀ (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (s t : Localization.Away p),
        b (s ⊗ₜ[A] f) (t ⊗ₜ[A] g) =
          (s * t) ⊗ₜ[A] (wfIntegralTensor X d r a ha).map (Prod.mkHom f g) := by
  sorry

/-- The unique localized bilinear map; its values are prescribed on every numerator.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfRationalTensorHom (p : A)
    (M M' N N' : WfAmbientRationalCategory X d r a ha p) :=
  (wfRationalTensorHom_exists X d r a ha p M M' N N').exists.choose

private theorem wfRationalTensorHom_tmul (p : A)
    (M M' N N' : WfAmbientRationalCategory X d r a ha p)
    (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (s t : Localization.Away p) :
    wfRationalTensorHom X d r a ha p M M' N N' (s ⊗ₜ[A] f) (t ⊗ₜ[A] g) =
      (s * t) ⊗ₜ[A] (wfIntegralTensor X d r a ha).map (Prod.mkHom f g) :=
  (wfRationalTensorHom_exists X d r a ha p M M' N N').exists.choose_spec f g s t

/-- The extended tensor maps satisfy the bifunctor laws.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: on pure tensors the identity law follows from integral tensor's identity law and
1*1=1. Composition follows from integral functoriality and commutative multiplication of
localized scalars. Bilinearity extends these equations to all localized morphisms. -/
theorem wfRationalTensor_laws (p : A) :
    (∀ M N : WfAmbientRationalCategory X d r a ha p,
      wfRationalTensorHom X d r a ha p M M N N (𝟙 M) (𝟙 N) = 𝟙 _) ∧
    ∀ (M M' M'' N N' N'' : WfAmbientRationalCategory X d r a ha p)
      (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N''),
      wfRationalTensorHom X d r a ha p M M'' N N'' (f ≫ f') (g ≫ g') =
        wfRationalTensorHom X d r a ha p M M' N N' f g ≫
          wfRationalTensorHom X d r a ha p M' M'' N' N'' f' g' := by
  constructor
  · intro M N
    change wfRationalTensorHom X d r a ha p M M N N
      ((1 : Localization.Away p) ⊗ₜ[A] 𝟙 M.obj)
      ((1 : Localization.Away p) ⊗ₜ[A] 𝟙 N.obj) =
        (1 : Localization.Away p) ⊗ₜ[A] 𝟙 _
    rw [wfRationalTensorHom_tmul, one_mul]
    congr 1
    exact (wfIntegralTensor X d r a ha).map_id (M.obj, N.obj)
  · intro M M' M'' N N' N'' f f' g g'
    change wfRationalTensorHom X d r a ha p M M'' N N''
      (ScalarLocalization.composition A (WfCompleteCategory X d r a ha) p _ _ _ f' f)
      (ScalarLocalization.composition A (WfCompleteCategory X d r a ha) p _ _ _ g' g) =
        ScalarLocalization.composition A (WfCompleteCategory X d r a ha) p _ _ _
          (wfRationalTensorHom X d r a ha p M' M'' N' N'' f' g')
          (wfRationalTensorHom X d r a ha p M M' N N' f g)
    induction f using TensorProduct.induction_on with
    | zero => simp
    | add f₁ f₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
    | tmul s f =>
      induction f' using TensorProduct.induction_on with
      | zero => simp
      | add f₁ f₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
      | tmul t f' =>
        induction g using TensorProduct.induction_on with
        | zero => simp
        | add g₁ g₂ h₁ h₂ => simp only [map_add, h₁, h₂]
        | tmul u g =>
          induction g' using TensorProduct.induction_on with
          | zero => simp
          | add g₁ g₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
          | tmul v g' =>
            simp [ScalarLocalization.composition_tmul,
              wfRationalTensorHom_tmul, ← Functor.map_comp, mul_comm,
              mul_left_comm, Prod.mkHom]


/-- Completed tensor rationalized with the stated product-of-denominators convention.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfRationalTensor (p : A) :
    WfAmbientRationalCategory X d r a ha p × WfAmbientRationalCategory X d r a ha p ⥤
      WfAmbientRationalCategory X d r a ha p where
  obj MN := wfRationalTensorObj X d r a ha p MN.1 MN.2
  map {MN PQ} f := wfRationalTensorHom X d r a ha p MN.1 PQ.1 MN.2 PQ.2 f.1 f.2
  map_id MN := (wfRationalTensor_laws X d r a ha p).1 MN.1 MN.2
  map_comp f g := (wfRationalTensor_laws X d r a ha p).2 _ _ _ _ _ _ f.1 g.1 f.2 g.2


variable (e : Aut X)

/-- Exact coefficient transport preserves intrinsic completeness for the actual scalar list.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: the finite coefficient comparisons preserve every constant section a_j, and commute
with quotient maps. Their limit fixes a_j on the completed ring. Apply the exact inverse
site equivalences to the strict Koszul tower. They preserve products and both finite
fiber summands; the projection comparison commutes with 1-shift and with the signed
fiber differential. It identifies the (u,0) units, hence preserves their invertibility. -/
theorem wfIsoPullback_complete (M : WfCompleteCategory X d r a ha) :
    WfIsComplete X d r a ha ((pbcIsoAmbientPullback e.hom d).obj M.obj) := by
  sorry

/-- The same exact transport on all complete objects, before raw rationalization.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfCompletePullback : WfCompleteCategory X d r a ha ⥤ WfCompleteCategory X d r a ha :=
  ObjectProperty.lift (WfIsComplete X d r a ha)
    (ObjectProperty.ι (WfIsComplete X d r a ha) ⋙ pbcIsoAmbientPullback e.hom d)
    (wfIsoPullback_complete X d r a ha e)

/-- Constant sections are fixed by the completed coefficient identification.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: check the scalar action after every finite quotient projection. The constant
inverse-image comparison is adjoint to identity on constants, so fixes each residue.
The limit map therefore fixes every scalar. The sectionwise linear equation descends
through complexes and localization, and restricts to the complete full subcategory. -/
theorem wfCompletePullback_linear :
    (wfCompletePullback X d r a ha e).Additive ∧
      (wfCompletePullback X d r a ha e).Linear A := by
  sorry

/-- The additive part of the specified coefficient transport.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
instance wfCompletePullback_additive : (wfCompletePullback X d r a ha e).Additive :=
  (wfCompletePullback_linear X d r a ha e).1

/-- The A-linear part of the specified coefficient transport.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
instance wfCompletePullback_isLinear : (wfCompletePullback X d r a ha e).Linear A :=
  (wfCompletePullback_linear X d r a ha e).2

/-- Frobenius transport on the ambient raw rationalization, on every complete object.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev wfAmbientRationalPullback (p : A) :=
  ScalarLocalization.map A (WfCompleteCategory X d r a ha) p
    (wfCompletePullback X d r a ha e)

/-- The completion comparison is uniquely fixed by its unit square.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: on flat-term K-flat representatives use the degreewise balanced tensor comparison.
The coefficient limit identification fixes a_j, hence identifies Q_m and every transition.
On the product use the map whose components are the transported projections. The transition
identity makes this commute with 1-shift. On each fiber term B^i plus B^(i-1) use the
comparison on both summands; it commutes with (dx,(1-t)x-dy). This produces the displayed
isomorphism and its (u,0) unit equation. The reflector's Hom bijection shows uniqueness,
including when a representative is already flat K-flat and when the scheme is empty. -/
theorem wfPullbackCompletion_exists (M : PbcCompletedDerived X d) :
    ∃! c : (pbcIsoAmbientPullback e.hom d).obj (wfCompletionObj X d r a ha M) ≅
        wfCompletionObj X d r a ha ((pbcIsoAmbientPullback e.hom d).obj M),
      (pbcIsoAmbientPullback e.hom d).map (wfCompletionUnit X d r a ha M) ≫ c.hom =
        wfCompletionUnit X d r a ha ((pbcIsoAmbientPullback e.hom d).obj M) := by
  sorry

/-- The specified product/fiber comparison, determined equivalently by the unit square.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfPullbackCompletion (M : PbcCompletedDerived X d) :=
  (wfPullbackCompletion_exists X d r a ha e M).exists.choose

/-- The integral comparison is the completed canonical derived tensor comparison.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfIntegralTensorPullback (M N : WfCompleteCategory X d r a ha) :
    (wfCompletePullback X d r a ha e).obj ((wfIntegralTensor X d r a ha).obj (M, N)) ≅
      (wfIntegralTensor X d r a ha).obj
        ((wfCompletePullback X d r a ha e).obj M, (wfCompletePullback X d r a ha e).obj N) :=
  ObjectProperty.isoMk _
    (wfPullbackCompletion X d r a ha e ((wfOrdinaryDerivedTensor X d).obj (M.obj, N.obj)) ≪≫
      (ObjectProperty.ι (WfIsComplete X d r a ha)).mapIso
        ((wfCompletion X d r a ha).mapIso
          ((proEtaleCanonicalTensorComparison e.hom (pbcAdicCompletion X d)
            (pbcAdicCompletion X d) (asIso (completedCoefficientMap e.hom d))
            (wfTensorModel X d) (wfTensorModel X d)).app (M.obj, N.obj))))

/-- Rationalizing the constructed integral comparison fixes every component uniquely.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: tensor with one the integral comparison and its inverse on Hom modules. The
integral comparison is natural by naturality of the canonical tensor comparison and
of the product/fiber comparison. Its naturality extends to all fractions by A-linearity
and inversion of p. Every object is an original integral object, so the component
formula gives uniqueness. The two displayed directions are thus fixed, not chosen. -/
theorem wfRationalTensorPullback_exists (p : A) :
    ∃! mu : wfRationalTensor X d r a ha p ⋙ wfAmbientRationalPullback X d r a ha e p ≅
        ((wfAmbientRationalPullback X d r a ha e p).prod
          (wfAmbientRationalPullback X d r a ha e p)) ⋙ wfRationalTensor X d r a ha p,
      ∀ M N : WfCompleteCategory X d r a ha,
        mu.hom.app (⟨M⟩, ⟨N⟩) =
          (ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p).map
            (wfIntegralTensorPullback X d r a ha e M N).hom := by
  sorry

/-- The typed pullback/tensor comparison in the displayed direction of the source.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfRationalTensorPullback (p : A) :=
  (wfRationalTensorPullback_exists X d r a ha e p).exists.choose

/-- The exact PBC integral subcategory lies in this same intrinsically complete category.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: its first defining condition supplies an intrinsic-completion witness after the
canonical completed-ring presentation comparison. The mutually inverse exact coefficient
restrictions preserve the strict Koszul tower and unit. The Koszul reflector shows
independence of the generating tuple and representative. Therefore the canonical
representative and the given generating tuple have invertible intrinsic unit. -/
theorem wfConstructible_complete (M : PbcBoundedConstructibleComplete X d) :
    WfIsComplete X d r a ha M.obj := by
  sorry

/-- Inclusion of the specified constructible objects, retaining all their derived arrows.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfIntegralConstructibleInclusion :
    PbcBoundedConstructibleComplete X d ⥤ WfCompleteCategory X d r a ha :=
  ObjectProperty.lift (WfIsComplete X d r a ha)
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X d))
    (wfConstructible_complete X d r a ha)

/-- The inclusion on rational coefficients is uniquely determined by integral localization.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: the inclusion is A-linear since its underlying maps are unchanged. Extend its
Hom maps by tensor with the identity of A[1/p]. This respects the given composition
and identity formulas. Every localized morphism is a fraction of an integral morphism,
and the objects are unchanged, so the equality determines the functor uniquely. -/
theorem wfConstructibleInclusion_exists (p : A) :
    ∃! F : PbcRationalCategory X d p ⥤ WfAmbientRationalCategory X d r a ha p,
      pbcRationalization X d p ⋙ F =
        wfIntegralConstructibleInclusion X d r a ha ⋙
          ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p := by
  sorry

/-- The raw rational inclusion with its actual unchanged integral object function.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfConstructibleInclusion (p : A) :=
  (wfConstructibleInclusion_exists X d r a ha p).exists.choose

/-- Inclusion commutes with the same coefficient transport, normalized by identity on objects.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: both inclusions and both pullbacks act on the same ambient derived objects and
maps. Their integral composites agree after the faithful ambient inclusion. The unique
rational extension retains these object identities and sends every integral arrow to
itself tensored with one. Thus the displayed object equality is literal. -/
theorem wfConstructiblePullback_obj (p : A) (M : PbcRationalCategory X d p) :
    (wfAmbientRationalPullback X d r a ha e p).obj
        ((wfConstructibleInclusion X d r a ha p).obj M) =
      (wfConstructibleInclusion X d r a ha p).obj
        ((pbcRationalIsoPullback e d p).obj M) := by
  sorry

end AlgebraicGeometry.Scheme

namespace WeilConjectures
open AlgebraicGeometry AlgebraicGeometry.Scheme
variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (CommRingCat.of D.k₀)))
  [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (E : Padic.FiniteCoefficientFields c.l c.Qbar)

/-- The singleton generator is exactly the stipulated uniformizer ideal.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: the range of the constant function on Fin 1 is the singleton uniformizer, and
pbcIntegralDatum defines its ideal as the span of that singleton. -/
theorem wfUniformizer_generates :
    Ideal.span (Set.range (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)) =
      (pbcStageDatum.{u} c.l c.Qbar E).ideal := by
  rw [Set.range_const]
  change Ideal.span {pbcUniformizer c.l (pbcFiniteField c.l c.Qbar E)} = _
  rfl

/-- The actual ambient rational category at the finite coefficient field E.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev WfAmbient := WfAmbientRationalCategory (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
  (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- Completed tensor at E on arbitrary ambient objects, with the specified scalar ring.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev wfTensor := wfRationalTensor (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
  (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- Geometric Frobenius on this ambient category, using the coefficient-limit identification.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev wfAmbientFrobenius := wfAmbientRationalPullback (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
  (wfUniformizer_generates D c E) (D.geometricFrobenius X₀) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- Inclusion of the node's Weil-complex carriers into the stipulated ambient category.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev wfWeilCarrier (K : WeilD D c X₀ E) : WfAmbient D c X₀ E :=
  (wfConstructibleInclusion (D.geometricFiber X₀).left
    (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
    (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)).obj K.carrier

/-- The given Weil isomorphism, transported by the faithful ambient coefficient inclusion.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfWeilStructure (K : WeilD D c X₀ E) :
    (wfAmbientFrobenius D c X₀ E).obj (wfWeilCarrier D c X₀ E K) ≅
      wfWeilCarrier D c X₀ E K :=
  eqToIso (wfConstructiblePullback_obj (D.geometricFiber X₀).left
    (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
    (wfUniformizer_generates D c E) (D.geometricFrobenius X₀)
    (pbcStageUniformizer.{u} c.l c.Qbar E) K.carrier) ≪≫
      (wfConstructibleInclusion (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
        (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)).mapIso K.str

/-- Tensor Frobenius is mu followed by tensor of the two given Weil isomorphisms.
The output is ambient; restriction to an exact bifunctor of Weil complexes is separate.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfTensorFrobenius (K L : WeilD D c X₀ E) :
    (wfAmbientFrobenius D c X₀ E).obj
        ((wfTensor D c X₀ E).obj (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L)) ≅
      (wfTensor D c X₀ E).obj (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L) :=
  (wfRationalTensorPullback (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E)
    1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E) (wfUniformizer_generates D c E)
    (D.geometricFrobenius X₀) (pbcStageUniformizer.{u} c.l c.Qbar E)).app
      (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L) ≪≫
    (wfTensor D c X₀ E).mapIso
      { hom := Prod.mkHom (wfWeilStructure D c X₀ E K).hom (wfWeilStructure D c X₀ E L).hom
        inv := Prod.mkHom (wfWeilStructure D c X₀ E K).inv (wfWeilStructure D c X₀ E L).inv }

end WeilConjectures
