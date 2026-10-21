/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Successive derived quotients with the quotient-ring action

Source: blueprint main-20261015, integral criterion reductions, second paragraph
(blueprint: lem-pe-successive-quotient-linear-triangle).
The endpoints are localized termwise restrictions of the specified K-flat tensor models.
The counit equations identify these models with the derived reductions of the given K.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r wB wS wPrev wN wOne
open CategoryTheory CategoryTheory.Pretriangulated
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- Localization with its module category specified before elaborating the complex.
Source: Stacks 05RU (blueprint: lem-pe-successive-quotient-linear-triangle). -/
abbrev successiveQuotientLocalization (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{wS} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R))] :
    CochainComplex (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ℤ ⥤
      DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) :=
  DerivedCategory.Q

section Models
variable {B S : Sheaf J CommRingCat.{r}} {φ : B ⟶ S}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wS} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J S))]

/-- The termwise extension in the recorded derived-change-of-rings presentation.
Source: Stacks 06YY (blueprint: lem-pe-successive-quotient-linear-triangle). -/
def successiveQuotientTensorModel (F : DerivedChangeOfRingsCochainModel φ)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ) :
    CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S)) ℤ :=
  (F.E.mapHomologicalComplex (.up ℤ)).obj P

/-- A pure tensor in the presented extension, using its fixed object equality.
The existing scalar-first convention writes the paper's x tensor s as s tensor x.
Source: Stacks 03EK, 06YY (blueprint: lem-pe-successive-quotient-linear-triangle). -/
def successiveQuotientTensorSection (F : DerivedChangeOfRingsCochainModel φ)
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J B))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) : (F.E.obj M).val.obj U :=
  (eqToHom (F.obj_eq M).symm).val.app U
    ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
      (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] x))

/-- Restrict the scalar action on every term and differential of the tensor model.
Source: Stacks 03D7, 06YY (blueprint: lem-pe-successive-quotient-linear-triangle). -/
def successiveQuotientRestrictedModel {A : Sheaf J CommRingCat.{r}} (a : A ⟶ S)
    (F : DerivedChangeOfRingsCochainModel φ)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ) :
    CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J A)) ℤ :=
  (Functor.mapHomologicalComplex
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map a))
    (.up ℤ)).obj (successiveQuotientTensorModel F P)
end Models

section TriangleData
variable {B SPrev SN SOne : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wPrev} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SPrev))]
  [HasDerivedCategory.{wN} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SN))]
  [HasDerivedCategory.{wOne} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SOne))]

/-- The witnesses and equations of the quotient-linear triangle assertion, packaged
before specializing the three coefficient sheaves to the principal-power quotients.
Every coefficient arrow and every tensor arrow is fixed by the displayed equations.
This structure constructs no additional derived functor or coefficient ring.
Source: blueprint, integral criterion reductions, second paragraph; Stacks 06YY, 0152
(blueprint: lem-pe-successive-quotient-linear-triangle). -/
structure SuccessiveQuotientLinearTriangle
    (t : (B.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections)
    (πPrev : B ⟶ SPrev) (πN : B ⟶ SN) (πOne : B ⟶ SOne)
    (FPrev : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wPrev} πPrev)
    (FN : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wN} πN)
    (FOne : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wOne} πOne)
    (K : DerivedCategory (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)))
    (G P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (e : DerivedCategory.Q.obj G ≅ K) (f : P ⟶ G) where
  /-- Quotient to the preceding coefficient ring. -/
  rPrev : SN ⟶ SPrev
  /-- Quotient to the first coefficient ring. -/
  rOne : SN ⟶ SOne
  /-- The canonical normalization of the first quotient map. -/
  rPrev_projection : πN ≫ rPrev = πPrev
  /-- The canonical normalization of the second quotient map. -/
  rOne_projection : πN ≫ rOne = πOne
  /-- Derived computation of the preceding quotient. -/
  ePrev : FPrev.T.obj K ≅ DerivedCategory.Q.obj (successiveQuotientTensorModel FPrev P)
  /-- Derived computation of the middle quotient. -/
  eN : FN.T.obj K ≅ DerivedCategory.Q.obj (successiveQuotientTensorModel FN P)
  /-- Derived computation of the first quotient. -/
  eOne : FOne.T.obj K ≅ DerivedCategory.Q.obj (successiveQuotientTensorModel FOne P)
  /-- The preceding computation is the one induced by the universal counit. -/
  computesPrev : FPrev.T.map (DerivedCategory.Q.map f ≫ e.hom) ≫ ePrev.hom = FPrev.ε.app P
  /-- The middle computation is the one induced by the universal counit. -/
  computesN : FN.T.map (DerivedCategory.Q.map f ≫ e.hom) ≫ eN.hom = FN.ε.app P
  /-- The first computation is the one induced by the universal counit. -/
  computesOne : FOne.T.map (DerivedCategory.Q.map f ≫ e.hom) ≫ eOne.hom = FOne.ε.app P
  /-- The termwise multiplication map, linear over the middle coefficient ring. -/
  α : successiveQuotientRestrictedModel rPrev FPrev P ⟶ successiveQuotientTensorModel FN P
  /-- The termwise quotient map, linear over the middle coefficient ring. -/
  β : successiveQuotientTensorModel FN P ⟶ successiveQuotientRestrictedModel rOne FOne P
  /-- The connecting morphism in the middle coefficient derived category. -/
  δ : (successiveQuotientLocalization SN).obj
        (successiveQuotientRestrictedModel rOne FOne P) ⟶
      ((successiveQuotientLocalization SN).obj
        (successiveQuotientRestrictedModel rPrev FPrev P))⟦(1 : ℤ)⟧
  /-- Distinguishedness over the middle coefficient ring. -/
  distinguished : Triangle.mk ((successiveQuotientLocalization SN).map α)
      ((successiveQuotientLocalization SN).map β) δ ∈
    distTriang (DerivedCategory (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J SN)))
  /-- Multiplication by t on the coefficient tensor factor. -/
  alpha_formula : ∀ (i : ℤ) (U : Cᵒᵖ) (b : B.obj.obj U) (x : (P.X i).val.obj U),
    (α.f i).val.app U (successiveQuotientTensorSection FPrev (P.X i) U
      (πPrev.hom.app U b) x) =
    successiveQuotientTensorSection FN (P.X i) U
      (πN.hom.app U ((@id (B.obj.obj U) (t.val U)) * b)) x
  /-- Quotient on the coefficient tensor factor. -/
  beta_formula : ∀ (i : ℤ) (U : Cᵒᵖ) (b : B.obj.obj U) (x : (P.X i).val.obj U),
    (β.f i).val.app U (successiveQuotientTensorSection FN (P.X i) U (πN.hom.app U b) x) =
    successiveQuotientTensorSection FOne (P.X i) U (πOne.hom.app U b) x
end TriangleData

variable [HasSheafify J CommRingCat.{r}]
  (B : Sheaf J CommRingCat.{r}) (t : (B.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections)

/-- Successive derived reductions form the specified distinguished triangle in D(B/t^n).
The statement uses any representative G of K and any flat-term K-flat resolution P to G.
The three e's are the canonical derived computations: their equations explicitly use
that resolution, the representative isomorphism and the universal cochain counit.
Restriction is termwise, exactly as specified in the node. The pure-tensor equations
characterize the first two maps even when quotient sections lift only locally.

Source: blueprint main-20261015, integral criterion reductions, second paragraph;
Stacks 03D7, 03ER, 06YS, 06YY, 0152
(blueprint: lem-pe-successive-quotient-linear-triangle).

Proof:
1. The coefficient maps send [b] to [tb] and [b] to [b]. Local quotient lifts show
well-definedness and exactness. If tb = t^n c, injectivity of t gives b = t^(n-1)c.
The quotient map is locally surjective; this proves the coefficient short exact
sequence as B-modules and as R_n-modules, without choosing points of the site.
2. Resolve an arbitrary representative by a flat-term K-flat complex (06YS).
Apply the sheafified tensor termwise. The formulas on pure tensors commute with
restriction and with the differentials, and are R_n-linear.
3. Flatness, defined as exactness of the sheaf tensor functor (03ER), makes the
resulting sequence degreewise short exact. Restriction retains the underlying
abelian sheaves, so kernels, images and cokernels give the same exactness over R_n.
4. Apply DerivedCategory.triangleOfSES_distinguished in Mod(R_n) (0152).
Its first two maps are the localizations of the displayed cochain maps.
5. The universal counit of derived change of rings is invertible on P (06YY).
Compose its inverse comparison with the image of P to G and G to K to identify
all three objects with K_j. Restriction preserves quasi-isomorphisms and shifts,
since it retains the abelian sheaf and differential. This identifies the endpoints
with the termwise restrictions of K_(n-1) and K_1. Tensor symmetry changes the
scalar-first formulas to the paper's second-factor formulas. No bound or completeness
is used, and the construction applies to every flat-term K-flat resolution. -/
theorem successive_quotient_linear_triangle (n : ℕ) (hn : 1 < n)
    (ht : ∀ U : Cᵒᵖ, Function.Injective
      (fun b : B.obj.obj U ↦ (@id (B.obj.obj U) (t.val U)) * b))
    [HasDerivedCategory.{wB} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B))]
    [HasDerivedCategory.{wPrev} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J (principalPowerRingQuotient B t (n - 1))))]
    [HasDerivedCategory.{wN} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J (principalPowerRingQuotient B t n)))]
    [HasDerivedCategory.{wOne} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J (principalPowerRingQuotient B t 1)))]
    (FPrev : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wPrev}
      (principalPowerRingProjection B t (n - 1)))
    (FN : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wN}
      (principalPowerRingProjection B t n))
    (FOne : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wOne}
      (principalPowerRingProjection B t 1))
    (K : DerivedCategory (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)))
    (G P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (e : DerivedCategory.Q.obj G ≅ K) (f : P ⟶ G)
    (hf : CochainComplex.IsKFlatResolutionIndependentCoefficients (R := B) f)
    (hflat : ∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) :
    Nonempty (SuccessiveQuotientLinearTriangle t
      (principalPowerRingProjection B t (n - 1)) (principalPowerRingProjection B t n)
      (principalPowerRingProjection B t 1) FPrev FN FOne K G P e f) := sorry

end SheafOfModules
