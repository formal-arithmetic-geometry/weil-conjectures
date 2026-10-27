/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.Paper.LissePointNormalization
public import Sheaf.Paper.LisseTensorPullbackRealization
public import Sheaf.Paper.LisseFieldNormalization
public import Sheaf.Paper.PointProEtaleSectionsExactOfUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.SixFunctors.PointRingedEvaluationModel
import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel
import Sheaf.Paper.CoefficientComplexRationalization
import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
import Sheaf.Paper.PointSectionsFiniteness

/-! # Sections and the normalized lisse fibre at the geometric point

Source: Bhatt--Scholze, Lemma 6.8.12, Proposition 6.8.14(2), Remark 6.8.15;
Stacks 03EL, 07A4 and 0A8X (blueprint: lem-tw-lisse-point-sections-realization).

The comparison data in the conclusion retain the ordinary section formula, the
termwise derived normalization, the actual size-descent counit and the specified
pullback comparison. Tensor and scalar maps are characterized on pure sections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme MonoidalCategory
open scoped TensorProduct MonoidalCategory ChangeOfRings
namespace WeilConjectures.LisseRealization
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The coefficient unit as an actual degree-zero integral complex.
Source: BS 6.8.12; Stacks 0A8X (blueprint: lem-tw-lisse-point-sections-realization). -/
abbrev pointIntegralUnit :=
  (DerivedCategory.singleFunctor (integralTowerModules l E (point D l hl).scheme) 0).obj
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E
      (point D l hl).scheme))

/-- The rational coefficient unit in the ordinary module derived category.
Source: BS 6.8.15 (blueprint: lem-tw-lisse-point-sections-realization). -/
abbrev pointRationalUnit :=
  (DerivedCategory.singleFunctor (Modules D l hl E (point D l hl)) 0).obj
    (SheafOfModules.unit ((adicLisseForget (point D l hl).scheme).obj
      (rationalCoefficientSheaf l (point D l hl).scheme E)))

/-- All point comparisons, with exact sections and their representative normalization.
The tensor maps on the recorded fibre are fixed by the square with the normalized
localization map; their section formulas fix the ordinary comparisons, including zero rank.
Source: BS 6.8.12, 6.8.14(2), 6.8.15; Stacks 03EL, 07A4 and 0A8X
(blueprint: lem-tw-lisse-point-sections-realization). -/
structure PointSectionsRealization
    (a : ∀ X : Base D l hl, At D l hl E X)
    (t : ∀ X : Base D l hl, RealizationTensorComparison D l hl E X (a X))
    (r : ∀ (X Y : Base D l hl) (f : X.scheme ⟶ Y.scheme),
      RealizationPullComparison D l hl E f (a X) (a Y)) where
  [additive : (sections D l hl E).Additive]
  [limits : PreservesFiniteLimits (sections D l hl E)]
  [colimits : PreservesFiniteColimits (sections D l hl E)]
  point : PointAt D l hl E (a (LisseRealization.point D l hl))
  normalized : PointNormalized D l hl E (a (LisseRealization.point D l hl)) point
  integral_constants : Function.Bijective (pointCompletedConstant D.k l E)
  rational_constants : Function.Bijective (pointConstants D l E)
  integral_hom : ∀ C : DerivedCategory
    (integralTowerModules l E (LisseRealization.point D l hl).scheme),
    (pointIntegralUnit D l hl E ⟶ C) ≃+
      ↑((DerivedCategory.homologyFunctor _ 0).obj
        ((pointCompletedDerivedSections D.k l E).obj C))
  rational_hom : ∀ C : DerivedCategory (Modules D l hl E (LisseRealization.point D l hl)),
    (pointRationalUnit D l hl E ⟶ C) ≃+
      ↑((DerivedCategory.homologyFunctor _ 0).obj
        ((sections D l hl E).mapDerivedCategory.obj C))
  integral_hom_natural : ∀ (C C' : DerivedCategory
    (integralTowerModules l E (LisseRealization.point D l hl).scheme))
    (f : pointIntegralUnit D l hl E ⟶ C) (g : C ⟶ C'),
    integral_hom C' (f ≫ g) =
      (DerivedCategory.homologyFunctor _ 0).map
        ((pointCompletedDerivedSections D.k l E).map g) (integral_hom C f)
  integral_hom_one :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) 0).hom.app _
      ((DerivedCategory.homologyFunctor _ 0).map
        ((Functor.mapDerivedCategorySingleFunctor (pointCompletedSections D.k l E) 0).hom.app
          (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E
            (LisseRealization.point D l hl).scheme)))
          (integral_hom _ (𝟙 (pointIntegralUnit D l hl E)))) =
      pointCompletedConstant D.k l E 1
  rational_hom_natural : ∀ (C C' : DerivedCategory
    (Modules D l hl E (LisseRealization.point D l hl)))
    (f : pointRationalUnit D l hl E ⟶ C) (g : C ⟶ C'),
    rational_hom C' (f ≫ g) =
      (DerivedCategory.homologyFunctor _ 0).map
        ((sections D l hl E).mapDerivedCategory.map g) (rational_hom C f)
  rational_hom_one :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u + 1} E) 0).hom.app _
      ((DerivedCategory.homologyFunctor _ 0).map
        ((Functor.mapDerivedCategorySingleFunctor (sections D l hl E) 0).hom.app
          (SheafOfModules.unit ((adicLisseForget (LisseRealization.point D l hl).scheme).obj
            (rationalCoefficientSheaf l (LisseRealization.point D l hl).scheme E))))
          (rational_hom _ (𝟙 (pointRationalUnit D l hl E)))) = pointConstants D l E 1
  hom_scalar : ∀ (C : sfIntegralConstructibleCategory l E
    (LisseRealization.point D l hl).scheme) (q : ℤ) (c : E)
    (f : pointIntegralUnit D l hl E ⟶ C.obj⟦q⟧),
    rational_hom _ (c • ((t (LisseRealization.point D l hl)).derived_unit.inv ≫
      (pbcDerivedExtend (scalar D l hl E (a (LisseRealization.point D l hl)))).map f)) =
    (DerivedCategory.homologyFunctor _ 0).map
      (normalized.derived.hom.app (C.obj⟦q⟧))
      (((pointModuleRationalization l E).mapDerivedCategoryHomologyFunctorIso 0).hom.app
        ((pointCompletedDerivedSections D.k l E).obj (C.obj⟦q⟧))
          (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] integral_hom _ f))
  tensor_sections : ∀ M N : Modules D l hl E (LisseRealization.point D l hl),
    (sections D l hl E).obj (M ⊗ N) ≅
      ModuleCat.of E ((sections D l hl E).obj M ⊗[E] (sections D l hl E).obj N)
  tensor_sections_normalized : ∀ (M N : Modules D l hl E (LisseRealization.point D l hl))
    (x : (sections D l hl E).obj M) (y : (sections D l hl E).obj N),
    (tensor_sections M N).hom
      (pure D l hl E M N (op (ProEt.mk (𝟙 _))) x y) = x ⊗ₜ[E] y
  unit_sections : (sections D l hl E).obj
    (SheafOfModules.unit ((adicLisseForget (LisseRealization.point D l hl).scheme).obj
      (rationalCoefficientSheaf l (LisseRealization.point D l hl).scheme E))) ≅
    ModuleCat.of E (ULift.{u + 1} E)
  unit_sections_normalized : ∀ c : E, unit_sections.hom (pointConstants D l E c) = ULift.up c
  fibre_tensor : ∀ (K L : Raw D l hl E (LisseRealization.point D l hl))
    (_hK : Lisse D l hl E (LisseRealization.point D l hl) K)
    (_hL : Lisse D l hl E (LisseRealization.point D l hl) L),
    (fibre D l hl E).obj ((tensor D l hl E (LisseRealization.point D l hl)).obj (K, L)) ≅
      ModuleCat.of E ((fibre D l hl E).obj K ⊗[E] (fibre D l hl E).obj L)
  tensor_square : ∀ (K L : Raw D l hl E (LisseRealization.point D l hl))
    (hK : Lisse D l hl E (LisseRealization.point D l hl) K)
    (hL : Lisse D l hl E (LisseRealization.point D l hl) L),
    (fibre_tensor K L hK hL).hom ≫
        ModuleCat.ofHom (TensorProduct.map
          (point.comparison.hom.app ⟨K, hK⟩).hom (point.comparison.hom.app ⟨L, hL⟩).hom) =
      point.comparison.hom.app
        ⟨_, (t (LisseRealization.point D l hl)).lisse.tensor_mem K L hK hL⟩ ≫
      (sections D l hl E).map
        ((t (LisseRealization.point D l hl)).lisse.tensor K L hK hL).hom ≫
      (tensor_sections _ _).hom
  fibre_unit : (fibre D l hl E).obj
    (unit D l hl E (LisseRealization.point D l hl)) ≅ ModuleCat.of E (ULift.{u + 1} E)
  unit_square : fibre_unit.hom = point.comparison.hom.app
      ⟨_, (t (LisseRealization.point D l hl)).lisse.unit_mem⟩ ≫
    (sections D l hl E).map (t (LisseRealization.point D l hl)).lisse.unit.hom ≫
      unit_sections.hom
  pull_tensor : ∀ (X : Base D l hl)
    (x : (LisseRealization.point D l hl).scheme ⟶ X.scheme),
    PullTensor D l hl E x (a (LisseRealization.point D l hl)) (a X)
      (t (LisseRealization.point D l hl)).lisse (t X).lisse
      (r (LisseRealization.point D l hl) X x).lisse
  comparison : ∀ (X : Base D l hl)
    (x : (LisseRealization.point D l hl).scheme ⟶ X.scheme)
    (K : Raw D l hl E X) (_hK : Lisse D l hl E X K),
    (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory.obj
        ((pointRationalFibre D l hl E).obj ((pull D l hl E x).obj K)).obj ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u + 1} E) 0).obj
        ((sections D l hl E).obj
          ((ordinaryPull l E x).obj (((a X).sheaf D l hl E).obj K)))
  comparison_normalized : ∀ (X : Base D l hl)
    (x : (LisseRealization.point D l hl).scheme ⟶ X.scheme)
    (K : Raw D l hl E X) (hK : Lisse D l hl E X K),
    ∃ e : ((a X).J.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj
      (((a X).sheaf D l hl E).obj K)),
      ((DerivedCategory.homologyFunctor _ 0).map e.hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app _ = 𝟙 _) ∧
      (comparison X x K hK).hom =
        (pointRationalNormalization D l hl E ((pull D l hl E x).obj K)).hom ≫
        normalized.derived.hom.app ((pull D l hl E x).obj K).obj.obj ≫
        (sections D l hl E).mapDerivedCategory.map
          ((a (LisseRealization.point D l hl)).integral.inv.app
            ((pull D l hl E x).obj K).obj) ≫
        (sections D l hl E).mapDerivedCategory.map
          ((r (LisseRealization.point D l hl) X x).comparison.hom.app K ≫
            (ContinuousRational.derivedPull x (coefficientPull l E x)).map e.hom ≫
            ((r (LisseRealization.point D l hl) X x).normalized.degree_zero _
              (((a X).image _).mpr ⟨K, hK, ⟨Iso.refl _⟩⟩)).hom) ≫
        (Functor.mapDerivedCategorySingleFunctor (sections D l hl E) 0).hom.app _
  degree_zero : ∀ (X : Base D l hl)
    (x : (LisseRealization.point D l hl).scheme ⟶ X.scheme)
    (K : Raw D l hl E X) (hK : Lisse D l hl E X K),
    (DerivedCategory.homologyFunctor _ 0).map (comparison X x K hK).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app _ =
    ((ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategoryHomologyFunctorIso 0).inv.app
        ((pointRationalFibre D l hl E).obj ((pull D l hl E x).obj K)).obj ≫
      point.comparison.hom.app
        ⟨_, (r (LisseRealization.point D l hl) X x).lisse.preserves K hK⟩ ≫
      (sections D l hl E).map
        ((r (LisseRealization.point D l hl) X x).lisse.comparison K hK).hom
  finite : ∀ (X : Base D l hl)
    (x : (LisseRealization.point D l hl).scheme ⟶ X.scheme)
    (K : Raw D l hl E X) (_hK : Lisse D l hl E X K),
    FiniteDimensional E ((sections D l hl E).obj
      ((ordinaryPull l E x).obj (((a X).sheaf D l hl E).obj K)))
  naturality : ∀ (X : Base D l hl)
    (x : (LisseRealization.point D l hl).scheme ⟶ X.scheme)
    (K L : Raw D l hl E X) (hK : Lisse D l hl E X K) (hL : Lisse D l hl E X L)
    (f : K ⟶ L),
    (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory.map
        (((pointRationalFibre D l hl E ⋙ (DerivedCategory.pointFiniteDimensional E).ι).map
          ((pull D l hl E x).map f))) ≫
      (comparison X x L hL).hom = (comparison X x K hK).hom ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((sections D l hl E).map ((ordinaryPull l E x).map
            (((a X).sheaf D l hl E).map f)))

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]

/-- The actual scalar square at the point. The left comparison is the recorded phi
(inverting sections-tensor followed by completion); the right one uses the same
completion map through FieldNormalized. The ordinary and derived counit equations
fix the intervening sections comparison on all fractions.
Source: BS 6.8.14(2), 6.8.15 (blueprint: lem-tw-lisse-point-sections-realization). -/
structure PointSectionsScalarCompatibility
    (aE : ∀ X : Base D l hl, At D l hl E X)
    (tE : ∀ X : Base D l hl, RealizationTensorComparison D l hl E X (aE X))
    (rE : ∀ (X Y : Base D l hl) (f : X.scheme ⟶ Y.scheme),
      RealizationPullComparison D l hl E f (aE X) (aE Y))
    (nE : PointSectionsRealization D l hl E aE tE rE)
    (aF : ∀ X : Base D l hl, At D l hl F X)
    (tF : ∀ X : Base D l hl, RealizationTensorComparison D l hl F X (aF X))
    (rF : ∀ (X Y : Base D l hl) (f : X.scheme ⟶ Y.scheme),
      RealizationPullComparison D l hl F f (aF X) (aF Y))
    (nF : PointSectionsRealization D l hl F aF tF rF)
    (i : E →ₐ[ℚ_[l]] F)
    (b : FieldChange D l hl E F i (point D l hl) (aE (point D l hl)) (aF (point D l hl)))
    (nb : FieldNormalized D l hl E F i (point D l hl)
      (aE (point D l hl)) (aF (point D l hl)) b) where
  [additiveE : (LisseRealization.sections D l hl E).Additive]
  [limitsE : PreservesFiniteLimits (LisseRealization.sections D l hl E)]
  [colimitsE : PreservesFiniteColimits (LisseRealization.sections D l hl E)]
  [additiveF : (LisseRealization.sections D l hl F).Additive]
  [limitsF : PreservesFiniteLimits (LisseRealization.sections D l hl F)]
  [colimitsF : PreservesFiniteColimits (LisseRealization.sections D l hl F)]
  ordinary : sections D l hl E ⋙ ModuleCat.extendScalars.{u, u, u + 1} i.toRingHom ≅
    pbcExtend b.coefficient ⋙ sections D l hl F
  sections : ∀ (M : Modules D l hl E (point D l hl)) (c : F)
    (m : (LisseRealization.sections D l hl E).obj M),
    ordinary.hom.app M (c ⊗ₜ[E, i.toRingHom] m) =
      pbcTensorSection b.coefficient M (op (ProEt.mk (𝟙 _))) (pointConstants D l F c) m
  derived : (LisseRealization.sections D l hl E).mapDerivedCategory ⋙
      pointCoefficientFieldDerivedTensor l E F i ≅
    pbcDerivedExtend b.coefficient ⋙ (LisseRealization.sections D l hl F).mapDerivedCategory
  derived_normalized : ∀ P : CochainComplex (Modules D l hl E (point D l hl)) ℤ,
    derived.hom.app (DerivedCategory.Q.obj P) ≫
        (LisseRealization.sections D l hl F).mapDerivedCategory.map
          (pbcComplexCounit b.coefficient P) ≫
        (LisseRealization.sections D l hl F).mapDerivedCategoryFactors.hom.app
          (((pbcExtend b.coefficient).mapHomologicalComplex (.up ℤ)).obj P) =
      (pointCoefficientFieldDerivedTensor l E F i).map
          ((LisseRealization.sections D l hl E).mapDerivedCategoryFactors.hom.app P) ≫
        (ModuleCat.extendScalars.{u, u, u + 1} i.toRingHom).mapDerivedCategoryFactors.hom.app
          (((LisseRealization.sections D l hl E).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)
  square : ∀ C : sfIntegralConstructibleCategory l E (point D l hl).scheme,
    HEq
      ((pointRationalSectionsScalarExtensionIso l E F i D hl C.obj
          ((pointIntegralConstructible_iff l E D hl C.obj).mpr C.property)).hom ≫
        (pointCoefficientFieldDerivedTensor l E F i).map
          (nE.normalized.derived.hom.app C.obj ≫
            (LisseRealization.sections D l hl E).mapDerivedCategory.map
              ((aE (point D l hl)).integral.inv.app C)) ≫
        derived.hom.app ((aE (point D l hl)).J.obj
          ((sfRationalConstructibleLocalization l E (point D l hl).scheme).obj C)))
      (nF.normalized.derived.hom.app
          ((sfConstructibleIntegralScalarExtension D.p l hl E F i
            (point D l hl).scheme).obj C).obj ≫
        (LisseRealization.sections D l hl F).mapDerivedCategory.map
          ((aF (point D l hl)).integral.inv.app
              ((sfConstructibleIntegralScalarExtension D.p l hl E F i
                (point D l hl).scheme).obj C) ≫
            (aF (point D l hl)).J.map
              (eqToHom ((sfRationalScalarExtension_existsUnique l E (point D l hl).scheme
                D.p hl F i).exists.choose_spec.2.1
                  ((sfRationalConstructibleLocalization l E
                    (point D l hl).scheme).obj C)).symm) ≫
            nb.derived.hom.app
              ((sfRationalConstructibleLocalization l E (point D l hl).scheme).obj C)))
  pullback : ∀ (X : Base D l hl)
    (x : (point D l hl).scheme ⟶ X.scheme)
    (bX : FieldChange D l hl E F i X (aE X) (aF X))
    (_nbX : FieldNormalized D l hl E F i X (aE X) (aF X) bX),
    Mixed D l hl E F i x (aE (point D l hl)) (aE X) (aF (point D l hl)) (aF X)
      (rE (point D l hl) X x).lisse (rF (point D l hl) X x).lisse b bX

/-- The sections-localization comparison and its tensor-compatible point specialization.

Source: Bhatt--Scholze, Lemma 6.8.12, Proposition 6.8.14(2), Remark 6.8.15;
Stacks 03EL, 07A4, 0A8X (blueprint: lem-tw-lisse-point-sections-realization).

Proof:
1. Continuous coefficients at the one-point scheme identify B(s) with R and A(s)
with E by evaluation, inverse to constants. The point ringed-evaluation model,
lem-sf-point-ringed-evaluation-model, identifies sections with exact ringed-point
pullback. Its scalar tensor comparison, together with exact localization
(lem-tw-lisse-localization-restriction and lem-weil-coefficient-complex-rationalization),
shows that the ordinary map c tensor z to c(1 tensor z) is an isomorphism.
2. Apply this map termwise. It commutes with differentials and preserves
quasi-isomorphisms by lem-weil-point-proetale-sections-exact. Naturality for a
roof follows by composing chain naturality with the inverse of its quasi-isomorphism.
This gives precisely PointNormalized.derived and its representative equation.
3. Specialize lem-sfb-derived-internal-hom-sections-model to the coefficient unit.
Evaluation at 1 identifies its Hom complex with sections, inverse z to (b to bz).
Under these identifications the homology map in every integer degree sends
f tensor c to c F(f), because both evaluate at 1 to c(1 tensor z).
4. For x and lisse K, use the specified comparison of
lem-tw-lisse-tensor-pullback-realization and its normalized degree-zero identification.
Compose size descent, lambda, the inverse integral realization, sections of this
pullback comparison, and exact sections of a single object. This is the displayed
comparison_normalized equation. It is natural on rational arrows by the fraction
formula for realization and the recorded fibre. Its H^0 map is exactly the square
of def-real-lisse-point-normalization, followed by ordinary module pullback.
5. By lem-weil-point-sections-finiteness the source has finite-dimensional
cohomology. The target is in degree zero, so both are finite-dimensional there.
6. The point evaluation tensor map and realization tensor map are the same
localization-and-sections construction. Their inverse sends x tensor y to the
pure section tensor, and their unit sends 1 to 1. The normalized pullback map
respects these tensors: by lem-tw-lisse-scalar-comparison-coherence, or directly
on pulled-back local bases, both composites send e_i tensor e_j to that tensor.
Equality is local, so the square holds globally. The empty sum gives the zero map.
7. The finite-coefficient compatibility is stated separately below, using the
specified sections-scalar comparison of lem-weil-point-sections-scalar-extension.
Its completion maps cancel against those in the normalized realization scalar map,
leaving ordinary multiplication of scalars. No new fibre or arbitrary vector-space
identification is chosen. -/
theorem lisse_point_sections_realization
    (a : ∀ X : Base D l hl, At D l hl E X)
    (t : ∀ X : Base D l hl, RealizationTensorComparison D l hl E X (a X))
    (r : ∀ (X Y : Base D l hl) (f : X.scheme ⟶ Y.scheme),
      RealizationPullComparison D l hl E f (a X) (a Y)) :
    Nonempty (PointSectionsRealization D l hl E a t r) := by
  sorry

/-- Finite coefficient extension commutes with this same point normalization through
phi, the stipulated inverse sections/completion map. The counit equation states that
the scalar comparison is termwise the ordinary balanced tensor map, including all
field fractions. Taking H^0 and conjugating by the specified size-descent normalization
gives the scalar square for the recorded fibre and the lisse comparison at x.

Source: BS 6.8.14(2), 6.8.15 (blueprint: lem-tw-lisse-point-sections-realization).

Proof: use step 7 above. Both the recorded phi and FieldNormalized invert the
same chi, so completion cancels. The remaining scalar associator sends
(z tensor a) tensor b to z tensor (ab) along either route. Naturality on integral
arrows extends to every rational arrow by scalar linearity. The specified
pointRationalFibreScalarIso is conjugate to precisely this phi under size descent,
so the same square holds for Fib. Compatibility of the specified realization
pullback with finite scalar extension is retained in the pullback field, including
its balanced-section formula and actual compatibility equation at every x. Combining
that equation with square and comparison_normalized gives the scalar square for
the displayed derived point comparison at every x. The
identity and tower equations reduce to those of phi and scalar associators;
this includes equal fields and ramified extensions with unrelated uniformizers. -/
theorem lisse_point_sections_scalar_compatibility
    (aE : ∀ X : Base D l hl, At D l hl E X)
    (tE : ∀ X : Base D l hl, RealizationTensorComparison D l hl E X (aE X))
    (rE : ∀ (X Y : Base D l hl) (f : X.scheme ⟶ Y.scheme),
      RealizationPullComparison D l hl E f (aE X) (aE Y))
    (nE : PointSectionsRealization D l hl E aE tE rE)
    (aF : ∀ X : Base D l hl, At D l hl F X)
    (tF : ∀ X : Base D l hl, RealizationTensorComparison D l hl F X (aF X))
    (rF : ∀ (X Y : Base D l hl) (f : X.scheme ⟶ Y.scheme),
      RealizationPullComparison D l hl F f (aF X) (aF Y))
    (nF : PointSectionsRealization D l hl F aF tF rF)
    (i : E →ₐ[ℚ_[l]] F)
    (b : FieldChange D l hl E F i (point D l hl) (aE (point D l hl)) (aF (point D l hl)))
    (nb : FieldNormalized D l hl E F i (point D l hl)
      (aE (point D l hl)) (aF (point D l hl)) b) :
    Nonempty (PointSectionsScalarCompatibility D l hl E F aE tE rE nE aF tF rF nF i b nb) := by
  sorry

end WeilConjectures.LisseRealization
