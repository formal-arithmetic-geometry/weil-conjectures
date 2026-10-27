/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.CategoryTheory.SheafPolynomialCotangentComparison
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import Sheaf.CategoryTheory.Sites.InverseImageDifferentials
import Sheaf.SecSmoothPurity.CochainInverseComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Geometric inverse image of the naive cotangent complex

Source: Stacks Project, Modules on Sites, Tag 08TZ (lemma-pullback-NL), using
Tag 08TY's standard polynomial presentation
(blueprint: lem-sfb-topos-naive-cotangent-pullback).

The comparison retains its polynomial normalization and the formulas on conormal
classes and universal differential tensors. Its derived isomorphism is the localization
of the resulting actual chain isomorphism. The termwise inverse image is recorded with
its degree identifications, avoiding any extra exactness assumption on inverse image.
The underlying set sheaves and the compatibility of the transported ring map are
written through the algebraic inverse-image interface
(def-weil-pbc-algebraic-inverse-image) itself.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SheafPolynomialCotangent

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {L : GrothendieckTopology D}

/-- The variable inclusion into the sheaf polynomial algebra, in the lifted set
universe of algebraic inverse image. Source: Stacks 08TY and 08TZ
(blueprint: lem-sfb-topos-naive-cotangent-pullback). -/
def liftedVariables (A : Sheaf J CommRingCat.{u}) (E : Sheaf J (Type u)) :
    (sheafCompose J uliftFunctor.{u, u}).obj E ⟶
      (sheafCompose J (forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj
        (polynomialSheaf A E) where
  hom :=
    { app := fun U ↦ TypeCat.ofHom (fun e ↦ ULift.up
        ((toSheafify J (polynomials A E)).app U (MvPolynomial.X e.down)))
      naturality := by
        intro U V r
        ext e
        apply congrArg ULift.up
        have h := ConcreteCategory.congr_hom
          ((toSheafify J (polynomials A E)).naturality r) (MvPolynomial.X e.down)
        change (toSheafify J (polynomials A E)).app V
            (MvPolynomial.X (E.obj.map r e.down)) =
          (polynomialSheaf A E).obj.map r
            ((toSheafify J (polynomials A E)).app U (MvPolynomial.X e.down))
        change (toSheafify J (polynomials A E)).app V
            ((polynomials A E).map r (MvPolynomial.X e.down)) =
          (polynomialSheaf A E).obj.map r
            ((toSheafify J (polynomials A E)).app U (MvPolynomial.X e.down)) at h
        simpa [polynomials] using h }

/-- A canonical inverse-image comparison of the standard two-term complexes.
The polynomial lift preserves coefficients, variables and evaluation. The two formulas
specify its conormal and differential components on all generalized sections, including
sections that do not come from global sections of a site object.
Source: Stacks 08TZ, with the presentations of 08TY
(blueprint: lem-sfb-topos-naive-cotangent-pullback). -/
structure InverseComparison
    (g : GeometricMorphism (Sheaf L (Type u)) (Sheaf J (Type u)))
    {A B : Sheaf J CommRingCat.{u}} {AI BI : Sheaf L CommRingCat.{u}}
    (f : A ⟶ B) (fi : AI ⟶ BI)
    (IA : SheafOfModules.AlgebraicInverseImageOfUniverses.{u, u, u, u, u, u} g.inverse A AI)
    (IB : SheafOfModules.AlgebraicInverseImageOfUniverses.{u, u, u, u, u, u} g.inverse B BI)
    (K : Model (canonical f)) (KI : Model (canonical fi)) where
  polynomial : SheafOfModules.AlgebraicInverseImageOfUniverses.{u, u, u, u, u, u}
    g.inverse
    (polynomialSheaf A (sets B)) (polynomialSheaf AI (sets BI))
  coefficients :
    g.inverse.map ((sheafCompose J (forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map
        (base A (sets B))) ≫ polynomial.ringUnderlying.hom =
      IA.ringUnderlying.hom ≫
        (sheafCompose L (forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map (base AI (sets BI))
  generatorCompatibility :
    g.inverse.map (liftedVariables A (sets B)) ≫ polynomial.ringUnderlying.hom =
    IB.ringUnderlying.hom ≫ liftedVariables AI (sets BI)
  evaluation :
    g.inverse.map ((sheafCompose J (forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map
        (evaluation f (𝟙 (sets B)))) ≫ IB.ringUnderlying.hom =
      polynomial.ringUnderlying.hom ≫
        (sheafCompose L (forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map
          (evaluation fi (𝟙 (sets BI)))
  components : ∀ n : ℤ, IB.modules.obj (K.complex.X n) ≅ KI.complex.X n
  differential : ∀ i j : ℤ,
    IB.modules.map (K.complex.d i j) ≫ (components j).hom =
      (components i).hom ≫ KI.complex.d i j
  conormal : ∀ (T : Sheaf J (Type u))
    (p : T ⟶ (sheafCompose J (forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj
      (polynomialSheaf A (sets B)))
    (q : T ⟶ (sheafCompose J (forget AddCommGrpCat.{u} ⋙ uliftFunctor.{u, u})).obj
      ((SheafOfModules.toSheaf _).obj (K.complex.X (-1)))),
    (∀ (U : Cᵒᵖ) (t : T.obj.obj U),
      ∃ j : (kernelIdeal (canonical f)).sections U.unop,
        (p.hom.app U t).down = j.val ∧
        (q.hom.app U t).down = K.quotient.val.app U j) →
    ∀ (V : Dᵒᵖ) (t : (g.inverse.obj T).obj.obj V)
      (j : (kernelIdeal (canonical fi)).sections V.unop),
      (polynomial.ringUnderlying.hom.hom.app V ((g.inverse.map p).hom.app V t)).down = j.val →
      ((components (-1)).hom.val.app V)
        ((IB.moduleUnderlying.inv.app (K.complex.X (-1))).hom.app V
          ((g.inverse.map q).hom.app V t)).down = KI.quotient.val.app V j
  tensors : ∀ (T : Sheaf J (Type u))
    (b : T ⟶ (sheafCompose J (forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj B)
    (p : T ⟶ (sheafCompose J (forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj
      (polynomialSheaf A (sets B)))
    (z : T ⟶ (sheafCompose J (forget AddCommGrpCat.{u} ⋙ uliftFunctor.{u, u})).obj
      ((SheafOfModules.toSheaf _).obj (K.complex.X 0))),
    (∀ (U : Cᵒᵖ) (t : T.obj.obj U),
      (z.hom.app U t).down = K.degreeZero.inv.val.app U
        (tensorD (canonical f) U (b.hom.app U t).down (p.hom.app U t).down)) →
    ∀ (V : Dᵒᵖ) (t : (g.inverse.obj T).obj.obj V),
      KI.degreeZero.hom.val.app V
        (((components 0).hom.val.app V)
          ((IB.moduleUnderlying.inv.app (K.complex.X 0)).hom.app V
            ((g.inverse.map z).hom.app V t)).down) =
        tensorD (canonical fi) V
          (IB.ringUnderlying.hom.hom.app V ((g.inverse.map b).hom.app V t)).down
          (polynomial.ringUnderlying.hom.hom.app V ((g.inverse.map p).hom.app V t)).down
  pulled : CochainComplex (ringedSiteModules.{u} (siteModuleRings BI)) ℤ
  pulledDegree : ∀ n : ℤ, pulled.X n ≅ IB.modules.obj (K.complex.X n)
  pulledDifferential : ∀ i j : ℤ,
    pulled.d i j ≫ (pulledDegree j).hom =
      (pulledDegree i).hom ≫ IB.modules.map (K.complex.d i j)
  chainIso : pulled ≅ KI.complex
  chainIso_components : ∀ n : ℤ,
    chainIso.hom.f n = (pulledDegree n).hom ≫ (components n).hom
  derivedIso : (localization BI).obj pulled ≅ (localization BI).obj KI.complex
  derivedIso_eq : derivedIso = (localization BI).mapIso chainIso

/-- Geometric inverse image commutes canonically with the standard naive cotangent
complex, in the derived category of modules over the transported ring.
Source: Stacks Project, Modules on Sites, Tag 08TZ (lemma-pullback-NL)
(blueprint: lem-sfb-topos-naive-cotangent-pullback).

Proof, following the five DAG steps:
1. The polynomial comparison preserves coefficients, generators and evaluation
   (lem-trf-geometric-standard-differential-comparison). Exact inverse image identifies
   the evaluation kernel with the target kernel (lem-trf-geometric-inverse-image-exact).
2. The kernel square is the image of multiplication on the tensor square of the kernel.
   Local tensor representations identify this image with locally finite sums of products
   (lem-pc-sites-sheaf-tensor-bilinear-universal, def-pur-sheaf-tensor-product and
   lem-weil-pbc-site-sheafification-sections-local). Inverse image preserves the tensor
   pairing and its image (lem-pur-independent-inverse-image-tensor-comparison and
   lem-trf-geometric-inverse-image-exact), hence preserves this square.
3. Exactness identifies the quotient by that square, with its transported scalar action.
   The resulting isomorphism is the displayed formula on generalized conormal classes.
4. The differential comparison preserves the universal derivation
   (lem-trf-topos-inverse-image-differentials). Combine it with the tensor comparison
   to obtain the degree-zero isomorphism and its displayed differential-tensor formula.
5. Both composites with the conormal quotient send j to dj tensor 1. This quotient
   remains an epimorphism by exactness, so cancellation proves the differential square.
   The components give an actual chain isomorphism of the termwise inverse image with
   the target standard complex. Apply the localization of def-weil-abstract-derived-category
   to this chain isomorphism to obtain exactly the asserted derived isomorphism.
-/
theorem inverseImage_naiveCotangent
    (g : GeometricMorphism (Sheaf L (Type u)) (Sheaf J (Type u)))
    {A B : Sheaf J CommRingCat.{u}} {AI BI : Sheaf L CommRingCat.{u}}
    (f : A ⟶ B) (fi : AI ⟶ BI)
    (IA : SheafOfModules.AlgebraicInverseImageOfUniverses.{u, u, u, u, u, u} g.inverse A AI)
    (IB : SheafOfModules.AlgebraicInverseImageOfUniverses.{u, u, u, u, u, u} g.inverse B BI)
    (_hf : g.inverse.map ((sheafCompose J (forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map f) ≫
        IB.ringUnderlying.hom =
      IA.ringUnderlying.hom ≫
        (sheafCompose L (forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map fi)
    (K : Model (canonical f)) (KI : Model (canonical fi)) :
    Nonempty (InverseComparison g f fi IA IB K KI) := by
  sorry

end CategoryTheory.SheafPolynomialCotangent
