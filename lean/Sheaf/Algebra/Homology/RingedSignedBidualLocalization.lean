/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.Paper.DerivedInternalHomFilteredColimitData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Signed ordinary biduality and the two augmentation comparisons

Source: Stacks Project, sites-cohomology.tex, Tags 0A8X, 0A92 and 0A97
(blueprint: lem-sfb-ringed-signed-bidual-localization).

The statement uses only the prerequisite product Hom complex, coefficient unit,
fixed augmentation and localization factorization. It gives a family of actual chain
maps with uniqueness, zero product components, naturality, and the localization equation.
The comparison isomorphisms are fixed by their displayed homs.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

/-- Signed ordinary biduality is natural and agrees with the derived evaluation transpose
under the two fixed augmentation comparisons, without a flatness hypothesis.

Source: Stacks Project, sites-cohomology.tex, Tags 0A8X (section-hom-complexes),
0A92 (lemma-evaluate-and-more) and 0A97 (lemma-internal-hom-evaluate)
(blueprint: lem-sfb-ringed-signed-bidual-localization).

Proof plan, following the node's eight steps:
1. Use the actual Hom-product projections and localized sheaf Hom. For x in degree a,
   its q-component sends phi to (-1)^(a*q) phi(x) when a+q=0. Evaluation commutes
   with every restriction and is linear. All other coefficient-degree targets are zero.
   Product and sheaf-Hom extensionality give uniqueness, without summing components.
2. For q=-a-1 the Hom differential gives d_D(phi)=-(-1)^q phi d_E. Consequently
   d_B beta(x) has sign (-1)^(a+1+a*(q+1)+q+1)=(-1)^((a+1)*q), the sign of
   beta(d_E x). In other degrees both targets vanish. This proves the chain-map identity.
3. For f:E to E', both naturality composites evaluate to (-1)^(a*q) phi(f(x)).
   Check all localized sections and product projections to obtain the chain-map equality.
4. Put I=I(O). The hypotheses make Hom(E,eta_O) and Hom(D,eta_O) quasi-isomorphisms.
   Their localizations followed by the inverse fixed Hom factorization are gamma_E
   and gamma_D. Use the fixed K-injective comparison throughout (0A95, 08J7).
5. Choose K-flat flat-term resolutions p:P to E and t:T to D (06YS). The chain maps
   g=Hom(p,I) Hom(E,eta_O) t and h=Hom(t,I) Hom(D,eta_O) beta_E p localize to
   H(Qp,O) gamma_E Qt and H(Qt,O) gamma_D Q(beta_E) Qp respectively.
6. The stipulated uncurrying model on T,P identifies the uncurrying of Qg with
   epsilon_(QE,O) after (gamma_E Qt tensor Qp). On generators its chain model is
   u(tau tensor x)=eta_O(t(tau)(p(x))), followed by the inverse localized augmentation.
7. Apply the same model on P,T to h. Its chain model v(x tensor tau) is
   (-1)^(a*q) u(tau tensor x), and is zero off a+q=0. Thus v=u after the actual
   signed total-tensor swap. Sheafification and coproduct inclusions determine these
   maps, and the recorded symmetry normalization identifies their derived images.
8. Transposition naturality and symmetry naturality give exactly this same uncurrying
   for H(Qt,O) H(gamma_E,O) b_(QE) Qp. Injectivity of transposition identifies it
   with Qh; cancel Qp and H(Qt,O). Neither E nor D was assumed K-flat, bounded or perfect.
-/
theorem ringed_signed_bidual_localization
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (s : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (_coherence : RingedDerivedTensorCoherence.{c, v, u, w} J R S T s) :
    ∃ β : ∀ E : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ,
        E ⟶ homComplex (R := R)
          (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
          (ringedTensorUnitComplex.{c, v, u} J R),
      ∀ E : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ,
        (∀ (a q : ℤ) (h : a + q = 0) (h' : q + a = 0) (U : Cᵒᵖ)
          (x : (E.X a).val.obj U) (W : (Over U.unop)ᵒᵖ)
          (φ : ((homComplex (R := R) E
            (ringedTensorUnitComplex.{c, v, u} J R)).X q).val.obj (op W.unop.left)),
          (((coefficientHomComponent.{u, c, v} J R
            (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
            (ringedTensorUnitComplex.{c, v, u} J R) a q 0 h').val.app U
              (((β E).f a).val.app U x)).app W).hom φ =
            (a * q).negOnePow •
              (((coefficientHomComponent.{u, c, v} J R E
                (ringedTensorUnitComplex.{c, v, u} J R) q a 0 h).val.app
                  (op W.unop.left) φ).app (op (Over.mk (𝟙 W.unop.left)))).hom
                    ((E.X a).val.map W.unop.hom.op x)) ∧
        (∀ β' : E ⟶ homComplex (R := R)
            (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
            (ringedTensorUnitComplex.{c, v, u} J R),
          (∀ (a q : ℤ) (h : a + q = 0) (h' : q + a = 0) (U : Cᵒᵖ)
            (x : (E.X a).val.obj U) (W : (Over U.unop)ᵒᵖ)
            (φ : ((homComplex (R := R) E
              (ringedTensorUnitComplex.{c, v, u} J R)).X q).val.obj (op W.unop.left)),
            (((coefficientHomComponent.{u, c, v} J R
              (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
              (ringedTensorUnitComplex.{c, v, u} J R) a q 0 h').val.app U
                ((β'.f a).val.app U x)).app W).hom φ =
              (a * q).negOnePow •
                (((coefficientHomComponent.{u, c, v} J R E
                  (ringedTensorUnitComplex.{c, v, u} J R) q a 0 h).val.app
                    (op W.unop.left) φ).app (op (Over.mk (𝟙 W.unop.left)))).hom
                      ((E.X a).val.map W.unop.hom.op x)) →
          β' = β E) ∧
        (∀ (a q k : ℤ) (h : q + a = k) (_hk : k ≠ 0),
          (β E).f a ≫ coefficientHomComponent.{u, c, v} J R
            (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
            (ringedTensorUnitComplex.{c, v, u} J R) a q k h = 0) ∧
        (∀ (E' : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) (f : E ⟶ E'),
          f ≫ β E' = β E ≫
            ((homComplexFunctor (R := R)).map
              (((homComplexFunctor (R := R)).map f.op).app
                (ringedTensorUnitComplex.{c, v, u} J R)).op).app
                  (ringedTensorUnitComplex.{c, v, u} J R)) ∧
        (∀ (_hE : QuasiIso (((homComplexFunctor (R := R)).obj (op E)).map
              ((SfbHomFilteredColimit.resolutionUnit.{c, v, u} J R).app
                (ringedTensorUnitComplex.{c, v, u} J R))))
          (_hD : QuasiIso (((homComplexFunctor (R := R)).obj
              (op (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)))).map
                ((SfbHomFilteredColimit.resolutionUnit.{c, v, u} J R).app
                  (ringedTensorUnitComplex.{c, v, u} J R)))),
          ∃ γE : DerivedCategory.Q.obj
              (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)) ≅
            (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
              (op (DerivedCategory.Q.obj E),
                DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)),
          ∃ γD : DerivedCategory.Q.obj (homComplex (R := R)
              (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
              (ringedTensorUnitComplex.{c, v, u} J R)) ≅
            (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
              (op (DerivedCategory.Q.obj
                (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))),
                DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)),
            γE.hom = DerivedCategory.Q.map
              (((homComplexFunctor (R := R)).obj (op E)).map
                ((SfbHomFilteredColimit.resolutionUnit.{c, v, u} J R).app
                  (ringedTensorUnitComplex.{c, v, u} J R))) ≫
              (coefficientHomResolutionIso.{u, c, v, w} J R E
                (ringedTensorUnitComplex.{c, v, u} J R)).inv ∧
            γD.hom = DerivedCategory.Q.map
              (((homComplexFunctor (R := R)).obj
                (op (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)))).map
                  ((SfbHomFilteredColimit.resolutionUnit.{c, v, u} J R).app
                    (ringedTensorUnitComplex.{c, v, u} J R))) ≫
              (coefficientHomResolutionIso.{u, c, v, w} J R
                (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
                (ringedTensorUnitComplex.{c, v, u} J R)).inv ∧
            S.transpose (DerivedCategory.Q.obj E)
                ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
                  (op (DerivedCategory.Q.obj E),
                    DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)))
                (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))
                ((s.braiding (DerivedCategory.Q.obj E)
                  ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
                    (op (DerivedCategory.Q.obj E),
                      DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)))).hom ≫
                  S.evaluation (DerivedCategory.Q.obj E)
                    (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))) ≫
              (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
                (Prod.mkHom γE.hom.op
                  (𝟙 (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)))) =
            DerivedCategory.Q.map (β E) ≫ γD.hom) := by
  sorry

end CategoryTheory
