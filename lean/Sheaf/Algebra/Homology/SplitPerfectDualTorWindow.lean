/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients

/-! # Signed duals and Tor windows for split-perfect sheaf complexes

Source: Stacks Project, sites-cohomology.tex, Tags 08JH, 08JJ and 08G1.
(blueprint: lem-sfb-split-perfect-dual-tor-window).
The dual is the recorded product Hom complex. The projection below fixes its
identification with the dual of the term in the opposite degree, including the sign.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- The canonical projection from degree `n` of `Hom(E,R[0])` to `Hom(E^(-n),R)`.
It is the product projection followed by the canonical identification `R[0]^0 ≅ R`.
Source: Stacks Project, Tag 08JJ and Section 0A8X, Hom complexes.
(blueprint: lem-sfb-split-perfect-dual-tor-window). -/
def splitPerfectDualProjection
    (E : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ) (n : ℤ) :
    (homComplex.{c, v, max c v r, max c v r} (R := R) E
      (ringedTensorUnitComplex.{c, v, r} J R)).X n ⟶
      SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) (E.X (-n))
        (SheafOfModules.unit.{v, c, max c v r} ((sheafCompose J (forget₂ CommRingCat.{max c v r}
            RingCat.{max c v r})).obj R)) :=
  homComplexπ.{c, v, max c v r, max c v r} (R := R) E (ringedTensorUnitComplex.{c, v, r} J R) n
      (-n) 0
      (neg_add_cancel n) ≫
    SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (E.X (-n)))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (SheafOfModules.unit.{v, c, max c v r} ((sheafCompose J (forget₂ CommRingCat.{max c v r}
            RingCat.{max c v r})).obj R))).hom

/-- A bounded finite-free-retract complex and its signed dual have the stated Tor windows.
Source: Stacks Project, Tags 08JH, 08JJ and 08G1, implication (2) to (1).
(blueprint: lem-sfb-split-perfect-dual-tor-window).

Proof:
1. Apply lem-sfb-ringed-site-finite-retract-dual-exact to every degree of the specified
   package. Internal Hom from that term is a retract of a finite-power functor and is exact.
2. Tensor by a finite-free retract is likewise a natural retract of a finite-power functor.
   A finite direct sum preserves short exact sequences; local lifts for its finitely many
   coordinates have a common refinement. Include, lift, and project to prove exactness
   of the retract. This proves tensor exactness and def-pc-flat-sheaf-modules flatness.
3. Apply lem-pc-bounded-exact-term-hom-quasi-iso to each K-injective resolution of R[0].
   The comparison is a quasi-isomorphism even for unbounded targets. With the fixed
   resolution of def-pur-derived-internal-hom, it identifies the ordinary dual with RHom.
4. By lem-sfb-ringed-site-bounded-dual-components, the surviving product projection is
   invertible, its differential is (-1)^(n+1) times precomposition, and its support is
   [-b,-a]. The target complex R[0] contributes no differential.
5. Dualize the given degreewise splitting using precomposition by p and then i. Their
   composite is identity. The coordinate-dual isomorphism identifies the middle object
   with the same finite power of R. Apply step 2 to these retracts to obtain flat dual terms.
6. Apply lem-weil-pbc-independent-bounded-flat-kflat to E and its dual. Then
   lem-sf-ringed-kflat-single-tensor-comparison identifies tensor with any M[0] with the
   ordinary termwise tensor complex; M itself need not be flat.
7. Those tensor complexes have zero terms outside [a,b] and [-b,-a]. Kernels and images
   at those degrees are zero. The representing isomorphisms and
   def-weil-derived-cohomology-sheaves give the two cohomology vanishings below.
No constant coefficient, point, or constructibility assumption enters these arguments. -/
theorem splitPerfect_dual_torWindow
    [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
    (a b : ℤ) (_hab : a ≤ b)
    (E : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (_hE : ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (pE : SheafOfModules.StrictPerfectCoefficientPackageOnSite.{c, v, max c v r} _ E) :
    (∀ n : ℤ, exactFunctor _ _ (tensorLeft (E.X n)) ∧
      exactFunctor _ _ 
        ((SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).obj (op (E.X n)))) ∧
    (∀ (I : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (f : ringedTensorUnitComplex.{c, v, r} J R ⟶ I),
      I.IsKInjective → QuasiIso f →
        QuasiIso (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op E)).map f)) ∧
    Nonempty (DerivedCategory.Q.obj
      (homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedTensorUnitComplex.{c, v, r} J R)) ≅
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op (DerivedCategory.Q.obj E),
          DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, r} J R))) ∧
    (∀ n : ℤ, IsIso (splitPerfectDualProjection.{c, v, r} J R E n)) ∧
    (∀ n : ℤ,
      (homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedTensorUnitComplex.{c, v, r} J
          R)).d n (n + 1) ≫
          splitPerfectDualProjection.{c, v, r} J R E (n + 1) =
        (n + 1).negOnePow • (splitPerfectDualProjection.{c, v, r} J R E n ≫
          SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (E.d (-(n + 1)) (-n))
            (𝟙 (SheafOfModules.unit
              ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))))) ∧
    (∀ n : ℤ, n < -b ∨ -a < n →
      IsZero ((homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedTensorUnitComplex.{c, v,
          r} J R)).X n)) ∧
    (∀ n : ℤ,
      SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (pE.p (-n))
          (𝟙 (SheafOfModules.unit
            ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) ≫
        SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (pE.i (-n))
          (𝟙 (SheafOfModules.unit
            ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) =
          𝟙 _) ∧
    (∀ n : ℤ, Nonempty
      (SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R)
          (∏ᶜ fun _ : Fin (pE.N (-n)) ↦ SheafOfModules.unit
            ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
          (SheafOfModules.unit.{v, c, max c v r} ((sheafCompose J (forget₂ CommRingCat.{max c v r}
              RingCat.{max c v r})).obj R)) ≅
        (∏ᶜ fun _ : Fin (pE.N (-n)) ↦ SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))) ∧
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (J := J) (R := R) (E.X n) ∧
      SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (J := J) (R := R)
        ((homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedTensorUnitComplex.{c, v, r} J
            R)).X n)) ∧
    (∀ (M : RingedTensorModules.{c, v, r} J R) (q : ℤ),
      (q < a ∨ b < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((SheafOfModules.siteDerivedTensorIndependentCoefficients.{c, v, max c v r, w} J R).obj
          (DerivedCategory.Q.obj E,
            DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj M))))) ∧
      (q < -b ∨ -a < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((SheafOfModules.siteDerivedTensorIndependentCoefficients.{c, v, max c v r, w} J R).obj
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
            (op (DerivedCategory.Q.obj E),
              DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, r} J R)),
            DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj M)))))) := by
  sorry

end CategoryTheory
