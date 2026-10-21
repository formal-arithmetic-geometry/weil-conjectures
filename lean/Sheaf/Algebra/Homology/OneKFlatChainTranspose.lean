/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Algebra.Homology.RingedSliceEvaluationModels
public import Sheaf.Algebra.Homology.RingedTensorComplexConstraints
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap

/-! # Chain transposition with one K-flat tensor factor

Source: Stacks Project, Cohomology on Sites, Tags 08J9, 06YP, 06YT, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose).
The comparison extends the fixed two-K-flat normalization. The first complex is
arbitrary and unbounded. Hom uses the recorded product projections, and the pure
sections are the actual sheafification-unit and direct-sum generators.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe c v u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R))]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
  (T : CoefficientTensorModels.{u, c, v, w} J R S)

/-- The arbitrary-first-factor tensor comparison.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainComparison :=
  ∀ (A P : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ),
  CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P →
  (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R) (P.X n)) →
  (DerivedCategory.Q.obj ((coefficientTotalTensor.{u, c, v} J R).obj (A, P)) ≅
    S.tensor.obj (DerivedCategory.Q.obj A, DerivedCategory.Q.obj P))

/-- Agreement with the fixed normalization on two K-flat representatives.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainComparisonNormalization
    (comparison : OneKFlatChainComparison.{c, v, u, w} J R S) : Prop :=
  ∀ (A P : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ)
  (hA : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) A)
  (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P)
  (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R)
    (P.X n)),
  comparison A P hP hflat = T.iso J R S A P hA hP

/-- Naturality in the arbitrary first factor and the allowed second factor.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainComparisonNaturality
    (comparison : OneKFlatChainComparison.{c, v, u, w} J R S) : Prop :=
  ∀ (A A' P P' : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ)
  (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P)
  (hP' : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P')
  (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R)
    (P.X n))
  (hflat' : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R)
    (P'.X n))
  (a : A ⟶ A') (b : P ⟶ P'),
  DerivedCategory.Q.map ((coefficientTotalTensor.{u, c, v} J R).map (Prod.mkHom a b)) ≫
      (comparison A' P' hP' hflat').hom =
    (comparison A P hP hflat).hom ≫
      S.tensor.map (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b))

/-- Ordinary chain uncurrying into a K-injective target.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainUncurry :=
  ∀ (A P : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ),
  CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P →
  (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R) (P.X n)) →
  ∀ E : CochainComplex (SheafOfModules.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ,
    E.IsKInjective →
  (A ⟶ homComplex.{c, v, max c v u, max c v u} (R := R) P E) →
  ((coefficientTotalTensor.{u, c, v} J R).obj (A, P) ⟶ E)

/-- No sign is introduced in the ordered tensor A,P.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainUncurryPure
    (uncurry : OneKFlatChainUncurry.{c, v, u} J R) : Prop :=
  ∀ (A P E : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ)
  (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P)
  (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R)
    (P.X n))
  (hE : E.IsKInjective) (f : A ⟶ homComplex.{c, v, max c v u, max c v u} (R := R) P E)
  (n m k : ℤ) (h : n + m = k) (h' : m + n = k) (U : Cᵒᵖ)
  (x : (A.X n).val.obj U) (y : (P.X m).val.obj U),
  ((uncurry A P hP hflat E hE f).f k).val.app U
      (coefficientTensorGenerator.{u, c, v} J R A P n m k h U x y) =
    (((coefficientHomComponent.{u, c, v} J R P E n m k h').val.app U
      ((f.f n).val.app U x)).app (op (Over.mk (𝟙 U.unop)))).hom y

/-- The fixed derived transpose is represented by this chain map.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainTransposeEquation
    (comparison : OneKFlatChainComparison.{c, v, u, w} J R S)
    (uncurry : OneKFlatChainUncurry.{c, v, u} J R) : Prop :=
  ∀ (A P E : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ)
  (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P)
  (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R)
    (P.X n))
  (hE : E.IsKInjective) (f : A ⟶ homComplex.{c, v, max c v u, max c v u} (R := R) P E),
  (comparison A P hP hflat).hom ≫
      (S.transpose (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj E)).symm
          (DerivedCategory.Q.map f ≫
            DerivedCategory.Q.map
              (((homComplexFunctor.{c, v, max c v u, max c v u} (R := R)).obj (op P)).map
                (CategoryTheory.coefficientHomAugmentation.{c, v, u} J R E)) ≫
            (coefficientHomResolutionIso.{u, c, v, w} J R P E).inv) =
    DerivedCategory.Q.map (uncurry A P hP hflat E hE f)

/-- Simultaneous chain naturality, with the Hom source contravariant.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainUncurryNaturality
    (uncurry : OneKFlatChainUncurry.{c, v, u} J R) : Prop :=
  ∀ (A' A P' P E E' : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ)
  (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P)
  (hP' : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P')
  (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R)
    (P.X n))
  (hflat' : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R)
    (P'.X n))
  (hE : E.IsKInjective) (hE' : E'.IsKInjective)
  (a : A' ⟶ A) (b : P' ⟶ P) (e : E ⟶ E')
  (f : A ⟶ homComplex.{c, v, max c v u, max c v u} (R := R) P E),
  uncurry A' P' hP' hflat' E' hE'
      (a ≫ f ≫ ((homComplexFunctor.{c, v, max c v u, max c v u} (R := R)).map b.op).app E ≫
        ((homComplexFunctor.{c, v, max c v u, max c v u} (R := R)).obj (op P')).map e) =
    (coefficientTotalTensor.{u, c, v} J R).map (Prod.mkHom a b) ≫
      uncurry A P hP hflat E hE f ≫ e

/-- All tensor representative quasi-isomorphisms become invertible, even in P.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainTensorInverts : Prop :=
  ∀ (A A' P P' : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ)
  (a : A ⟶ A') (b : P ⟶ P'),
  CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P →
  CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P' →
  (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R) (P.X n)) →
  (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R) (P'.X n)) →
  QuasiIso a → QuasiIso b →
  IsIso (DerivedCategory.Q.map
    ((coefficientTotalTensor.{u, c, v} J R).map (Prod.mkHom a b)))

/-- Hom representative quasi-isomorphisms become invertible.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainHomInverts : Prop :=
  ∀ (P P' E E' : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ)
  (b : P' ⟶ P) (e : E ⟶ E'),
  CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P →
  CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P' →
  (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R) (P.X n)) →
  (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R) (P'.X n)) →
  E.IsKInjective → E'.IsKInjective → QuasiIso b → QuasiIso e →
  IsIso (DerivedCategory.Q.map
    (((homComplexFunctor.{c, v, max c v u, max c v u} (R := R)).map b.op).app E ≫
      ((homComplexFunctor.{c, v, max c v u, max c v u} (R := R)).obj (op P')).map e))

/-- The Hom identification used in transpose_eq is itself an isomorphism.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainHomComparisonIsIso : Prop :=
  ∀ (P E : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ),
  E.IsKInjective → IsIso
    (DerivedCategory.Q.map
        (((homComplexFunctor.{c, v, max c v u, max c v u} (R := R)).obj (op P)).map
          (CategoryTheory.coefficientHomAugmentation.{c, v, u} J R E)) ≫
      (coefficientHomResolutionIso.{u, c, v, w} J R P E).inv)

/-- The simultaneous one-K-flat comparison and its chain representatives, with their
normalization and all representative compatibility equations. This structure only
packages the conclusion; it supplies no additional hypothesis on a complex.
Source: Stacks 08J9, 06YU and 0A90 (blueprint: lem-sfb-hom-kflat-chain-transpose). -/
structure OneKFlatChainTransposeData where
  /-- The arbitrary-first-factor tensor comparison. -/
  comparison : OneKFlatChainComparison.{c, v, u, w} J R S
  /-- Agreement with the fixed normalization on two K-flat representatives. -/
  comparison_normalization : OneKFlatChainComparisonNormalization.{c, v, u, w} J R S T comparison
  /-- Naturality in the arbitrary first factor and the allowed second factor. -/
  comparison_naturality : OneKFlatChainComparisonNaturality.{c, v, u, w} J R S comparison
  /-- Ordinary chain uncurrying into a K-injective target. -/
  uncurry : OneKFlatChainUncurry.{c, v, u} J R
  /-- No sign is introduced in the ordered tensor A,P. -/
  uncurry_pure : OneKFlatChainUncurryPure.{c, v, u} J R uncurry
  /-- The fixed derived transpose is represented by this chain map. -/
  transpose_eq : OneKFlatChainTransposeEquation.{c, v, u, w} J R S comparison uncurry
  /-- Simultaneous chain naturality, with the Hom source contravariant. -/
  uncurry_naturality : OneKFlatChainUncurryNaturality.{c, v, u} J R uncurry
  /-- All tensor representative quasi-isomorphisms become invertible, even in P. -/
  tensor_inverts : OneKFlatChainTensorInverts.{c, v, u, w} J R
  /-- Hom representative quasi-isomorphisms become invertible. -/
  hom_inverts : OneKFlatChainHomInverts.{c, v, u, w} J R
  /-- The Hom identification used in transpose_eq is itself an isomorphism. -/
  hom_comparison_isIso : OneKFlatChainHomComparisonIsIso.{c, v, u, w} J R
  /-- Factor interchange is the actual Koszul braiding, with sign (-1)^(n*m). -/
  interchange_sign : CategoryTheory.RingedDerivedNative.symmetryPure.{c, v, u} J R

/-- An arbitrary unbounded first complex and one flat-term K-flat second complex
compute the fixed derived tensor and its ordinary chain evaluation transpose.
Source: Stacks Project, Tags 08J9, 06YP, 06YT, 06YU, 0A90 and 0A95
(blueprint: lem-sfb-hom-kflat-chain-transpose).

Proof:
1. For fixed P, K-flatness makes A ↦ Q(A tensor P) invert quasi-isomorphisms
   (lem-pur-kflat-tensor-quasiiso-independent). Factor it through localization
   (lem-weil-pbc-localization-universal-property). The equivalence from localized
   flat-term K-flat complexes (lem-weil-pbc-site-derived-tensor-descent) extends
   the fixed normalized two-K-flat comparison uniquely. For q:F→A a flat-term
   K-flat resolution (lem-pc-kflat-resolution), its value is the normalized
   comparison followed by Qq tensor 1 and preceded by Q(q tensor 1) inverse.
   This proves independence of q and naturality in both tensor arguments.
2. On each (n,m) summand define the bilinear evaluation (a,p) ↦ f(a)(p).
   Sheafify and use the direct-sum universal property. The Hom differential
   gives d(f(a)(p)) = f(da)(p) + (-1)^n f(a)(dp), exactly the tensor differential;
   thus this is a chain map without a sign in the order A,P (Tag 0A90).
3. The actual factor interchange sends a tensor p to (-1)^(n*m) p tensor a.
   The differential coefficients agree because (n+1)m = nm+m and
   n+n(m+1) = nm modulo two. Reversing the interchange multiplies by
   (-1)^(2nm)=1, so it is the Koszul symmetry (Tag 06YU).
4. For the fixed augmentation u:E→I(E), Hom(P,u) is a quasi-isomorphism
   between these Hom representatives since both targets are K-injective
   (lem-pur-rhom-well-defined). Its localization followed by the inverse
   fixed factorization is exactly the Hom identification in transpose_eq.
5. Precompose f with q:F→A and postcompose with Hom(P,u). The existing
   two-K-flat normalization identifies its chain transpose with
   u ∘ uncurry(f) ∘ (q tensor 1). Naturality of the given adjunction and
   the comparison from step 1 then permit cancellation of Q(q tensor 1),
   yielding transpose_eq for A. This is the same adjunction, not a new one.
6. For maps a:A'→A, b:P'→P, e:E→E', evaluation on each generator is
   e(f(a(x))(b(y))). The tensor and product universal properties give the
   displayed chain naturality. Localize it, using the natural fixed
   augmentation and Hom factorization, to obtain derived naturality.
7. For a quasi-isomorphism b:P'→P use q:F→A and the tensor square.
   Both vertical maps are quasi-isomorphisms by K-flatness of P and P'.
   The top map is one by the symmetry of step 3 and K-flatness of F.
   Consequently the bottom map becomes invertible after localization.
   Hom quasi-isomorphisms are inverted by lem-pur-rhom-well-defined.
   The naturality equalities therefore also hold after solving for any
   of these inverses. No truncation or flatness of A is used. -/
theorem oneKFlatChainTranspose :
    Nonempty (OneKFlatChainTransposeData.{c, v, u, w} J R S T) := by
  sorry

end WeilConjectures
