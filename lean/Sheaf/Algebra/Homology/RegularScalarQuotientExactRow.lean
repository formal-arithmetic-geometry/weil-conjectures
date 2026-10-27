/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Algebra.Homology.RegularScalarQuotientNotation
import Sheaf.Algebra.Homology.RegularScalarQuotientPresentation
import Sheaf.Algebra.Homology.RegularScalarQuotientModuleRow
import Sheaf.Algebra.Homology.RegularScalarQuotientTensorComparison
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Regular scalar quotients and their exact row

Source: blueprint sk-lem-sp-tower, first proof paragraph;
Stacks Project, Tags 03EI, 03CY, 03EK and 06YQ.
(blueprint: lem-sp-regular-scalar-quotient-exact-row).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.RegularScalarQuotient

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J CommRingCat.{r}]
  (R : Sheaf J CommRingCat.{r}) (t : (unit R).sections)

omit [HasSheafify J CommRingCat.{r}] in
private theorem cone_support (f : unit R ⟶ unit R) :
    Nonempty ((CochainComplex.mappingCone
        ((CochainComplex.singleFunctor (Modules R) 0).map f)).X (-1) ≅ unit R) ∧
    Nonempty ((CochainComplex.mappingCone
        ((CochainComplex.singleFunctor (Modules R) 0).map f)).X 0 ≅ unit R) ∧
    ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero ((CochainComplex.mappingCone
      ((CochainComplex.singleFunctor (Modules R) 0).map f)).X i) := by
  let S := single (unit R)
  let φ := (CochainComplex.singleFunctor (Modules R) 0).map f
  have hz (i : ℤ) (hi : i ≠ 0) : IsZero (S.X i) :=
    HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (unit R) i hi
  refine ⟨⟨?e₁⟩, ⟨?e₀⟩, ?_⟩
  case e₁ =>
    exact HomologicalComplex.homotopyCofiber.XIsoBiprod φ (-1) 0 (by decide) ≪≫
      (isoBiprodZero (hz (-1) (by omega))).symm ≪≫
      HomologicalComplex.singleObjXSelf (.up ℤ) 0 (unit R)
  case e₀ =>
    exact HomologicalComplex.homotopyCofiber.XIsoBiprod φ 0 1 rfl ≪≫
      (isoZeroBiprod (hz 1 (by omega))).symm ≪≫
      HomologicalComplex.singleObjXSelf (.up ℤ) 0 (unit R)
  intro i hi₁ hi₀
  exact (CochainComplex.mappingCone.isZero_X_iff φ i).2
    ⟨hz (i + 1) (by omega), hz i hi₀⟩

omit [HasSheafify J CommRingCat.{r}] in
private theorem cone_kflat (f : unit R ⟶ unit R) :
    CochainComplex.IsKFlatIndependentCoefficients
      (CochainComplex.mappingCone ((CochainComplex.singleFunctor (Modules R) 0).map f)) := by
  let S := single (unit R)
  let φ := (CochainComplex.singleFunctor (Modules R) 0).map f
  let K := CochainComplex.mappingCone φ
  have : K.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (cone_support R f).2.2 i (by omega) (by omega)
  apply SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R K 0
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive R
  have hs (i : ℤ) : ObjectProperty.flat (S.X i) := by
    by_cases hi : i = 0
    · exact ObjectProperty.prop_of_iso _
        (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 (unit R) i hi).symm
        (ObjectProperty.prop_unit _)
    · exact ObjectProperty.prop_of_isZero _
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (unit R) i hi)
  intro i
  have hb : ObjectProperty.flat (S.X (i + 1) ⊞ S.X i) :=
    ObjectProperty.prop_biprod_of_isClosedUnderBinaryProducts _ _ _ (hs _) (hs _)
  have hk : ObjectProperty.flat (K.X i) :=
    ObjectProperty.prop_of_iso _
      (HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl).symm hb
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R _).symm hk.2

omit [HasSheafify J CommRingCat.{r}] in
private theorem cone_augmentation {M N : Modules R} (f : M ⟶ M) (g : M ⟶ N)
    (h : f ≫ g = 0) :
    ∃ ε : CochainComplex.mappingCone
        ((CochainComplex.singleFunctor (Modules R) 0).map f) ⟶ single N,
      (singleIn M ≫ (CochainComplex.mappingCone.inr
        ((CochainComplex.singleFunctor (Modules R) 0).map f)).f 0) ≫ ε.f 0 =
          g ≫ singleIn N ∧
      ((ShortComplex.mk f g h).ShortExact → QuasiIso ε) := by
  let F := CochainComplex.singleFunctor (Modules R) 0
  let S := (ShortComplex.mk f g h).map F
  refine ⟨CochainComplex.mappingCone.descShortComplex S, ?_, ?_⟩
  · change singleIn M ≫ (CochainComplex.mappingCone.inr S.f).f 0 ≫
        (CochainComplex.mappingCone.descShortComplex S).f 0 = g ≫ singleIn N
    rw [CochainComplex.mappingCone.inr_f_descShortComplex_f S]
    change singleIn M ≫ (F.map g).f 0 = g ≫ singleIn N
    change singleIn M ≫ ((HomologicalComplex.single (Modules R) (.up ℤ) 0).map g).f 0 = _
    rw [HomologicalComplex.single_map_f_self]
    simp [singleIn]
  · intro hs
    have hF : PreservesFiniteLimits F :=
      inferInstanceAs (PreservesFiniteLimits (HomologicalComplex.single (Modules R) (.up ℤ) 0))
    have hF' : PreservesFiniteColimits F :=
      inferInstanceAs (PreservesFiniteColimits
        (HomologicalComplex.single (Modules R) (.up ℤ) 0))
    exact CochainComplex.mappingCone.quasiIso_descShortComplex (hs.map_of_exact F)

/-- The regular-scalar Koszul resolutions, normalized tensor identification and exact
four-term row over the higher quotient ring.

Source: blueprint sk-lem-sp-tower, proof paragraph 1, coefficient tensor calculation;
Stacks Project, Tags 03EI, 03CY, 03EK and 06YQ.
(blueprint: lem-sp-regular-scalar-quotient-exact-row).

Proof:
1. Cancel t repeatedly on each R(U). The sectionwise sequence for multiplication
   by t^(k+1) and its quotient is exact. Exact module sheafification (03EI) gives
   the quotient cokernel and the quasi-isomorphism of the augmented Koszul complex.
2. Its only nonzero terms are copies of the unit module. The tensor-unit formulas
   x tensor r maps to rx and x maps to x tensor 1 show that these terms are flat;
   zero terms are flat. The bounded-above flat K-flat theorem (06YQ) applies.
3. In B_n[0] tensor K_m only the (0,-1) and (0,0) summands survive. The right
   unitor identifies both with B_n. The total differential has sign (-1)^0=1,
   hence is multiplication by t^(m+1). The augmentation is coefficient reduction.
4. On sectionwise quotient representatives define a([x])=[t^(n-m)x]. A change
   by t^(m+1)y changes this by t^(n+1)y, so it is well-defined and B_n-linear.
   If its image vanishes, cancellation of t^(n-m) proves its injectivity.
5. Cancel t^(m+1) in t^(m+1)x=t^(n+1)y. This identifies the first kernel
   with the image of a and with the complementary-power ideal. The second kernel
   is the image of multiplication by t^(m+1); reduction is surjective.
6. Sheafify the exact row (03EI). Sheafification of modules over the quotient
   ring presheaf (03CY) supplies its quotient-ring-linear structure. The comparison
   with ring sheafification is an isomorphism on underlying sets, so the middle
   terms are the regular B_n-module. The representative formulas pin all maps.
   At n=m the complementary power is zero: a and reduction are identities and
   multiplication by t^(m+1) vanishes. This includes unit t and the zero ring. -/
theorem regularScalarQuotient_exactRow
    (hregular : ∀ U : Cᵒᵖ, Function.Injective
      (fun x : R.obj.obj U ↦ (@id (R.obj.obj U) (t.val U)) * x)) :
    (∀ k : ℕ, ∃ ε : principalKoszul R t k ⟶ single (Q R t k),
      CochainComplex.IsKFlatResolutionIndependentCoefficients ε ∧
      koszulRight R t k ≫ ε.f 0 = ringMap (projection R t k) ≫ singleIn (Q R t k) ∧
      Nonempty ((principalKoszul R t k).X (-1) ≅ unit R) ∧
      Nonempty ((principalKoszul R t k).X 0 ≅ unit R) ∧
      ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero ((principalKoszul R t k).X i)) ∧
    ∀ (n m : ℕ) (_hm : m ≤ n),
      ∃ red : B R t n ⟶ B R t m,
      projection R t n ≫ red = projection R t m ∧
      ∃ (a : (res red).obj (unit (B R t m)) ⟶ unit (B R t n))
        (ε : P R t n m ⟶ single ((res red).obj (unit (B R t m))))
        (e : tensor R t n m ≅ restrictedP R t n m),
        (∀ (U : Cᵒᵖ) (x : R.obj.obj U),
          a.val.app U ((projection R t m).hom.app U x) =
            (projection R t n).hom.app U ((@id (R.obj.obj U) (t.val U)) ^ (n - m) * x)) ∧
        rightIn (B R t n) (scalarImage R t (projection R t n))
            (unit (B R t n)) (m + 1) ≫ ε.f 0 =
          ringMap red ≫ singleIn ((res red).obj (unit (B R t m))) ∧
        tensorIn R t n m (-1) (koszulLeft R t m) ≫ e.hom.f (-1) =
          (res (projection R t n)).map
            (leftIn (B R t n) (scalarImage R t (projection R t n))
              (unit (B R t n)) (m + 1)) ∧
        tensorIn R t n m 0 (koszulRight R t m) ≫ e.hom.f 0 =
          (res (projection R t n)).map
            (rightIn (B R t n) (scalarImage R t (projection R t n))
              (unit (B R t n)) (m + 1)) ∧
        Mono a ∧ Epi (ringMap red) ∧
        (∃ ha : a ≫ mul (B R t n) (scalarImage R t (projection R t n))
            (unit (B R t n)) (m + 1) = 0,
          (ShortComplex.mk a (mul (B R t n) (scalarImage R t (projection R t n))
            (unit (B R t n)) (m + 1)) ha).Exact) ∧
        (∃ hb : mul (B R t n) (scalarImage R t (projection R t n))
            (unit (B R t n)) (m + 1) ≫ ringMap red = 0,
          (ShortComplex.mk (mul (B R t n) (scalarImage R t (projection R t n))
            (unit (B R t n)) (m + 1)) (ringMap red) hb).Exact) ∧
        imageSubobject a = imageSubobject
          (mul (B R t n) (scalarImage R t (projection R t n))
            (unit (B R t n)) (n - m)) ∧
        (∀ h : n = m,
          red = eqToHom (congrArg (B R t) h) ∧
          (∀ (U : Cᵒᵖ) (x : (B R t m).obj.obj U),
            a.val.app U x = (eqToHom (congrArg (B R t) h.symm)).hom.app U x) ∧
          mul (B R t n) (scalarImage R t (projection R t n))
            (unit (B R t n)) (m + 1) = 0) := by
  constructor
  · intro k
    obtain ⟨hz, hs⟩ := regularScalarQuotient_presentation R t hregular k
    obtain ⟨ε, hε, hq⟩ := cone_augmentation R
      (endoPow (globalSectionMultiplication R t) (k + 1))
      (ringMap (projection R t k)) hz
    obtain ⟨h₁, h₀, hzero⟩ := cone_support R
      (endoPow (globalSectionMultiplication R t) (k + 1))
    exact ⟨ε, ⟨hq hs, cone_kflat R _⟩, hε, h₁, h₀, hzero⟩
  · intro n m hm
    obtain ⟨red, hred, a, ha, hmono, hepi, hex₁, ⟨hb, hex₂⟩, him, hdiag⟩ :=
      regularScalarQuotient_moduleRow R t hregular n m hm
    obtain ⟨ε, hε, _⟩ := cone_augmentation (B R t n)
      (mul (B R t n) (scalarImage R t (projection R t n))
        (unit (B R t n)) (m + 1)) (ringMap red) hb
    obtain ⟨e, he₁, he₀⟩ := regularScalarQuotient_tensorComparison R t n m
    exact ⟨red, hred, a, ε, e, ha, hε, he₁, he₀,
      hmono, hepi, hex₁, ⟨hb, hex₂⟩, him, hdiag⟩

end CategoryTheory.RegularScalarQuotient
