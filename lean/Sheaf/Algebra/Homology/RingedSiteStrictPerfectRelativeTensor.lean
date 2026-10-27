/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Sheaf.CategoryTheory.Sites.RingedSitePoint
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction

/-! # Strict-perfect relative tensor models on a ringed site

Source: Stacks Project, sites-cohomology.tex, Tags 06YQ, 06YU, 0E8K, 0DEN;
spaces-perfect.tex, Tag 0DKJ, local tensor calculation.
(blueprint: lem-sfb-ringed-strict-perfect-relative-tensor)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r wA wR wAU wRU i

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

/-- The existing module category, with commutative coefficients forgotten to rings.
Source: Stacks Project, Modules on Sites, Section 03DA;
owned by def-weil-sheaf-of-modules-category.
(blueprint: lem-sfb-ringed-strict-perfect-relative-tensor) -/
abbrev strictPerfectModules
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    (A : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A)

/-- The existing restriction of scalars, applied to the underlying ring-sheaf map.
Source: Stacks Project, Modules on Sites, Section 03DA;
owned by def-pc-sheaf-restrict-scalars.
(blueprint: lem-sfb-ringed-strict-perfect-relative-tensor) -/
abbrev strictPerfectRestrictScalars
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    {R A : Sheaf J CommRingCat.{r}} (φ : R ⟶ A) :=
  SheafOfModules.restrictScalars.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)

/-- The existing exactness instance for restriction of scalars, in the item notation.
Source: Stacks Project, Modules on Sites, Section 03DA;
lem-pe-restricted-kflat-tensor-identification supplies this proof dependency.
(blueprint: lem-sfb-ringed-strict-perfect-relative-tensor) -/
instance strictPerfectRestrictScalarsPreservesFiniteLimits
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} {R A : Sheaf J CommRingCat.{r}} (φ : R ⟶ A) :
    PreservesFiniteLimits (strictPerfectRestrictScalars φ) :=
  restrictedTensorScalars_preservesFiniteLimits φ

/-- The existing exactness instance for restriction of scalars, in the item notation.
Source: Stacks Project, Modules on Sites, Section 03DA;
lem-pe-restricted-kflat-tensor-identification supplies this proof dependency.
(blueprint: lem-sfb-ringed-strict-perfect-relative-tensor) -/
instance strictPerfectRestrictScalarsPreservesFiniteColimits
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} {R A : Sheaf J CommRingCat.{r}} (φ : R ⟶ A) :
    PreservesFiniteColimits (strictPerfectRestrictScalars φ) :=
  restrictedTensorScalars_preservesFiniteColimits φ

/-- The signed direct-sum total of the existing sheaf tensor bifunctor.
Source: Stacks Project, sites-cohomology.tex, Tag 06YM;
owned by def-pc-tensor-complex-sheaves and def-pur-sheaf-tensor-product.
(blueprint: lem-sfb-ringed-strict-perfect-relative-tensor) -/
abbrev strictPerfectTotalTensor
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (A : Sheaf J CommRingCat.{r})
    (K L : CochainComplex (strictPerfectModules A) ℤ) :=
  CochainComplex.mapBifunctor K L
    (@curriedTensor (strictPerfectModules A) _ (SheafOfModules.monoidalCategory A))

/-- A slice has the same size bound as the original site. This is Mathlib's
`CostructuredArrow.essentiallySmall` instance, exposed for its `Over` presentation.
Source: the small-site convention and Stacks Project, Sites, localization.
(blueprint: lem-sfb-ringed-strict-perfect-relative-tensor) -/
instance strictPerfectSliceSmall
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (U : C) : EssentiallySmall.{r} (Over U) :=
  letI : LocallySmall.{r} C := locallySmall_of_essentiallySmall C
  CostructuredArrow.essentiallySmall (S := 𝟭 C) (T := U)

/-- Termwise slice restriction, using Mathlib's sectionwise restriction functor.
Source: Stacks Project, sites-cohomology.tex, Tag 0E8K.
(blueprint: lem-sfb-ringed-strict-perfect-relative-tensor) -/
abbrev strictPerfectSliceComplex
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (A : Sheaf J RingCat.{r}) (U : C)
    (M : CochainComplex (ringedSiteModules.{r} A) ℤ) :=
  letI := CategoryTheory.module_overFunctor_preservesZero A U
  ((overFunctor A U).mapHomologicalComplex (.up ℤ)).obj M

/-- The recorded derived slice restriction, with its coefficient category exposed as
modules over the restricted commutative ring sheaf. The two presentations have the same
sections, actions and sheaf condition.
Source: Stacks Project, sites-cohomology.tex, Tag 0E8K.
(blueprint: lem-sfb-ringed-strict-perfect-relative-tensor) -/
abbrev strictPerfectDerivedSlice
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (A : Sheaf J CommRingCat.{r}) (U : C)
    [HasDerivedCategory.{wA} (strictPerfectModules A)]
    [hAU : HasDerivedCategory.{wAU} (strictPerfectModules (A.over U))]
    (P : DerivedCategory (strictPerfectModules A)) :
    DerivedCategory (strictPerfectModules (A.over U)) :=
  letI : HasDerivedCategory.{wAU} (SheafOfModules.{r}
      (((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A).over U)) := hAU
  ringedSiteDerivedRestrictionOfUniverses.{u, v, r, r, wA, wAU}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A) U P

/-- A strict-perfect local model computes the derived tensor and every relative tensor
with a module in degree zero, with the sum of the two degree intervals as a Tor bound.
Source: Stacks Project, sites-cohomology.tex, Tags 06YQ, 06YU, 0E8K, 0DEN;
spaces-perfect.tex, Tag 0DKJ.
(blueprint: lem-sfb-ringed-strict-perfect-relative-tensor)

Proof:
1. Conservative-point flatness (lem-sfb-ringed-site-conservative-flatness, Stacks 05VC)
   makes the scalar restriction of each M term flat. Flatness survives slice restriction
   (lem-weil-pbc-slice-restriction-flat); both restrictions retain the same sections.
2. Each L term retracts from a finite free module, so tensor with it is a retract of a
   finite sum of identity functors and is exact. Bounded-above flat complexes are K-flat
   (lem-pc-bounded-above-flat-kflat-site).
3. Choose a flat-term K-flat representative for P by
   lem-weil-pbc-site-derived-tensor-descent. The one-sided comparison of
   lem-trf-site-one-sided-tensor-normalization computes its tensor with M. Restrict it
   to U: only finitely many q in [c,d] contribute in each degree, so ordinary tensor
   restriction (lem-sfb-localized-site-tensor-restriction) gives a chain isomorphism
   of totals. The signed differentials agree by naturality. K-flatness and flat terms
   survive restriction (lem-sfb-ringed-site-restriction-kflat and the flat restriction
   lemma). Thus this is the derived tensor of the restrictions.
4. Substitute the given local derived isomorphism for P, and apply the same one-sided
   comparison with L, giving precisely the signed total tensor T in the statement.
5. Its degree n summands are L^p tensor M^q with p+q=n. Only the finite rectangle
   [a,b] times [c,d] contributes. Tensoring a splitting of L^p from a finite free
   module gives a splitting from a finite sum of M^q. Outside [a+c,b+d] all summands
   vanish (def-pc-tensor-complex-sheaves and def-pur-sheaf-tensor-product).
6. Finite sums and retracts of flat R_U modules are flat. Hence the scalar restriction
   of T is termwise flat; it is bounded above and therefore K-flat. No R-flatness of A
   is needed (def-pc-flat-sheaf-modules, lem-pc-bounded-above-flat-kflat-site).
7. Scalar restriction is exact and induces a derived functor with the canonical Q
   comparison (lem-pe-restricted-kflat-tensor-identification). Apply it to the model
   isomorphism. Scalar and slice restrictions commute sectionwise.
8. For any F repeat step 3 over R with the second complex F[0], now with only one
   summand per degree. Substitute step 7 and apply one-sided normalization to the
   R_U-flat K-flat complex Res T. This gives the asserted derived isomorphism.
9. The ordinary tensor with F_U[0] is zero in every degree outside [a+c,b+d]. Its
   cohomology vanishes there, and the derived isomorphism transfers this vanishing.
   Zero complexes, rank-zero summands and empty slices obey the same calculations.
-/
theorem ringedSite_strictPerfect_relativeTensor
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    (R A : Sheaf J CommRingCat.{r}) (φ : R ⟶ A) (U : C)
    [HasDerivedCategory.{wA} (strictPerfectModules A)]
    [HasDerivedCategory.{wR} (strictPerfectModules R)]
    [HasDerivedCategory.{wAU} (strictPerfectModules (A.over U))]
    [HasDerivedCategory.{wRU} (strictPerfectModules (R.over U))]
    (I : Type i)
    (points : I → GeometricMorphism (Type r) (Sheaf J (Type r)))
    (hpoints : JointlyReflectIsomorphisms (fun j : I ↦ (points j).inverse))
    (stalks : ∀ j : I, RingedSitePoint R (points j))
    (M : CochainComplex (strictPerfectModules A) ℤ) (P : DerivedCategory (strictPerfectModules A))
    (L : CochainComplex (strictPerfectModules (A.over U)) ℤ) (a b c d : ℤ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (hM : ∀ q : ℤ, q < c ∨ d < q → IsZero (M.X q))
    (hflat : ∀ (j : I) (q : ℤ),
      Module.Flat (stalks j).ring
        ((stalks j).modules.obj ((strictPerfectRestrictScalars φ).obj (M.X q))))
    (hL : ∀ p : ℤ, p < a ∨ b < p → IsZero (L.X p))
    (hfree : ∀ p : ℤ, ∃ (k : ℕ)
      (ι : L.X p ⟶ free (R := (sheafCompose (J.over U)
        (forget₂ CommRingCat.{r} RingCat.{r})).obj (A.over U)) (ULift.{r} (Fin k)))
      (π : free (R := (sheafCompose (J.over U)
        (forget₂ CommRingCat.{r} RingCat.{r})).obj (A.over U)) (ULift.{r} (Fin k)) ⟶ L.X p),
        ι ≫ π = 𝟙 (L.X p))
    (eL : strictPerfectDerivedSlice A U P ≅
        DerivedCategory.Q.obj L) :
    ∃ T : CochainComplex (strictPerfectModules (A.over U)) ℤ,
      T = strictPerfectTotalTensor (A.over U) L
        (strictPerfectSliceComplex ((sheafCompose J
          (forget₂ CommRingCat.{r} RingCat.{r})).obj A) U M) ∧
      Nonempty (strictPerfectDerivedSlice A U
        ((siteDerivedTensorIndependentCoefficients J A).obj (P, DerivedCategory.Q.obj M)) ≅
          DerivedCategory.Q.obj T) ∧
      (∀ n : ℤ, ∃ (k : ℕ) (q : Fin k → ℤ) (s : Fin k → ℕ)
        (N : Fin k → strictPerfectModules (A.over U)),
        Nonempty (T.X n ≅ ∐ N) ∧
        ∀ j : Fin k, ∃
          (ι : N j ⟶ ∐ (fun _ : Fin (s j) ↦
            (M.X (q j)).over U))
          (π : (∐ (fun _ : Fin (s j) ↦ (M.X (q j)).over U)) ⟶ N j),
          ι ≫ π = 𝟙 (N j)) ∧
      (∀ n : ℤ, n < a + c ∨ b + d < n → IsZero (T.X n)) ∧
      (∀ n : ℤ, IsFlatOnSite (J := J.over U) (R := R.over U)
        ((strictPerfectRestrictScalars ((J.overPullback CommRingCat.{r} U).map φ)).obj (T.X n))) ∧
      CochainComplex.IsKFlatIndependentCoefficients (R := R.over U)
        (((strictPerfectRestrictScalars
            ((J.overPullback CommRingCat.{r} U).map φ)).mapHomologicalComplex
            (.up ℤ)).obj T) ∧
      Nonempty (((strictPerfectRestrictScalars
        ((J.overPullback CommRingCat.{r} U).map φ)).mapDerivedCategory).obj
        (strictPerfectDerivedSlice A U
          ((siteDerivedTensorIndependentCoefficients J A).obj (P, DerivedCategory.Q.obj M))) ≅
        DerivedCategory.Q.obj
          (((strictPerfectRestrictScalars
            ((J.overPullback CommRingCat.{r} U).map φ)).mapHomologicalComplex
            (.up ℤ)).obj T)) ∧
      (∀ F : strictPerfectModules R,
        Nonempty (strictPerfectDerivedSlice R U
          ((siteDerivedTensorIndependentCoefficients J R).obj
            ((strictPerfectRestrictScalars φ).mapDerivedCategory.obj
              ((siteDerivedTensorIndependentCoefficients J A).obj (P, DerivedCategory.Q.obj M)),
              DerivedCategory.Q.obj
                ((HomologicalComplex.single (strictPerfectModules R) (.up ℤ) 0).obj F))) ≅
          DerivedCategory.Q.obj (strictPerfectTotalTensor (R.over U)
            (((strictPerfectRestrictScalars
            ((J.overPullback CommRingCat.{r} U).map φ)).mapHomologicalComplex
            (.up ℤ)).obj T)
            ((HomologicalComplex.single (strictPerfectModules (R.over U))
              (.up ℤ) 0).obj (F.over U)))) ∧
        ∀ n : ℤ, n < a + c ∨ b + d < n → IsZero
          ((DerivedCategory.homologyFunctor (strictPerfectModules (R.over U)) n).obj
            (strictPerfectDerivedSlice R U
              ((siteDerivedTensorIndependentCoefficients J R).obj
                ((strictPerfectRestrictScalars φ).mapDerivedCategory.obj
                  ((siteDerivedTensorIndependentCoefficients J A).obj
                    (P, DerivedCategory.Q.obj M)),
                  DerivedCategory.Q.obj
                    ((HomologicalComplex.single (strictPerfectModules R)
                      (.up ℤ) 0).obj F)))))) := by
  sorry

end SheafOfModules
