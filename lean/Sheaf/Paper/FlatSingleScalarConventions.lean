/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.Paper.FlatSingleScalarInterface
import Sheaf.Paper.FlatSingleScalarOrdinaryComparison
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Flat single complexes and the derived scalar comparison

Source: Stacks Project, Tags 03ER, 06YQ, 06YY and 06XN.
(blueprint: lem-sfb-flat-single-scalar-conventions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r wR wB
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped ChangeOfRings
namespace SheafOfModules.FlatSingleScalar
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {R B : Sheaf J CommRingCat.{r}} (φ : R ⟶ B)

variable [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wB} (Modules B)]

/-- The canonical degree-zero counit, including the termwise-single-complex comparison.
It is a natural transformation on all modules, hence also on the full subcategory of
flat modules. Source: Stacks 06YY and Derived Categories 06XN
(blueprint: lem-sfb-flat-single-scalar-conventions). -/
def degreeZeroCounit (F : Modules R ⥤ Modules B) [F.Additive]
    (L : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules B))
    (ε : DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    HomologicalComplex.single (Modules R) (.up ℤ) 0 ⋙ DerivedCategory.Q ⋙ L ⟶
      F ⋙ HomologicalComplex.single (Modules B) (.up ℤ) 0 ⋙ DerivedCategory.Q :=
  Functor.whiskerLeft (HomologicalComplex.single (Modules R) (.up ℤ) 0) ε ≫
    Functor.whiskerRight (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom
      DerivedCategory.Q

/-- The ordinary comparison preserves balancing projections on every local pure tensor.
Source: Stacks 03EK and blueprint change of scalars (2)
(blueprint: lem-sfb-flat-single-scalar-conventions). -/
def Normalized (d : Identifications φ) (s : DerivedChangeOfRingsCochainModel φ)
    (e : monExtension φ d ≅ s.E) : Prop :=
  ∀ (M : Modules R) (U : Cᵒᵖ) (b : B.obj.obj U) (m : M.val.obj U),
    ((eqToHom (s.obj_eq M)).val.app U)
      ((e.hom.app M).val.app U
        ((projection φ d M).val.app U (tensorSection (scalarAlgebra φ) M U b m))) =
      (toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
        (b ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)

/-- Counit-preserving derived comparison, invertible flat degree-zero comparisons,
and their natural compatibility square. Naturality is built into the three natural
transformations, so the square restricts naturally to all maps between flat modules.
Source: Stacks 06YY, 06XN and blueprint total left derived functors
(blueprint: lem-sfb-flat-single-scalar-conventions). -/
def DerivedCompatible (d : Identifications φ) (s : DerivedChangeOfRingsCochainModel φ)
    (e : monExtension φ d ≅ s.E) : Prop :=
  ∀ (L : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules B))
    (ε : DerivedCategory.Q ⋙ L ⟶
      (monExtension φ d).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
    L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Modules R) (.up ℤ)) →
    ∃ eL : L ≅ s.T,
      (Functor.whiskerLeft DerivedCategory.Q eL.hom ≫ s.ε =
        ε ≫ Functor.whiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)).hom
          DerivedCategory.Q) ∧
      ∀ (M : Modules R), IsFlatOnSite M →
        IsIso ((degreeZeroCounit (monExtension φ d) L ε).app M) ∧
        IsIso ((degreeZeroCounit s.E s.T s.ε).app M) ∧
        eL.hom.app (DerivedCategory.Q.obj
            ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj M)) ≫
          (degreeZeroCounit s.E s.T s.ε).app M =
        (degreeZeroCounit (monExtension φ d) L ε).app M ≫
          DerivedCategory.Q.map
            ((HomologicalComplex.single (Modules B) (.up ℤ) 0).map (e.hom.app M))

omit [HasDerivedCategory (Modules R)] in
private theorem single_flat_kflat (M : Modules R) (hM : IsFlatOnSite M) :
    CochainComplex.IsKFlatForTotalTensor
      ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj M) ∧
    CochainComplex.IsKFlatIndependentCoefficients
      ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj M) := by
  have h : PreservesFiniteLimits (siteSheafTensorRight (A := R) M) ∧
      PreservesFiniteColimits (siteSheafTensorRight (A := R) M) := hM
  have := h.1
  have := h.2
  have : PreservesFiniteLimits (tensorRight M) :=
    preservesFiniteLimits_of_natIso (siteSheafTensorRightIso R M)
  have : PreservesFiniteColimits (tensorRight M) :=
    preservesFiniteColimits_of_natIso (siteSheafTensorRightIso R M)
  have : PreservesFiniteLimits (tensorLeft M) :=
    preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M).symm
  have : PreservesFiniteColimits (tensorLeft M) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M).symm
  constructor
  · constructor
    · intro P Q f hf
      have := hf
      have hg := HomologicalComplex.quasiIso_map_of_preservesHomology f (tensorLeft M)
      exact (quasiIso_iff_of_arrow_mk_iso _ _
        (Arrow.isoMk
          (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor (Modules R)) M P)
          (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor (Modules R)) M Q)
          (CochainComplex.mapBifunctorSingle₁Iso_hom_naturality _ _ f).symm)).2 hg
    · intro P Q f hf
      have := hf
      have hg := HomologicalComplex.quasiIso_map_of_preservesHomology f (tensorRight M)
      exact (quasiIso_iff_of_arrow_mk_iso _ _
        (Arrow.isoMk
          (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (Modules R)) M P)
          (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (Modules R)) M Q)
          (CochainComplex.mapBifunctorSingle₂Iso_hom_naturality _ _ f).symm)).2 hg
  · intro P hP i
    apply HomologicalComplex.ExactAt.of_iso (e :=
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (Modules R)) M P).symm)
    exact ShortComplex.Exact.map (hP i) (tensorRight M)

private theorem derived_compatible (d : Identifications φ)
    (s : DerivedChangeOfRingsCochainModel φ) (e : monExtension φ d ≅ s.E)
    (hflat : ∀ M : Modules R, IsFlatOnSite M →
      CochainComplex.IsKFlatIndependentCoefficients
        ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj M)) :
    DerivedCompatible φ d s e := by
  intro L ε hL
  let := hL
  let := s.universal
  let W := HomologicalComplex.quasiIso (Modules R) (.up ℤ)
  let k := Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ))
    DerivedCategory.Q
  let eL : L ≅ s.T := Functor.leftDerivedNatIso L s.T ε s.ε W k
  have he : Functor.whiskerLeft DerivedCategory.Q eL.hom ≫ s.ε = ε ≫ k.hom :=
    Functor.leftDerivedNatTrans_fac L s.T ε s.ε W k.hom
  refine ⟨eL, he, ?_⟩
  intro M hM
  have : IsIso (s.ε.app ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj M)) :=
    s.computes _ (hflat M hM)
  have hs : IsIso ((degreeZeroCounit s.E s.T s.ε).app M) := by
    dsimp [degreeZeroCounit]
    infer_instance
  have hsq :
      eL.hom.app (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj M)) ≫
        (degreeZeroCounit s.E s.T s.ε).app M =
      (degreeZeroCounit (monExtension φ d) L ε).app M ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.single (Modules B) (.up ℤ) 0).map (e.hom.app M)) := by
    have heM := NatTrans.congr_app he
      ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj M)
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_obj] at heM
    dsimp only [degreeZeroCounit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_obj]
    simp only [Category.assoc]
    rw [← Category.assoc, heM]
    simp only [Category.assoc, k, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    rw [← DerivedCategory.Q.map_comp]
    rw [← DerivedCategory.Q.map_comp]
    apply congrArg (fun f ↦ ε.app _ ≫ DerivedCategory.Q.map f)
    apply HomologicalComplex.to_single_hom_ext
    simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_hom_app_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Functor.comp_obj,
      Functor.comp_map, Mod.extendScalars_map, Category.assoc]
    exact (e.hom.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom).symm
  have hm : IsIso ((degreeZeroCounit (monExtension φ d) L ε).app M) := by
    have hi : IsIso ((degreeZeroCounit (monExtension φ d) L ε).app M ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.single (Modules B) (.up ℤ) 0).map (e.hom.app M))) := by
      rw [← hsq]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (DerivedCategory.Q.map
        ((HomologicalComplex.single (Modules B) (.up ℤ) 0).map (e.hom.app M)))
  exact ⟨hm, hs, hsq⟩

/-- Flat degree-zero scalar comparisons agree in the two conventions, without local
freeness or flatness of B. Source: Stacks 03EK, 03ER(3), 06YQ, 06YY, 06XN and blueprint
change of scalars (2) (blueprint: lem-sfb-flat-single-scalar-conventions).

Proof, following all six steps of the DAG:
1. In Mod(R) the middle monoid in Mod.extendScalars is the tensor unit R. The two
   arrows send b tensor r tensor m to b φ(r) tensor m and b tensor rm. They agree
   by sectionwise balancing and sheafification (def-pur-sheaf-tensor-product,
   def-weil-pbc-sheafification). The identity of B tensor_R M descends through the
   coequalizer, and coequalizer uniqueness proves both inverse identities.
2. The first-factor action makes this inverse B-linear: after B tensor q both
   action formulas are multiplication b'b tensor m. For f:M to N, both composites
   after q send b tensor m to b tensor f(m). Coequalizer uniqueness gives naturality.
   These computations take place before sheafification, not on arbitrary global
   tensor sections (sk-def-sfb-change-of-scalars).
3. Flatness says that - tensor_R M is exact. Exact-functor homology comparison
   (lem-weil-pbc-exact-functor-complex-cohomology) proves preservation of acyclicity
   and quasi-isomorphisms. The sum-total tensor with M[0] has only one summand in
   each degree; the reverse order agrees by symmetry with sign (-1)^0 = 1.
   Thus both recorded K-flat predicates hold (def-sfb-preserves-kflat-quasi-iso,
   def-pc-kflat-complex).
4. The identity K-flat resolution computes the ringed-site derived counit
   (lem-pur-derived-change-of-rings). Its degree-zero component is invertible.
   The sectionwise tensor flip agrees with the chosen first-factor convention.
5. The universal property of the total left derived counits
   (def-sfb-left-derived-functor) lifts the ordinary natural isomorphism to eL.
   Lift its inverse as well. Counit uniqueness gives the two inverse identities
   and the displayed counit equation; no exactness of scalar extension is used.
6. Evaluate that equation on M[0] and use the natural single-complex comparison.
   This is the stated square. Its other three arrows are isomorphisms, hence so
   is the monoid-side degree-zero counit. All comparisons are natural
   transformations, so the square is natural on maps between flat sheaves.
   Flatness is used only for M[0], never for B over R. -/
theorem flat_single_scalar_conventions :
    (∀ (M : Modules R), IsFlatOnSite M →
      CochainComplex.IsKFlatForTotalTensor
        ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj M) ∧
      CochainComplex.IsKFlatIndependentCoefficients
        ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj M)) ∧
    ∃ d : Identifications φ, ∀ s : DerivedChangeOfRingsCochainModel φ,
      ∃ e : monExtension φ d ≅ s.E, Normalized φ d s e ∧ DerivedCompatible φ d s e := by
  refine ⟨fun M hM ↦ single_flat_kflat M hM, ?_⟩
  obtain ⟨d, hd⟩ := ordinary_scalar_comparison φ
  refine ⟨d, ?_⟩
  intro s
  obtain ⟨e, he⟩ := hd s
  exact ⟨e, he, derived_compatible φ d s e (fun M hM ↦ (single_flat_kflat M hM).2)⟩

end SheafOfModules.FlatSingleScalar
