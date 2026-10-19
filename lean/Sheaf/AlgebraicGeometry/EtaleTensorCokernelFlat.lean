/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Abelian.Refinements
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-!
# Flat cokernels from ordinary tensor cohomology on the small etale site

Source: the Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-kunneth-ordinary`,
lemma `lem-kun-tor-cokernel-flat` (blueprint: lem-kun-tor-cokernel-flat).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

-- The following two private helpers repeat the proved Tor diagram chase from
-- WeilConjectures.CategoryTheory.DerivedCategory.FlatModel, with tensor-colimit
-- preservation replacing monoidal closedness. This permits independent site universes.
private theorem flat_iff_tensorLeft_preservesFiniteLimits
    {A : Type*} [Category A] [MonoidalCategory A] [BraidedCategory A]
    [∀ X : A, PreservesColimitsOfSize.{0, 0} (tensorLeft X)] (X : A) :
    ObjectProperty.flat X ↔ PreservesFiniteLimits (tensorLeft X) := by
  refine ⟨fun h ↦ h.1.1, fun h ↦ ⟨⟨h,
    (inferInstance : PreservesFiniteColimits (tensorLeft X))⟩, ?_, ?_⟩⟩
  · exact preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)
  · exact preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

-- The Tor diagram chase of FlatModel.flat_opcycles_of_exactAt uses only right exactness
-- of tensor, supplied here directly by colimit preservation instead of closedness.
private theorem flat_opcycles_of_tensor_exactAt
    {A : Type*} [Category A] [Abelian A] [MonoidalCategory A] [BraidedCategory A]
    [MonoidalPreadditive A]
    [∀ X : A, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    (P : CochainComplex A ℤ) (a : ℤ)
    (h₁ : ObjectProperty.flat (P.X (a - 1))) (h₂ : ObjectProperty.flat (P.X a))
    (hP : ∀ F : A, (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1)) :
    ObjectProperty.flat (P.opcycles a) := by
  have := h₁.tensorLeft.preservesFiniteLimits
  have := h₂.tensorLeft.preservesFiniteLimits
  rw [flat_iff_tensorLeft_preservesFiniteLimits,
    Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  refine ⟨hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance, ?_⟩
  have := hS.mono_f
  have := hS.epi_g
  dsimp
  set d := P.d (a - 1) a
  set d' := P.d (a - 1 - 1) (a - 1)
  set p := P.pOpcycles a
  have hdp : d ≫ p = 0 := P.d_pOpcycles _ _
  have (F : A) : PreservesColimitsOfSize.{0, 0} (tensorRight F) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)
  -- the cokernel sequence `P^{a-1} ⟶ P^a ⟶ C ⟶ 0`, tensored with any object, stays exact
  have hcok (F : A) : (ShortComplex.mk (d ▷ F) (p ▷ F)
      (by rw [← comp_whiskerRight, hdp, MonoidalPreadditive.zero_whiskerRight])).Exact := by
    have h : (ShortComplex.mk d p hdp).Exact :=
      ShortComplex.exact_of_g_is_cokernel _ (P.opcyclesIsCokernel _ _ (by simp))
    exact h.map_of_epi_of_preservesCokernel (tensorRight F) (by dsimp; infer_instance)
      inferInstance
  have hpe (F : A) : Epi (p ▷ F) := (tensorRight F).map_epi p
  have hge (X : A) : Epi (X ◁ S.g) := (tensorLeft X).map_epi S.g
  refine Preadditive.mono_of_cancel_zero _ (fun {T} x hx ↦ ?_)
  -- lift `x` to `P^a ⊗ S.X₁`
  obtain ⟨T₁, π₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi (p ▷ S.X₁) x
  -- its image in `P^a ⊗ S.X₂` dies in `C ⊗ S.X₂`, so it comes from `P^{a-1} ⊗ S.X₂`
  obtain ⟨T₂, π₂, _, z, hz⟩ :=
      (hcok S.X₂).exact_up_to_refinements (y ≫ P.X a ◁ S.f) (by
    dsimp
    rw [Category.assoc, whisker_exchange, ← Category.assoc, ← hy, Category.assoc,
      hx, comp_zero])
  -- the image of `z` in `P^{a-1} ⊗ S.X₃` is a cycle, hence a boundary
  have hex := (HomologicalComplex.exactAt_iff' _ (a - 1 - 1) (a - 1) a (by simp)
    (by simp)).1 (hP S.X₃)
  obtain ⟨T₃, π₃, _, w, hw⟩ := hex.exact_up_to_refinements (z ≫ P.X (a - 1) ◁ S.g) (by
    change (z ≫ P.X (a - 1) ◁ S.g) ≫ d ▷ S.X₃ = 0
    dsimp at hz
    rw [Category.assoc, whisker_exchange, ← Category.assoc, ← hz, Category.assoc,
      Category.assoc, ← MonoidalCategory.whiskerLeft_comp, S.zero,
      MonoidalPreadditive.whiskerLeft_zero, comp_zero, comp_zero])
  let w₀ : T₃ ⟶ P.X (a - 1 - 1) ⊗ S.X₃ := w
  have hw₂ : π₃ ≫ z ≫ P.X (a - 1) ◁ S.g = w₀ ≫ d' ▷ S.X₃ := hw
  obtain ⟨T₄, π₄, _, w', hw'⟩ :=
    surjective_up_to_refinements_of_epi (P.X (a - 1 - 1) ◁ S.g) w₀
  dsimp at hz
  -- correcting `z` by a boundary, it comes from `P^{a-1} ⊗ S.X₁`
  have hz' : (π₄ ≫ π₃ ≫ z - w' ≫ d' ▷ S.X₂) ≫ P.X (a - 1) ◁ S.g = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, hw₂, Category.assoc,
      ← whisker_exchange, ← reassoc_of% hw', sub_self]
  have hex₁ : (S.map (tensorLeft (P.X (a - 1)))).Exact := hS.exact.map _
  have : Mono (S.map (tensorLeft (P.X (a - 1)))).f :=
    (tensorLeft (P.X (a - 1))).map_mono S.f
  have : Mono (P.X a ◁ S.f) := (tensorLeft (P.X a)).map_mono S.f
  let v : T₄ ⟶ P.X (a - 1) ⊗ S.X₁ := hex₁.lift _ hz'
  have hv : v ≫ P.X (a - 1) ◁ S.f = π₄ ≫ π₃ ≫ z - w' ≫ d' ▷ S.X₂ :=
    hex₁.lift_f _ hz'
  have hvy : v ≫ d ▷ S.X₁ = π₄ ≫ π₃ ≫ π₂ ≫ y := by
    rw [← cancel_mono (P.X a ◁ S.f)]
    simp only [Category.assoc]
    rw [← whisker_exchange, reassoc_of% hv,
      Preadditive.sub_comp, Category.assoc, Category.assoc, ← hz, Category.assoc,
      ← comp_whiskerRight, P.d_comp_d, MonoidalPreadditive.zero_whiskerRight, comp_zero,
      sub_zero]
  rw [← cancel_epi (π₄ ≫ π₃ ≫ π₂ ≫ π₁), comp_zero]
  simp only [Category.assoc]
  rw [hy, ← reassoc_of% hvy, ← comp_whiskerRight, hdp,
    MonoidalPreadditive.zero_whiskerRight, comp_zero]

set_option synthInstance.maxHeartbeats 100000 in
-- Tensor totalization through ringedSiteModules needs more coproduct-instance search steps.
set_option synthInstance.maxSize 1024 in
/-- The cokernel in degree `a` of a complex of flat constant-coefficient module sheaves
is flat if ordinary tensor with every module sheaf has zero cohomology below `a`.
`mapBifunctor` is direct-sum totalization, and `singleFunctor _ 0` places the test
module sheaf in degree zero. The opcycle is the cokernel of `K.d (a - 1) a`.

Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-tor-cokernel-flat.md`
(blueprint: lem-kun-tor-cokernel-flat).

Proof:
1. Apply the vanishing hypothesis with `n = a - 1`. By
`def-pc-acyclic-complex-modules`, zero cohomology is exactness in that degree.
2. The degree-zero tensor comparison identifies this complex with termwise
`tensorRight M` applied to `K`. The comparison `siteSheafTensorRightIso` converts
`IsFlatOnSite` into categorical flatness. Tensor preserves colimits, so it preserves
cokernel sequences and epimorphisms.
3. For a short exact sequence of test sheaves, lift a section of the kernel of
`K.opcycles a ⊗ M₁ → K.opcycles a ⊗ M₂`, using epimorphic refinements, to
`K.X a ⊗ M₁`. Its image comes from `K.X (a - 1) ⊗ M₂`. In the third test sheaf
this preimage is a cycle, hence a boundary by step 1. Lift that boundary and
subtract it. Flatness of `K.X (a - 1)` now lifts the corrected preimage from the
first test sheaf, and flatness of `K.X a` identifies its differential with the
original lift. The section of the opcycles was therefore zero. Thus tensoring
with the opcycles preserves monomorphisms, hence is exact; the same tensor
comparison gives `IsFlatOnSite`.
-/
theorem isFlat_opcycles_of_tensor_cohomology_vanishing
    (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u})
    (K : CochainComplex
      (ringedSiteModules.{u + 1} ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ)))) ℤ)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := T.smallEtaleTopology)
      (R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
        (CommRingCat.of Λ)) (K.X i))
    (a : ℤ)
    (hvanish : ∀ M : ringedSiteModules.{u + 1} ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ))),
      ∀ n : ℤ, n < a → IsZero
        ((CochainComplex.mapBifunctor K ((CochainComplex.singleFunctor _ 0).obj M)
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory
            ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
              (CommRingCat.of Λ))))).homology n)) :
    SheafOfModules.IsFlatOnSite (J := T.smallEtaleTopology)
      (R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
        (CommRingCat.of Λ)) (K.opcycles a) := by
  classical
  let R : Sheaf T.smallEtaleTopology CommRingCat.{u + 1} :=
    (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ)
  let A := SheafOfModules.{u + 1} ((sheafCompose T.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let : MonoidalPreadditive A := by
    have (M : A) : (tensorLeft M).Additive :=
      SheafOfModules.tensorLeft_additive_independent R M
    have (M : A) : (tensorRight M).Additive :=
      Functor.additive_of_iso (F := tensorLeft M)
        (BraidedCategory.tensorLeftIsoTensorRight M)
    exact
      { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
        zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
        whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
        add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  have (M : A) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (tensorLeft M)
  have hcatflat (i : ℤ) : ObjectProperty.flat (K.X i) := by
    have hr : exactFunctor _ _ (tensorRight (K.X i)) :=
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso R (K.X i)) (hflat i)
    have : PreservesFiniteLimits (tensorRight (K.X i)) := hr.1
    exact (flat_iff_tensorLeft_preservesFiniteLimits _).2
      (preservesFiniteLimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight (K.X i)).symm)
  have hterm (M : A) :
      (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj K).ExactAt (a - 1) := by
    have h := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (hvanish M (a - 1) (by omega))
    exact h.of_iso (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) M K)
  have hop := flat_opcycles_of_tensor_exactAt K a (hcatflat _) (hcatflat _) hterm
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (K.opcycles a)).symm hop.2

end AlgebraicGeometry.Etale
