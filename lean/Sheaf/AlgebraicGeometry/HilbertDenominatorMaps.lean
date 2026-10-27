/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.MeromorphicDenominatorIdeal
public import Mathlib.RingTheory.Lasker
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
import Sheaf.AlgebraicGeometry.HilbertDenominatorKernelComparison
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.Modules.StalkTensor
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # The two canonical maps out of a denominator-module product

Source: Stacks Project, Divisors, Tag 02P2.
-/

@[expose] public section

universe u
open scoped AlgebraicGeometry.Scheme.Modules
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

private theorem image_factor_of_kernel_zero {C : Type*} [Category C] [Abelian C]
    {P Q R : C} (f : P ⟶ Q) (g : P ⟶ R) (h : kernel.ι f ≫ g = 0) :
    ∃ d : image f ⟶ R, factorThruImage f ≫ d = g := by
  refine ⟨(Abelian.coimageIsoImage' f).inv ≫ cokernel.desc (kernel.ι f) g h, ?_⟩
  rw [← Category.assoc, Abelian.factorThruImage_comp_coimageIsoImage'_inv,
    cokernel.π_desc]

private theorem image_mono_of_kernel_comparison {C : Type*} [Category C] [Abelian C]
    {P Q R : C} (f : P ⟶ Q) (g : P ⟶ R)
    (h : kernel.ι f ≫ g = 0) (h' : kernel.ι g ≫ f = 0) :
    ∃ d : image f ⟶ R, factorThruImage f ≫ d = g ∧ Mono d := by
  have hg : kernel.ι f ≫ factorThruImage g = 0 := by
    apply (cancel_mono (image.ι g)).mp
    simpa only [Category.assoc, image.fac, zero_comp] using h
  have hf : kernel.ι g ≫ factorThruImage f = 0 := by
    apply (cancel_mono (image.ι f)).mp
    simpa only [Category.assoc, image.fac, zero_comp] using h'
  obtain ⟨a, ha⟩ := image_factor_of_kernel_zero f (factorThruImage g) hg
  obtain ⟨b, hb⟩ := image_factor_of_kernel_zero g (factorThruImage f) hf
  have hab : a ≫ b = 𝟙 _ := by
    apply (cancel_epi (factorThruImage f)).mp
    rw [← Category.assoc, ha, hb, Category.comp_id]
  have : Mono a := mono_of_mono_fac hab
  refine ⟨a ≫ image.ι g, ?_, inferInstance⟩
  rw [← Category.assoc, ha, image.fac]

private theorem hilbert_stalk_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (x : X) (h : Subsingleton ((presheaf M).stalk x)) :
    Subsingleton ((presheaf N).stalk x) := by
  let T := toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have : Subsingleton (T.obj M) := h
  exact (T.mapIso e).addCommGroupIsoToAddEquiv.symm.injective.subsingleton

private theorem hilbert_stalk_tensor {X : Scheme.{u}} (M F : X.Modules) (x : X)
    (h : Subsingleton ((presheaf M).stalk x)) :
    Subsingleton ((presheaf (M ⊗ F)).stalk x) := by
  have : Subsingleton (M.presheaf.stalk x) := h
  exact (stalkTensorEquiv M F x).injective.subsingleton

private theorem hilbert_cokernel_tensor_stalk {X : Scheme.{u}} {M N : X.Modules}
    (i : M ⟶ N) (F : X.Modules) (x : X)
    (h : Subsingleton ((presheaf (cokernel i : X.Modules)).stalk x)) :
    Subsingleton ((presheaf (cokernel (i ▷ F) : X.Modules)).stalk x) := by
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft F) :=
    (ihom.adjunction F).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0, 0} (tensorRight F) := by
    constructor
    intro J inst
    exact preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)
  exact hilbert_stalk_iso (PreservesCokernel.iso (tensorRight F) i) x
    (hilbert_stalk_tensor (cokernel i) F x h)

/-- The geometric assertion of Stacks Project, Divisors, Tag 02P2
(blueprint: lem-sc-hilbert-denominator-maps).

Proof: Apply the affine kernel comparison to the multiplication map f from
I tensor F to F and the denominator map g from I tensor F to F tensor L.
The identity kernel(f) to g = 0 factors g through coimage(f), hence image(f).
The reverse identity similarly constructs a map image(g) to image(f).
Cancellation of the epimorphic image factors shows that these two image maps
are inverse. Thus the induced jF is the composite of an isomorphism of images
and the monomorphic inclusion image(g) to F tensor L, and is monomorphic.
Its defining factorization is the first displayed equality.

For the support assertions, tensorRight F preserves cokernels: tensorLeft F
is left adjoint to internal Hom, and symmetry identifies these two functors.
Therefore coker(i tensor F) is (coker i) tensor F, and likewise for j.
On stalks this is the tensor product of stalk modules, which vanishes when
the first module vanishes. The cokernel of an image inclusion is the cokernel
of the original morphism, and composing with the unitor or braiding does not
change a cokernel up to isomorphism. Transporting the two stalk vanishings
along these cokernel isomorphisms gives the assertions. The proof also covers
the empty scheme and zero stalk modules, and uses no dimension or properness.
-/
theorem hilbert_denominator_maps {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules)
    (hFcoh : AlgebraicGeometry.RingedSpace.IsCoherent X.toRingedSpace F)
    (hFsupport : ∀ x : X, ¬ Subsingleton ((presheaf F).stalk x))
    (hFnoEmbedded : ∀ (U : X.Opens) (_ : IsAffineOpen U)
      (p : Ideal (Γ(X, U))),
      p ∈ associatedPrimes (Γ(X, U)) (Γ(F, U)) →
        Minimal (fun q : Ideal (Γ(X, U)) =>
          q ∈ associatedPrimes (Γ(X, U)) (Γ(F, U))) p)
    (L : X.Modules) [L.IsInvertible]
    (s : unit X ⟶ meromorphicModule X L)
    (hs : Mono (meromorphicSectionMap X L s)) :
    ∃ jF : idealModuleProduct (pullback.fst s (toMeromorphicModule X L)) F ⟶ tensorObj F L,
      factorThruImage ((pullback.fst s (toMeromorphicModule X L)) ▷ F ≫ (λ_ F).hom) ≫ jF =
        (pullback.snd s (toMeromorphicModule X L)) ▷ F ≫ (β_ L F).hom ∧
      Mono jF ∧
      (∀ x : X,
        Subsingleton ((presheaf (cokernel (pullback.fst s (toMeromorphicModule X L)) :
          X.Modules)).stalk x) →
        Subsingleton ((presheaf (cokernel (idealModuleProductι
          (pullback.fst s (toMeromorphicModule X L)) F) : X.Modules)).stalk x)) ∧
      (∀ x : X,
        Subsingleton ((presheaf (cokernel (pullback.snd s (toMeromorphicModule X L)) :
          X.Modules)).stalk x) →
        Subsingleton ((presheaf (cokernel jF : X.Modules)).stalk x)) := by
  obtain ⟨h, h'⟩ :=
    hilbert_denominator_kernel_comparison F hFcoh hFsupport hFnoEmbedded L s hs
  obtain ⟨jF, hjF, hmjF⟩ := image_mono_of_kernel_comparison
    ((pullback.fst s (toMeromorphicModule X L)) ▷ F ≫ (λ_ F).hom)
    ((pullback.snd s (toMeromorphicModule X L)) ▷ F ≫ (β_ L F).hom) h h'
  refine ⟨jF, hjF, hmjF, ?_, ?_⟩
  · intro x hx
    have hv := hilbert_cokernel_tensor_stalk (pullback.fst s (toMeromorphicModule X L)) F x hx
    let f := (pullback.fst s (toMeromorphicModule X L)) ▷ F
    have e : cokernel (idealModuleProductι (pullback.fst s (toMeromorphicModule X L)) F) ≅
        cokernel f :=
      (cokernelEpiComp (factorThruImage (f ≫ (λ_ F).hom))
        (image.ι (f ≫ (λ_ F).hom))).symm ≪≫
      cokernelIsoOfEq (image.fac _) ≪≫ cokernelCompIsIso f (λ_ F).hom
    exact hilbert_stalk_iso e.symm x hv
  · intro x hx
    have hv := hilbert_cokernel_tensor_stalk (pullback.snd s (toMeromorphicModule X L)) F x hx
    let g := (pullback.snd s (toMeromorphicModule X L)) ▷ F
    have e : cokernel jF ≅ cokernel g :=
      (cokernelEpiComp
        (factorThruImage ((pullback.fst s (toMeromorphicModule X L)) ▷ F ≫ (λ_ F).hom))
        jF).symm ≪≫ cokernelIsoOfEq hjF ≪≫ cokernelCompIsIso g (β_ L F).hom
    exact hilbert_stalk_iso e.symm x hv

end AlgebraicGeometry.Scheme.Modules
