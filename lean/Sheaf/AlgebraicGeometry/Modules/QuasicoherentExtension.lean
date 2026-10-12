/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.Modules.AffineExtensionSectionSurjectivity
import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Extensions of quasi-coherent modules

Source: Stacks Project, Schemes, Lemma 01IE, applied on an affine open cover
(blueprint: lem-pc-quasi-coherent-extension).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

private theorem tilde_preservesKernel (R : CommRingCat.{u})
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    Limits.PreservesLimit (Limits.parallelPair f 0) (tilde.functor R) := by
  let T := tilde.functor R
  let ff : T.FullyFaithful := tilde.fullyFaithfulFunctor (R := R)
  let : T.Full := ff.full
  let : T.Faithful := ff.faithful
  let : T.IsLeftAdjoint := (tilde.adjunction (R := R)).isLeftAdjoint
  let := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts T
  let : T.Additive := Functor.additive_of_preservesBinaryBiproducts T
  have : (T.obj M).IsQuasicoherent := by
    change (tilde.{u} (R := R) M).IsQuasicoherent
    infer_instance
  have : (T.obj N).IsQuasicoherent := by
    change (tilde.{u} (R := R) N).IsQuasicoherent
    infer_instance
  let k := Limits.kernel (T.map f)
  have hk : k.IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel (T.map f)
  have : IsIso (Scheme.Modules.fromTildeΓ (R := R) k) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) k
  let e : T.obj ((moduleSpecΓFunctor (R := R)).obj k) ≅ k :=
    asIso (Scheme.Modules.fromTildeΓ (R := R) k)
  let t := T.preimage (e.hom ≫ Limits.kernel.ι (T.map f))
  have ht : t ≫ f = 0 := by
    apply T.map_injective
    simp only [Functor.map_comp, Functor.map_preimage, Functor.map_zero,
      Category.assoc, Limits.kernel.condition, Limits.comp_zero, t]
  let c := Limits.KernelFork.ofι t ht
  have hc : Limits.IsLimit (c.map T) := by
    apply Limits.IsLimit.ofIsoLimit (Limits.kernelIsKernel (T.map f))
    exact Limits.Fork.ext e.symm (by simp [c, t, Limits.KernelFork.map])
  have hc' : Limits.IsLimit c :=
    Limits.isLimitOfReflects T ((c.isLimitMapConeEquiv T).symm hc)
  exact Limits.preservesLimit_of_preserves_limit_cone hc'
    ((c.isLimitMapConeEquiv T).symm hc)


/-- In a short exact sequence of modules on a scheme, quasi-coherence of both end terms
implies quasi-coherence of the middle term.
Source: Stacks Project, Schemes, Lemma 01IE, and locality of quasi-coherence
(blueprint: lem-pc-quasi-coherent-extension).

Proof:
1. Restrict to an affine open cover. Restriction preserves short exact sequences and
   quasi-coherence of the end terms (lem-weil-pbc-module-restriction-open-immersion-colimits).
   Write the end terms as associated modules using the affine quasi-coherent equivalence
   (lem-weil-pbc-affine-tilde-gamma-adjunction).
2. On an affine open, let M₂ be the sections of the middle term. For a section m of M₃,
   the elements a for which a*m lifts to M₂ form an ideal. Around each prime m lifts on
   a principal open D(f). Quasi-compactness of V(f) and localization of the first term
   supply a common power of f killing the differences of local lifts, which then glue.
   Thus a power of f lies in the ideal; the ideal lies in no prime and is the unit ideal.
   This proves exactness on global sections. Form the adjunction map from the associated
   module of M₂ to the middle term. Repeat the argument on each principal open, use
   exactness of localization and the five lemma to show this map is bijective there.
   Since principal opens form a basis, it is an isomorphism. Associated modules are
   quasi-coherent (lem-weil-pbc-spec-module-tilde-sections).
3. Quasi-coherence on the affine open cover implies quasi-coherence on the scheme
   (pqf-def-coherent). -/
theorem isQuasicoherent_of_shortExact {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    S.X₂.IsQuasicoherent := by
  refine isQuasicoherent_of_iSup_opensRange_eq_top S.X₂
    (fun U : {U : X.Opens // IsAffineOpen U} ↦ U.2.fromSpec)
    iSup_opensRange_fromSpec_eq_top (fun U ↦ ?_)
  let T := S.map (restrictFunctor U.2.fromSpec)
  have hT : T.ShortExact := hS.map_of_exact (restrictFunctor U.2.fromSpec)
  letI : (T.X₁).IsQuasicoherent := by
    exact isQuasicoherent_restrictFunctor _ _
  letI : (T.X₃).IsQuasicoherent := by
    exact isQuasicoherent_restrictFunctor _ _
  let R : CommRingCat.{u} := Γ(X, U.1)
  let G := moduleSpecΓFunctor (R := R)
  let L := tilde.functor R
  letI : G.IsRightAdjoint := (tilde.adjunction (R := R)).isRightAdjoint
  letI := CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts G
  letI : G.Additive := Functor.additive_of_preservesBinaryBiproducts G
  letI : Epi (G.map T.g) := epi_globalSections_of_shortExact T hT
  letI : Mono T.f := hT.mono_f
  have hG : (T.map G).ShortExact :=
    { exact := hT.exact.map_of_mono_of_preservesKernel G inferInstance inferInstance
      mono_f := (inferInstance : Mono (G.map T.f))
      epi_g := (inferInstance : Epi (G.map T.g)) }
  letI : ∀ {M N : ModuleCat.{u} R} (f : M ⟶ N),
      CategoryTheory.Limits.PreservesLimit (CategoryTheory.Limits.parallelPair f 0) L :=
    fun {_ _} f ↦ tilde_preservesKernel R f
  letI : CategoryTheory.Limits.PreservesFiniteLimits L :=
    Functor.preservesFiniteLimits_of_preservesKernels L
  have hL : ((T.map G).map L).ShortExact := hG.map_of_exact L
  let φ : ((T.map G).map L) ⟶ T :=
    { τ₁ := T.X₁.fromTildeΓ
      τ₂ := T.X₂.fromTildeΓ
      τ₃ := T.X₃.fromTildeΓ
      comm₁₂ := (fromTildeΓNatTrans.naturality T.f).symm
      comm₂₃ := (fromTildeΓNatTrans.naturality T.g).symm }
  have hφ : IsIso φ.τ₂ :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hL hT
  have h₂ : T.X₂.IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ T.X₂).mpr hφ
  letI : ((restrictFunctor U.2.fromSpec).obj S.X₂).IsQuasicoherent := h₂
  exact presentationOfIsIsoFromTildeΓ _

end AlgebraicGeometry.Scheme.Modules
