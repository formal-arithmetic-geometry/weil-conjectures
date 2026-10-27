/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.FppfFamilyAffineEffectivityReduction
import Sheaf.AlgebraicGeometry.AffineDescentSaturationQuasiAffineCover
import Sheaf.AlgebraicGeometry.DescentSaturationInvariantOpen
import Sheaf.AlgebraicGeometry.QuasiAffineFpqcDescent
import WeilConjectures.AlgebraicGeometry.InvariantOpenEffectiveDescent
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphismComparison

/-!
# Effective fppf descent for separated locally quasi-finite schemes

Source: Stacks Project, More on Morphisms, Tag 02W8,
`lemma-separated-locally-quasi-finite-morphisms-fppf-descend`
(blueprint: lem-trf-separated-lqf-fppf-effective-descent).

The covering-family scheme descent datum and its geometric effectivity are the existing
`AlgebraicGeometry.SchemeCoverDescentDatum` and
`AlgebraicGeometry.SchemeCoverDescentDatum.IsEffective` interfaces. The theorem below
states that an fppf covering datum whose local structure morphisms are separated and
locally quasi-finite is effective. No quasi-compactness or local finite-presentation
hypothesis on the local structure morphisms is included.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem property_sigmaMap
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (n : ℕ) (Y B : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ B i)
    (hf : ∀ i, P (f i)) : P (Limits.Sigma.map f) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := P) (sigmaOpenCover B)
  intro i
  have hsq : IsPullback (f i) (Sigma.ι Y i) (Sigma.ι B i) (Limits.Sigma.map f) := by
    refine IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_
    apply le_antisymm
    · rintro x ⟨y, hxy⟩
      obtain ⟨j, x, rfl⟩ := (sigmaOpenCover Y).exists_eq x
      simp only [sigmaOpenCover_f, ← Scheme.Hom.comp_apply, Sigma.ι_map] at hxy
      have hij : i = j := by
        simpa only [Sigma.mk.injEq] using congrArg Sigma.fst
          ((sigmaι_eq_iff B _ _ y _).mp hxy)
      subst j
      exact ⟨x, rfl⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨f i x, by simp only [← Scheme.Hom.comp_apply, Sigma.ι_map]⟩
  change P (pullback.snd (Limits.Sigma.map f) (Sigma.ι B i))
  rw [← P.cancel_left_of_respectsIso hsq.flip.isoPullback.hom,
    hsq.flip.isoPullback_hom_snd]
  exact hf i

/-- Effective fppf descent for separated locally quasi-finite schemes.

Source: Stacks Project, More on Morphisms, Tag 02W8,
`lemma-separated-locally-quasi-finite-morphisms-fppf-descend`
(blueprint: lem-trf-separated-lqf-fppf-effective-descent).
The proof follows Tag 02W8. First, separatedness and local quasi-finiteness are invariant
under base change and are stable for the finite coproducts used in the fppf-family
reduction, including the empty coproduct. The fppf-family effectivity reduction then
reduces to a single flat surjective finite-presentation morphism of affine schemes.
For each affine open in the local scheme, its saturated image is open and quasi-compact;
the cocycle makes these opens invariant. Restriction preserves separatedness and local
quasi-finiteness, and the quasi-compact separated locally quasi-finite morphisms are
quasi-affine. Effective descent for quasi-affine data on the fpqc singleton, followed
by gluing over the invariant open cover, gives effectivity of the original datum.
-/
theorem separated_lqf_fppf_effective_descent
    {I : Type (u + 1)} (T : Scheme.{u}) (U : I → Scheme.{u})
    (f : ∀ i, U i ⟶ T)
    (hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T)
    (D : SchemeCoverDescentDatum f)
    (hsep : ∀ i, IsSeparated (D.localScheme i).hom)
    (hlqf : ∀ i, Scheme.Hom.IsLocallyQuasiFinite (D.localScheme i).hom) :
    D.IsEffective := by
  classical
  let P : MorphismProperty Scheme.{u} :=
    @IsSeparated ⊓ (@LocallyQuasiFinite ⊓ @LocallyOfFiniteType)
  refine fppf_family_isEffective_of_affine_singletons P ?_ ?_ T U f hcov D ?_
  · intro n Y B g hg
    exact property_sigmaMap P n Y B g hg
  · intro A B _ _ p hp hs hlfp hqc hqs V E hV
    have : Flat p := hp
    have : Surjective p := hs
    have : LocallyOfFinitePresentation p := hlfp
    have : QuasiCompact p := hqc
    have : QuasiSeparated p := hqs
    have : IsSeparated V.hom := hV.1
    have hl : V.hom.IsLocallyQuasiFinite :=
      (V.hom.isLocallyQuasiFinite_iff).2 hV.2
    obtain ⟨W, hW, hcover⟩ := E.affine_descent_saturation_quasi_affine_cover p hl
    have hrestrict := fun C : V.left.affineOpens ↦
      E.exists_descentDatum_saturation_open p C.1 C.2 (W C) (hW C).1
    choose E' hcompat using hrestrict
    refine E.isEffective_of_effective_open_cover p.singleton_mem_fpqcPrecoverage W ?_
      E' ?_ ?_
    · intro x
      have hx : x ∈ (⨆ C, W C) := by rw [hcover]; trivial
      simpa only [TopologicalSpace.Opens.mem_iSup] using hx
    · intro C Z a b h v
      have hv : v ≫ Over.homMk (W C).ι rfl =
          Over.homMk (v.left ≫ (W C).ι)
            (by simpa only [Over.mk_hom, Category.assoc] using Over.w v) := by
        ext
        rfl
      simpa only [hv] using hcompat C Z a b h v
    · intro C
      have : IsQuasiAffineHom (Over.mk ((W C).ι ≫ V.hom)).hom := (hW C).2.2.2
      exact (E' C).isEffective_of_isQuasiAffineHom_fpqc p p.singleton_mem_fpqcPrecoverage
  · intro i
    exact ⟨hsep i, ((D.localScheme i).hom.isLocallyQuasiFinite_iff).1 (hlqf i)⟩

end AlgebraicGeometry
