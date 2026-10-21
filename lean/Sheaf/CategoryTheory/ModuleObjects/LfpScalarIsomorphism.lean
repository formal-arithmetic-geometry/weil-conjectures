/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap

/-!
# Local finite presentation under a ring-object isomorphism

Source: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-def-sfb-dc-restricted-functors/lem-sfb-dc-open-lower-shriek-preserves.proof.md`,
proof paragraph on locally finitely presented restrictions
(blueprint: lem-sfb-lfp-scalar-isomorphism).

The statement records invariance of pro-étale local finite presentations under restriction
of scalars along an isomorphism of commutative ring objects, including the same covering
family and presentation ranks, and the equivalent extension-of-scalars formulation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}}
variable {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]

omit [IsCommMonObj R] [IsCommMonObj S] in
private theorem presentation_comap (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S} (m n : ℕ)
    (h : ∃ f : Mod.finiteFree S m ⟶ Mod.finiteFree S n,
      Nonempty (N ≅ cokernel f)) :
    ∃ f : Mod.finiteFree R m ⟶ Mod.finiteFree R n,
      Nonempty ((Mod.comap φ).obj N ≅ cokernel f) := by
  obtain ⟨f, ⟨e⟩⟩ := h
  exact ⟨(Mod.finiteFreeIsoComap φ m).inv ≫ (Mod.comap φ).map f ≫
      (Mod.finiteFreeIsoComap φ n).hom,
    ⟨(Mod.comap φ).mapIso e ≪≫ PreservesCokernel.iso _ f ≪≫
      cokernel.mapIso _ _ (Mod.finiteFreeIsoComap φ m)
        (Mod.finiteFreeIsoComap φ n) (by simp)⟩⟩

omit [IsCommMonObj R] [IsCommMonObj S] in
private theorem presentation_comap_iff (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S} (m n : ℕ) :
    (∃ f : Mod.finiteFree S m ⟶ Mod.finiteFree S n,
      Nonempty (N ≅ cokernel f)) ↔
    (∃ f : Mod.finiteFree R m ⟶ Mod.finiteFree R n,
      Nonempty ((Mod.comap φ).obj N ≅ cokernel f)) := by
  refine ⟨presentation_comap φ m n, fun h ↦ ?_⟩
  obtain ⟨f, ⟨e⟩⟩ := presentation_comap (asIso φ).inv m n h
  exact ⟨f, ⟨(Mod.comapEquivalenceOfIsIso φ).unitIso.app N ≪≫ e⟩⟩

private theorem presentation_iso {T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj T] {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) T}
    (e : M ≅ N) (m n : ℕ) :
    (∃ f : Mod.finiteFree T m ⟶ Mod.finiteFree T n,
      Nonempty (M ≅ cokernel f)) ↔
    (∃ f : Mod.finiteFree T m ⟶ Mod.finiteFree T n,
      Nonempty (N ≅ cokernel f)) := by
  constructor
  · rintro ⟨f, ⟨p⟩⟩
    exact ⟨f, ⟨e.symm ≪≫ p⟩⟩
  · rintro ⟨f, ⟨p⟩⟩
    exact ⟨f, ⟨e ≪≫ p⟩⟩

omit [IsCommMonObj R] [IsCommMonObj S] in
private theorem presentation_mapMod_comap_iff (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    {Y : Scheme.{u}} (g : Y ⟶ X) (m n : ℕ) :
    (∃ f : Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} g).obj S) m ⟶
        Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} g).obj S) n,
      Nonempty (((ProEtale.upperStar Ab.{u + 1} g).mapMod S).obj N ≅ cokernel f)) ↔
    (∃ f : Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} g).obj R) m ⟶
        Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} g).obj R) n,
      Nonempty (((ProEtale.upperStar Ab.{u + 1} g).mapMod R).obj
        ((Mod.comap φ).obj N) ≅ cokernel f)) := by
  let F := ProEtale.upperStar Ab.{u + 1} g
  exact (presentation_comap_iff (F.map φ) m n).trans
    (presentation_iso ((F.mapModComapIso φ).app N) m n).symm

omit [IsCommMonObj R] [IsCommMonObj S] in
private theorem lfp_comap_iff (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S} :
    IsLocallyFinitelyPresented S N ↔
      IsLocallyFinitelyPresented R ((Mod.comap φ).obj N) := by
  constructor
  · rintro ⟨𝒰, h⟩
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨n, m, f, e⟩ := h i
    obtain ⟨f', e'⟩ := (presentation_mapMod_comap_iff φ (𝒰.f i) m n).mp ⟨f, e⟩
    exact ⟨n, m, f', e'⟩
  · rintro ⟨𝒰, h⟩
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨n, m, f, e⟩ := h i
    obtain ⟨f', e'⟩ := (presentation_mapMod_comap_iff φ (𝒰.f i) m n).mpr ⟨f, e⟩
    exact ⟨n, m, f', e'⟩

private theorem lfp_iso {T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj T] {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) T}
    (e : M ≅ N) :
    IsLocallyFinitelyPresented T M ↔ IsLocallyFinitelyPresented T N := by
  constructor
  · rintro ⟨𝒰, h⟩
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨n, m, f, p⟩ := h i
    obtain ⟨f', p'⟩ :=
      (presentation_iso ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod T |>.mapIso e)
        m n).mp ⟨f, p⟩
    exact ⟨n, m, f', p'⟩
  · rintro ⟨𝒰, h⟩
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨n, m, f, p⟩ := h i
    obtain ⟨f', p'⟩ :=
      (presentation_iso ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod T |>.mapIso e)
        m n).mpr ⟨f, p⟩
    exact ⟨n, m, f', p'⟩

set_option linter.unusedSectionVars false in
/--
Local finite presentation is invariant under restriction and extension of scalars along an
isomorphism of commutative ring objects.  A fixed pro-étale cover and fixed finite ranks admit
presentations on one side exactly when they do on the other.

Source: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-def-sfb-dc-restricted-functors/lem-sfb-dc-open-lower-shriek-preserves.proof.md`,
proof paragraph on locally finitely presented restrictions
(blueprint: lem-sfb-lfp-scalar-isomorphism).

Proof, following the node:
1. Put ψ = φ⁻¹. The symmetric closed sheaf tensor preserves colimits
   (`sk-def-sfb-sheaf-tensor`); sheaves are abelian by
   `lem-sfb-grothendieck-sheafification`. Equalizers and coequalizers therefore exist
   (`def-sp-abelian`). Clause 5 of `sk-def-sfb-change-of-scalars` identifies Ext_ψ with
   Res_φ and Ext_φ with Res_ψ. Double restriction restores the original action, with
   identity underlying comparison. Composing a presentation isomorphism with a module
   isomorphism leaves the ranks unchanged (`def-sfb-finitely-presented-module`).
2. Apply `lem-sfb-internal-extension-finite-presentation` to ψ to transport a
   presentation of N with ranks m,n to Res_φ N. Conversely extend a presentation of
   Res_φ N along φ, then use Ext_φ Res_φ N ≅ N. Both ranks are unchanged.
3. Fix the pro-étale cover 𝒰. Each inverse image F_i = u_i^* is strong symmetric
   monoidal (`def-sfb-finite-upper-star-monoidal`, `lem-sfb-finite-upper-star-braided`),
   so F_i R and F_i S are commutative and F_i φ is invertible. The comparison of
   `def-sfb-comap-mapmod-square`, with identity coefficient comparisons, identifies
   mapMod(F_i)(Res_φ N) with Res_(F_i φ)(mapMod(F_i) N). Apply step 2 on each member
   and compose the presentation isomorphisms. No index, cover, m or n changes.
   Existentially quantifying the ranks and cover gives
   `def-sfb-locally-finitely-presented` on both sides.
4. For an R-module M use Ext_φ M ≅ Res_ψ M and apply step 3 to ψ. Pullback sends this
   isomorphism to an isomorphism, so composing the presentation isomorphisms gives
   the extension equivalence with the very same covers and ranks.
-/
theorem isLocallyFinitelyPresented_comap_iff_sameCover
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S} :
    (IsLocallyFinitelyPresented S N ↔
        IsLocallyFinitelyPresented R ((Mod.comap φ).obj N)) ∧
      (∀ (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X) (i : 𝒰.I₀)
          (m n : ℕ),
        (∃ f : Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).obj S) m ⟶
            Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).obj S) n,
          Nonempty
            ((((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod S).obj N) ≅
              cokernel f)) ↔
          (∃ f : Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).obj R) m ⟶
            Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).obj R) n,
          Nonempty
            ((((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).obj
              ((Mod.comap φ).obj N)) ≅ cokernel f))) ∧
      (∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
        (IsLocallyFinitelyPresented R M ↔
          IsLocallyFinitelyPresented S ((Mod.extendScalars φ).obj M)) ∧
        ∀ (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X) (i : 𝒰.I₀)
            (m n : ℕ),
          (∃ f : Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).obj R) m ⟶
              Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).obj R) n,
            Nonempty
              ((((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).obj M) ≅
                cokernel f)) ↔
            (∃ f : Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).obj S) m ⟶
              Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).obj S) n,
            Nonempty
              ((((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod S).obj
                ((Mod.extendScalars φ).obj M)) ≅ cokernel f))) := by
  -- The direct finite-free restriction comparison keeps both ranks unchanged.
  refine ⟨lfp_comap_iff φ, fun 𝒰 i m n ↦
    presentation_mapMod_comap_iff φ (𝒰.f i) m n, ?_⟩
  intro M
  let e := (Mod.extendScalarsIsoComapInv φ).app M
  refine ⟨(lfp_comap_iff (asIso φ).inv).trans (lfp_iso e.symm), ?_⟩
  intro 𝒰 i m n
  exact (presentation_mapMod_comap_iff (asIso φ).inv (𝒰.f i) m n).trans
    (presentation_iso
      ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod S |>.mapIso e.symm) m n)

end AlgebraicGeometry.ProEtale
