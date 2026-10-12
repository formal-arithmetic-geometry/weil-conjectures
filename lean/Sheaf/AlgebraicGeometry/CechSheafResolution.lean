/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Sheaf.AlgebraicGeometry.CechSheafConstruction
import Sheaf.AlgebraicGeometry.CechSheafLocalQuasiIso
/-! # The augmented Čech complex of module sheaves

Source: blueprint lem-pc-cech-resolution, proof paragraph 1.
(blueprint: lem-pc-cech-sheaf-resolution).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

-- A map is invertible when it is invertible on every member of an open cover.
private theorem isIso_of_restrict {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map f)) : IsIso f := by
  have : Mono f := Scheme.Modules.mono_of_restrict f U hU fun i ↦ by
    have := h i
    infer_instance
  have : Epi f := (Preadditive.epi_iff_isZero_cokernel f).2 (by
    apply Scheme.Modules.isZero_of_iSup_eq_top _ U hU
    intro i
    have := h i
    exact (PreservesCokernel.iso (Scheme.Modules.restrictFunctor (U i).ι) f).isZero_iff.mpr
      (isZero_cokernel_of_epi _))
  exact isIso_of_mono_of_epi f

-- Exact restriction identifies local homology maps with the global homology map.
private theorem quasiIso_of_restrict {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    {K L : CochainComplex X.Modules ℕ} (f : K ⟶ L)
    (h : ∀ i, QuasiIso (((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).map f)) : QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  apply isIso_of_restrict U hU
  intro i
  let R := Scheme.Modules.restrictFunctor (U i).ι
  let φ := (HomologicalComplex.shortComplexFunctor X.Modules (ComplexShape.up ℕ) n).map f
  have hφ : ShortComplex.QuasiIso (R.mapShortComplex.map φ) := by
    have := h i
    exact (quasiIsoAt_iff ((R.mapHomologicalComplex (ComplexShape.up ℕ)).map f) n).mp
      inferInstance
  have : IsIso (ShortComplex.homologyMap (R.mapShortComplex.map φ)) :=
    (ShortComplex.quasiIso_iff _).mp hφ
  have he := ShortComplex.mapHomologyIso_inv_naturality φ R
  have : IsIso (R.map (ShortComplex.homologyMap φ) ≫
      ((L.sc n).mapHomologyIso R).inv) := by
    rw [he]
    infer_instance
  exact (isIso_comp_right_iff _ ((L.sc n).mapHomologyIso R).inv).mp inferInstance

/-- The usual, unnormalized Čech sheaf complex resolves a module on any open cover.
Source: blueprint lem-pc-cech-resolution, proof paragraph 1, and the term description
in its statement. (blueprint: lem-pc-cech-sheaf-resolution)

Proof: for an open W put P(W) = j_W,* (F restricted to W). For inclusions W ⊆ Z,
restriction of sections on Z ∩ V to W ∩ V gives P(Z) → P(W), linearly over O_X(V).
These maps define a functor on the opposite opens category. Apply cechComplexFunctor
U to P to construct D, and augment by the restriction maps from F. The sheaf axiom
is preserved by open direct image and by products; hence these are module sheaves.
On sections, P(W)(V) = F(W ∩ V), with scalar action restricted from O_X(V).
The product universal property identifies the underlying module presheaf of each term
with the displayed Čech term and identifies all face maps, hence the differentials.
The same calculation gives the displayed augmentation formula and the term isomorphisms.
Restrict to U_i. Inserting index i in a tuple gives a homotopy of the augmented complex
whose alternating differential satisfies dh + hd = identity; degree zero is the sheaf
restriction augmentation. Thus the augmentation is a quasi-isomorphism on each U_i.
Homology sheaves vanish locally if they vanish on a covering, so it is a quasi-isomorphism
on X. This also covers the empty cover of the empty scheme and the zero module.
The sectionwise differential and augmentation specify the complex up to compatible
isomorphism, so the existential does not select arbitrary undetermined data. -/
theorem exists_cech_sheaf_resolution
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (F : X.Modules) :
    ∃ (D : CochainComplex X.Modules ℕ)
      (ε : (CochainComplex.single₀ X.Modules).obj F ⟶ D)
      (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor U).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).X p),
      (∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor U).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).d p (p + 1)) ∧
      (∀ (y : Fin 1 → ι) (V : X.Opens),
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫ ε.f 0).val ≫
          (e 0).hom ≫
            Pi.π (fun y : Fin 1 → ι =>
              ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
                (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat).obj
                  (op (∏ᶜ fun l => U (y l)))) y).app (op V) =
          F.presheafModuleCat.map (prod.snd : (∏ᶜ fun l => U (y l)) ⨯ V ⟶ V).op) ∧
      (∀ p : ℕ, Nonempty (D.X p ≅ ∏ᶜ fun y : Fin (p + 1) → ι =>
        (Scheme.Modules.pushforward (⨅ l, U (y l)).ι).obj (F.restrict (⨅ l, U (y l)).ι))) ∧
      QuasiIso ε := by
  obtain ⟨D, ε, e, hd, hε, hterms⟩ := exists_augmented_cech_sheaf_complex U F
  refine ⟨D, ε, e, hd, hε, hterms, ?_⟩
  exact quasiIso_of_restrict U hU ε fun i ↦
    augmented_cech_sheaf_quasiIso_restrict U F D ε e hd hε i

end AlgebraicGeometry
