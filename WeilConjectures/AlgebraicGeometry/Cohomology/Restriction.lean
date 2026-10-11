/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AcyclicResolution
public import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Restricting resolutions to open subschemes

Restriction along an open immersion `f : X ⟶ Y` is exact and sends injective `𝒪_Y`-modules to
flasque, hence acyclic, `𝒪_X`-modules. So the restriction of an injective resolution of `ℱ` is an
acyclic resolution of `ℱ|_X`, which computes its cohomology
(`AlgebraicGeometry.Scheme.Modules.H.cyclesZeroSuccAddEquiv`).

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exactAt_restrict`: restriction keeps a complex exact.
- `AlgebraicGeometry.Scheme.Modules.restrictCyclesIso`: the cycles of the restricted complex are
  the restriction of the cycles.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

instance : PreservesFiniteLimits (restrictFunctor f) :=
  PreservesLimitsOfSize.preservesFiniteLimits _

instance : PreservesFiniteColimits (restrictFunctor f) :=
  PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _

/-- The restriction of a complex of `𝒪_Y`-modules along an open immersion. -/
noncomputable abbrev restrictComplex (K : CochainComplex Y.Modules ℕ) :
    CochainComplex X.Modules ℕ :=
  ((restrictFunctor f).mapHomologicalComplex _).obj K

/-- Restriction along an open immersion keeps a complex exact. -/
lemma exactAt_restrict {K : CochainComplex Y.Modules ℕ} {i : ℕ} (h : K.ExactAt i) :
    (restrictComplex f K).ExactAt i :=
  ShortComplex.Exact.map h (restrictFunctor f)

/-- The cycles of the restriction of a complex are the restriction of its cycles. -/
noncomputable def restrictCyclesIso (K : CochainComplex Y.Modules ℕ) (i : ℕ) :
    (restrictComplex f K).cycles i ≅ (K.cycles i).restrict f :=
  (K.sc i).mapCyclesIso (restrictFunctor f)

@[reassoc]
lemma restrictCyclesIso_hom_iCycles (K : CochainComplex Y.Modules ℕ) (i : ℕ) :
    (restrictCyclesIso f K i).hom ≫ (restrictFunctor f).map (K.iCycles i) =
      (restrictComplex f K).iCycles i :=
  (K.sc i).mapCyclesIso_hom_iCycles (restrictFunctor f)
@[reassoc]
lemma restrictCyclesIso_inv_iCycles (K : CochainComplex Y.Modules ℕ) (i : ℕ) :
    (restrictCyclesIso f K i).inv ≫ (restrictComplex f K).iCycles i =
      (restrictFunctor f).map (K.iCycles i) := by
  rw [← restrictCyclesIso_hom_iCycles, Iso.inv_hom_id_assoc]

@[reassoc]
lemma map_toCycles_restrictCyclesIso_inv (K : CochainComplex Y.Modules ℕ) (n : ℕ) :
    (restrictFunctor f).map (K.toCycles n (n + 1)) ≫ (restrictCyclesIso f K (n + 1)).inv =
      (restrictComplex f K).toCycles n (n + 1) := by
  rw [← cancel_mono ((restrictComplex f K).iCycles (n + 1)), Category.assoc,
    restrictCyclesIso_inv_iCycles, ← Functor.map_comp, HomologicalComplex.toCycles_i,
    HomologicalComplex.toCycles_i]
  rfl

/-- Restricting global sections of `M` to the open subscheme `X`. -/
noncomputable def restrictSections (M : Y.Modules) : Γ(M, ⊤) →+ Γ(M.restrict f, ⊤) :=
  (M.presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op).hom

lemma restrictSections_naturality {M N : Y.Modules} (φ : M ⟶ N) (s : Γ(M, ⊤)) :
    restrictSections f N (φ.app ⊤ s) = ((restrictFunctor f).map φ).app ⊤ (restrictSections f M s) :=
  congrArg (fun g ↦ g s) (congrArg AddCommGrpCat.Hom.hom (φ.mapPresheaf.naturality
    (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op)).symm
/-- Restriction of global sections of the cycles `Zⁿ⁺¹` of `K` to sections of the cycles of the
restricted complex. -/
noncomputable def restrictCyclesSections (K : CochainComplex Y.Modules ℕ) (n : ℕ) :
    Γ(K.cycles (n + 1), ⊤) →+ Γ((restrictComplex f K).cycles (n + 1), ⊤) :=
  ((restrictCyclesIso f K (n + 1)).inv.app ⊤).hom.comp (restrictSections f (K.cycles (n + 1)))

lemma range_app_toCycles_le_comap_restrictCyclesSections (K : CochainComplex Y.Modules ℕ)
    (n : ℕ) :
    ((K.toCycles n (n + 1)).app ⊤).hom.range ≤
      (((restrictComplex f K).toCycles n (n + 1)).app ⊤).hom.range.comap
        (restrictCyclesSections f K n) := by
  rintro _ ⟨t, rfl⟩
  refine ⟨restrictSections f (K.X n) t, ?_⟩
  change _ = ((restrictCyclesIso f K (n + 1)).inv.app ⊤)
    (restrictSections f _ ((K.toCycles n (n + 1)).app ⊤ t))
  rw [restrictSections_naturality, ← ConcreteCategory.comp_apply, ← Hom.comp_app,
    map_toCycles_restrictCyclesIso_inv]
  rfl

variable {ℱ : Y.Modules}

/-- **Restriction of cohomology classes to an open subscheme**, `H^{n+1}(Y, ℱ) ⟶ H^{n+1}(X, ℱ|_X)`
for an open immersion `f : X ⟶ Y`, computed with an injective resolution `I` of `ℱ`: a class is
represented by a section of the cycles `Zⁿ⁺¹` of `I` (`H.cyclesZeroSuccAddEquiv`), which is
restricted to `X`, where it represents a class of the acyclic resolution `I|_X` of `ℱ|_X`. -/
noncomputable def H.restrictSucc (I : InjectiveResolution ℱ) (n : ℕ) :
    ℱ.H (n + 1) →+ (ℱ.restrict f).H (n + 1) :=
  let K := I.cocomplex
  have hK' : ∀ j, (restrictComplex f K).ExactAt (j + 1) := fun j ↦
    exactAt_restrict f (I.cocomplex_exactAt_succ j)
  have hacyc' : ∀ j m, Subsingleton (((restrictComplex f K).X j).H (m + 1)) := fun j m ↦
    subsingleton_H_restrict_of_injective f (K.X j) m
  (H.map ((restrictCyclesIso f K 0).hom ≫ (restrictFunctor f).map I.isoCyclesZero.inv)
      (n + 1)).comp <|
  (H.cyclesZeroSuccAddEquiv (restrictComplex f K) hK' hacyc' n).symm.toAddMonoidHom.comp <|
  (QuotientAddGroup.map _ _ (restrictCyclesSections f K n)
      (range_app_toCycles_le_comap_restrictCyclesSections f K n)).comp <|
  (H.cyclesZeroSuccAddEquiv K I.cocomplex_exactAt_succ
      (fun _ m ↦ subsingleton_H_of_injective _ m) n).toAddMonoidHom.comp
    (H.map I.isoCyclesZero.hom (n + 1))

end AlgebraicGeometry.Scheme.Modules
