/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.LocallyPerfect.FinitelyGenerated

/-!
# Subcomplexes spanned by a subcomplex and finitely many global sections

Let `N` be a cochain complex of pro-étale sheaves of `Λ`-modules on a scheme `Y`, let
`φ : S ⟶ N` be a chain map and let `xₖ` be finitely many global sections of terms of `N`. This
file defines the subcomplex `span φ x ⊆ N` spanned by the image of `φ` and the `xₖ` (together
with their differentials), as the image of the chain map `S ⨿ ⨿ₖ unitDisk (p k) ⟶ N`.

In the proof that dualizable complexes are locally perfect (Stacks, Tag 0FPV), `φ` is the
inclusion of the constant complex `c(E₀)` which agrees with `N` in high degrees, and the `xₖ`
are the sections provided by the local retract statement; the resulting subcomplex agrees with
`N` in high degrees, and its terms in the other degrees are globally finitely generated.

## Main definitions

- `AlgebraicGeometry.ProEtale.span`, `AlgebraicGeometry.ProEtale.spanι`: the subcomplex and its
  inclusion.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open _root_.AlgebraicGeometry.Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {Y : Scheme.{u}}
  {S N : CochainComplex (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ℤ} (φ : S ⟶ N)
  {m : ℕ} (p : Fin m → ℤ) (x : ∀ k, (N.X (p k)).obj.obj (op (terminalProEt Y)))

/-- The chain map `S ⨿ ⨿ₖ unitDisk (p k) ⟶ N` given by `φ` and the sections `xₖ`. -/
noncomputable def spanDesc : S ⨿ ∐ (fun k ↦ unitDisk (X := Y) (Λ := Λ) (p k)) ⟶ N :=
  coprod.desc φ (generatedSubcomplexDesc N p x)

/-- The subcomplex of `N` spanned by the image of `φ` and the sections `xₖ`. -/
noncomputable def span : CochainComplex (Sheaf (Scheme.ProEt.topology Y)
    (ModuleCat.{u + 1} Λ)) ℤ :=
  Limits.image (spanDesc φ p x)

/-- The inclusion of the subcomplex `span φ p x` into `N`. -/
noncomputable def spanι : span φ p x ⟶ N :=
  Limits.image.ι _

instance : Mono (spanι φ p x) := by
  dsimp [spanι]
  infer_instance

instance (i : ℤ) : Mono ((spanι φ p x).f i) :=
  (HomologicalComplex.eval _ (.up ℤ) i).map_mono _

/-- The factorisation of `φ` through `span φ p x`. -/
noncomputable def spanLift : S ⟶ span φ p x :=
  coprod.inl ≫ factorThruImage (spanDesc φ p x)

@[reassoc (attr := simp)]
lemma spanLift_spanι : spanLift φ p x ≫ spanι φ p x = φ := by
  simp [spanLift, spanι, spanDesc]

/-- The sections `xₖ` lie in `span φ p x`. -/
lemma exists_spanι_f_app_eq (k : Fin m) :
    ∃ x' : ((span φ p x).X (p k)).obj.obj (op (terminalProEt Y)),
      ((spanι φ p x).f (p k)).hom.app _ x' = x k := by
  refine ⟨unitHomEquiv _ ((HomologicalComplex.doubleXIso₀ _ _).inv ≫
    (Sigma.ι _ k ≫ coprod.inr ≫ factorThruImage (spanDesc φ p x)).f (p k)), ?_⟩
  rw [← unitHomEquiv_comp, Category.assoc, ← HomologicalComplex.comp_f, Category.assoc,
    Category.assoc, spanι, image.fac, spanDesc, coprod.inr_desc, generatedSubcomplexDesc,
    Sigma.ι_desc, unitDiskHom,
    ← HomologicalComplex.evalCompCoyonedaCorepresentableByDoubleId_homEquiv_apply (h := by simp),
    Equiv.apply_symm_apply]
  exact (unitHomEquiv (N.X (p k))).apply_symm_apply (x k)

/-- In a degree where `φ` is an epimorphism, the inclusion of `span φ p x` is an
isomorphism. -/
lemma isIso_spanι_f (i : ℤ) [Epi (φ.f i)] : IsIso ((spanι φ p x).f i) := by
  have : Epi ((spanLift φ p x).f i ≫ (spanι φ p x).f i) := by
    rw [← HomologicalComplex.comp_f, spanLift_spanι]
    infer_instance
  have : Epi ((spanι φ p x).f i) := epi_of_epi_fac rfl
  exact isIso_of_mono_of_epi _

/-- The terms of `span φ p x` in the degrees where `S` has globally finitely generated terms are
globally finitely generated. -/
lemma isGloballyFinitelyGenerated_span_X (i : ℤ) (hS : IsGloballyFinitelyGenerated (S.X i)) :
    IsGloballyFinitelyGenerated ((span φ p x).X i) := by
  have : Epi ((factorThruImage (spanDesc φ p x)).f i) :=
    (HomologicalComplex.eval _ (.up ℤ) i).map_epi _
  exact ((hS.coprod (isGloballyFinitelyGenerated_sigma_unitDisk_X p i)).of_iso
    (PreservesColimitPair.iso (HomologicalComplex.eval _ (.up ℤ) i) _ _).symm).of_epi
      ((factorThruImage (spanDesc φ p x)).f i)

end AlgebraicGeometry.ProEtale
