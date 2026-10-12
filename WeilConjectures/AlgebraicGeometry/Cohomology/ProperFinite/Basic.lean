/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveFinite
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-!
# Finiteness of cohomology over a noetherian ring: formal properties

For a scheme `X` with a morphism `p : X ⟶ Spec A`, `AlgebraicGeometry.Scheme.Modules.FiniteH p M`
says that every cohomology group `H^q(X, M)` is a finite `A`-module. We record its stability
under isomorphisms and short exact sequences, its invariance under pushforward along affine
morphisms, and its relation with the sections of the higher direct images along `p`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- `FiniteH p M` says that every cohomology group `H^q(X, M)` is a finite `A`-module, for the
`A`-module structure `AlgebraicGeometry.Scheme.Modules.moduleHOfSpec p`. -/
def FiniteH (p : X ⟶ Spec (.of A)) (M : X.Modules) : Prop :=
  ∀ q : ℕ, letI := moduleHOfSpec p M q; Module.Finite A (M.H q)

variable {p : X ⟶ Spec (.of A)}

lemma FiniteH.of_iso {M N : X.Modules} (e : M ≅ N) (h : FiniteH p M) : FiniteH p N :=
  fun q ↦ finite_H_of_iso p e q (h q)

lemma FiniteH.of_isZero {M : X.Modules} (h : IsZero M) : FiniteH p M := fun q ↦ by
  letI := moduleHOfSpec p M q
  have := subsingleton_H_of_isZero h q
  infer_instance

lemma FiniteH.X₃ [IsNoetherianRing A] {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : FiniteH p S.X₁) (h₂ : FiniteH p S.X₂) : FiniteH p S.X₃ :=
  fun q ↦ finite_H_of_shortExact p hS q (h₂ q) (h₁ (q + 1))

/-- The middle term of a short exact sequence has finite cohomology if the outer terms do. -/
lemma FiniteH.X₂ [IsNoetherianRing A] {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : FiniteH p S.X₁) (h₃ : FiniteH p S.X₃) : FiniteH p S.X₂ :=
  sorry

/-- The first term of a short exact sequence has finite cohomology if the other two do. -/
lemma FiniteH.X₁ [IsNoetherianRing A] {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₂ : FiniteH p S.X₂) (h₃ : FiniteH p S.X₃) : FiniteH p S.X₁ :=
  sorry

/-- Finiteness of cohomology is invariant under pushforward along an affine morphism. -/
theorem finiteH_pushforward_iff {Y : Scheme.{u}} (i : X ⟶ Y) [IsAffineHom i]
    (p : Y ⟶ Spec (.of A)) (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] :
    FiniteH p ((pushforward i).obj M) ↔ FiniteH (i ≫ p) M :=
  sorry

/-- Over `Spec A`, finiteness of the cohomology of `M` is finiteness of the global sections of
the higher direct images of `M`, these being the cohomology groups. -/
theorem finiteH_iff_finite_sections_higherDirectImage (p : X ⟶ Spec (.of A)) [QuasiCompact p]
    [IsSeparated p] [HasInjectiveResolutions X.Modules] (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] :
    FiniteH p M ↔
      ∀ q, Module.Finite Γ(Spec (.of A), ⊤) Γ((higherDirectImage p q).obj M, ⊤) :=
  sorry

end AlgebraicGeometry.Scheme.Modules
