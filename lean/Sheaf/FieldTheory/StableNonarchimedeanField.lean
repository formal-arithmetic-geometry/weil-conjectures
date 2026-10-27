module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Stable nonarchimedean valued fields

Source: Bosch–Güntzer–Remmert, Non-Archimedean Analysis, Definition 3.6.1/1,
printed p.156 (blueprint: def-trf-stable-nonarchimedean-field).

Stability requires an orthogonal basis for the minimal-polynomial spectral norm on
every finite extension. Neither completeness nor separability is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u v

/-- A nonarchimedean valued field is stable if every finite extension, endowed with
its minimal-polynomial spectral norm, has an orthogonal basis. The finite supremum
is the maximum of the weighted coefficient norms; the basis has positive cardinality
because an extension field is nontrivial. No normed-field structure on the extension
is assumed: its norm is specifically `spectralNorm K E`.

Source: Bosch–Güntzer–Remmert, Non-Archimedean Analysis, Definition 3.6.1/1,
printed p.156 (blueprint: def-trf-stable-nonarchimedean-field). -/
def IsStableNonarchimedeanField (K : Type u) [NormedField K] [IsUltrametricDist K] :
    Prop :=
  ∀ (E : Type (max u v)) [Field E] [Algebra K E] [FiniteDimensional K E],
    ∃ b : Module.Basis (Fin (Module.finrank K E)) K E,
      ∀ a : Fin (Module.finrank K E) → K,
        spectralNorm K E (∑ i, a i • b i) = ⨆ i, ‖a i‖ * spectralNorm K E (b i)
