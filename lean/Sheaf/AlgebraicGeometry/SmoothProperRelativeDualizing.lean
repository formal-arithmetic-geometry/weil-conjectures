/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # The dualizing complex of a smooth proper morphism

Source: Stacks Project, Tag 0BRT, Lemma 48.15.7
(blueprint: lem-sc-smooth-proper-relative-dualizing-general).
-/

universe u wX wS

open CategoryTheory

namespace AlgebraicGeometry

/-- For a smooth proper morphism of relative dimension `d` over a Noetherian scheme,
the right adjoint of derived pushforward takes the structure sheaf to `Ωᵈ[d]`.
Source: Stacks Project, Tag 0BRT, Lemma 48.15.7
(blueprint: lem-sc-smooth-proper-relative-dualizing-general).

`R` and `comparison` specify the restriction of the recorded derived direct image to
quasi-coherent complexes; `adj` identifies `a` as its right adjoint. `O` and `hO` specify
the structure sheaf in degree zero in that full subcategory. Relative differentials are
the shared sheaf `f.relativeDifferentials`, canonically the diagonal conormal sheaf
(Tag 08S2); `exteriorSheaf` is its sheafified sectionwise exterior power.

Proof, following the node:
1. Properness implies finite type, so `X` and `X ×_S X` are Noetherian
(lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-proper-base-change).
The Noetherian adjoint theorem supplies right adjoints `a` and `c` for `f` and its diagonal
(lem-pc-noetherian-derived-direct-image-right-adjoint).
2. The diagonal is a Koszul-regular immersion of codimension `d`, hence perfect and proper
(lem-sc-smooth-proper-diagonal-koszul-regular).
3. Smoothness implies flatness (lem-pc-smooth-flat). The diagonal evaluation identity gives
`O_X ≅ c(Lpr₁* a(O_S))` (lem-sc-smooth-proper-diagonal-pushforward-structure, Tag 0E2Q).
4. The perfect-immersion projection formula identifies this with
`LΔ* Lpr₁* a(O_S) ⊗ᴸ c(O_{X ×_S X})`
(lem-sc-smooth-proper-diagonal-tensor-formula, Tag 0A9U).
5. Koszul duality identifies `c(O_{X ×_S X})` with `⋀ᵈ N_Δ[-d]`
(lem-sc-smooth-proper-diagonal-koszul-dual, Tag 0BR0).
6. The diagonal conormal sheaf is `Ω¹_{X/S}`
(lem-sc-smooth-proper-diagonal-conormal-differentials, Tag 08S2).
7. Since `pr₁ ∘ Δ = id`, these give `O_X ≅ a(O_S) ⊗ᴸ ⋀ᵈ N_Δ[-d]`.
The conormal sheaf is finite locally free of rank `d`
(lem-sc-smooth-omega-finite-locally-free), so its dual has invertible top exterior power.
Cancel that shifted invertible object. Its inverse is `⋀ᵈ C_Δ[d] = Ωᵈ_{X/S}[d]`, giving
the asserted isomorphism. -/
theorem smoothProper_dualizing
    (X S : Scheme.{u}) [CompactSpace S] [IsLocallyNoetherian S]
    (f : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory S)
    (comparison : R ⋙ (schemeDerivedQCohProperty S).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory X)
    (adj : R ⊣ a) (O : schemeDerivedQCohCategory S)
    (hO : O.obj ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings S.toRingedSpace))) :
    Nonempty ((a.obj O).obj ≅
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (Scheme.Modules.exteriorSheaf f.relativeDifferentials d))⟦(d : ℤ)⟧) := by
  sorry

end AlgebraicGeometry
