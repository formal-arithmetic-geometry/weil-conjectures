/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.InvertibleSectionLocalization
import Sheaf.AlgebraicGeometry.ProjectiveLineTwistMultiplication
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

/-!
# Serre comparison for the graded section module

Source: Stacks Project, Coherent Modules, Proposition 0BXD (blueprint:
lem-sc-p1-serre-section-module-comparison).

Let `P = Proj k[x₀,x₁]` and `G(n) = G ⊗ 𝒪_P(n)` with `𝒪_P(n) = Proj.twist 𝒜 n`. The
associated sheaf `M~` of `M_{≥0} = ⨁_{n ≥ 0} Γ(P, G(n))` is determined by its sections
`Γ(D₊(f), M~) = (M_{≥0})_{(f)}` on the basis of standard opens `D₊(f)`
(`f` homogeneous of positive degree), and the canonical morphism `M~ ⟶ G` is, on
`D₊(f)`, the degree-zero localization map `t / fʳ ↦ s`, where `s ∈ Γ(D₊(f), G)` is the
section with `s ⊗ fʳ = t|_{D₊(f)}` (multiplication by `fʳ`, the morphism
`G ◁ Proj.unitToTwist`, is invertible on `D₊(f)`). A morphism of sheaves is an
isomorphism iff it is bijective on the sections over a basis, so the node's conclusion
is stated as the bijectivity of these localization maps: surjectivity (every section
over `D₊(f)` is some `t / fʳ`) and injectivity (`t / fʳ ↦ 0` forces `fᵉ t = 0`). No
graded module, associated-sheaf or comparison-morphism declaration on `Proj` exists in
the library (the TODO of `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist`),
so the statement is written through these section-level maps.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/--
For a coherent module `G` on `P = Proj k[x₀,x₁]`, the canonical morphism from the
sheaf associated to the non-negative graded section module
`M_{≥0} = ⨁_{n ≥ 0} Γ(P, G ⊗ 𝒪_P(n))` to `G` is an isomorphism: on every standard
open `D₊(f)` (`f` homogeneous of degree `d > 0`) the degree-zero localization map
`(M_{≥0})_{(f)} → Γ(D₊(f), G)`, `t / fʳ ↦ s` with `s ⊗ fʳ = t|_{D₊(f)}`, is surjective
(first clause) and injective (second clause: `t|_{D₊(f)} = 0` gives `fᵉ t = 0`).

Source: Stacks Project, Coherent Modules, Proposition 0BXD, final paragraph
of the proof (blueprint: lem-sc-p1-serre-section-module-comparison).
Proof: the standard opens `D₊(x₀)` and `D₊(x₁)` cover `Proj k[x₀,x₁]`;
on `D₊(xᵢ)` the associated sheaf of `N = ⨁_{m ∈ ℤ} Γ(P, G(m))` has sections `N_{(xᵢ)}`
(def-weil-pbc-proj-twisting-sheaf); the non-negative truncation `M_{≥0}` has the same
degree-zero localization (multiply a negative-degree representative by a power of `xᵢ`);
lem-sc-p1-invertible-section-localization applied to `𝒪_P(1)`, `s = xᵢ` and the
quasi-coherent `G` (coherent on the locally Noetherian `P`) identifies `N_{(xᵢ)}` with
`Γ(D₊(xᵢ), G)` through the canonical localization map; the local isomorphisms glue. -/
theorem serreSectionModuleComparison
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (hG : RingedSpace.IsCoherent
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toRingedSpace G)
    {d : ℕ} (hd : 0 < d) {f : MvPolynomial (Fin 2) k}
    (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k d) :
    (∀ s : Γ(G, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) f),
      ∃ (r : ℕ) (t : Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
          (0 + ((r • d : ℕ) : ℤ)), ⊤)),
        (G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
          (0 + ((r • d : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top :
              Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op t =
          Scheme.Modules.Hom.app
            ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded r hf))
            (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) f) s) ∧
    (∀ (r : ℕ) (t : Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
          (0 + ((r • d : ℕ) : ℤ)), ⊤)),
      (G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
          (0 + ((r • d : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top :
              Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op t = 0 →
        ∃ e : ℕ, Scheme.Modules.Hom.app
          (G ◁ Proj.twistMul (0 + ((r • d : ℕ) : ℤ)) (SetLike.pow_mem_graded e hf)) ⊤ t = 0) := by
  sorry

end AlgebraicGeometry
