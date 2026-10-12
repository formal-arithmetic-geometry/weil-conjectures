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
import Sheaf.AlgebraicGeometry.ProjHomogeneousSectionTensorPowers
import Sheaf.AlgebraicGeometry.SectionClearingDenominatorsQCQS
import Sheaf.AlgebraicGeometry.SectionRestrictionSTorsion
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Noetherian

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
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)
  let L := Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (0 + (d : ℤ))
  let σ := (Proj.unitToTwist hf).app ⊤ (Scheme.Modules.unitSectionsEquiv ⊤ 1)
  have : CompactSpace P :=
    QuasiCompact.compactSpace_of_compactSpace (Proj.toSpecZero _)
  have : QuasiSeparatedSpace P := quasiSeparatedSpace_of_quasiSeparated (Proj.toSpecZero _)
  have : IsNoetherianRing (MvPolynomial.homogeneousSubmodule (Fin 2) k 0) :=
    isNoetherianRing_of_ringEquiv k (MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin 2) k)
  have : IsLocallyNoetherian P :=
    LocallyOfFiniteType.isLocallyNoetherian (Proj.toSpecZero _)
  have : G.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType P G).mp hG).1
  obtain ⟨hL, hU, a, b, ha, hb⟩ := proj_homogeneous_section_tensor_powers k hd hf
  let : L.IsInvertible := hL
  constructor
  · intro s
    obtain ⟨r, t, ht⟩ := Scheme.Modules.exists_tensorPowSection_eq_restrict_qcqs
      L σ G _ hU s
    let e := whiskerLeftIso G (a r)
    refine ⟨r, e.hom.app ⊤ t, ?_⟩
    rw [← Scheme.Modules.Hom.app_presheaf_map, ht]
    rw [← Scheme.Modules.rightUnitor_inv_comp_whiskerLeft_app]
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app]
    change (((ρ_ G).inv ≫ G ◁ Scheme.Modules.tensorPowSection
      (Scheme.Modules.homOfGlobalSection L σ) r ≫ G ◁ (a r).hom).app _) s = _
    rw [← MonoidalCategory.whiskerLeft_comp, ha]
  · intro r t ht
    have : (L.tensorPow r).IsInvertible := inferInstance
    have := Scheme.Modules.IsInvertible.of_iso (a r)
    have := Scheme.Modules.isQuasicoherent_tensorObj (X := P) G
      (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (0 + ((r • d : ℕ) : ℤ)))
    obtain ⟨n, hn⟩ := Scheme.Modules.section_restriction_s_torsion
      (X := P) L _ σ t _ hU ht
    refine ⟨n, ?_⟩
    let T := Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (0 + ((r • d : ℕ) : ℤ))
    have hm :
        (ρ_ (G ⊗ T)).inv ≫ (G ⊗ T) ◁
            Scheme.Modules.tensorPowSection (Scheme.Modules.homOfGlobalSection L σ) n ≫
          (α_ G T (L.tensorPow n)).hom ≫ G ◁ (b (0 + ((r • d : ℕ) : ℤ)) n).hom =
        G ◁ Proj.twistMul (0 + ((r • d : ℕ) : ℤ))
          (SetLike.pow_mem_graded n hf) := by
      rw [← hb, whiskerLeft_comp, whiskerLeft_comp, whiskerLeft_rightUnitor_inv]
      simp only [Category.assoc]
      rw [associator_naturality_right_assoc]
    rw [← hm, ← Category.assoc, Scheme.Modules.Hom.comp_app,
      ConcreteCategory.comp_apply, Scheme.Modules.rightUnitor_inv_comp_whiskerLeft_app,
      hn, map_zero]

end AlgebraicGeometry
