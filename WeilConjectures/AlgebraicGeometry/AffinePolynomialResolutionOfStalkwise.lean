/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectMorphism
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPolynomial.Basic
import WeilConjectures.AlgebraicGeometry.AffinePolynomialLocalizedFiniteProjectiveDimension
import WeilConjectures.RingTheory.ProjectiveDimensionLocusOpen
import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension

/-! # A bounded polynomial resolution from finite stalk Tor dimension

Source: Stacks Project, Tag 069C, proof of (3) implies (1), and Tags 068X and 068W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

private theorem finite_projectiveDimension_of_localized
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (h : ∀ p : PrimeSpectrum R, ∃ n : ℕ,
      HasProjectiveDimensionLE (M.localizedModule p.asIdeal.primeCompl) n) :
    ∃ n : ℕ, HasProjectiveDimensionLE M n := by
  classical
  let O (n : ℕ) : Set (PrimeSpectrum R) :=
    {p | HasProjectiveDimensionLE (M.localizedModule p.asIdeal.primeCompl) n}
  have hcover : Set.univ ⊆ ⋃ n, O n := by
    intro p _
    obtain ⟨n, hn⟩ := h p
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O
    (fun n ↦ ModuleCat.isOpen_hasProjectiveDimensionLE_locus M n) hcover
  refine ⟨s.sup id, (M.hasProjectiveDimensionLE_iff_forall_primeSpectrum _).mpr ?_⟩
  intro p
  obtain ⟨n, hn, hpn⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ p))
  have : HasProjectiveDimensionLE (M.localizedModule p.asIdeal.primeCompl) n := hpn
  exact hasProjectiveDimensionLT_of_ge _ (n + 1) (s.sup id + 1)
    (Nat.add_le_add_right (Finset.le_sup (f := id) hn) 1)

namespace AlgebraicGeometry

/-- A finite polynomial presentation of an affine chart admits a bounded projective
resolution of its coordinate algebra over the polynomial ring
(Stacks, Tags 069C, 068X and 068W). -/
theorem affinePolynomial_boundedResolution_of_stalkwise
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hperfect : HasStalkwiseFiniteTorDimension f)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (n : ℕ) (g : MvPolynomial (Fin n) Γ(Y, U) →+* Γ(X, V))
    (hg : Function.Surjective g)
    (hcomp : g.comp (MvPolynomial.C) = (f.appLE U V e).hom) :
    ∃ (d : ℕ) (P : ProjectiveResolution
        ((ModuleCat.restrictScalars g).obj (ModuleCat.of Γ(X, V) Γ(X, V)))),
      ∀ i : ℕ, d < i → IsZero (P.complex.X i) := by
  let R := MvPolynomial (Fin n) Γ(Y, U)
  let M := (ModuleCat.restrictScalars g).obj (ModuleCat.of Γ(X, V) Γ(X, V))
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsNoetherianRing R := inferInstance
  let φ : ModuleCat.of R R ⟶ M :=
    ModuleCat.semilinearMapAddEquiv g _ _ g.toSemilinearMap
  have hφ : Function.Surjective φ.hom := hg
  have : Module.Finite R M := Module.Finite.of_surjective φ.hom hφ
  obtain ⟨d, hd⟩ := finite_projectiveDimension_of_localized (R := R) M
    (affinePolynomial_localized_finiteProjectiveDimension_of_stalkwise
      f hperfect U hU V hV e n g hg hcomp)
  have : HasProjectiveDimensionLE M d := hd
  let := HasExt.standard (ModuleCat.{u} R)
  obtain ⟨P, hP⟩ := (ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE M d).mpr
    hd
  exact ⟨d, P, hP⟩

end AlgebraicGeometry
