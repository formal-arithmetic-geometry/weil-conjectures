/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Finite modules free at all primes are locally free on an affine cover

Source: Stacks Project, Algebra, Tag 0GWM, together with Tag 01XZ
(blueprint: lem-sc-affine-finite-module-free-locus).

## Main statements

- `Module.finite_free_at_primes_localized_cover`: the finite principal-open cover.
- `AlgebraicGeometry.isFiniteLocallyFree_tilde_of_free_at_primes`: its sheaf formulation.
-/

@[expose] public section

universe u v

namespace Module

/-- A finite module over a Noetherian ring which is free at every prime (its free locus
`Module.freeLocus A M`, the primes `p` with `M_p` free over `A_p`, is all of `Spec A`; `M_p` is
then finite free, `M` being finite) is finite free after localization at finitely many
elements generating the unit ideal.  The corresponding
principal opens give the finite locally free affine cover (Stacks, Tag 0GWM).
(blueprint: lem-sc-affine-finite-module-free-locus)

Proof:
1. By `lem-sc-noetherian-finite-module-finite-presentation`, finite modules over a
   Noetherian ring are finitely presented.
2. At each prime apply `lem-sc-finitely-presented-free-at-prime-principal` (Tag 0GWM)
   to get an element outside the prime whose localization is free. Localization preserves
   finiteness, so it is finite free; these principal opens cover the spectrum.
3. By `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`, quasi-compactness extracts
   finitely many of these opens, and their elements generate the unit ideal.
4. By `lem-weil-pbc-spec-module-tilde-sections` (Tags 01I1 and 01I2), sections on each
   principal open are the corresponding localized module, compatibly with restriction.
   The finite free modules therefore give local trivializations of the associated sheaf.
-/
theorem finite_free_at_primes_localized_cover
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hfree : Module.freeLocus A M = Set.univ) :
    ∃ (n : ℕ) (f : Fin n → A),
      Ideal.span (Set.range f) = ⊤ ∧
        ∀ i : Fin n,
          Module.Free (Localization.Away (f i))
            (LocalizedModule.Away (f i) M) ∧
          Module.Finite (Localization.Away (f i))
            (LocalizedModule.Away (f i) M) := by
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  have : Module.Projective A M := Module.freeLocus_eq_univ_iff.mp hfree
  obtain ⟨n, f, hf, hloc⟩ := Module.exists_standardFreeCover_of_finite_projective A M
  exact ⟨n, f, hf, fun i ↦ ⟨(hloc i).2, (hloc i).1⟩⟩

end Module

namespace AlgebraicGeometry

/-- The sheaf formulation of the finite principal-cover criterion: the associated module
sheaf is finite locally free, allowing different finite ranks on different opens.
Source: Stacks Project, Tags 0GWM, 01XZ, 01I1, 01I2, and Definition 17.14.1 (Tag 01C6).
(blueprint: lem-sc-affine-finite-module-free-locus)

Proof:
1. `lem-sc-noetherian-finite-module-finite-presentation` makes the finite module finitely
   presented over the Noetherian ring.
2. `lem-sc-finitely-presented-free-at-prime-principal` supplies a finite free principal
   neighborhood at each prime, using preservation of finiteness under localization.
3. `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` extracts a finite cover whose
   elements generate the unit ideal, as in `Module.finite_free_at_primes_localized_cover`.
4. `lem-weil-pbc-spec-module-tilde-sections` identifies the sheaf on these opens with the
   sheaves of the localized modules, compatibly on their principal-open bases. Their finite
   bases give local isomorphisms with finite free structure sheaves, exactly Tag 01C6.
-/
theorem isFiniteLocallyFree_tilde_of_free_at_primes
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hfree : Module.freeLocus A M = Set.univ) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (tilde (R := CommRingCat.of A) (ModuleCat.of A M)) := by
  classical
  let F := tilde (R := CommRingCat.of A) (ModuleCat.of A M)
  let P := (moduleSpecΓFunctor (R := CommRingCat.of A)).obj F
  let e := tilde.isoTop (R := CommRingCat.of A) (ModuleCat.of A M)
  have : Module.Finite A P := Module.Finite.equiv e.toLinearEquiv
  have hP : Module.freeLocus A P = Set.univ := by
    exact (Module.freeLocus_congr e.toLinearEquiv).symm.trans hfree
  obtain ⟨n, f, hf, hloc⟩ := Module.finite_free_at_primes_localized_cover hP
  have (i : Fin n) : Module.Free (Localization.Away (f i))
      (LocalizedModule.Away (f i) P) := (hloc i).1
  have (i : Fin n) : Module.Finite (Localization.Away (f i))
      (LocalizedModule.Away (f i) P) := (hloc i).2
  let κ (i : ULift.{u} (Fin n)) :=
    Module.Free.ChooseBasisIndex (Localization.Away (f i.down))
      (LocalizedModule.Away (f i.down) P)
  let j (i : ULift.{u} (Fin n)) := Spec.map (show CommRingCat.of A ⟶
      CommRingCat.of (Localization.Away (f i.down)) from
    CommRingCat.ofHom (algebraMap A (Localization.Away (f i.down))))
  have hj (i : ULift.{u} (Fin n)) : (j i).opensRange =
      PrimeSpectrum.basicOpen (f i.down) :=
    Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of A) (f i.down)
  refine Scheme.Modules.isFiniteLocallyFree_of_restrict_iso_free F j ?_ κ ?_
  · simpa only [hj, iSup_ulift] using
      (PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hf)
  · intro i
    exact Scheme.Modules.nonempty_restrict_iso_free_of_localizedModule F (f i.down)
      (Module.Free.chooseBasis (Localization.Away (f i.down))
        (LocalizedModule.Away (f i.down) P)).repr

end AlgebraicGeometry
