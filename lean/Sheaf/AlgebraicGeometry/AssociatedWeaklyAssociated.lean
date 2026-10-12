module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
import Sheaf.RingTheory.AnnihilatorEqIffMinimalPrimeOfFG
import Sheaf.Topology.PresheafModuleStalkFunctor

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-! # Associated and weakly associated points at finitely generated stalks
Source: literature/stacks-project/divisors.tex, Tag 05AR (blueprint: lem-sc-ass-weakass-fg-stalk).
-/

/-- Association and weak association agree at a point whose maximal ideal is finitely
generated (Stacks Tag 05AR, first assertion). The stalk `F_x` is the
`𝒪_{X,x}`-module `(RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F`
(def-weil-pbc-module-stalk); `x` is associated when `m_x` is the annihilator (colon ideal)
of some `s ∈ F_x`, and weakly associated when `m_x` is a minimal prime over such an
annihilator (the form of `Ideal.annihilator_eq_iff_mem_minimalPrimes_of_fg`).

Proof: identify the local ring and stalk module using [def-weil-pbc-module-stalk], then
apply [lem-sc-ass-weakass-fg-prime] to the maximal ideal and stalk module.
(blueprint: lem-sc-ass-weakass-fg-stalk) -/
theorem associated_iff_weaklyAssociated_of_fg_stalk
    (X : Scheme.{u}) (F : X.Modules) (x : X)
    (hF : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F)
    (hfg : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).FG) :
    (∃ s : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F,
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
        (⊥ : Submodule (X.presheaf.stalk x)
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)).colon {s}) ↔
    (∃ s : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F,
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
        ((⊥ : Submodule (X.presheaf.stalk x)
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)).colon
            {s}).minimalPrimes) := by
  sorry

end AlgebraicGeometry
