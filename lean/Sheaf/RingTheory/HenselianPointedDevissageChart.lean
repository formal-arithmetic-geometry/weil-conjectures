/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.TraceFormula.CompleteAlgebraDevissage
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Sheaf.AlgebraicGeometry.PointedAffineDevissage
import WeilConjectures.RingTheory.HenselianLocalRootLifting
import WeilConjectures.RingTheory.RootLiftingEtaleRetraction
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Pointed complete dévissage over a henselian local base

Source: Stacks Project, flat.tex, Tags 05I1, 05HZ and the first proof paragraph of
Tag 05PG (blueprint: lem-sfb-henselian-pointed-devissage-chart).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace AlgebraicGeometry

/-- The actual fraction module at the marked prime, with its canonical local-ring action.

Source: Stacks Project, flat.tex, Tag 05PG, first proof paragraph; module localization
as in Algebra, localization of modules
(blueprint: lem-sfb-henselian-pointed-devissage-chart). -/
noncomputable def henselianChartLocalization {C : Type u} [CommRing C]
    (q : PrimeSpectrum C) (N : ModuleCat.{v} C) :
    ModuleCat.{max u v} (Localization.AtPrime q.asIdeal) :=
  letI := LocalizedModule.moduleOfIsLocalization (S := q.asIdeal.primeCompl)
    (M := N) (T := Localization.AtPrime q.asIdeal)
  ModuleCat.of (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl N)

/-- Existence of the finite-type pointed algebraic chart used in local flattening.

Source: Stacks Project, flat.tex, Tags 05I1 and 05HZ, and Tag 05PG, first proof
paragraph (blueprint: lem-sfb-henselian-pointed-devissage-chart).

Proof:
1. Write the local essentially finite type algebra as `(C₀)_{q₀}`. The `C₀`-span
   of finitely many generators of `P` is a finite module `N₀` with localization `P`.
   This uses the fraction construction of `def-weil-pbc-module-localization`.
2. Apply `lem-sfb-pointed-affine-devissage-etale-existence` to the affine scheme
   and the tilde of `N₀`, using `lem-weil-pbc-lft-affine-pairs`,
   `lem-weil-pbc-spec-module-tilde-sections`, `lem-weil-pbc-affine-tilde-gamma-adjunction`
   and `lem-weil-pbc-quasi-coherent-finite-type-affine` for the affine dictionary.
3. `lem-weil-pbc-henselian-local-root-lifting` and
   `lem-weil-pbc-root-lifting-etale-retraction` give the marked base retraction.
   Restrict the pointed chain by `lem-trf-devissage-pointed-restriction`.
   `lem-weil-pbc-fibre-product-affine-spectra` and
   `lem-weil-pbc-tilde-pullback-base-change` identify `C` and `N` after base change.
   Etale cancellation and base change (`lem-weil-pbc-etale-composition-cancellation`,
   `lem-weil-pbc-etale-scheme-base-change`) and the affine finite-presentation
   criterion (`lem-weil-pbc-lfp-affine-opens-finite-presentation`) give finite type.
4. Localize at the marked prime. Etale flatness, the affine stalk localization
   (`lem-weil-pbc-affine-open-stalk-localization`) and
   `lem-weil-pbc-flat-local-hom-faithfully-flat` make `B → C_q` faithfully flat local.
   Localization and tensor associativity identify `N_q` with `C_q ⊗[B] P`.
5. Use `lem-trf-pointed-devissage-affine-translation` and
   `def-trf-pointed-scheme-devissage-data`. The unique point in each finite fibre
   gives the unique prime above `q_i`; the first and successive closed immersions
   give the displayed contractions. The translation supplies the module and
   cokernel isomorphisms. An empty chain is allowed for the zero module.
6. Smoothness implies flatness (`lem-pc-smooth-flat` and
   `lem-weil-pbc-flat-ring-map-iff-flat-affine`) and finite presentation. Smooth
   fibres are geometrically reduced (`sbc-lem-smooth-geometrically-reduced`);
   their geometric irreducibility includes nonemptiness. Consequently every
   field extension of every residue fibre is a nonzero domain, by
   `def-pc-geometrically-irreducible`, `def-weil-irreducible-components` and
   `def-pc-integral-scheme`.
-/
theorem exists_henselian_pointed_devissage_chart
    (A B : Type u) [CommRing A] [CommRing B] [HenselianLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    (P : Type v) [AddCommGroup P] [Module B P] [Module.Finite B P] :
    ∃ (C : CommAlgCat.{u} A) (_ : Algebra.FiniteType A C)
      (N : ModuleCat.{max u v} C) (_ : Module.Finite C N) (q : PrimeSpectrum C)
      (f : B →ₐ[A] Localization.AtPrime q.asIdeal),
      q.asIdeal.comap (algebraMap A C) = IsLocalRing.maximalIdeal A ∧
      IsLocalHom f.toRingHom ∧ f.toRingHom.FaithfullyFlat ∧
      Nonempty (henselianChartLocalization q N ≃ₗ[Localization.AtPrime q.asIdeal]
        (ModuleCat.extendScalars f.toRingHom).obj (ModuleCat.of B P)) ∧
      ∃ d : CompleteAlgebraDevissage A C (IsLocalRing.maximalIdeal A) N,
        (∀ i : Fin d.n, (algebraMap A (d.B i)).Flat ∧
          Algebra.FinitePresentation A (d.B i)) ∧
        (∀ (i : Fin d.n) (a : PrimeSpectrum A) (K : Type (max u w)) [Field K]
          [Algebra a.asIdeal.ResidueField K] [Algebra A K]
          [IsScalarTower A a.asIdeal.ResidueField K], IsDomain (d.B i ⊗[A] K)) ∧
        ∃ (qi : ∀ i : Fin d.n, PrimeSpectrum (d.B i))
          (pi : ∀ i : Fin d.n, PrimeSpectrum (d.A i)),
          (∀ i, (qi i).asIdeal.comap (algebraMap A (d.B i)) =
            IsLocalRing.maximalIdeal A) ∧
          (∀ i, (pi i).asIdeal.comap (d.bToA i).toRingHom = (qi i).asIdeal) ∧
          (∀ (i : Fin d.n) (p : PrimeSpectrum (d.A i)),
            p.asIdeal.comap (d.bToA i).toRingHom = (qi i).asIdeal → p = pi i) ∧
          (∀ (i : Fin d.n) (hi : i.val = 0),
            (pi i).asIdeal.comap (d.sToA i hi).toRingHom = q.asIdeal) ∧
          (∀ (i j : Fin d.n) (hij : j.val = i.val + 1),
            (pi j).asIdeal.comap (d.bToAnext i j hij).toRingHom = (qi i).asIdeal) := by
  sorry

end AlgebraicGeometry
