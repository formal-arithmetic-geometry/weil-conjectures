/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedSectionsComplex
public import WeilConjectures.Algebra.Homology.IdealPowerTorsionCocomplexInclusion
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Sheaf.AlgebraicGeometry.Morphisms.PuncturedInjectiveRestrictionExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # The punctured sections complex is the torsion quotient

Source: Stacks Project, Tags 0BK0, 0A6T, and 09T2.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- On the complement of the closed point, the complex of sections of associated
injective modules is the categorical quotient by maximal-ideal-power torsion.
Source: Stacks Project, Tag 0BK0, Lemma 51.8.2; Tag 0A6T, Lemma 51.2.1;
and Tag 09T2, Lemma 36.8.1.
(blueprint: lem-sbc-punctured-sections-torsion-quotient).

Proof: A prime containing the maximal ideal equals it, so hW identifies W with
Spec R minus V(m). Choose finite generators f_i of m, using Noetherianity.
For each injective module E, the associated sheaf is flasque by 09T2, and the
restriction map tilde.toOpen E W is surjective since its sections on the whole
spectrum identify with E by tilde.isoTop. Its kernel is Gamma_m(E): a section
vanishes on W if and only if it vanishes on each D(f_i); localization gives
exponents e_i with f_i^e_i killing it. Increase each exponent to be positive.
Every monomial of degree sum e_i is divisible by some f_i^e_i, so the ideal power
m^(sum e_i) annihilates it. Conversely, m^N annihilating a section makes its
localization at each f_i zero. The first isomorphism theorem now identifies the
quotient by Ideal.primaryComponent E m with sections on W. The maps tilde.toOpen
are natural in E, so these isomorphisms commute with the resolution differentials
and give an isomorphism of complexes. Cokernels in complexes are degreewise,
identifying the source with the categorical cokernel of the explicit inclusion.
If m=0 or W is empty, the restriction target is zero and Gamma_m(E)=E, so this
construction still applies. This is a chain-level assertion, with no cohomology
comparison or derived torsion in its proof. -/
theorem nonempty_injective_quotient_iso_punctured_sections
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R)
    (I : InjectiveResolution (ModuleCat.of R R : ModuleCat.{u} R)) :
    Nonempty (cokernel (ModuleCat.idealPowerTorsionCocomplexι
        (IsLocalRing.maximalIdeal R) I.cocomplex) ≅
      puncturedSectionsComplex R W I.cocomplex) := by
  classical
  let t := ModuleCat.idealPowerTorsionCocomplexι (IsLocalRing.maximalIdeal R) I.cocomplex
  let r := puncturedSectionsRestriction R W I.cocomplex
  have hr (k : ℕ) := injective_punctured_restriction_exact R W hW (I.cocomplex.X k)
  have hz : t ≫ r = 0 := by
    apply HomologicalComplex.hom_ext
    intro k
    change ModuleCat.ofHom (Ideal.primaryComponent (I.cocomplex.X k)
      (IsLocalRing.maximalIdeal R)).subtype ≫ tilde.toOpen (R := .of R) (I.cocomplex.X k) W = 0
    ext x
    have hx : x.val ∈ (tilde.toOpen (R := .of R) (I.cocomplex.X k) W).hom.ker := by
      rw [(hr k).1]
      exact x.property
    exact hx
  let S := ShortComplex.mk t r hz
  have hS : S.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro k
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2
      change LinearMap.range (Ideal.primaryComponent (I.cocomplex.X k)
        (IsLocalRing.maximalIdeal R)).subtype =
        (tilde.toOpen (R := .of R) (I.cocomplex.X k) W).hom.ker
      rw [Submodule.range_subtype, (hr k).1]
    · change Mono (t.f k)
      exact ModuleCat.idealPowerTorsionCocomplexι_f_mono _ _ _
    · change Epi (tilde.toOpen (R := .of R) (I.cocomplex.X k) W)
      exact (ModuleCat.epi_iff_surjective _).2 (hr k).2
  exact ⟨IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel t) hS.gIsCokernel⟩

end AlgebraicGeometry.Scheme
