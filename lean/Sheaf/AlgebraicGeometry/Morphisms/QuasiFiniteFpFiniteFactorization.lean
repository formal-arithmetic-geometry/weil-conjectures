/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization

/-!
# Finitely presented Zariski main finite factorization

Source: Stacks Project, More on Morphisms, Tag 0F2N,
`lemma-quasi-finite-separated-pass-through-finite-addendum`, with the quasi-compact and
quasi-separated finite factor made explicit
(blueprint: lem-weil-pbc-quasifinite-fp-finite-factorization).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A separated quasi-finite morphism of finite presentation over a quasi-compact,
quasi-separated scheme factors through a finite, finitely presented, quasi-compact,
quasi-separated scheme by a quasi-compact open immersion.

Source: Stacks Project, Tag 0F2N,
`lemma-quasi-finite-separated-pass-through-finite-addendum`
(blueprint: lem-weil-pbc-quasifinite-fp-finite-factorization).

Proof plan:
1. Local finite presentation implies local finite type. Apply
   `thm-pqf-zmt-factorization` to obtain a quasi-compact open immersion into a finite
   scheme `T₀` over `S`.
2. By `lem-weil-pbc-finite-closed-fp-approximation`, write `T₀` as a directed inverse
   limit of finite, finitely presented `S`-schemes with closed transition maps.
3. Finite morphisms are affine. Apply `lem-weil-pbc-affine-morphism-permanence` and
   `lem-weil-pbc-qcqs-morphism-permanence` to see that the stages and `T₀` are qcqs,
   and that `X` is quasi-compact.
4. Closed transitions are affine by `lem-weil-pbc-closed-immersion-integral-separated-uc`.
   Descend the quasi-compact open image of `X` using `pqf-lem-limit-qc-open-descends`.
   The inverse images of this open form a limit presenting `X`; their transitions
   remain closed immersions, since quotients remain quotients after localization.
5. Each restricted stage is locally of finite type over `S`, by localizing finite-type
   affine charts. Apply `lem-weil-pbc-closed-limit-lfp-stabilization` to identify `X`
   with a sufficiently late open stage.
6. Use that stage's finite ambient scheme as `T`. The restricted projection is over `S`,
   giving `j ≫ p = f`. The stage is qcqs, and its structure map is finite and finitely
   presented. Since `X` is quasi-compact and `T` quasi-separated,
   `lem-weil-pbc-qcqs-morphism-permanence` gives quasi-compactness of `j`. -/
theorem Scheme.Hom.exists_qcqs_finitePresentation_factorization
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (hq : f.IsQuasiFinite)
    [CompactSpace S] [QuasiSeparatedSpace S] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f] :
    ∃ (T : Scheme.{u}) (j : X ⟶ T) (p : T ⟶ S),
      IsOpenImmersion j ∧ QuasiCompact j ∧ IsFinite p ∧
      LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ QuasiSeparated p ∧
      j ≫ p = f ∧ CompactSpace T ∧ QuasiSeparatedSpace T := by
  have : LocallyQuasiFinite f := by
    apply locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr
    intro s
    apply isDiscrete_iff_discreteTopology.mpr
    apply discreteTopology_iff_isOpen_singleton.mpr
    rintro ⟨x, hx⟩
    change f x = s at hx
    subst s
    have hopen := hq.2.2 x
    rw [← (f.fiberHomeo (f x)).isOpen_image] at hopen
    simpa only [Set.image_singleton, Scheme.Hom.asFiber,
      Homeomorph.apply_symm_apply] using hopen
  obtain ⟨T, j, p, hj, hjc, hp, hpfp, hjp⟩ :=
    f.exists_isOpenImmersion_isFinite_locallyOfFinitePresentation
  let := hp
  exact ⟨T, j, p, hj, hjc, hp, hpfp, inferInstance, inferInstance, hjp,
    QuasiCompact.compactSpace_of_compactSpace p, quasiSeparatedSpace_of_quasiSeparated p⟩

end AlgebraicGeometry
