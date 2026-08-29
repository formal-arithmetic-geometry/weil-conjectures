/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.DisjointnessBlowup
public import WeilConjectures.Compactification.FiniteTypeDirected
public import WeilConjectures.Compactification.IdealSheafPower
public import WeilConjectures.Mathlib.AlgebraicGeometry.Properties

/-!

# The disjointness reduction in Conrad's Theorem 2.4, Case 3

This file contains the first of the two opening reductions of Conrad's proof of Case 3 of
Theorem 2.4 in *Deligne's notes on Nagata compactifications* (blueprint:
`lemma:nagata-conrad-case3-disjointness-reduction`).

The data is a qcqs scheme `X` with quasi-compact opens `U ≤ V`, a morphism `p : Y ⟶ X`
from a qcqs scheme and a section `f : U ⟶ Y` of `p` over `U` whose image is closed in
`p ⁻¹ V`. After one `V`-admissible blow-up of `X` the closure of the image of (the base
change of) `f` no longer meets the part lying over the closure of `V ∖ U`.

The blow-up is produced by Deligne's disjointness lemma
(`AlgebraicGeometry.disjoint_closure_range_of_blowupMap_sup`, blueprint
`lemma:nagata-conrad-disjointness-blowup`) applied to the two centres

* `I₁`, a finite-type quasi-coherent subideal of the vanishing ideal of the reduced closed
  subscheme `closure (V ∖ U)` which still restricts to the unit ideal on `U`, and
* `I₂ = I₁ * I₁ ⊔ K ^ n`, where `K` is a finite-type ideal sheaf cutting out `X ∖ V` and
  `n` is large enough that `K ^ n` pulls back into `I₁ ^ 2 · 𝒪_Y + I_{closure f(U)}`.

The exponent `n` comes from `Scheme.IdealSheafData.exists_pow_le`, and the passage from
the vanishing ideal of `closure (V ∖ U)`, which need not be of finite type, to the
finite-type subideal `I₁` is the compactness of a finite-type ideal sheaf against the
directed supremum of the finite-type subideals
(`Scheme.IdealSheafData.exists_le_of_ofFiniteType_le_iSup`).

## Main results

- `AlgebraicGeometry.exists_isAdmissible_disjoint_closure_range_of_le`: the disjointness
  blow-up (blueprint: `lemma:nagata-conrad-case3-disjointness-reduction`).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- Products of quasi-coherent ideal sheaves are monotone in both arguments. -/
lemma mul_mono {I₁ I₂ J₁ J₂ : X.IdealSheafData} (hI : I₁ ≤ I₂) (hJ : J₁ ≤ J₂) :
    I₁ * J₁ ≤ I₂ * J₂ :=
  fun U ↦ Ideal.mul_mono (hI U) (hJ U)

/-- Products of quasi-coherent ideal sheaves distribute over suprema. -/
lemma iSup_mul {ι : Type*} (I : ι → X.IdealSheafData) (J : X.IdealSheafData) :
    (⨆ i, I i) * J = ⨆ i, I i * J :=
  Scheme.IdealSheafData.ext <| funext fun U ↦ by
    simp only [ideal_mul, Pi.mul_apply, ideal_iSup, iSup_apply, Submodule.iSup_mul]

/-- A finite-type quasi-coherent ideal sheaf has finite-type powers. -/
lemma ofFiniteType.pow {I : X.IdealSheafData} (hI : I.ofFiniteType) (n : ℕ) :
    (I ^ n).ofFiniteType := by
  induction n with
  | zero => simpa using ofFiniteType_top
  | succ n ih => rw [pow_succ]; exact ih.mul hI

/-- The support of a power of a quasi-coherent ideal sheaf is contained in its support. -/
lemma support_pow_le {I : X.IdealSheafData} (n : ℕ) : (I ^ n).support ≤ I.support := by
  cases n with
  | zero => simp
  | succ n => simp

end Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- **Conrad's Theorem 2.4, Case 3, Step 1**: the disjointness blow-up.

Let `X` be qcqs, let `U ≤ V` be quasi-compact opens of `X`, let `p : Y ⟶ X` be a morphism
from a qcqs scheme and let `f : U ⟶ Y` be a section of `p` over `U` whose image is closed
in `p ⁻¹ V`. There is a `V`-admissible blow-up of `X` after which the closure of the image
of the base change of `f` is disjoint from the part lying over the closure of `V ∖ U`.

The base change is left flexible: `Z'` and `Y'` are arbitrary schemes over `Y` and over
`(I₁ ⊔ I₂).blowup` fitting into the two commuting squares, exactly as in
`AlgebraicGeometry.disjoint_closure_range_of_blowupMap_sup`.
(Blueprint: `lemma:nagata-conrad-case3-disjointness-reduction`.) -/
theorem exists_isAdmissible_disjoint_closure_range_of_le
    [CompactSpace X] [QuasiSeparatedSpace X] {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] {p : Y ⟶ X}
    (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι)
    (hfc : IsClosed ((p ⁻¹ᵁ V).ι ⁻¹' Set.range f)) :
    ∃ B : IsAdmissible X V,
      ∀ {Z' Y' : Scheme.{u}} {r : Z' ⟶ Y} {p' : Z' ⟶ B.I.blowup}
        (_ : r ≫ p = p' ≫ B.I.blowupMap)
        {fY : Y' ⟶ U.toScheme} {f' : Y' ⟶ Z'} [QuasiCompact f']
        (_ : f' ≫ r = fY ≫ f),
        Disjoint (closure (Set.range f'))
          (p' ⁻¹' closure (B.I.blowupMap ⁻¹' ((V : Set X) \ (U : Set X)))) := by
  haveI : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  -- `V ∖ U` is closed in `V`, so its closure misses `U`
  have hcl : closure ((V : Set X) \ (U : Set X)) ⊆ (U : Set X)ᶜ :=
    closure_minimal (fun _ hx ↦ hx.2) U.isOpen.isClosed_compl
  -- the reduced structure on `closure (V ∖ U)`
  set H : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨_, isClosed_closure (s := (V : Set X) \ (U : Set X))⟩
    with hHdef
  have hHsupp : (H.support : Set X) = closure ((V : Set X) \ (U : Set X)) := by
    rw [hHdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  -- `H` restricts to the unit ideal on `U`
  have hHU : H.comap U.ι = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff]
    ext1
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, hHsupp]
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ hcl hx ?_
    rw [← Scheme.Opens.range_ι]
    exact Set.mem_range_self x
  -- a finite-type closed subscheme structure on `X ∖ V`
  obtain ⟨K, hKft, hKsupp⟩ := X.exists_finiteType_ideal_coe_support_eq_compl V hV
  -- the graph lies over `U`
  have hYU : Set.range (f ≫ p) ⊆ (U : Set X) := by
    rw [hf, Scheme.Opens.range_ι]
  -- the graph is closed in `p ⁻¹ V`, so the closure of the graph meets `p ⁻¹ V` in it
  have hgraph : closure (Set.range f) ∩ ((p ⁻¹ᵁ V : X.Opens.obj _) : Set Y) ⊆ Set.range f := by
    sorry
  -- the set-theoretic containment feeding `exists_pow_le`
  have hsupp : (((H * H).comap p ⊔ f.ker).support : Set Y) ⊆ ((K.comap p).support : Set Y) := by
    sorry
  obtain ⟨n, hn⟩ := Scheme.IdealSheafData.exists_pow_le (hKft.comap p) hsupp
  sorry

end AlgebraicGeometry
