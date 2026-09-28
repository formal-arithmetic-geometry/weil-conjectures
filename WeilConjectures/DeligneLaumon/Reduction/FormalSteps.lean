/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.DeligneLaumon.Reduction.Weights

/-!
# The formal reductions of the Deligne–Laumon direct-image bound

The Deligne–Laumon bound — that `Rʳf₀!F` is mixed of weights at most `w + r` (blueprint
`sk-thm-dl-general-sheaf`, stated for a single morphism as
`AlgebraicGeometry.HasDirectImageWeightBound`) — is reduced to the case of a relative affine line
by three formal steps, all of which are stated in this file:

- it propagates along compositions, by the compact-support Leray spectral sequence;
- it propagates from an open and its closed complement to the ambient scheme, by the open–closed
  triangle;
- it holds outright for separated quasi-finite morphisms, whose compact-support direct image is
  exact and preserves both mixedness and punctual upper weight bounds.

## Main statements

- `AlgebraicGeometry.HasDirectImageWeightBound.comp`: blueprint `sk-l-dl-general-composition`.
- `AlgebraicGeometry.HasDirectImageWeightBound.of_openClosed`: blueprint
  `sk-l-dl-general-excision`.
- `AlgebraicGeometry.isZero_higherLowerShriek_of_quasiFinite`,
  `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.higherLowerShriek_zero_of_quasiFinite` and
  `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost.higherLowerShriek_zero_of_quasiFinite`: blueprint
  `sk-l-dl-general-quasifinite`.

## References

- [Deligne, *La conjecture de Weil : II*][deligne1980], Publ. Math. IHÉS **52** (1980), §1.8 and
  §3.3, where the composition and quasi-finite steps appear.
- [Laumon, *Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil*][laumon1987], Publ. Math. IHÉS **65** (1987), for the reduction to the affine line.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ}

/-- If the direct-image weight assertion holds for `f : X ⟶ Z` and for `g : Z ⟶ Y`, then it holds
for `f ≫ g`:

```
X --- f ---> Z --- g ---> Y
 \                        ^
  `-------- f ≫ g --------'
```

(blueprint: `sk-l-dl-general-composition`). -/
theorem HasDirectImageWeightBound.comp {X Z Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] {f : X ⟶ Z} {g : Z ⟶ Y}
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [g.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g]
    (hf : HasDirectImageWeightBound k₀ ι f) (hg : HasDirectImageWeightBound k₀ ι g) :
    HasDirectImageWeightBound k₀ ι (f ≫ g) :=
  -- Run the Frobenius-equivariant compact-support Leray spectral sequence
  -- `E₂^{a,b} = Rᵃg₀!Rᵇf₀!F ⇒ Rᵃ⁺ᵇ(f ≫ g)₀!F`, whose `E₂`-terms are mixed of weights at most
  -- `w + a + b`; the abutment is filtered by subquotients of the `E₂`-terms, and `.of_mono`,
  -- `.of_epi` and `.of_mono_cokernel` preserve mixed upper bounds.
  sorry

/-- Let `j : U ⟶ X` be an open immersion whose closed complement is `i : Z ⟶ X`. If the
direct-image weight assertion holds for `j ≫ f` and for `i ≫ f`, then it holds for `f`:

```
U --- j ---> X <--- i --- Z
  \          |          /
   `- j ≫ f  | f   i ≫ f -'
       \     v     /
        `--> Y <--'
```

(blueprint: `sk-l-dl-general-excision`). -/
theorem HasDirectImageWeightBound.of_openClosed {U X Z Y : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    {j : U ⟶ X} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] {i : Z ⟶ X} [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))] {f : X ⟶ Y}
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hij : IsCompl (Set.range j.base) (Set.range i.base))
    (hU : HasDirectImageWeightBound k₀ ι (j ≫ f))
    (hZ : HasDirectImageWeightBound k₀ ι (i ≫ f)) :
    HasDirectImageWeightBound k₀ ι f :=
  -- Apply `Rf₀!` to the open–closed triangle `j₀!j₀^*K ⟶ K ⟶ i₀*i₀^*K ⟶ [1]`: in each degree
  -- the middle term has a subobject that is a quotient of the open term, with quotient a
  -- subobject of the closed term, so splicing the two filtrations gives the bound. The same
  -- argument on the *target*, using compact-support base change, allows a finite stratification
  -- of the base; that form belongs with the base-change statement of `sec-six-functors` and is
  -- not stated here.
  sorry

section QuasiFinite

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- For a separated quasi-finite morphism `f : X ⟶ Y` of `k₀`-schemes the higher direct images
with compact support `Rʳf₀!` vanish for `r > 0` (blueprint: `sk-l-dl-general-quasifinite`). -/
theorem isZero_higherLowerShriek_of_quasiFinite (r : ℕ) (hr : 0 < r) (F : WeilSheaf k₀ l X) :
    IsZero ((WeilSheaf.higherLowerShriek k₀ l f r).obj F) :=
  -- Compact-support base change identifies the stalks of `Rʳf₀!F` with the cohomology of a
  -- finite geometric fibre, which is concentrated in degree zero.
  sorry

/-- For a separated quasi-finite morphism `f : X ⟶ Y` of `k₀`-schemes the exact functor `f₀!`
preserves mixed upper weight bounds (blueprint: `sk-l-dl-general-quasifinite`). -/
theorem WeilSheaf.IsMixedOfWeightsAtMost.higherLowerShriek_zero_of_quasiFinite {w : ℝ}
    {F : WeilSheaf k₀ l X} (h : F.IsMixedOfWeightsAtMost ι w) :
    ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).IsMixedOfWeightsAtMost ι w :=
  -- `f₀!` is exact by `isZero_higherLowerShriek_of_quasiFinite`, so it transports a mixed
  -- filtration; its quotients stay punctually pure of the same weight by the orbit computation
  -- of `WeilSheaf.HasWeightsAtMost.higherLowerShriek_zero_of_quasiFinite`.
  sorry

/-- For a separated quasi-finite morphism `f : X ⟶ Y` of `k₀`-schemes the exact functor `f₀!`
preserves punctual upper weight bounds (blueprint: `sk-l-dl-general-quasifinite`). -/
theorem WeilSheaf.HasWeightsAtMost.higherLowerShriek_zero_of_quasiFinite {w : ℝ}
    {F : WeilSheaf k₀ l X} (h : F.HasWeightsAtMost ι w) :
    ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).HasWeightsAtMost ι w :=
  -- At a closed point `y` Frobenius permutes the stalk summands; on an orbit of length `e` an
  -- eigenvalue `α` upstairs contributes eigenvalues `β` with `βᵉ = α` downstairs, whose
  -- normalized weights agree because `q_x = q_yᵉ`.
  sorry

end QuasiFinite

end AlgebraicGeometry
