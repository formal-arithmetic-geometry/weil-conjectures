/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-!
# Ample invertible modules and the Hilbert degree

An `𝒪_X`-module is *very ample* relative to `f : X ⟶ S` if it is the pullback of `𝒪(1)` along
a closed immersion of `X` into a projective space `ℙ(n; S)` over `S`; it is then invertible. An
invertible module on a `K`-scheme is *ample* if some positive tensor power of it is very ample.
For an ample invertible module `M` on a proper `K`-scheme `X` of dimension `g`, the function
`m ↦ χ(X, M^{⊗ m})` is a numerical polynomial of degree at most `g`, and the *degree of `X` with
respect to `M`* is `g!` times its leading coefficient.

`AlgebraicGeometry.IsVeryAmple` and `AlgebraicGeometry.IsAmple` are built on the twisting sheaf
`AlgebraicGeometry.ProjectiveSpace.twist`. The degree `AlgebraicGeometry.Scheme.Hom.degree` is
the `g`-th forward difference `fwdDiff` at `0` of the Hilbert function `m ↦ χ(X, M^{⊗ m})`, with
the Euler characteristic `AlgebraicGeometry.Scheme.Modules.eulerChar`; it is `g!` times the
leading coefficient whenever that function is a numerical polynomial of degree at most `g`
(`Polynomial.fwdDiff_iter_degree_eq_factorial`).

## Main definitions

- `AlgebraicGeometry.IsVeryAmple`, `AlgebraicGeometry.IsAmple`: very ample and ample modules.
- `AlgebraicGeometry.Scheme.Hom.hilbertFunction`: the Hilbert function `m ↦ χ(X, M^{⊗ m})`.
- `AlgebraicGeometry.Scheme.Hom.degree`: the degree of a proper scheme with respect to an ample
  invertible module.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.degree_eq_degree_of_topologicalKrullDim_eq_one`: in dimension
  one the degree is the cohomological degree `χ(M) - χ(𝒪_X)`.
- `AlgebraicGeometry.IsVeryAmple.isInvertible`: a very ample module is invertible.
- `AlgebraicGeometry.Scheme.Modules.finiteDimensional_H`: the cohomology of an invertible module
  on a proper scheme over a field is finite-dimensional.
- `AlgebraicGeometry.Scheme.Modules.degree_eq_sum_of_pairwise_disjoint`: the degree is additive
  over a finite disjoint union of open subschemes.
- `AlgebraicGeometry.Scheme.Modules.degree_eq_zero_of_topologicalKrullDim_le_zero`: an
  invertible module on a connected noetherian scheme of dimension `0` has degree `0`.
- `AlgebraicGeometry.IsAmple.pullback`: the restriction of an ample module to a closed subscheme
  is ample.
- `AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple_of_connectedSpace`: an ample invertible
  module on a connected proper curve has positive degree.
- `AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple`: an ample invertible module on a proper
  curve has positive degree.
- `AlgebraicGeometry.Scheme.Hom.fwdDiff_iter_eulerChar_tensorObj_tensorPow`: twisting the
  Hilbert function by a coherent module of generic rank `r` multiplies the degree by `r`.
- `AlgebraicGeometry.Scheme.Hom.degree_pullback`: the degree multiplies by the degree of the
  morphism under pullback along a finite surjective morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Function MonoidalCategory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

/-- Blueprint `sk-def-av-ample-degree`: Ample modules and the Hilbert degree.

An `𝒪_X`-module `M` is *very ample* relative to `f : X ⟶ S` if there is a closed immersion
`i : X ⟶ ℙ(n; S)` over `S`, into a projective space with finitely many homogeneous
coordinates, with `i^* 𝒪(1) ≅ M`.

This is the "projective" variant of the notion: Hartshorne (II.5) and EGA II (4.4.2) only ask
for an immersion. The two agree when `f` is proper, since an immersion from a proper
`S`-scheme into the separated `S`-scheme `ℙ(n; S)` is closed, and every use of very ample
modules in the project is for a proper `f`. -/
def IsVeryAmple {S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) : Prop :=
  ∃ (n : Type u) (i : X ⟶ ℙ(n; S)), Finite n ∧ IsClosedImmersion i ∧ i ≫ ℙ(n; S) ↘ S = f ∧
    Nonempty (ProjectiveSpace.twistRestrict i 1 ≅ M)

/-- **A very ample module is invertible**, being the pullback of the invertible module
`𝒪(1)`. -/
lemma IsVeryAmple.isInvertible {S : Scheme.{u}} {f : X ⟶ S} {M : X.Modules}
    (h : IsVeryAmple f M) : M.IsInvertible := by
  obtain ⟨n, i, -, -, -, ⟨e⟩⟩ := h
  exact Scheme.Modules.IsInvertible.of_iso e

/-- Blueprint `sk-def-av-ample-degree`: Ample modules and the Hilbert degree.

An invertible `𝒪_X`-module is *ample* if some positive tensor power of it is very ample. -/
def IsAmple (f : X ⟶ Spec (.of K)) (M : X.Modules) : Prop :=
  ∃ m : ℕ, 0 < m ∧ IsVeryAmple f (M.tensorPow m)

/-- The Hilbert function `m ↦ χ(X, M^{⊗ m})` of an `𝒪_X`-module `M` on a `K`-scheme `X`, with
the Euler characteristic `AlgebraicGeometry.Scheme.Modules.eulerChar` over `K`. -/
noncomputable def Scheme.Hom.hilbertFunction (f : X ⟶ Spec (.of K)) (M : X.Modules) : ℕ → ℤ :=
  letI : X.Over (Spec (.of K)) := ⟨f⟩
  fun m ↦ Scheme.Modules.eulerChar K (M.tensorPow m)

open scoped fwdDiff in
/-- Blueprint `sk-def-av-ample-degree`: Ample modules and the Hilbert degree.

The degree of a `K`-scheme `X` of dimension `g` with respect to an `𝒪_X`-module `M`: the `g`-th
forward difference at `0` of the Hilbert function `m ↦ χ(X, M^{⊗ m})`. When the Hilbert
function is a numerical polynomial of degree at most `g`, as it is for `X` proper and `M` ample
invertible, this equals `g!` times its coefficient of `m^g`. Here `g` is the topological Krull
dimension of `X`, read as `0` if `X` is empty or infinite-dimensional.

The value is meaningful only for `f` proper and `M` coherent: otherwise the Euler
characteristics involved may be junk values. -/
noncomputable def Scheme.Hom.degree (f : X ⟶ Spec (.of K)) (M : X.Modules) : ℤ :=
  Δ_[1]^[((topologicalKrullDim X).unbotD 0).toNat] (f.hilbertFunction M) 0

/-- The degree as an explicit alternating sum of Euler characteristics:
`∑_{i=0}^{g} (-1)^(g-i) (g choose i) χ(X, M^{⊗ i})`. -/
lemma Scheme.Hom.degree_eq_sum (f : X ⟶ Spec (.of K)) (M : X.Modules) :
    f.degree M = ∑ i ∈ Finset.range (((topologicalKrullDim X).unbotD 0).toNat + 1),
      ((-1 : ℤ) ^ (((topologicalKrullDim X).unbotD 0).toNat - i) *
        (((topologicalKrullDim X).unbotD 0).toNat.choose i : ℤ)) • f.hilbertFunction M i := by
  rw [degree, fwdDiff_iter_eq_sum_shift]
  simp

/-- On a `K`-scheme of dimension one, the degree with respect to `M` is the cohomological
degree `χ(M) - χ(𝒪_X)` of `AlgebraicGeometry.Scheme.Modules.degree`. -/
lemma Scheme.Hom.degree_eq_degree_of_topologicalKrullDim_eq_one (f : X ⟶ Spec (.of K))
    (h : topologicalKrullDim X = 1) (M : X.Modules) :
    letI : X.Over (Spec (.of K)) := ⟨f⟩
    f.degree M = Scheme.Modules.degree K M := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  have hg : ((topologicalKrullDim X).unbotD 0).toNat = 1 := by
    rw [h]
    rfl
  rw [degree, hg, Function.iterate_one, fwdDiff, zero_add, Scheme.Modules.degree]
  simp only [hilbertFunction, Scheme.Modules.tensorPow_zero]
  rw [Scheme.Modules.tensorPow_succ, Scheme.Modules.tensorPow_zero,
    Scheme.Modules.eulerChar_congr K (MonoidalCategory.rightUnitor M)]
  rfl

namespace Scheme.Modules

section Additivity

variable (K) [X.Over (Spec (.of K))]

/-- **Finiteness of cohomology.** The cohomology of an invertible module on a proper scheme over
a field `K` is finite-dimensional over `K`. This is a special case of the finiteness theorem
for the cohomology of coherent modules on proper schemes (EGA III, 3.2.1).

This is used in the proof of blueprint `lem-sc-ample-positive-degree`. -/
instance finiteDimensional_H [IsProper (X ↘ Spec (.of K))] (M : X.Modules) [M.IsInvertible]
    (q : ℕ) : FiniteDimensional K (M.H q) :=
  sorry

/-- **The degree is additive over a finite disjoint union.** If a noetherian scheme `X` of
finite dimension is the disjoint union of finitely many open subschemes `U i`, then
`deg M = ∑ᵢ deg (M|_{U i})`, provided the cohomology of `M` and `𝒪_X` is finite-dimensional. -/
theorem degree_eq_sum_of_pairwise_disjoint [IsNoetherian X] {n : ℕ}
    (hn : topologicalKrullDim X ≤ n) {ι : Type*}
    [Fintype ι] (U : ι → X.Opens) (hU : _root_.Pairwise (Disjoint on U)) (hcover : ⨆ i, U i = ⊤)
    (M : X.Modules) [∀ q, FiniteDimensional K (M.H q)]
    [∀ q, FiniteDimensional K ((𝟙_ X.Modules).H q)] :
    M.degree K = ∑ i,
      letI : (U i).toScheme.Over (Spec (.of K)) := ⟨(U i).ι ≫ X ↘ Spec (.of K)⟩
      ((Scheme.Modules.pullback (U i).ι).obj M).degree K := by
  let (i : ι) : (U i).toScheme.Over (Spec (.of K)) := ⟨(U i).ι ≫ X ↘ Spec (.of K)⟩
  simp only [degree, Finset.sum_sub_distrib]
  rw [eulerChar_eq_sum_of_pairwise_disjoint K hn U hU hcover M]
  congr 1
  exact (eulerChar_eq_sum_of_pairwise_disjoint K hn U hU hcover (𝟙_ X.Modules)).trans
    (Finset.sum_congr rfl fun i _ ↦ eulerChar_congr K (pullbackObjUnitIso _))

/-- On a connected locally noetherian `K`-scheme of dimension `0`, every invertible module has
degree `0`: the scheme is artinian, hence discrete, hence a single point, on which every
invertible module is trivial. -/
theorem degree_eq_zero_of_topologicalKrullDim_le_zero [IsLocallyNoetherian X] [ConnectedSpace X]
    (hdim : topologicalKrullDim X ≤ 0) (L : X.Modules) [L.IsInvertible] : L.degree K = 0 := by
  have := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  have : Subsingleton X := Set.subsingleton_univ_iff.mp isPreconnected_univ.subsingleton
  obtain ⟨e⟩ := IsInvertible.nonempty_iso_unit (Classical.arbitrary X) L
  rw [degree_congr K e, degree_unit]

end Additivity

end Scheme.Modules

/-- **The restriction of an ample module to a closed subscheme is ample.** If `L^{⊗ n}` is the
pullback of `𝒪(1)` along a closed immersion `X ⟶ ℙ(m; K)`, then `(i^* L)^{⊗ n} ≅ i^* (L^{⊗ n})`
is its pullback along the closed immersion `Z ⟶ X ⟶ ℙ(m; K)` (Stacks, Properties of Schemes,
Section 28.26).

This is used in the proof of blueprint `lem-sc-ample-positive-degree`. -/
theorem IsAmple.pullback {Z : Scheme.{u}} {f : X ⟶ Spec (.of K)} {L : X.Modules}
    (hL : IsAmple f L) (i : Z ⟶ X) [IsClosedImmersion i] :
    IsAmple (i ≫ f) ((Scheme.Modules.pullback i).obj L) :=
  sorry

/-- **An ample module on a connected proper curve has positive degree.** Let `K` be
algebraically closed, `X` a connected proper curve over `K` and `L` an ample invertible
`𝒪_X`-module. Then `deg L = χ(L) - χ(𝒪_X) > 0`.

This is the connected case of blueprint `lem-sc-ample-positive-degree`, recorded there as
classical input without a separate proof. -/
@[stacks 0B5X]
theorem Scheme.Hom.degree_pos_of_isAmple_of_connectedSpace [IsAlgClosed K]
    (f : X ⟶ Spec (.of K)) [IsProper f] [ConnectedSpace X] (hdim : topologicalKrullDim X = 1)
    (L : X.Modules) [L.IsInvertible] (hample : IsAmple f L) : 0 < f.degree L :=
  sorry

/-- Blueprint `sk-prop-av-ample-positive`: Ample modules on proper curves have positive degree.

Let `K` be algebraically closed, `C` a proper curve over `K` of dimension one (possibly
disconnected) and `L` an ample invertible `𝒪_C`-module. Then `deg L > 0`.

This is also blueprint `lem-sc-ample-positive-degree`. The proof decomposes `C` into its
finitely many connected components `C_i`, which are open and closed. The degree is additive
over them (`AlgebraicGeometry.Scheme.Modules.degree_eq_sum_of_pairwise_disjoint`); a component
of dimension `0` is a single point, so contributes `0`; a component of dimension `1` contributes
a positive degree by the connected case
`AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple_of_connectedSpace`, since `L|_{C_i}` is
ample (`AlgebraicGeometry.IsAmple.pullback`). If all components had dimension `0`,
`C` would be discrete, so at least one has dimension `1`. -/
theorem Scheme.Hom.degree_pos_of_isAmple [IsAlgClosed K] (f : X ⟶ Spec (.of K)) [IsProper f]
    (hdim : topologicalKrullDim X = 1) (L : X.Modules) [L.IsInvertible] (hample : IsAmple f L) :
    0 < f.degree L := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  have : IsProper (X ↘ Spec (.of K)) := ‹IsProper f›
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  have : Fintype (ConnectedComponents X) := Fintype.ofFinite _
  -- The connected components `U c` of `X`, open and closed in `X`.
  let U (c : ConnectedComponents X) : X.Opens :=
    ⟨ConnectedComponents.mk ⁻¹' {c}, (isOpen_discrete {c}).preimage
      ConnectedComponents.continuous_coe⟩
  have hU : _root_.Pairwise (Disjoint on U) := fun c d hcd ↦
    Opens.coe_disjoint.mp ((Set.disjoint_singleton.mpr hcd).preimage ConnectedComponents.mk)
  have hcover : ⨆ c, U c = ⊤ := eq_top_iff.mpr fun x _ ↦
    Opens.mem_iSup.mpr ⟨ConnectedComponents.mk x, rfl⟩
  let (c : ConnectedComponents X) : (U c).toScheme.Over (Spec (.of K)) := ⟨(U c).ι ≫ f⟩
  have hdimU (c : ConnectedComponents X) :
      topologicalKrullDim (U c) = 1 ∨ topologicalKrullDim (U c) ≤ 0 := by
    rcases (hdim ▸ topologicalKrullDim_subspace_le X (U c)).lt_or_eq with h | h
    · exact Or.inr (Order.le_of_lt_succ h)
    · exact Or.inl h
  -- Each component contributes a nonnegative degree, positive if it has dimension `1`.
  have hdeg (c : ConnectedComponents X) :
      0 ≤ ((Scheme.Modules.pullback (U c).ι).obj L).degree K ∧
      (topologicalKrullDim (U c) = 1 →
        0 < ((Scheme.Modules.pullback (U c).ι).obj L).degree K) := by
    have : ConnectedSpace (U c) := by
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      have : (U x : Set X) = connectedComponent x := connectedComponents_preimage_singleton
      exact isConnected_iff_connectedSpace.mp (this ▸ isConnected_connectedComponent)
    have hclosed : IsClosed (U c : Set X) :=
      (isClosed_discrete {c}).preimage ConnectedComponents.continuous_coe
    have : IsClosedImmersion (U c).ι := .of_isPreimmersion _ (by simpa using hclosed)
    have hpos (h1 : topologicalKrullDim (U c) = 1) :
        0 < ((Scheme.Modules.pullback (U c).ι).obj L).degree K := by
      have := ((U c).ι ≫ f).degree_pos_of_isAmple_of_connectedSpace h1 _ (hample.pullback _)
      rwa [degree_eq_degree_of_topologicalKrullDim_eq_one _ h1] at this
    refine ⟨?_, hpos⟩
    rcases hdimU c with h | h
    · exact (hpos h).le
    · exact (Scheme.Modules.degree_eq_zero_of_topologicalKrullDim_le_zero K h _).ge
  rw [degree_eq_degree_of_topologicalKrullDim_eq_one f hdim,
    Scheme.Modules.degree_eq_sum_of_pairwise_disjoint K hdim.le U hU hcover L]
  refine Finset.sum_pos' (fun c _ ↦ (hdeg c).1) ?_
  -- Some component has dimension `1`: otherwise every component is discrete, hence so is `X`.
  by_contra! h
  have : DiscreteTopology X := by
    refine discreteTopology_iff_isOpen_singleton.mpr fun x ↦ ?_
    have := IsLocallyArtinian.of_topologicalKrullDim_le_zero
      ((hdimU (ConnectedComponents.mk x)).resolve_left fun h1 ↦
        (h _ (Finset.mem_univ _)).not_gt ((hdeg _).2 h1))
    have hd : DiscreteTopology (U (ConnectedComponents.mk x)) :=
      IsLocallyArtinian.discreteTopology (X := (U (ConnectedComponents.mk x)).toScheme)
    have := (U (ConnectedComponents.mk x)).isOpen.isOpenMap_subtype_val _
      (@isOpen_discrete _ _ hd {(⟨x, rfl⟩ : U (ConnectedComponents.mk x))})
    convert this using 1
    ext y
    constructor
    · rintro rfl
      exact ⟨⟨y, rfl⟩, rfl, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      rw [Set.mem_singleton_iff.mp hz]
      rfl
  have := topologicalKrullDim_zero_of_discreteTopology X
  rw [hdim] at this
  exact absurd this (by decide)

open scoped fwdDiff in
/-- **The leading coefficient of a twisted Hilbert function only depends on the generic rank.**
Let `Y` be an integral proper `K`-scheme of dimension `g`, `M` an ample invertible `𝒪_Y`-module
and `E` a coherent `𝒪_Y`-module which is free of rank `r` on a nonempty open subset of `Y`. Then
the `g`-th forward difference at `0` of `m ↦ χ(Y, E ⊗ M^{⊗ m})` is `r` times the degree of `Y`
with respect to `M`. Both `m ↦ χ(Y, E ⊗ M^{⊗ m})` and `m ↦ r χ(Y, M^{⊗ m})` are numerical
polynomials of degree at most `g` (blueprint `lem-sc-hilbert-polynomial`), and their difference
has degree at most `g - 1`: by additivity of `χ` and dévissage, `E` may be compared with
`𝒪_Y^{⊕ r}` up to coherent modules supported on a proper closed subset, of dimension `< g`.

This is the input on Hilbert polynomials used in the proof of blueprint
`lem-sc-deg-pullback-finite`. -/
theorem Scheme.Hom.fwdDiff_iter_eulerChar_tensorObj_tensorPow [IsIntegral Y]
    (f : Y ⟶ Spec (.of K)) [IsProper f] (M : Y.Modules) [M.IsInvertible] (hample : IsAmple f M)
    (E : Y.Modules) [E.IsFinitePresentation] {U : Y.Opens} (hU : (U : Set Y).Nonempty) {r : ℕ}
    (e : (Scheme.Modules.pullback U.ι).obj E ≅ SheafOfModules.free (ULift.{u} (Fin r))) :
    letI : Y.Over (Spec (.of K)) := ⟨f⟩
    Δ_[1]^[((topologicalKrullDim Y).unbotD 0).toNat]
      (fun m ↦ Scheme.Modules.eulerChar K (E ⊗ M.tensorPow m)) 0 = r * f.degree M :=
  sorry

/-- Blueprint `sk-prop-av-deg-pullback`: Degree of a pullback under a finite morphism.

Let `g : X ⟶ Y` be a finite surjective morphism of proper `K`-varieties of the same dimension,
let `M` be an ample invertible `𝒪_Y`-module and let `d = [k(X) : k(Y)]` be the degree of `g`.
Then `deg_{g^*M}(X) = d * deg_M(Y)`.

This is also blueprint `lem-sc-deg-pullback-finite` (Stacks 0BEX). Both sides are `g`-th forward
differences at `0`, where `dim X = dim Y` since `g` is finite surjective
(`AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_eq_of_surjective`). By the projection formula
`χ(X, (g^* M)^{⊗ m}) = χ(X, g^* M^{⊗ m}) = χ(Y, g_* g^* M^{⊗ m}) = χ(Y, g_* 𝒪_X ⊗ M^{⊗ m})`, and
`g_* 𝒪_X` is a coherent module of generic rank `d`, so the leading coefficients compare by
`AlgebraicGeometry.Scheme.Hom.fwdDiff_iter_eulerChar_tensorObj_tensorPow`.

```
  X ────────── g ─────────▶ Y
    ╲                       │
     ╲  fX                  │ fY
      ╲                     ▼
       ╲───────────▶ Spec K
```
-/
theorem Scheme.Hom.degree_pullback [IsIntegral X] [IsIntegral Y] (fX : X ⟶ Spec (.of K))
    (fY : Y ⟶ Spec (.of K)) [IsProper fX] [IsProper fY] (g : X ⟶ Y) (hg : g ≫ fY = fX)
    [IsFinite g] [Surjective g] (M : Y.Modules) [M.IsInvertible] (hample : IsAmple fY M) :
    fX.degree ((Scheme.Modules.pullback g).obj M) =
      g.finrank (genericPoint Y) * fY.degree M := by
  subst hg
  let : Y.Over (Spec (.of K)) := ⟨fY⟩
  let : X.Over (Spec (.of K)) := ⟨g ≫ fY⟩
  have : g.IsOver (Spec (.of K)) := ⟨rfl⟩
  have := LocallyOfFiniteType.isLocallyNoetherian fY
  have := Scheme.Modules.isFinitePresentation_pushforward_unit g
  obtain ⟨U, hU, ⟨e⟩⟩ := Scheme.Modules.exists_pullback_pushforward_unit_iso_free g
  rw [← fY.fwdDiff_iter_eulerChar_tensorObj_tensorPow M hample _ hU e, degree,
    g.topologicalKrullDim_eq_of_surjective]
  refine congrArg (fun F : ℕ → ℤ ↦ (fwdDiff 1)^[_] F 0) (funext fun m ↦ ?_)
  -- `χ(X, (g^* M)^{⊗ m}) = χ(X, g^* M^{⊗ m}) = χ(Y, g_* g^* M^{⊗ m}) = χ(Y, g_* 𝒪_X ⊗ M^{⊗ m})`
  obtain ⟨e₁⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso g M m
  obtain ⟨e₂⟩ := Scheme.Modules.nonempty_pushforward_pullback_iso g (M.tensorPow m)
  change Scheme.Modules.eulerChar K _ = _
  rw [← Scheme.Modules.eulerChar_congr K e₁, ← Scheme.Modules.eulerChar_congr K e₂,
    Scheme.Modules.eulerChar_pushforward_of_isAffineHom]

end AlgebraicGeometry
