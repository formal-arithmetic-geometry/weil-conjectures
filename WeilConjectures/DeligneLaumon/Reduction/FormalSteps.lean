/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Compactification.QuasiFinite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import WeilConjectures.WeilSheaf.LowerShriekPackage
public import WeilConjectures.WeilSheaf.StalkUpperStar

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

Once it holds for `f`, it passes from sheaves to complexes: `Rf₀!` preserves Weil complexes mixed
of weights at most `w`, by the hypercohomology spectral sequence.

## Main statements

- `AlgebraicGeometry.HasDirectImageWeightBound.comp`: blueprint `sk-l-dl-general-composition`,
  through its form `AlgebraicGeometry.WeilSheaf.isMixedOfWeightsAtMost_higherLowerShriek_comp` for
  a single sheaf.
- `AlgebraicGeometry.WeilSheaf.exists_filtration_higherLowerShriek_comp`: the abutment filtration
  of the compact-support Leray spectral sequence, used in `lem-zl-composition-weight-bound`.
- `AlgebraicGeometry.HasDirectImageWeightBound.of_openClosed`: blueprint
  `sk-l-dl-general-excision`.
- `AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost.of_openClosed`: blueprint
  `lem-zl-open-closed-weight`.
- `AlgebraicGeometry.HasDirectImageComplexWeightBound.of_openClosed`,
  `AlgebraicGeometry.HasDirectImageWeightBound.of_openClosed_target`,
  `AlgebraicGeometry.HasDirectImageComplexWeightBound.of_openClosed_target` and
  `AlgebraicGeometry.WeilSheaf.isMixedOfWeightsAtMost_higherLowerShriek_of_shortExact`: blueprint
  `lem-zl-morphism-open-closed-reduction`, the open–closed reductions on the source and on the
  target and the reduction along short exact sequences of coefficients.
- `AlgebraicGeometry.HasDirectImageWeightBound.isMixedOfWeightsAtMost_derivedLowerShriek`:
  blueprint `lem-zl-sheaves-to-complexes`.
- `AlgebraicGeometry.isZero_higherLowerShriek_of_quasiFinite`,
  `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.higherLowerShriek_zero_of_quasiFinite` and
  `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost.higherLowerShriek_zero_of_quasiFinite`: blueprint
  `sk-l-dl-general-quasifinite`, and its consequence
  `AlgebraicGeometry.HasDirectImageWeightBound.of_locallyQuasiFinite`.

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

/-- The direct-image weight assertion only depends on the morphism, not on the instance
arguments through which it is stated. -/
theorem HasDirectImageWeightBound.of_eq {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] {f f' : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [f'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f'] [LocallyOfFiniteType f']
    [QuasiCompact f'] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (h : f = f')
    (hf : HasDirectImageWeightBound k₀ ι f) : HasDirectImageWeightBound k₀ ι f' := by
  subst h
  exact hf

/-! ### Composition

The blueprint argument for the composition step runs through the composition isomorphism
`R(f ≫ g)₀! ≅ Rg₀! ∘ Rf₀!` and the compact-support Leray spectral sequence
`E₂^{a,b} = Rᵃg₀!Rᵇf₀!F ⇒ Rᵃ⁺ᵇ(f ≫ g)₀!F`. The composition isomorphism is the composition law of
the six-functor package (`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_comp_iso`);
the output of the spectral sequence needed here, the finite abutment filtration by subquotients
of the `E₂`-terms, is obtained by dévissage along the truncations of `Rf₀!F`
(`AlgebraicGeometry.WeilComplex.prop_homologySheaf_obj`).
-/

section Composition

variable {X Z Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Z) (g : Z ⟶ Y)
  [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [g.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

-- `Fact (ringChar k₀ ≠ l)` is used, through the type of the Weil sheaves; the linter does not
-- see this
set_option linter.unusedSectionVars false in
/-- The abutment of the compact-support Leray spectral sequence
`E₂^{a,b} = Rᵃg₀!Rᵇf₀!F ⇒ Rᵃ⁺ᵇ(f ≫ g)₀!F`: in each total degree `n` the sheaf `Rⁿ(f ≫ g)₀!F`
carries a finite filtration `0 = G 0 ↪ G 1 ↪ ⋯ ↪ G m ≅ Rⁿ(f ≫ g)₀!F` whose successive
quotients `E_∞^{a,b}`, `a + b = n`, are subquotients of the `E₂`-terms `Rᵃg₀!Rᵇf₀!F`: quotients
of subobjects of them (blueprint: `lem-zl-composition-weight-bound`, from
`lem-zl-shriek-composition`, `def-weil-pbc-hypercohomology-filtrations` and
`lemma-weil-pbc-hypercohomology-convergence`). -/
theorem WeilSheaf.exists_filtration_higherLowerShriek_comp (F : WeilSheaf k₀ l X) (n : ℕ) :
    ∃ (m : ℕ) (G : Fin (m + 1) → WeilSheaf k₀ l Y) (φ : ∀ i : Fin m, G i.castSucc ⟶ G i.succ),
      IsZero (G 0) ∧
        IsIsomorphic (G (Fin.last m)) ((WeilSheaf.higherLowerShriek k₀ l (f ≫ g) n).obj F) ∧
        (∀ i : Fin m, Mono (φ i)) ∧
        ∀ i : Fin m, ∃ a b : ℕ, a + b = n ∧ ∃ (S : WeilSheaf k₀ l Y)
          (j : S ⟶ (WeilSheaf.higherLowerShriek k₀ l g a).obj
            ((WeilSheaf.higherLowerShriek k₀ l f b).obj F))
          (p : S ⟶ cokernel (φ i)), Mono j ∧ Epi p := by
  have := locallyOfFiniteType_over_of_isOver f (S := Spec (CommRingCat.of k₀))
  let E₂ : ℕ → ℕ → WeilSheaf k₀ l Y := fun a b ↦
    (WeilSheaf.higherLowerShriek k₀ l g a).obj ((WeilSheaf.higherLowerShriek k₀ l f b).obj F)
  -- the subquotients of the `E₂`-terms of total degree `m`, and the sheaves filtered by them
  let Q₀ : ℤ → ObjectProperty (WeilSheaf k₀ l Y) := fun m E ↦
    ∃ a b : ℕ, (a + b : ℤ) = m ∧ Nonempty (E ≅ E₂ a b)
  let P : ℤ → ObjectProperty (WeilSheaf k₀ l Y) := fun m ↦
    (ObjectProperty.subquotientClosure (Q₀ m)).filtrationClosure
  -- the cohomology sheaves of `Rf₀!F`
  let Q : ℤ → ObjectProperty (WeilSheaf k₀ l Z) := fun b G ↦
    IsZero G ∨ ∃ m : ℕ, (m : ℤ) = b ∧ Nonempty (G ≅ (WeilSheaf.higherLowerShriek k₀ l f m).obj F)
  have hQiso (b : ℤ) : (Q b).IsClosedUnderIsomorphisms := ⟨fun e h ↦ h.elim
    (fun h ↦ Or.inl (h.of_iso e.symm)) (fun ⟨m, hm, ⟨e'⟩⟩ ↦ Or.inr ⟨m, hm, ⟨e.symm ≪≫ e'⟩⟩)⟩
  let Rg := WeilComplex.derivedLowerShriek k₀ l g
  have key := WeilComplex.prop_homologySheaf_obj Rg Q P (fun _ _ hG ↦ Or.inl hG)
    (fun a b G hG ↦ ?_) ((WeilComplex.derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj F))
    (fun b ↦ ?_) n
  rotate_left
  · rcases hG with hG | ⟨m, rfl, ⟨e⟩⟩
    · exact (P _).prop_of_isZero ((WeilComplex.homologySheaf a).map_isZero
        (Rg.map_isZero (WeilSheaf.toComplex.map_isZero hG)))
    rcases lt_or_ge a 0 with ha | ha
    · exact (P _).prop_of_isZero (WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg g G ha)
    obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    refine ObjectProperty.le_filtrationClosure _ (ObjectProperty.le_subquotientClosure _
      ⟨a, m, rfl, ⟨?_⟩⟩)
    exact (WeilComplex.homologySheaf a).mapIso (Rg.mapIso (WeilSheaf.toComplex.mapIso e)) ≪≫
      ((WeilSheaf.higherLowerShriekIso g a).app _).symm
  · rcases lt_or_ge b 0 with hb | hb
    · exact Or.inl (WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg f F hb)
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hb
    exact Or.inr ⟨m, rfl, ⟨((WeilSheaf.higherLowerShriekIso f m).app F).symm⟩⟩
  obtain ⟨c⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) f g
  have key' : P n ((WeilSheaf.higherLowerShriek k₀ l (f ≫ g) n).obj F) :=
    (P n).prop_of_iso (((WeilComplex.homologySheaf n).mapIso (c.app _)).symm ≪≫
      ((WeilSheaf.higherLowerShriekIso (f ≫ g) n).app F).symm) key
  obtain ⟨m, G, φ, h0, hlast, hmono, hφ⟩ := ObjectProperty.filtrationClosure_iff.1 key'
  refine ⟨m, G, φ, h0, hlast, hmono, fun i ↦ ?_⟩
  obtain ⟨Y', S, j, p, ⟨a, b, hab, ⟨e⟩⟩, _, _⟩ := hφ i
  exact ⟨a, b, by exact_mod_cast hab, S, j ≫ e.hom, p, mono_comp _ _, inferInstance⟩

variable {f g}

/-- Let `F` be a Weil sheaf on `X` such that `Rᵇf₀!F` is mixed of weights at most `w + b` for every
`b`, and suppose the direct-image weight assertion holds for `g`. Then `Rⁿ(f ≫ g)₀!F` is mixed of
weights at most `w + n` for every `n` (blueprint: `lem-zl-composition-weight-bound`, for a single
sheaf).

The `E₂`-term `Rᵃg₀!Rᵇf₀!F` of the compact-support Leray spectral sequence is mixed of weights
at most `w + b + a`, so its subquotients `E_∞^{a,b}` are, and the abutment `Rⁿ(f ≫ g)₀!F` is
filtered by these. -/
theorem WeilSheaf.isMixedOfWeightsAtMost_higherLowerShriek_comp {w : ℝ} {F : WeilSheaf k₀ l X}
    (hF : ∀ b : ℕ,
      ((WeilSheaf.higherLowerShriek k₀ l f b).obj F).IsMixedOfWeightsAtMost ι (w + b))
    (hg : HasDirectImageWeightBound k₀ ι g) (n : ℕ) :
    ((WeilSheaf.higherLowerShriek k₀ l (f ≫ g) n).obj F).IsMixedOfWeightsAtMost ι (w + n) := by
  obtain ⟨m, G, φ, h0, hlast, hmono, hφ⟩ :=
    WeilSheaf.exists_filtration_higherLowerShriek_comp (l := l) f g F n
  refine WeilSheaf.IsMixedOfWeightsAtMost.of_filtration G φ h0 hlast fun i ↦ ?_
  obtain ⟨a, b, hab, S, j, p, _, _⟩ := hφ i
  have hE := hg (w + b) _ (hF b) a
  rw [show w + (b : ℝ) + a = w + n by rw [← hab]; push_cast; ring] at hE
  exact (hE.of_mono j).of_epi p

/-- If the direct-image weight assertion holds for `f : X ⟶ Z` and for `g : Z ⟶ Y`, then it holds
for `f ≫ g`:

```
X --- f ---> Z --- g ---> Y
 \                        ^
  `-------- f ≫ g --------'
```

(blueprint: `sk-l-dl-general-composition`, proved as `lem-zl-composition-weight-bound`). -/
theorem HasDirectImageWeightBound.comp (hf : HasDirectImageWeightBound k₀ ι f)
    (hg : HasDirectImageWeightBound k₀ ι g) : HasDirectImageWeightBound k₀ ι (f ≫ g) :=
  fun w F hF ↦ WeilSheaf.isMixedOfWeightsAtMost_higherLowerShriek_comp (hf w F hF) hg

end Composition

/-- If the direct-image weight assertion holds for `f : X ⟶ Y`, then `Rf₀!` carries bounded
constructible Weil complexes mixed of weights at most `w` to complexes mixed of weights at most
`w` (blueprint: `lem-zl-sheaves-to-complexes`).

The blueprint argument is the hypercohomology spectral sequence
`E₂^{a,b} = Rᵃf₀!𝓗ᵇ(K) ⇒ 𝓗ᵃ⁺ᵇ(Rf₀!K)`: its `E₂`-terms are mixed of weights at most `w + a + b` by
the hypothesis, and the abutment is filtered by subquotients of them. -/
theorem HasDirectImageWeightBound.isMixedOfWeightsAtMost_derivedLowerShriek
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec
    (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    (hf : HasDirectImageWeightBound k₀ ι f) {w : ℝ} {K : WeilComplex k₀ l X}
    (hK : K.IsMixedOfWeightsAtMost ι w) :
    ((WeilComplex.derivedLowerShriek k₀ l f).obj K).IsMixedOfWeightsAtMost ι w := by
  have := locallyOfFiniteType_over_of_isOver f (S := Spec (CommRingCat.of k₀))
  intro n
  rw [WeilSheaf.isMixedOfWeightsAtMost_iff_filtrationClosure]
  refine WeilComplex.prop_homologySheaf_obj (WeilComplex.derivedLowerShriek k₀ l f)
    (fun b ↦ (WeilSheaf.isPunctuallyPureOfWeightLE ι (w + b)).filtrationClosure)
    (fun n ↦ (WeilSheaf.isPunctuallyPureOfWeightLE ι (w + n)).filtrationClosure)
    (fun _ _ hG ↦ .of_isZero hG) (fun a b G hG ↦ ?_) K
    (fun b ↦ WeilSheaf.isMixedOfWeightsAtMost_iff_filtrationClosure.1 (hK b)) n
  rcases lt_or_ge a 0 with ha | ha
  · exact .of_isZero (WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg f G ha)
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    have := hf (w + b) G (WeilSheaf.isMixedOfWeightsAtMost_iff_filtrationClosure.2 hG) m
    rw [← WeilSheaf.isMixedOfWeightsAtMost_iff_filtrationClosure]
    refine this.mono_weight (le_of_eq ?_)
    push_cast
    ring

section QuasiFinite

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
attribute [local instance] Compactification.over in
/-- For a separated quasi-finite morphism `f : X ⟶ Y` of `k₀`-schemes the higher direct images
with compact support `Rʳf₀!` vanish for `r > 0` (blueprint: `sk-l-dl-general-quasifinite`). -/
theorem isZero_higherLowerShriek_of_quasiFinite (r : ℕ) (hr : 0 < r) (F : WeilSheaf k₀ l X) :
    IsZero ((WeilSheaf.higherLowerShriek k₀ l f r).obj F) := by
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k₀))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (CommRingCat.of k₀))
  -- By Zariski's main theorem `f` has a compactification `X ⟶[i] Z ⟶[g] Y` with `g` finite, so
  -- `Rʳf₀!F ≅ Rʳg₀*(i₀!F)`, which vanishes for `r > 0` as `g₀*` is exact.
  obtain ⟨c, _, _⟩ := Compactification.exists_isFinite_of_locallyQuasiFinite f
  obtain ⟨e⟩ := WeilSheaf.nonempty_higherLowerShriek_iso_higherLowerStar (l := l) f c r F
  exact (WeilSheaf.isZero_higherLowerStar_of_isFinite c.g r hr _).of_iso e

attribute [local instance] Compactification.over in
/-- For a separated quasi-finite morphism `f : X ⟶ Y` of `k₀`-schemes the exact functor `f₀!`
preserves mixed upper weight bounds (blueprint: `sk-l-dl-general-quasifinite`). -/
theorem WeilSheaf.IsMixedOfWeightsAtMost.higherLowerShriek_zero_of_quasiFinite {w : ℝ}
    {F : WeilSheaf k₀ l X} (h : F.IsMixedOfWeightsAtMost ι w) :
    ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).IsMixedOfWeightsAtMost ι w := by
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k₀))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (CommRingCat.of k₀))
  -- By Zariski's main theorem `f` has a compactification `X ⟶[i] Z ⟶[g] Y` with `g` finite, so
  -- `f₀!F ≅ g₀*(i₀!F)`; both `i₀!` and the finite direct image `g₀*` preserve mixedness.
  obtain ⟨c, _, _⟩ := Compactification.exists_isFinite_of_locallyQuasiFinite f
  have : LocallyOfFiniteType (c.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y ↘ Spec (CommRingCat.of k₀)))
  obtain ⟨e⟩ := WeilSheaf.nonempty_higherLowerShriek_iso_higherLowerStar (l := l) f c 0 F
  exact ((h.extensionByZero c.i).higherLowerStar_zero_of_isFinite c.g).of_iso e.symm

set_option linter.unusedSectionVars false in
attribute [local instance] Compactification.over in
/-- For a separated quasi-finite morphism `f : X ⟶ Y` of `k₀`-schemes the exact functor `f₀!`
preserves punctual upper weight bounds (blueprint: `sk-l-dl-general-quasifinite`). -/
theorem WeilSheaf.HasWeightsAtMost.higherLowerShriek_zero_of_quasiFinite {w : ℝ}
    {F : WeilSheaf k₀ l X} (h : F.HasWeightsAtMost ι w) :
    ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).HasWeightsAtMost ι w := by
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k₀))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (CommRingCat.of k₀))
  -- `f₀!F ≅ g₀*(i₀!F)` for a compactification with `g` finite; at a closed point `y` Frobenius
  -- permutes the stalk summands of `g₀*`, and an orbit of length `e` gives eigenvalues `β` with
  -- `βᵉ` an eigenvalue upstairs, whose normalized weights agree because `q_x = q_yᵉ`.
  obtain ⟨c, _, _⟩ := Compactification.exists_isFinite_of_locallyQuasiFinite f
  have : LocallyOfFiniteType (c.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y ↘ Spec (CommRingCat.of k₀)))
  obtain ⟨e⟩ := WeilSheaf.nonempty_higherLowerShriek_iso_higherLowerStar (l := l) f c 0 F
  exact ((h.extensionByZero c.i).higherLowerStar_zero_of_isFinite c.g).of_epi e.inv

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The direct-image weight assertion holds for a separated quasi-finite morphism `f`: `Rʳf₀!`
vanishes for `r > 0`, and `f₀!` preserves mixed upper weight bounds
(blueprint: `sk-l-dl-general-quasifinite`). -/
theorem HasDirectImageWeightBound.of_locallyQuasiFinite : HasDirectImageWeightBound k₀ ι f := by
  have := locallyOfFiniteType_over_of_isOver f (S := Spec (CommRingCat.of k₀))
  intro w F hF r
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simpa using hF.higherLowerShriek_zero_of_quasiFinite f
  · exact WeilSheaf.isMixedOfWeightsAtMost_of_isZero
      (isZero_higherLowerShriek_of_quasiFinite f r hr F) _

end QuasiFinite

/-! ### Open–closed decompositions

The blueprint argument for the open–closed reduction runs through the open–closed triangle
`j₀!j₀^*K ⟶ K ⟶ i₀*i₀^*K ⟶ K[1]`, the long exact cohomology sequence of a triangle and compact
support base change. The open–closed triangle, the composition law and base change are taken
from the six-functor package of `WeilConjectures.WeilSheaf.LowerShriekPackage`; the reductions are
derived from them as in the blueprint.
-/

section OpenClosed

/-- Pulling back along an immersion `h : W ⟶ X` preserves mixed upper weight bounds: restrict
the filtration, a closed point of `W` being a closed point of `X` with the same residue field,
stalk and local Frobenius (blueprint: `lem-zl-morphism-open-closed-reduction`, restriction). -/
theorem WeilSheaf.IsMixedOfWeightsAtMost.upperStar {W X : Scheme.{u}}
    [W.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k₀))] [X.Over
    (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (h : W ⟶ X)
    [IsImmersion h] [h.IsOver (Spec (CommRingCat.of k₀))] {w : ℝ} {F : WeilSheaf k₀ l X}
    (hF : F.IsMixedOfWeightsAtMost ι w) :
    ((WeilSheaf.upperStar h).obj F).IsMixedOfWeightsAtMost ι w := by
  rw [WeilSheaf.isMixedOfWeightsAtMost_iff_filtrationClosure] at hF ⊢
  exact ObjectProperty.filtrationClosure_map (WeilSheaf.upperStar h)
    (fun _ ⟨v, hv, hG⟩ ↦ ⟨v, hv, hG.upperStar h⟩) hF

/-- Pulling back along an immersion `h : W ⟶ X` carries Weil complexes mixed of weights at most
`w` to Weil complexes mixed of weights at most `w`: `h^*` is exact, so it commutes with taking
cohomology sheaves, and it preserves mixed upper bounds of sheaves
(blueprint: `lem-zl-morphism-open-closed-reduction`, restriction). -/
theorem WeilComplex.IsMixedOfWeightsAtMost.upperStar {W X : Scheme.{u}}
    [W.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k₀))] [X.Over
    (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (h : W ⟶ X)
    [IsImmersion h] [h.IsOver (Spec (CommRingCat.of k₀))] {w : ℝ} {K : WeilComplex k₀ l X}
    (hK : K.IsMixedOfWeightsAtMost ι w) :
    ((WeilComplex.upperStar h).obj K).IsMixedOfWeightsAtMost ι w :=
  fun b ↦ ((hK b).upperStar h).of_iso
    ((WeilComplex.upperStarCompHomologySheafIso h b).app K).symm

/-- Extension by zero `j₀!` along an open immersion `j : U ⟶ X` carries Weil complexes mixed of
weights at most `w` to Weil complexes mixed of weights at most `w`: it has the same stalks at the
points of `U` and zero stalks elsewhere, and extends filtrations by zero
(blueprint: `lem-zl-morphism-open-closed-reduction`, part 2). -/
theorem WeilComplex.IsMixedOfWeightsAtMost.derivedLowerShriek_of_isOpenImmersion
    {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (U ↘ Spec
    (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] {w : ℝ} {K : WeilComplex k₀ l U}
    (hK : K.IsMixedOfWeightsAtMost ι w) :
    ((WeilComplex.derivedLowerShriek k₀ l j).obj K).IsMixedOfWeightsAtMost ι w :=
  (HasDirectImageWeightBound.of_locallyQuasiFinite j).isMixedOfWeightsAtMost_derivedLowerShriek hK

/-- The direct image `i₀*` along a closed immersion `i : Z ⟶ X` carries Weil complexes mixed of
weights at most `w` to Weil complexes mixed of weights at most `w`, the case of a closed
immersion of the finite pushforward bound (blueprint: `lem-zl-finite-pushforward`, used in
`lem-zl-morphism-open-closed-reduction`, part 2). -/
theorem WeilComplex.IsMixedOfWeightsAtMost.derivedLowerStar_of_isClosedImmersion
    {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (Z ↘ Spec
    (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {w : ℝ}
    {K : WeilComplex k₀ l Z} (hK : K.IsMixedOfWeightsAtMost ι w) :
    ((WeilComplex.derivedLowerStar i).obj K).IsMixedOfWeightsAtMost ι w :=
  hK.derivedLowerStar_of_isFinite i

/-- Let `j : U ⟶ X` be an open immersion whose closed complement is `i : Z ⟶ X`. If the two
outer terms `j₀!j₀^*K` and `i₀*i₀^*K` of the localization triangle
`j₀!j₀^*K ⟶ K ⟶ i₀*i₀^*K ⟶ K[1]` are mixed of weights at most `w`, then so is `K`
(blueprint: `lem-zl-open-closed-weight`).

The blueprint argument is the extension stability of complex weights along the localization
triangle. -/
theorem WeilComplex.IsMixedOfWeightsAtMost.of_openClosed {U X Z : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] {j : U ⟶ X} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] {i : Z ⟶ X} [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) {w : ℝ} {K : WeilComplex k₀ l X}
    (hU : ((WeilComplex.derivedLowerShriek k₀ l j).obj
      ((WeilComplex.upperStar j).obj K)).IsMixedOfWeightsAtMost ι w)
    (hZ : ((WeilComplex.derivedLowerStar i).obj
      ((WeilComplex.upperStar i).obj K)).IsMixedOfWeightsAtMost ι w) :
    K.IsMixedOfWeightsAtMost ι w := by
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    WeilComplex.exists_distTriang_openClosed (k₀ := k₀) (l := l) hij K
  exact (WeilComplex.IsMixedOfWeightsAtMost.of_distTriang hT (hU.of_iso e₁.symm)
    (hZ.of_iso e₃.symm)).of_iso e₂

/-- Let `G` be a Weil sheaf on a `k₀`-scheme `X` of finite type, let `j : U ⟶ X` be an open
immersion whose closed complement is `i : Z ⟶ X`, and suppose that `j₀^*G` and `i₀^*G` are mixed
of weights at most `w`. Then `G` is mixed of weights at most `w`
(blueprint: `lem-zl-morphism-open-closed-reduction`, part 2).

The blueprint argument applies `lem-zl-open-closed-weight` to `G` placed in degree zero. -/
theorem WeilSheaf.IsMixedOfWeightsAtMost.of_openClosed {U X Z : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] [X.Over
    (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    {j : U ⟶ X} [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] {i : Z ⟶ X} [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) {w : ℝ} {G : WeilSheaf k₀ l X}
    (hU : ((WeilSheaf.upperStar j).obj G).IsMixedOfWeightsAtMost ι w)
    (hZ : ((WeilSheaf.upperStar i).obj G).IsMixedOfWeightsAtMost ι w) :
    G.IsMixedOfWeightsAtMost ι w := by
  have := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))
  have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  have hK := WeilComplex.IsMixedOfWeightsAtMost.of_openClosed (K := WeilSheaf.toComplex.obj G) hij
    (.derivedLowerShriek_of_isOpenImmersion j
      (hU.toComplex.of_iso ((WeilSheaf.toComplexCompUpperStarIso j).app G).symm))
    (.derivedLowerStar_of_isClosedImmersion i
      (hZ.toComplex.of_iso ((WeilSheaf.toComplexCompUpperStarIso i).app G).symm))
  exact ((hK 0).of_iso (WeilSheaf.toComplexCompHomologySheafIso.app G)).mono_weight (by simp)

/-- Let `j : U ⟶ X` be an open immersion whose closed complement is `i : Z ⟶ X`, and let
`f : X ⟶ Y`. Applying `Rf₀!` to the open–closed triangle of a Weil sheaf `F` and taking
cohomology sheaves gives exact sequences
`Rʳ(j ≫ f)₀! j₀^*F ⟶ Rʳf₀!F ⟶ Rʳ(i ≫ f)₀! i₀^*F`
(blueprint: `lem-zl-morphism-open-closed-reduction`, part 1, using `lem-sp-long-exact-of-triangle`).
-/
theorem WeilSheaf.exists_exact_higherLowerShriek_of_openClosed {U X Z Y : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    {j : U ⟶ X} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] {i : Z ⟶ X} [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))] {f : X ⟶ Y}
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) (F : WeilSheaf k₀ l X) (r : ℕ) :
    ∃ S : ShortComplex (WeilSheaf k₀ l Y), S.Exact ∧
      Nonempty (S.X₁ ≅ (WeilSheaf.higherLowerShriek k₀ l (j ≫ f) r).obj
        ((WeilSheaf.upperStar j).obj F)) ∧
      Nonempty (S.X₂ ≅ (WeilSheaf.higherLowerShriek k₀ l f r).obj F) ∧
      Nonempty (S.X₃ ≅ (WeilSheaf.higherLowerShriek k₀ l (i ≫ f) r).obj
        ((WeilSheaf.upperStar i).obj F)) := by
  have := locallyOfFiniteType_over_of_isOver f (S := Spec (CommRingCat.of k₀))
  have := locallyOfFiniteType_over_of_isOver j (S := Spec (CommRingCat.of k₀))
  have := locallyOfFiniteType_over_of_isOver i (S := Spec (CommRingCat.of k₀))
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← CategoryTheory.comp_over f (Spec (CommRingCat.of k₀))]; infer_instance
  have : QuasiSeparated (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← CategoryTheory.comp_over f (Spec (CommRingCat.of k₀))]; infer_instance
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    WeilComplex.exists_distTriang_openClosed (k₀ := k₀) (l := l) hij (WeilSheaf.toComplex.obj F)
  obtain ⟨c₁⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) j f
  obtain ⟨c₃⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) i f
  obtain ⟨p⟩ := WeilComplex.nonempty_derivedLowerShriek_iso_derivedLowerStar (k₀ := k₀) (l := l) i
  let Rf := WeilComplex.derivedLowerShriek k₀ l f
  let H := WeilComplex.homologySheaf (k₀ := k₀) (l := l) (X := Y) r
  refine ⟨_, WeilComplex.homologySheaf_exact₂ _ (Rf.map_distinguished T hT) r, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · exact H.mapIso (Rf.mapIso e₁ ≪≫ (c₁.app _).symm ≪≫
      (WeilComplex.derivedLowerShriek k₀ l (j ≫ f)).mapIso
        ((WeilSheaf.toComplexCompUpperStarIso j).app F)) ≪≫
      ((WeilSheaf.higherLowerShriekIso (j ≫ f) r).app _).symm
  · exact H.mapIso (Rf.mapIso e₂) ≪≫ ((WeilSheaf.higherLowerShriekIso f r).app _).symm
  · exact H.mapIso (Rf.mapIso (e₃ ≪≫ (p.app _).symm) ≪≫ (c₃.app _).symm ≪≫
      (WeilComplex.derivedLowerShriek k₀ l (i ≫ f)).mapIso
        ((WeilSheaf.toComplexCompUpperStarIso i).app F)) ≪≫
      ((WeilSheaf.higherLowerShriekIso (i ≫ f) r).app _).symm

/-- Compact support base change for the higher direct images: for a pullback square
```
X' --- g ---> X
|             |
f'            f
v             v
Y' --- h ---> Y
```
of `k₀`-schemes, `h₀^*Rʳf₀!F ≅ Rʳf'₀!g₀^*F`
(blueprint: `prop-functor-package`, item 4, used in `lem-zl-morphism-open-closed-reduction`,
part 2). -/
theorem WeilSheaf.nonempty_upperStar_higherLowerShriek_iso {X Y X' Y' : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [X'.Over (Spec (CommRingCat.of k₀))] [Y'.Over (Spec (CommRingCat.of k₀))]
    {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    {f' : X' ⟶ Y'} [f'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f']
    [LocallyOfFiniteType f'] [QuasiCompact f']
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y' ↘ Spec (CommRingCat.of k₀))]
    {g : X' ⟶ X} [g.IsOver (Spec (CommRingCat.of k₀))] {h : Y' ⟶ Y}
    [h.IsOver (Spec (CommRingCat.of k₀))] (hH : IsPullback g f' f h) (F : WeilSheaf k₀ l X)
    (r : ℕ) :
    Nonempty ((WeilSheaf.upperStar h).obj ((WeilSheaf.higherLowerShriek k₀ l f r).obj F) ≅
      (WeilSheaf.higherLowerShriek k₀ l f' r).obj ((WeilSheaf.upperStar g).obj F)) := by
  obtain ⟨e⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_upperStar_iso (k₀ := k₀) (l := l) hH
  have E : WeilSheaf.higherLowerShriek k₀ l f r ⋙ WeilSheaf.upperStar h ≅
      WeilSheaf.upperStar g ⋙ WeilSheaf.higherLowerShriek k₀ l f' r := by
    unfold WeilSheaf.higherLowerShriek
    exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (WeilComplex.upperStarCompHomologySheafIso h r).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e _ ≪≫
      Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (WeilSheaf.toComplexCompUpperStarIso g) _ ≪≫ Functor.associator _ _ _
  exact ⟨E.app F⟩

/-- Compact support base change for the total direct image: for a pullback square
```
X' --- g ---> X
|             |
f'            f
v             v
Y' --- h ---> Y
```
of `k₀`-schemes, `h₀^*Rf₀!K ≅ Rf'₀!g₀^*K`, so that `h₀^*Rf₀!K` is mixed of weights at most `w`
as soon as `Rf'₀!g₀^*K` is (blueprint: `prop-functor-package`, item 4, used in
`lem-zl-morphism-open-closed-reduction`, part 2). -/
theorem WeilComplex.IsMixedOfWeightsAtMost.upperStar_derivedLowerShriek_of_isPullback
    {X Y X' Y' : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [X'.Over (Spec (CommRingCat.of k₀))] [Y'.Over (Spec (CommRingCat.of k₀))]
    {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    {f' : X' ⟶ Y'} [f'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f']
    [LocallyOfFiniteType f'] [QuasiCompact f']
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y' ↘ Spec (CommRingCat.of k₀))]
    {g : X' ⟶ X} [g.IsOver (Spec (CommRingCat.of k₀))] {h : Y' ⟶ Y}
    [h.IsOver (Spec (CommRingCat.of k₀))] (hH : IsPullback g f' f h) {w : ℝ}
    {K : WeilComplex k₀ l X}
    (hK : ((WeilComplex.derivedLowerShriek k₀ l f').obj
      ((WeilComplex.upperStar g).obj K)).IsMixedOfWeightsAtMost ι w) :
    ((WeilComplex.upperStar h).obj
      ((WeilComplex.derivedLowerShriek k₀ l f).obj K)).IsMixedOfWeightsAtMost ι w := by
  obtain ⟨e⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_upperStar_iso (k₀ := k₀) (l := l) hH
  exact hK.of_iso (e.app K).symm

/-- Applying `Rʳf₀!` to a short exact sequence `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` of Weil sheaves gives an
exact sequence `Rʳf₀!F' ⟶ Rʳf₀!F ⟶ Rʳf₀!F''`, a piece of the long exact sequence of the
distinguished triangle `F' ⟶ F ⟶ F'' ⟶ F'[1]`
(blueprint: `lem-weil-heart-short-exact-triangles` and `lem-sp-long-exact-of-triangle`, used in
`lem-zl-morphism-open-closed-reduction`, part 3). -/
theorem WeilSheaf.exact_map_higherLowerShriek {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] {S : ShortComplex (WeilSheaf k₀ l X)}
    (hS : S.ShortExact) (r : ℕ) :
    (S.map (WeilSheaf.higherLowerShriek k₀ l f r)).Exact :=
  have := locallyOfFiniteType_over_of_isOver f (S := Spec (CommRingCat.of k₀))
  WeilComplex.homologySheaf_exact₂ _ ((WeilComplex.derivedLowerShriek k₀ l f).map_distinguished _
    (WeilSheaf.singleTriangle_distinguished hS)) r

/-- Let `j : U ⟶ X` be an open immersion whose closed complement is `i : Z ⟶ X`. If the
direct-image weight assertion holds for `j ≫ f` and for `i ≫ f`, then it holds for `f`:

```
U --- j ---> X <--- i --- Z
  \          |          /
   `- j ≫ f  | f   i ≫ f -'
       \     v     /
        `--> Y <--'
```

(blueprint: `sk-l-dl-general-excision`; this is part 1 of
`lem-zl-morphism-open-closed-reduction`, sheaf form). -/
theorem HasDirectImageWeightBound.of_openClosed {U X Z Y : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    {j : U ⟶ X} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] {i : Z ⟶ X} [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))] {f : X ⟶ Y}
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base))
    (hU : HasDirectImageWeightBound k₀ ι (j ≫ f))
    (hZ : HasDirectImageWeightBound k₀ ι (i ≫ f)) :
    HasDirectImageWeightBound k₀ ι f := by
  have := locallyOfFiniteType_over_of_isOver f (S := Spec (CommRingCat.of k₀))
  have := locallyOfFiniteType_over_of_isOver j (S := Spec (CommRingCat.of k₀))
  have := locallyOfFiniteType_over_of_isOver i (S := Spec (CommRingCat.of k₀))
  -- In each degree `r` the exact sequence `Rʳ(j ≫ f)₀! j₀^*F ⟶ Rʳf₀!F ⟶ Rʳ(i ≫ f)₀! i₀^*F`
  -- has outer terms mixed of weights at most `w + r`, hence so is the middle term.
  intro w F hF r
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    WeilSheaf.exists_exact_higherLowerShriek_of_openClosed (f := f) hij F r
  exact (WeilSheaf.IsMixedOfWeightsAtMost.of_exact hS
    ((hU w _ (hF.upperStar j) r).of_iso e₁.symm)
    ((hZ w _ (hF.upperStar i) r).of_iso e₃.symm)).of_iso e₂

/-- Let `j : U ⟶ X` be an open immersion whose closed complement is `i : Z ⟶ X`. If the complex
form of the direct-image weight assertion holds for `j ≫ f` and for `i ≫ f`, then it holds for
`f` (blueprint: `lem-zl-morphism-open-closed-reduction`, part 1, complex form).

The blueprint argument applies `Rf₀!` to the open–closed triangle of `K` and uses the extension
stability of complex weights (`lem-zl-complex-extension`). -/
theorem HasDirectImageComplexWeightBound.of_openClosed {U X Z Y : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    {j : U ⟶ X} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] {i : Z ⟶ X} [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))] {f : X ⟶ Y}
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base))
    (hU : HasDirectImageComplexWeightBound k₀ ι (j ≫ f))
    (hZ : HasDirectImageComplexWeightBound k₀ ι (i ≫ f)) :
    HasDirectImageComplexWeightBound k₀ ι f := by
  have := locallyOfFiniteType_over_of_isOver f (S := Spec (CommRingCat.of k₀))
  have := locallyOfFiniteType_over_of_isOver j (S := Spec (CommRingCat.of k₀))
  have := locallyOfFiniteType_over_of_isOver i (S := Spec (CommRingCat.of k₀))
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← CategoryTheory.comp_over f (Spec (CommRingCat.of k₀))]; infer_instance
  have : QuasiSeparated (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← CategoryTheory.comp_over f (Spec (CommRingCat.of k₀))]; infer_instance
  intro w K hK
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    WeilComplex.exists_distTriang_openClosed (k₀ := k₀) (l := l) hij K
  obtain ⟨c₁⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) j f
  obtain ⟨c₃⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) i f
  obtain ⟨p⟩ := WeilComplex.nonempty_derivedLowerShriek_iso_derivedLowerStar (k₀ := k₀) (l := l) i
  let Rf := WeilComplex.derivedLowerShriek k₀ l f
  have h₁ : (Rf.obj T.obj₁).IsMixedOfWeightsAtMost ι w :=
    ((hU w _ (hK.upperStar j)).of_iso (c₁.app _)).of_iso (Rf.mapIso e₁.symm)
  have h₃ : (Rf.obj T.obj₃).IsMixedOfWeightsAtMost ι w :=
    ((hZ w _ (hK.upperStar i)).of_iso (c₃.app _)).of_iso (Rf.mapIso (p.app _ ≪≫ e₃.symm))
  exact (WeilComplex.IsMixedOfWeightsAtMost.of_distTriang (Rf.map_distinguished T hT) h₁ h₃).of_iso
    (Rf.mapIso e₂)

section Target

variable {X Y V T X_V X_T : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [V.Over (Spec (CommRingCat.of k₀))]
  [T.Over (Spec (CommRingCat.of k₀))] [X_V.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X_V ↘ Spec (CommRingCat.of k₀))]
  [X_T.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X_T ↘ Spec (CommRingCat.of k₀))]
  {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  {j : V ⟶ Y} [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  {i : T ⟶ Y} [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
  {f_V : X_V ⟶ V} [f_V.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f_V]
  [LocallyOfFiniteType f_V] [QuasiCompact f_V] [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (V ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (V ↘ Spec (CommRingCat.of k₀))]
  {g_V : X_V ⟶ X} [g_V.IsOver (Spec (CommRingCat.of k₀))]
  {f_T : X_T ⟶ T} [f_T.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f_T]
  [LocallyOfFiniteType f_T] [QuasiCompact f_T] [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (T ↘ Spec (CommRingCat.of k₀))]
  {g_T : X_T ⟶ X} [g_T.IsOver (Spec (CommRingCat.of k₀))]

omit [QuasiCompact j] in
/-- Let `j : V ⟶ Y` be an open immersion whose closed complement is `i : T ⟶ Y`, and let
`f_V : X_V ⟶ V` and `f_T : X_T ⟶ T` be the base changes of `f : X ⟶ Y`. If the direct-image
weight assertion holds for `f_V` and for `f_T`, then it holds for `f`
(blueprint: `lem-zl-morphism-open-closed-reduction`, part 2, sheaf form).

By compact support base change `j₀^*Rʳf₀!F ≅ Rʳf_V₀!(F|_{X_V})` and
`i₀^*Rʳf₀!F ≅ Rʳf_T₀!(F|_{X_T})`, so both restrictions of `Rʳf₀!F` are mixed of weights at most
`w + r`, and the open–closed devissage on `Y` concludes. -/
theorem HasDirectImageWeightBound.of_openClosed_target
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) (H_V : IsPullback g_V f_V f j)
    (H_T : IsPullback g_T f_T f i) (h_V : HasDirectImageWeightBound k₀ ι f_V)
    (h_T : HasDirectImageWeightBound k₀ ι f_T) :
    HasDirectImageWeightBound k₀ ι f := by
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← CategoryTheory.comp_over f (Spec (CommRingCat.of k₀))]; infer_instance
  have : IsOpenImmersion g_V := MorphismProperty.of_isPullback H_V.flip ‹_›
  have : IsClosedImmersion g_T := MorphismProperty.of_isPullback H_T.flip ‹_›
  intro w F hF r
  obtain ⟨e_V⟩ := WeilSheaf.nonempty_upperStar_higherLowerShriek_iso H_V F r
  obtain ⟨e_T⟩ := WeilSheaf.nonempty_upperStar_higherLowerShriek_iso H_T F r
  exact WeilSheaf.IsMixedOfWeightsAtMost.of_openClosed hij
    ((h_V w _ (hF.upperStar g_V) r).of_iso e_V.symm)
    ((h_T w _ (hF.upperStar g_T) r).of_iso e_T.symm)

/-- Let `j : V ⟶ Y` be an open immersion whose closed complement is `i : T ⟶ Y`, and let
`f_V : X_V ⟶ V` and `f_T : X_T ⟶ T` be the base changes of `f : X ⟶ Y`. If the complex form of
the direct-image weight assertion holds for `f_V` and for `f_T`, then it holds for `f`
(blueprint: `lem-zl-morphism-open-closed-reduction`, part 2, complex form).

By compact support base change the restrictions of `Rf₀!K` to `V` and `T` are mixed of weights
at most `w`; extension by zero along `j` and the direct image along `i` preserve this, and the
open–closed devissage `lem-zl-open-closed-weight` concludes. -/
theorem HasDirectImageComplexWeightBound.of_openClosed_target
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) (H_V : IsPullback g_V f_V f j)
    (H_T : IsPullback g_T f_T f i) (h_V : HasDirectImageComplexWeightBound k₀ ι f_V)
    (h_T : HasDirectImageComplexWeightBound k₀ ι f_T) :
    HasDirectImageComplexWeightBound k₀ ι f := by
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← CategoryTheory.comp_over f (Spec (CommRingCat.of k₀))]; infer_instance
  have : IsOpenImmersion g_V := MorphismProperty.of_isPullback H_V.flip ‹_›
  have : IsClosedImmersion g_T := MorphismProperty.of_isPullback H_T.flip ‹_›
  intro w K hK
  exact WeilComplex.IsMixedOfWeightsAtMost.of_openClosed hij
    (.derivedLowerShriek_of_isOpenImmersion j
      (.upperStar_derivedLowerShriek_of_isPullback H_V (h_V w _ (hK.upperStar g_V))))
    (.derivedLowerStar_of_isClosedImmersion i
      (.upperStar_derivedLowerShriek_of_isPullback H_T (h_T w _ (hK.upperStar g_T))))

end Target

/-- Let `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` be a short exact sequence of Weil sheaves on `X`. If `Rʳf₀!F'`
and `Rʳf₀!F''` are mixed of weights at most `w + r` for every `r`, then so is `Rʳf₀!F`
(blueprint: `lem-zl-morphism-open-closed-reduction`, part 3). -/
theorem WeilSheaf.isMixedOfWeightsAtMost_higherLowerShriek_of_shortExact {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] {S : ShortComplex (WeilSheaf k₀ l X)}
    (hS : S.ShortExact) {w : ℝ}
    (h₁ : ∀ r : ℕ, ((WeilSheaf.higherLowerShriek k₀ l f r).obj S.X₁).IsMixedOfWeightsAtMost ι
      (w + r))
    (h₃ : ∀ r : ℕ, ((WeilSheaf.higherLowerShriek k₀ l f r).obj S.X₃).IsMixedOfWeightsAtMost ι
      (w + r))
    (r : ℕ) :
    ((WeilSheaf.higherLowerShriek k₀ l f r).obj S.X₂).IsMixedOfWeightsAtMost ι (w + r) :=
  WeilSheaf.IsMixedOfWeightsAtMost.of_exact (WeilSheaf.exact_map_higherLowerShriek f hS r)
    (h₁ r) (h₃ r)

end OpenClosed

end AlgebraicGeometry
