/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.PunctualSupport
public import WeilConjectures.WeilSheaf.DenseOpen
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.LisseFiltration
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunctionWeil

/-!
# The unit of a dense open of the affine line

Let `j : U₀ ↪ 𝔸¹` be a dense open immersion. For a Weil sheaf `G` on the affine line, the unit
`G ⟶ j_* j^* G` becomes an isomorphism on `U₀`, so its kernel and cokernel are punctual. These
facts, and the restriction of a lisse sheaf to a smaller dense open, are the sheaf-theoretic
input of the description of the simple curve perverse sheaves (blueprint
`prop-a1-curve-perverse-simples`).

## Main statements

- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.mono_unit_app`: the unit `G ⟶ j_* j^* G` is a
  monomorphism when `G` has no nonzero punctual subsheaf, and its cokernel is punctual
  (`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.support_finite_cokernel_unit_app`).
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.exists_mono_directImage`: a Weil sheaf without
  punctual subsheaf embeds into the direct image of its restriction to a dense lisse open, with
  punctual cokernel.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.exists_restrict_isLisse`: an irreducible lisse
  datum can be restricted to a smaller dense open, on which two given sheaves are lisse, without
  changing its direct image.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isZero_or_isZero_of_exact`: an exact sequence
  `A ↪ j_*N ⟶ B ↠ C` with `N` irreducible lisse, `C` punctual and `B` without punctual subsheaf,
  in which `A` and `C` are lisse on `U₀`, has `A = C = 0` or `B = 0`.

## Implementation notes

The open immersion `j` of a datum is separated as a monomorphism in the statements of the
adjunction `j^* ⊣ j_*`. The affine `U₀` gives a second instance, through the separatedness of
`U₀`, whose proof term differs; unifying the two statements is then very slow. We therefore raise
the priority of `AlgebraicGeometry.IsSeparated.isSeparated_of_mono` locally.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilSheaf

namespace LisseOnDenseOpen

attribute [local instance 1000] IsSeparated.isSeparated_of_mono

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (D : LisseOnDenseOpen k₀ l)

/-- The restriction `j^*` of the unit `G ⟶ j_* j^* G` of a dense open `j : U₀ ↪ 𝔸¹` is an
isomorphism, the counit `j^* j_* ⟶ 𝟭` being one. -/
theorem isIso_upperStar_map_unit_app (G : WeilSheaf k₀ l (affineLine k₀)) :
    IsIso ((upperStar D.j).map ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) D.j).unit.app
      G)) :=
  Adjunction.isIso_map_unit_app_of_isIso_counit_app _ G

/-- The kernel of the unit `G ⟶ j_* j^* G` is punctual: it vanishes on `U₀`. -/
theorem support_finite_kernel_unit_app (G : WeilSheaf k₀ l (affineLine k₀)) :
    (kernel ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) D.j).unit.app G)).support.Finite
    := by
  have := D.nonempty_U
  have := D.isIso_upperStar_map_unit_app G
  have : Mono ((upperStar D.j).map
      ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) D.j).unit.app G)) :=
    IsIso.mono_of_iso _
  exact support_finite_of_isZero_upperStar D.j _
    ((isZero_kernel_of_mono _).of_iso (PreservesKernel.iso (upperStar D.j) _))

/-- The cokernel of the unit `G ⟶ j_* j^* G` is punctual: it vanishes on `U₀`. -/
theorem support_finite_cokernel_unit_app (G : WeilSheaf k₀ l (affineLine k₀)) :
    (cokernel ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) D.j).unit.app G)).support.Finite
    := by
  have := D.nonempty_U
  have := D.isIso_upperStar_map_unit_app G
  have : Epi ((upperStar D.j).map
      ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) D.j).unit.app G)) :=
    IsIso.epi_of_iso _
  exact support_finite_of_isZero_upperStar D.j _
    ((isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso (upperStar D.j) _))

/-- The unit `G ⟶ j_* j^* G` is a monomorphism when `G` has no nonzero punctual subsheaf: its
kernel is punctual. -/
theorem mono_unit_app {G : WeilSheaf k₀ l (affineLine k₀)}
    (hG : ∀ (G' : WeilSheaf k₀ l (affineLine k₀)) (i : G' ⟶ G), Mono i → G'.support.Finite →
      IsZero G') :
    Mono ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) D.j).unit.app G) :=
  Preadditive.mono_of_isZero_kernel _
    (hG _ (kernel.ι _) inferInstance (D.support_finite_kernel_unit_app G))

/-- Every morphism from a punctual Weil sheaf to the direct image `j_* N'` of a lisse sheaf on
`U₀` vanishes (`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.eq_zero_of_support_finite`). -/
theorem eq_zero_of_support_finite_lowerStar {N' : WeilSheaf k₀ l D.U} (hN' : N'.IsLisse)
    {G : WeilSheaf k₀ l (affineLine k₀)} (hG : G.support.Finite)
    (i : G ⟶ (lowerStar D.j).obj N') : i = 0 :=
  ({ D with sheaf := N', lisse := hN' } : LisseOnDenseOpen k₀ l).eq_zero_of_support_finite hG i

/-- A punctual Weil sheaf `G` on the affine line whose restriction to `U₀` is lisse vanishes on
`U₀`: the unit `G ⟶ j_* j^* G` is a morphism from a punctual sheaf to the direct image of a lisse
sheaf, hence zero, and its restriction to `U₀` is invertible. -/
theorem isZero_upperStar_of_isLisse {G : WeilSheaf k₀ l (affineLine k₀)} (hG : G.support.Finite)
    (hGl : ((upperStar D.j).obj G).IsLisse) : IsZero ((upperStar D.j).obj G) := by
  have hi := D.isIso_upperStar_map_unit_app G
  rw [D.eq_zero_of_support_finite_lowerStar hGl hG
    ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) D.j).unit.app G), Functor.map_zero] at hi
  have := @IsIso.mono_of_iso _ _ _ _ _ hi
  exact IsZero.of_mono_zero _ _

/-- A Weil sheaf on `U₀` whose direct image vanishes is zero: `j^* j_* N' ≅ N'`. -/
theorem isZero_of_isZero_lowerStar {N' : WeilSheaf k₀ l D.U}
    (h : IsZero ((lowerStar D.j).obj N')) : IsZero N' :=
  ((upperStar D.j).map_isZero h).of_iso (upperStarDirectImageIso D.j N').symm

/-- A morphism of Weil sheaves on `U₀` whose direct image is an isomorphism is an isomorphism:
`j^* j_* ≅ 𝟭`. -/
theorem isIso_of_isIso_lowerStar_map {N' N : WeilSheaf k₀ l D.U} (i : N' ⟶ N)
    (h : IsIso ((lowerStar D.j).map i)) : IsIso i := by
  have hn := (upperStarLowerStarAdjunction (k₀ := k₀) (l := l) D.j).counit.naturality i
  have : IsIso (((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) D.j).counit.app N') ≫
      (𝟭 _).map i) := by
    have : IsIso ((lowerStar D.j ⋙ upperStar D.j).map i) :=
      Functor.map_isIso (upperStar D.j) ((lowerStar D.j).map i)
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_left _ ((𝟭 _).map i)

/-- For a lisse subsheaf `N' ⊆ N`, the cokernel of `j_* N' ⟶ j_* N` has no nonzero punctual
subsheaf: by left exactness of `j_*` it embeds into `j_*(N / N')`, the direct image of a lisse
sheaf. -/
theorem isZero_of_mono_cokernel_lowerStar_map {N' : WeilSheaf k₀ l D.U} (i : N' ⟶ D.sheaf)
    [Mono i] (hN' : N'.IsLisse) (G : WeilSheaf k₀ l (affineLine k₀))
    (g : G ⟶ cokernel ((lowerStar D.j).map i)) [Mono g] (hG : G.support.Finite) : IsZero G := by
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.Exact := ShortComplex.exact_cokernel i
  have hex := hS.map_of_mono_of_preservesKernel (lowerStar D.j) (inferInstanceAs (Mono i))
    inferInstance
  have := (ShortComplex.exact_iff_mono_cokernel_desc _).1 hex
  refine IsZero.of_mono_eq_zero g
    ((cancel_mono (cokernel.desc _ _ (S.map (lowerStar D.j)).zero)).1 ?_)
  rw [zero_comp]
  exact D.eq_zero_of_support_finite_lowerStar (hN'.kernel_cokernel D.lisse i).2 hG _

/-- **Restriction to a smaller dense open.** Given two Weil sheaves `A` and `C` on the affine
line, an irreducible lisse datum `(U₀, j, N)` can be restricted to a dense open `V ⊆ U₀` on which
`A` and `C` are lisse (generic lissity,
`AlgebraicGeometry.WeilSheaf.exists_dense_isLisse_upperStar`). The restriction `N|_V` is still
irreducible (`AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.upperStar_of_isDominant`) and has
the same direct image, the unit `N ⟶ k_* k^* N` of `k : V ↪ U₀` being an isomorphism for the
lisse `N` (`AlgebraicGeometry.WeilSheaf.IsLisse.nonempty_iso_directImage_upperStar`). -/
theorem exists_restrict_isLisse (hD : D.sheaf.IsIrreducibleLisse)
    (A C : WeilSheaf k₀ l (affineLine k₀)) :
    ∃ D' : LisseOnDenseOpen k₀ l, D'.sheaf.IsIrreducibleLisse ∧
      Nonempty (D'.directImage ≅ D.directImage) ∧ ((upperStar D'.j).obj A).IsLisse ∧
        ((upperStar D'.j).obj C).IsLisse := by
  obtain ⟨VA, hVA, hA⟩ := exists_dense_isLisse_upperStar ((upperStar D.j).obj A)
  obtain ⟨VC, hVC, hC⟩ := exists_dense_isLisse_upperStar ((upperStar D.j).obj C)
  set V : D.U.Opens := VA ⊓ VC
  have hV : Dense (V : Set D.U) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact hVA.inter_of_isOpen_left hVC VA.isOpen
  have : IsDominant V.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  -- lissity on `V` of a sheaf lisse on an open `W ⊇ V`
  have hlisse (W : D.U.Opens) (hVW : V ≤ W) (G : WeilSheaf k₀ l (affineLine k₀))
      (hG : ((upperStar W.ι).obj ((upperStar D.j).obj G)).IsLisse) :
      ((upperStar (V.ι ≫ D.j)).obj G).IsLisse := by
    have : (D.U.homOfLE hVW).IsOver (Spec (CommRingCat.of k₀)) :=
      ⟨by rw [← comp_over W.ι, Scheme.homOfLE_ι_assoc, comp_over V.ι]⟩
    exact (isLisse_upperStar_comp_iff V.ι D.j G).2 ((isLisse_upperStar_congr
      (Scheme.homOfLE_ι _ hVW) _).1 ((isLisse_upperStar_comp_iff _ W.ι _).2 (hG.upperStar _)))
  obtain ⟨e⟩ := D.lisse.nonempty_iso_directImage_upperStar V.ι (by rwa [Scheme.Opens.range_ι])
  let D' : LisseOnDenseOpen k₀ l :=
    { U := V
      j := V.ι ≫ D.j
      sheaf := (upperStar V.ι).obj D.sheaf
      lisse := D.lisse.upperStar V.ι }
  exact ⟨D', hD.upperStar_of_isDominant V.ι,
    ⟨(lowerStarCompIso V.ι D.j).symm.app _ ≪≫ (lowerStar D.j).mapIso e.symm⟩,
    hlisse VA inf_le_left A hA, hlisse VC inf_le_right C hC⟩

/-- **Simplicity of a middle extension, sheaf part** (`prop-a1-curve-perverse-simples`). Let
`A ↪ M ⟶ B ↠ C` be an exact sequence of Weil sheaves on the affine line with `M ≅ j_*N` for an
irreducible lisse `N`, `C` punctual and `B` without nonzero punctual subsheaf, such that `A` and
`C` are lisse on `U₀`. Then `C` vanishes on `U₀`, and `A|_{U₀} ⊆ N` is `0` or `N`:

- if `A|_{U₀} = 0`, then `A` is a punctual subsheaf of `j_*N`, hence zero, and `M ⟶ B` is
  injective and an isomorphism on `U₀`. The unit `B ⟶ j_* j^* B` is injective, `B` having no
  punctual subsheaf, and `M ⟶ B ⟶ j_* j^* B` is the isomorphism `M ⟶ j_* j^* M ≅ j_* j^* B`,
  so `M ⟶ B` is an isomorphism and `C = 0`;
- if `A|_{U₀} = N`, then `B|_{U₀} ⊆ C|_{U₀} = 0`, so `B` is punctual, hence zero. -/
theorem isZero_or_isZero_of_exact (hD : D.sheaf.IsIrreducibleLisse)
    {A M B C : WeilSheaf k₀ l (affineLine k₀)} (eM : M ≅ D.directImage) (a : A ⟶ M) (s : M ⟶ B)
    (t : B ⟶ C) [Mono a] [Epi t] (has : a ≫ s = 0) (hst : s ≫ t = 0)
    (h₁ : (ShortComplex.mk a s has).Exact) (h₂ : (ShortComplex.mk s t hst).Exact)
    (hA : ((upperStar D.j).obj A).IsLisse) (hC : C.support.Finite)
    (hCl : ((upperStar D.j).obj C).IsLisse)
    (hB : ∀ (G : WeilSheaf k₀ l (affineLine k₀)) (i : G ⟶ B), Mono i → G.support.Finite →
      IsZero G) :
    (IsZero A ∧ IsZero C) ∨ IsZero B := by
  sorry

end LisseOnDenseOpen

/-- **Embedding into a middle extension.** A Weil sheaf `F` on the affine line without nonzero
punctual subsheaf embeds into the direct image `j_* N` of its restriction `N` to a dense open
`j : U₀ ↪ 𝔸¹` on which it is lisse, with punctual cokernel: the kernel and the cokernel of the
unit `F ⟶ j_* j^* F` vanish on `U₀`. (blueprint: `prop-a1-curve-perverse-simples`) -/
theorem LisseOnDenseOpen.exists_mono_directImage {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] {F : WeilSheaf k₀ l (affineLine k₀)}
    (hF : ∀ (G : WeilSheaf k₀ l (affineLine k₀)) (i : G ⟶ F), Mono i → G.support.Finite →
      IsZero G) :
    ∃ (D : LisseOnDenseOpen k₀ l) (η : F ⟶ D.directImage), Mono η ∧
      (cokernel η).support.Finite := by
  have : IsNoetherian (affineLine k₀) :=
    isNoetherian_of_locallyOfFiniteType (affineLine k₀ ↘ Spec (.of k₀))
  obtain ⟨U, hU, hUl⟩ := exists_dense_isLisse_upperStar F
  have : IsDominant U.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  let D : LisseOnDenseOpen k₀ l :=
    { U := U, j := U.ι, sheaf := (upperStar U.ι).obj F, lisse := hUl }
  sorry

end WeilSheaf

end AlgebraicGeometry
