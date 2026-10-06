/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Integral.Exact

/-!
# Integral base changes of the base-change map

Two operations on a Cartesian square do not change whether its degree-`q` base-change map
`p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism, as long as the morphism involved is
integral:

- replacing the bottom right corner `T` by `T'` along an integral surjective `π : T' ⟶ T`,
  provided `BC(p, Λ, q - 1)` holds
  (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective`);
- replacing the base `S'` of `p'` by `S''` along an integral `π : S'' ⟶ S'` through which
  `g` factors (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_iff_of_isIntegralHom`).

Both rest on the exactness of the direct image along an integral morphism,
`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom`: in each case the
direct image along `π` (resp. along its base change `π'`) identifies the two base-change maps,
which is recorded in `AlgebraicGeometry.Etale.nonempty_arrowIso_baseChangeHomologyMap_lowerStar`
and `AlgebraicGeometry.Etale.nonempty_arrowIso_baseChangeHomologyMap_comp`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective`:
  integral surjective base change on the target.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_iff_of_isIntegralHom`: integral base
  change on the source.

## References

- Stacks Project, Lemma 59.88.3, <https://stacks.math.columbia.edu/tag/0F04>
- Stacks Project, Lemma 59.88.4, <https://stacks.math.columbia.edu/tag/0F05>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

section Target

variable {X S T Y T' Y' : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
  {e' : Y' ⟶ T'} {h' : Y' ⟶ X}

/-- The direct image along an integral morphism `π : T' ⟶ T` identifies base-change maps:
for Cartesian squares over `g : T ⟶ S` and over `π ≫ g`, the base-change map of the first
square at `π_* F'` is isomorphic, as an arrow, to the base-change map of the second square at
`F'`.

Since `π_*` is exact (`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom`)
the Grothendieck spectral sequence gives `R^q g_* π_* F' = R^q (π ≫ g)_* F'`; the integral base
change `e⁻¹ π_* F' = π''_* e'⁻¹ F'` along the base change `π'' : Y' ⟶ Y` of `π`, together with
the exactness of `π''_*`, gives `R^q h_* e⁻¹ π_* F' = R^q h'_* e'⁻¹ F'`, and the two base-change
maps correspond. This is the identification in the proof of blueprint
`sbc-lem-bc-integral-surjective`. -/
theorem Etale.nonempty_arrowIso_baseChangeHomologyMap_lowerStar (sq : IsPullback e h g p)
    (π : T' ⟶ T) [IsIntegralHom π] (sq' : IsPullback e' h' (π ≫ g) p) (q : ℤ)
    (F' : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty (Arrow.mk
      (Etale.baseChangeHomologyMap Λ sq q ((π)_*[ModuleCat.{u + 1} Λ].obj F')) ≅
        Arrow.mk (Etale.baseChangeHomologyMap Λ sq' q F')) :=
  sorry

/-- Blueprint `sbc-lem-bc-integral-surjective`: Integral surjective base change on the target.

Assume `BC(p, Λ, q - 1)` for some `q ≥ 1`. Let `g : T ⟶ S` be quasi-compact and
quasi-separated, `π : T' ⟶ T` integral and surjective, and consider Cartesian squares over `g`
and over `π ≫ g`. If the base-change map of the square over `π ≫ g` is an isomorphism at
`π⁻¹ F`, then the base-change map of the square over `g` is an isomorphism at `F`.

Since `π` is surjective, `F ⟶ π_* π⁻¹ F` is injective
(`AlgebraicGeometry.Etale.mono_unit_app_of_surjective`), so by
`AlgebraicGeometry.Etale.mono_cokernelMap` the cokernel of the base-change map at `F` embeds
into the one at `π_* π⁻¹ F`. The latter vanishes, the base-change map at `π_* π⁻¹ F` being
identified with the one over `π ≫ g` at `π⁻¹ F` by
`AlgebraicGeometry.Etale.nonempty_arrowIso_baseChangeHomologyMap_lowerStar`. The base-change
map at `F` is therefore surjective, and it is injective by
`AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`. -/
@[stacks 0F04]
theorem Etale.isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective (q : ℤ) (hq : 1 ≤ q)
    (hprev : Etale.BaseChangeProperty Λ p (q - 1)) [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p) (π : T' ⟶ T) [IsIntegralHom π] (hπ : Function.Surjective π.base)
    (sq' : IsPullback e' h' (π ≫ g) p) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsIso (Etale.baseChangeHomologyMap Λ sq' q ((π)^*[ModuleCat.{u + 1} Λ].obj F))) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  obtain ⟨φ⟩ := Etale.nonempty_arrowIso_baseChangeHomologyMap_lowerStar Λ sq π sq' q
    ((π)^*[ModuleCat.{u + 1} Λ].obj F)
  have : IsIso (Etale.baseChangeHomologyMap Λ sq q
      ((π)_*[ModuleCat.{u + 1} Λ].obj ((π)^*[ModuleCat.{u + 1} Λ].obj F))) :=
    (Arrow.isIso_iff_isIso_of_isIso φ.hom).2 hF
  have := Etale.mono_baseChangeHomologyMap Λ q hq hprev sq F
  have := Etale.mono_unit_app_of_surjective Λ π hπ F
  have hc := Etale.mono_cokernelMap Λ q hq hprev sq
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit.app F)
  have : Epi (Etale.baseChangeHomologyMap Λ sq q F) :=
    Preadditive.epi_of_isZero_cokernel _ (@IsZero.of_mono _ _ _ _ _ _ hc (isZero_cokernel_of_epi
      (Etale.baseChangeHomologyMap Λ sq q
        ((π)_*[ModuleCat.{u + 1} Λ].obj ((π)^*[ModuleCat.{u + 1} Λ].obj F)))))
  exact isIso_of_mono_of_epi _

end Target

section Source

variable {X' S' S'' X'' T Y : Scheme.{u}} {p' : X' ⟶ S'} {p'' : X'' ⟶ S''} {π' : X'' ⟶ X'}
  {g' : T ⟶ S''} {e : Y ⟶ T} {h'' : Y ⟶ X''}

/-- The direct image along the base change `π' : X'' ⟶ X'` of an integral morphism
`π : S'' ⟶ S'` identifies base-change maps: for a Cartesian square over `g' : T ⟶ S''` for
the base change `p''` of `p'` along `π`, the base-change map of the pasted square over
`g' ≫ π` is isomorphic, as an arrow, to the image under `π'_*` of the base-change map of the
square over `g'`.

Since `π` and `π'` are integral, `π_*` and `π'_*` are exact
(`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom`), so
`R^q (g' ≫ π)_* = π_* R^q g'_*` and `R^q (h'' ≫ π')_* = π'_* R^q h''_*`, and the integral base
change `p'⁻¹ π_* = π'_* p''⁻¹` identifies the sources. This is the identification in the
proof of blueprint `sbc-lem-bc-integral-base`. -/
theorem Etale.nonempty_arrowIso_baseChangeHomologyMap_comp (π : S'' ⟶ S') [IsIntegralHom π]
    (hπ : IsPullback π' p'' p' π) (sq'' : IsPullback e h'' g' p'')
    (sq : IsPullback e (h'' ≫ π') (g' ≫ π) p') (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty (Arrow.mk (Etale.baseChangeHomologyMap Λ sq q F) ≅
      Arrow.mk ((π')_*[ModuleCat.{u + 1} Λ].map (Etale.baseChangeHomologyMap Λ sq'' q F))) :=
  sorry

/-- Blueprint `sbc-lem-bc-integral-base`: Integral base change on the source.

Let `π : S'' ⟶ S'` be integral, `p'' : X'' ⟶ S''` the base change of `p' : X' ⟶ S'` along
`π`, and consider a Cartesian square for `p''` over `g' : T ⟶ S''` and the pasted Cartesian
square for `p'` over `g' ≫ π`. Then the base-change map of the pasted square at `F` is an
isomorphism if and only if the base-change map of the square over `g'` is.

The blueprint states the forward implication; the converse is what the proof of blueprint
`sbc-lem-bc-universal-test` uses. By
`AlgebraicGeometry.Etale.nonempty_arrowIso_baseChangeHomologyMap_comp` the first map is the
image under `π'_*` of the second, and `π'_*` is conservative
(`AlgebraicGeometry.Etale.reflectsIsomorphisms_lowerStar_of_isIntegralHom`), `π'` being
integral as a base change of `π`. -/
@[stacks 0F05]
theorem Etale.isIso_baseChangeHomologyMap_iff_of_isIntegralHom (π : S'' ⟶ S') [IsIntegralHom π]
    (hπ : IsPullback π' p'' p' π) (sq'' : IsPullback e h'' g' p'')
    (sq : IsPullback e (h'' ≫ π') (g' ≫ π) p') (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) ↔
      IsIso (Etale.baseChangeHomologyMap Λ sq'' q F) := by
  obtain ⟨φ⟩ := Etale.nonempty_arrowIso_baseChangeHomologyMap_comp Λ π hπ sq'' sq q F
  rw [Arrow.isIso_iff_isIso_of_isIso φ.hom]
  have : IsIntegralHom π' := MorphismProperty.of_isPullback hπ.flip inferInstance
  have := Etale.reflectsIsomorphisms_lowerStar_of_isIntegralHom Λ π'
  exact ⟨fun _ ↦ isIso_of_reflects_iso _ (π')_*[ModuleCat.{u + 1} Λ], fun _ ↦ inferInstance⟩

end Source

end AlgebraicGeometry
