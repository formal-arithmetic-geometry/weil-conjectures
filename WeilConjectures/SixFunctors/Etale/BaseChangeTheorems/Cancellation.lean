/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality

/-!
# Composition, cancellation and target locality of the base change property

For a coefficient ring `Λ` which is torsion as an additive group, the base change property
`AlgebraicGeometry.Etale.HasTorsionBaseChange` of proper morphisms

- is stable under composition (`AlgebraicGeometry.Etale.HasTorsionBaseChange.comp`);
- cancels along proper surjections: if `f` is proper and surjective and `f` and `f ≫ h` have the
  property, then so does `h` (`AlgebraicGeometry.Etale.HasTorsionBaseChange.of_comp`).

Composition is the vertical pasting law of the derived base change map. Cancellation is proved
on the side of injective acyclicity: an injective sheaf `I` on `Y` is a direct summand of
`f_* J` for an injective `J` on `X` (`AlgebraicGeometry.Etale.mono_homEquiv_of_surjective`), and
the higher direct images of the base change of `f_* J` along `h` vanish because
`R(h'f')_* = Rh'_* ∘ Rf'_*` and both `Rf'_*` and `R(h'f')_*` kill the higher cohomology of the
base change of `J`.

Finally, for an arbitrary coefficient ring the base change property is local on the target
(`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_affineOpens`).

## References

- Stacks Project, Lemma 59.91.7, <https://stacks.math.columbia.edu/tag/0A4C>
- Stacks Project, Lemma 59.91.8, <https://stacks.math.columbia.edu/tag/0A4D>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Composition stability of the base change property.** For a torsion coefficient ring `Λ`,
if `f : X ⟶ Y` and `h : Y ⟶ Z` satisfy the base change property, so does `f ≫ h`. For a
torsion ring the property is `AlgebraicGeometry.Etale.IsBaseChangeIso`, which is stable under
composition by the vertical pasting law of the derived base change map.
(blueprint: `prop-weil-pbc-composition-stability`, `lemma-weil-pbc-composition`) -/
@[stacks 0A4D]
theorem Etale.HasTorsionBaseChange.comp (hΛ : IsAddTorsion Λ) {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} (hf : Etale.HasTorsionBaseChange Λ f)
    (hh : Etale.HasTorsionBaseChange Λ h) : Etale.HasTorsionBaseChange Λ (f ≫ h) :=
  sorry

/-- **Composition stability of injective acyclicity.** For a torsion coefficient ring `Λ` and
proper morphisms `f : X ⟶ Y`, `h : Y ⟶ Z` with injective acyclicity, `f ≫ h` has injective
acyclicity. (blueprint: `prop-weil-pbc-composition-stability`, `lemma-weil-pbc-composition`) -/
theorem Etale.HasInjectiveAcyclicity.comp (hΛ : IsAddTorsion Λ) {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} [IsProper f] [IsProper h] (hf : Etale.HasInjectiveAcyclicity Λ f)
    (hh : Etale.HasInjectiveAcyclicity Λ h) : Etale.HasInjectiveAcyclicity Λ (f ≫ h) :=
  sorry

/-- **The retract supplied by a surjection.** Let `f : X ⟶ Y` be surjective, let `I` be a sheaf
on `Y` and `ι : f^* I ⟶ J` a monomorphism. Then the adjoint map `I ⟶ f_* J` is a monomorphism:
at a geometric point `ȳ` of `Y`, choose a geometric point `x̄` of `X` above it; the stalk map
`I_ȳ ⟶ (f_* J)_ȳ` followed by the restriction to `J_x̄` is the injection
`I_ȳ = (f^* I)_x̄ ⟶ J_x̄`. Geometric stalks are conservative. If `I` is injective, the
monomorphism splits, so `I` is a direct summand of `f_* J`.
(blueprint: `lem-weil-pbc-retract-supplied`) -/
theorem Etale.mono_homEquiv_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    {I : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ι : (f)^*[ModuleCat.{u + 1} Λ].obj I ⟶ J) [Mono ι] :
    Mono ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _ ι) :=
  sorry

/-- **Vanishing descends to a retract.** If `I` is a retract of `M` and the higher direct images
of `M` along `h` vanish in degree `q`, then so do those of `I`: the higher direct image functors
are additive, so `Rᵠh_* I` is a retract of `Rᵠh_* M = 0`.
(blueprint: `lem-weil-pbc-vanishing-descends-retract`) -/
theorem Etale.isZero_homology_rightDerivedFunctorPlus_of_retract {X Y : Scheme.{u}}
    (h : X ⟶ Y) {I M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (s : I ⟶ M)
    (r : M ⟶ I) (hsr : s ≫ r = 𝟙 I) (q : ℤ)
    (hM : IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
      (R+((h)_*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj M)))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
      (R+((h)_*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj I))) :=
  sorry

/-- **Cancellation of injective acyclicity along a proper surjection.** For a torsion
coefficient ring `Λ`, let `f : X ⟶ Y` be proper and surjective and `h : Y ⟶ Z` proper. If `f`
and `f ≫ h` have injective acyclicity, so does `h`.

Let `I` be an injective sheaf on `Y`; embed `f^* I` into an injective `J` on `X`. By
`AlgebraicGeometry.Etale.mono_homEquiv_of_surjective` the sheaf `I` is a direct summand of
`f_* J`. After a base change `Z' ⟶ Z`, the underived proper exchange identifies the base change
of `f_* J` with `f'_*` of the base change of `J`, whose higher direct images along `h'`
vanish since `Rh'_* ∘ Rf'_* = R(h'f')_*`, `IA(f)` and `IA(f ≫ h)`. The vanishing descends to the
direct summand. (blueprint: `lemma-weil-pbc-cancellation`) -/
@[stacks 0A4C]
theorem Etale.HasInjectiveAcyclicity.of_comp (hΛ : IsAddTorsion Λ) {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} [IsProper f] [Surjective f] [IsProper h]
    (hf : Etale.HasInjectiveAcyclicity Λ f) (hfh : Etale.HasInjectiveAcyclicity Λ (f ≫ h)) :
    Etale.HasInjectiveAcyclicity Λ h :=
  sorry

/-- **Cancellation of the base change property along a proper surjection.** For a torsion
coefficient ring `Λ`, let `f : X ⟶ Y` be proper and surjective and `h : Y ⟶ Z` proper. If `f`
and `f ≫ h` satisfy the base change property, so does `h`. This is
`AlgebraicGeometry.Etale.HasInjectiveAcyclicity.of_comp` transported along the equivalence of
the base change property and injective acyclicity.
(blueprint: `lemma-weil-pbc-cancellation`) -/
@[stacks 0A4C]
theorem Etale.HasTorsionBaseChange.of_comp (hΛ : IsAddTorsion Λ) {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} [IsProper f] [Surjective f] [IsProper h]
    (hf : Etale.HasTorsionBaseChange Λ f) (hfh : Etale.HasTorsionBaseChange Λ (f ≫ h)) :
    Etale.HasTorsionBaseChange Λ h :=
  sorry

/-- **Target locality of the base change property.** A morphism `f : X ⟶ Y` satisfies the base
change property as soon as its restrictions `f ∣_ U : f ⁻¹ᵁ U ⟶ U` over all affine opens `U`
of `Y` do: the derived base change map of a cartesian square over `Y` is an isomorphism as soon
as its pullbacks over the members of the open cover of the base change by the preimages of
the `U` are (`AlgebraicGeometry.Etale.isIso_baseChange_app_of_etale_cover`).
(blueprint: `lemma-weil-pbc-target-locality`) -/
theorem Etale.hasTorsionBaseChange_of_affineOpens {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ U : Y.affineOpens, Etale.HasTorsionBaseChange Λ (f ∣_ (U : Y.Opens))) :
    Etale.HasTorsionBaseChange Λ f :=
  sorry

end AlgebraicGeometry
