/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PuncturedRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionCoproduct
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare

/-!
# Restriction through the blow-up of a strictly local surface

This file assembles the proof of the blowup restriction vanishing (blueprint
`sk-lem-tf-blowup-restriction`). Abstractly: let `T'` be a scheme (in the application `T - D`),
`i' : U' ⟶ T'` an open immersion (`T - (D ∪ H) ⟶ T - D`) and `E` a complex on `U'` with finite
`ℓ`-group monodromy. Suppose given a transverse boundary configuration `(Z, X, Y)` (in the
application, a chart of the blow-up of `T` at `t` minus the strict transform of `D`) and a
morphism `φ : Z - Y ⟶ T'` with `φ⁻¹(U') = Z - (X ∪ Y)` (in the application the blow-up map,
`det-tf-blowup-configuration` (2), (3)). Let `ψ : W ⟶ T'` (the punctured curve `B - t`) be a
finite disjoint union of maps `W_j ⟶ Z - Y ⟶ T'` each of which factors through a strictly local
scheme `S_j ⟶ Z` whose closed point lies on `Y` (the strictly local branches of the strict
transform of `B`, `det-tf-blowup-strict-transform`). Then the restriction map
`RΓ(T', i'_! E) ⟶ RΓ(W, ψ^* i'_! E)` is zero: it is the tuple of the restrictions to the `W_j`
(`AlgebraicGeometry.Etale.eq_zero_of_globalSectionsRestriction_of_isColimit`), and each of those
factors through the restriction `RΓ(Z - Y, i_! φ^* E) ⟶ RΓ(W_j, -)`, which vanishes by the
punctured restriction lemma (`sk-lem-tf-punctured-restriction`,
`AlgebraicGeometry.Etale.globalSectionsRestriction_eq_zero_of_strictlyLocal`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The pullback of a complex with finite `ℓ`-group monodromy has finite `ℓ`-group monodromy. -/
lemma HasFiniteEllMonodromy.upperStar {ℓ : ℕ} {U V : Scheme.{u}} (f : V ⟶ U)
    {E : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hE : HasFiniteEllMonodromy ℓ E) :
    HasFiniteEllMonodromy ℓ (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E) :=
  sorry

/-- Base change for the derived extension by zero along a cartesian square of schemes
`g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions: `g''^* j_! E ≅ j'_! g'^* E`. -/
noncomputable def derivedOpenImmersionLowerShriekBaseChangeIso {U' U Z' Z : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z} [IsOpenImmersion j]
    [IsOpenImmersion j'] (hsq : IsPullback g' j' j g'')
    (E : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((g'')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj
        (((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E) ≅
      ((j')_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj
        (((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E) :=
  have := isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) hsq
  ((Functor.mapDerivedCategoryCompIso _ _).app E).symm ≪≫
    (Functor.mapDerivedCategoryNatIso
      (asIso (openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ)
        hsq.toCommSq))).symm.app E ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).app E


variable {k : Type u} [Field k] [IsAlgClosed k] {ℓ : ℕ} [Fact ℓ.Prime] [Finite Λ]
  {Z : Over (Spec (.of k))} {X Y : Scheme.{u}} {iX : X ⟶ Z.left} {iY : Y ⟶ Z.left}
  {UY UXY : Z.left.Opens}

/-- **Restriction through a transverse configuration vanishes** (assembly of the proof of
`sk-lem-tf-blowup-restriction`). Let `(Z, X, Y, z)` be a transverse boundary configuration with
`Y` connected, `i' : U' ⟶ T'` an open immersion, `E` a complex with finite `ℓ`-group monodromy on
`U'`, and `φ : Z - Y ⟶ T'` with `φ⁻¹(U') = Z - (X ∪ Y)` (a cartesian square). Let
`ψ : W ⟶ T'` with `W` the finite disjoint union of the `W_j`, such that each `W_j ⟶ W ⟶ T'`
factors as `W_j ⟶ Z - Y ⟶ T'` and `W_j ⟶ Z - Y ⟶ Z` factors through a strictly local scheme
`Spec R_j ⟶ Z` mapping its closed point to a closed point of `Y`. Then the restriction map
`RΓ(T', i'_! E) ⟶ RΓ(W, ψ^* i'_! E)` is zero. -/
theorem globalSectionsRestriction_eq_zero_of_transverse (hℓ : (ℓ : k) ≠ 0)
    (hΛ : IsNilpotent (ℓ : Λ)) (hZ : IsEtaleLimitOfSmoothSurfaces Z) (hX : IsRegularDivisor iX)
    (hY : IsRegularDivisor iY) (z : Z.left) (hz : MeetTransverselyAt iX iY z)
    (hUY : (UY : Set Z.left) = (Set.range iY)ᶜ)
    (hUXY : (UXY : Set Z.left) = (Set.range iX ∪ Set.range iY)ᶜ) (hle : UXY ≤ UY)
    [ConnectedSpace Y] {T' U' : Scheme.{u}} (i' : U' ⟶ T') [IsOpenImmersion i']
    (E : DerivedCategory (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : HasFiniteEllMonodromy ℓ E) (φ : UY.toScheme ⟶ T') (φU : UXY.toScheme ⟶ U')
    (hφ : IsPullback φU (Z.left.homOfLE hle) i' φ) {W : Scheme.{u}} (ψ : W ⟶ T')
    {J : Type} [Finite J] {Wj : J → Scheme.{u}} (w : ∀ j, Wj j ⟶ W)
    (hW : IsColimit (Cofan.mk W w)) (R : J → Type u) [∀ j, CommRing (R j)]
    [∀ j, IsStrictlyHenselianLocalRing (R j)] (c : ∀ j, Spec (.of (R j)) ⟶ Z.left) (s : J → Y)
    (hs : ∀ j, IsClosed ({s j} : Set Y))
    (hcs : ∀ j, c j (IsLocalRing.closedPoint (R j)) = iY (s j))
    (ι : ∀ j, Wj j ⟶ UY.toScheme) (jW : ∀ j, Wj j ⟶ Spec (.of (R j)))
    (hι : ∀ j, ι j ≫ UY.ι = jW j ≫ c j) (hψ : ∀ j, w j ≫ ψ = ι j ≫ φ) :
    globalSectionsRestriction ψ (((i')_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E) =
      0 := by
  let F := ((i')_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E
  let EZ := ((φU)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E
  have hZero : ∀ j, globalSectionsRestriction (ι j)
      (((Z.left.homOfLE hle)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj EZ) = 0 :=
    fun j ↦ globalSectionsRestriction_eq_zero_of_strictlyLocal hℓ hΛ hZ hX hY z hz hUY hUXY hle
      EZ (hE.upperStar φU) (c j) (s j) (hs j) (hcs j) (ι j) (jW j) (hι j)
  have hφj : ∀ j, globalSectionsRestriction (ι j)
      (((φ)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj F) = 0 := by
    intro j
    let e := derivedOpenImmersionLowerShriekBaseChangeIso hφ E
    have hn := globalSectionsRestriction_naturality (ι j) e.hom
    rw [hZero j, comp_zero] at hn
    rw [← cancel_mono ((rightDerivedGlobalSections _ _).map
      (((ι j)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.map e.hom)), zero_comp, ← hn]
  refine eq_zero_of_globalSectionsRestriction_of_isColimit w hW _ _ fun j ↦ ?_
  have hc := globalSectionsRestriction_comp ψ (w j) F
  have h0 : globalSectionsRestriction (w j ≫ ψ) F = 0 := by
    rw [hψ j]
    exact globalSectionsRestriction_comp_eq_zero_of_right _ _ _ (hφj j)
  rw [h0, zero_comp] at hc
  exact hc.symm

end AlgebraicGeometry.Etale
