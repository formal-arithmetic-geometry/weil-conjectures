/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection

/-!
# Exchange and projection transformations on module objects

Let `Λ` be a commutative condensed ring, with coefficient ring objects `Λ_X = p_X^* Λ`. This
file constructs, on the unbounded derived categories `D(Mod_{Λ_X})` of module objects, the
exchange and projection transformations between the derived pullback `Lf^*`, the derived
pushforward `Rf_*`, the extension by zero `Dj_!` along an open immersion and the derived lower
shriek `Rf_!(c) = Dj_! ⋙ Rp_*` attached to a compactification `c = (j, p)`.

For a commutative square

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

* `ProEtale.CondensedRing.derivedPullbackSquareIso`: the comparison
  `c_□ : Lf'^* Lg^* ≅ Lg'^* Lf^*` of the two pullbacks, from the composition isomorphisms of the
  derived pullback;
* `ProEtale.CondensedRing.derivedLowerStarExchange`: the direct-image exchange
  `Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*`, the adjoint of `Lg'^* ε_f ∘ c_□`;
* `ProEtale.CondensedRing.derivedOpenImmersionLowerShriekExchange`: for `f = j`, `f' = j'` open
  immersions, the open-extension exchange `b' : Dj'_! Lg'^* ⟶ Lg^* Dj_!`, the adjoint of
  `c_□ ∘ Lg'^*(η_j)`. For a cartesian square it is an isomorphism
  (`ProEtale.CondensedRing.isIso_derivedOpenImmersionLowerShriekExchange`): this is base change
  for the extension by zero on module objects;
* `ProEtale.CondensedRing.derivedLowerShriekExchange`: for a cartesian square and a
  compactification `c = (j, p)` of `f`, the compact-support exchange
  `Ex_! : Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*` into the base-changed compactification `c'`: the
  direct-image exchange of the proper square followed by the inverse of `b'` for the open
  square.

For a morphism `f` and objects `K` over `X`, `L` over `Y`:

* `ProEtale.CondensedRing.derivedLowerStarProjection`: the projection map
  `P_f : Rf_* K ⊗ᴸ L ⟶ Rf_* (K ⊗ᴸ Lf^* L)`, the adjoint of `(ε_f ⊗ 1) ∘ m`, `m` the monoidal
  comparison of `Lf^*`;
* `ProEtale.CondensedRing.derivedLowerShriekProjection`: the projection map
  `PF_c : Rf_!(c) K ⊗ᴸ L ⟶ Rf_!(c) (K ⊗ᴸ Lf^* L)`, the composite of `P_p`, of the inverse of the
  open-extension projection isomorphism `σ_j` and of the composition isomorphism
  `Lj^* Lp^* ≅ Lf^*`.

The open-extension projection map `σ_j` itself is
`ProEtale.CondensedRing.openImmersionProjectionComparison`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {jS : A ⥤ B} {jU : B ⥤ A} {jS' : A' ⥤ B'} {jU' : B' ⥤ A'} {H : A ⥤ A'} {H' : B ⥤ B'}

/-- If the units of `jS ⊣ jU` and `jS' ⊣ jU'` are isomorphisms, then `jU'` of the exchange
morphism `exchangeLeft aj aj' θ` is an isomorphism: it is the composite of `jU' jS' H` of the
unit of `jS ⊣ jU`, of `jU' jS'` of `θ`, and of `jU'` of the counit of `jS' ⊣ jU'`, which is
inverse to the unit by the triangle identity. -/
lemma isIso_map_exchangeLeft_app (aj : jS ⊣ jU) (aj' : jS' ⊣ jU') (θ : jU ⋙ H ≅ H' ⋙ jU')
    [IsIso aj.unit] [IsIso aj'.unit] (K : A) :
    IsIso (jU'.map ((exchangeLeft aj aj' θ).app K)) := by
  have (Y : B') : IsIso (jU'.map (aj'.counit.app Y)) := by
    have : IsIso (aj'.unit.app (jU'.obj Y) ≫ jU'.map (aj'.counit.app Y)) := by
      rw [aj'.right_triangle_components Y]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (aj'.unit.app (jU'.obj Y)) _
  rw [exchangeLeft_app]
  simp only [Functor.map_comp]
  infer_instance

/-- **Invertibility of the exchange morphism on the essential image.** Let `jS` and `jS'` be
fully faithful left adjoints. If `H' (jS K)` lies in the essential image of `jS'`, then the
component at `K` of the exchange morphism `exchangeLeft aj aj' θ : H ⋙ jS' ⟶ jS ⋙ H'` is an
isomorphism: it is a morphism between objects of the essential image of the fully faithful
`jS'`, and its image under `jU'` is an isomorphism
(`CategoryTheory.Adjunction.isIso_map_exchangeLeft_app`). -/
lemma isIso_exchangeLeft_app_of_mem_essImage (aj : jS ⊣ jU) (aj' : jS' ⊣ jU')
    (θ : jU ⋙ H ≅ H' ⋙ jU') [jS.Full] [jS.Faithful] [jS'.Full] [jS'.Faithful] (K : A)
    (hK : jS'.essImage (H'.obj (jS.obj K))) :
    IsIso ((exchangeLeft aj aj' θ).app K) := by
  have := isIso_map_exchangeLeft_app aj aj' θ K
  have : IsIso (aj'.counit.app (jS'.obj (H.obj K))) :=
    aj'.isIso_counit_app_iff_mem_essImage.2 (jS'.obj_mem_essImage _)
  have : IsIso (aj'.counit.app (H'.obj (jS.obj K))) := aj'.isIso_counit_app_iff_mem_essImage.2 hK
  have hnat := aj'.counit.naturality ((exchangeLeft aj aj' θ).app K)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hnat
  have : IsIso (aj'.counit.app (jS'.obj (H.obj K)) ≫ (exchangeLeft aj aj' θ).app K) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_left (aj'.counit.app _) _

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### The pullback comparison and the direct-image exchange -/

section Star

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Blueprint `pur713-def-pullback-comparison-module`: Comparison of the two pullbacks, module
objects.

For a commutative square `g' ≫ f = f' ≫ g`, the natural isomorphism
`c_□ = μ_{f,g'}⁻¹ ∘ μ_{g,f'} : Lf'^* Lg^* ≅ Lg'^* Lf^*` of functors
`D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_{X'}})`, with `μ` the composition isomorphisms of the derived
pullback (`ProEtale.CondensedRing.leftDerivedUpperStarComp`) and `L(f' ≫ g)^* = L(g' ≫ f)^*`. -/
noncomputable def derivedPullbackSquareIso (sq : CommSq g' f' f g) :
    L((g)^*⟦Λ⟧) ⋙ L((f')^*⟦Λ⟧) ≅ L((f)^*⟦Λ⟧) ⋙ L((g')^*⟦Λ⟧) :=
  (leftDerivedUpperStarComp Λ f' g).symm ≪≫ eqToIso (by rw [sq.w]) ≪≫
    leftDerivedUpperStarComp Λ g' f

/-- Blueprint `pur713-def-star-exchange-module`: Direct-image exchange, module objects.

For a commutative square `g' ≫ f = f' ≫ g`, the direct-image exchange
`Ex_{*,□} : Lg^* Rf_* ⟶ Rf'_* Lg'^*` of functors `D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_{Y'}})`: its
component at `K` is the adjoint, under `Lf'^* ⊣ Rf'_*`, of
`Lf'^* Lg^* Rf_* K ⟶ Lg'^* Lf^* Rf_* K ⟶ Lg'^* K`, the pullback comparison `c_□`
(`ProEtale.CondensedRing.derivedPullbackSquareIso`) followed by `Lg'^*` of the counit of
`Lf^* ⊣ Rf_*`. No invertibility is asserted. -/
noncomputable def derivedLowerStarExchange (sq : CommSq g' f' f g) :
    R((f)_*⟦Λ⟧) ⋙ L((g)^*⟦Λ⟧) ⟶ L((g')^*⟦Λ⟧) ⋙ R((f')_*⟦Λ⟧) :=
  Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f') (derivedPullbackSquareIso Λ sq)

end Star

/-! ### The open-extension exchange -/

section Open

variable {X Z X' Z' : Scheme.{u}} {j : X ⟶ Z} {g : Z' ⟶ Z} {j' : X' ⟶ Z'} {g' : X' ⟶ X}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- Blueprint `pur713-def-open-exchange-module`: Open-extension base-change map, module
objects.

For a commutative square `g' ≫ j = j' ≫ g` with `j`, `j'` open immersions, the open-extension
exchange `b' : Dj'_! Lg'^* ⟶ Lg^* Dj_!` of functors `D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_{Z'}})`: its
component at `K` is the adjoint, under `Dj'_! ⊣ Lj'^*`, of
`Lg'^* K ⟶ Lg'^* Lj^* Dj_! K ≅ Lj'^* Lg^* Dj_! K`, `Lg'^*` of the unit of `Dj_! ⊣ Lj^*`
followed by the pullback comparison of the square
(`ProEtale.CondensedRing.derivedPullbackSquareIso`). The adjunctions are
`ProEtale.CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction`, whose
right adjoint is the derived pullback `Lj^*`, canonically the levelwise `D(j^*)`. -/
noncomputable def derivedOpenImmersionLowerShriekExchange (sq : CommSq g' j' j g) :
    L((g')^*⟦Λ⟧) ⋙ D((j')_!open⟦Λ⟧) ⟶ D((j)_!open⟦Λ⟧) ⋙ L((g)^*⟦Λ⟧) :=
  Adjunction.exchangeLeft (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j)
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j')
    (derivedPullbackSquareIso Λ sq.flip)

/-- The extension by zero `Dj_!` on module objects along an open immersion is fully faithful,
the unit of the levelwise adjunction `Dj_! ⊣ D(j^*)` being an isomorphism. -/
lemma full_faithful_derivedOpenImmersionLowerShriek (j : X ⟶ Z) [IsOpenImmersion j] :
    D((j)_!open⟦Λ⟧).Full ∧ D((j)_!open⟦Λ⟧).Faithful := by
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  exact ⟨(derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).fullyFaithfulLOfIsIsoUnit.full,
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).fullyFaithfulLOfIsIsoUnit.faithful⟩

omit [IsOpenImmersion j] in
/-- For a cartesian square `g' ≫ j = j' ≫ g` with `j'` an open immersion, the pullback along
`g` of an extension by zero along `j` lies in the essential image of the extension by zero
along `j'`: on underlying sheaves this is base change for the pro-étale extension by zero
(`AlgebraicGeometry.ProEtale.openImmersionLowerShriekBaseChangeIso`), and the extension of
scalars along the isomorphism `α_g` does not change the underlying sheaf. -/
lemma upperStar_obj_openImmersionLowerShriek_mem_essImage [IsOpenImmersion j]
    (sq : IsPullback g' j' j g)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (j')_!open⟦Λ⟧.essImage ((g)^*⟦Λ⟧.obj ((j)_!open⟦Λ⟧.obj M)) :=
  mem_essImage_openImmersionLowerShriek_of_mem_essImage Λ j' _
    ⟨(g')^*[Ab.{u + 1}].obj M.X,
      ⟨(ProEtale.openImmersionLowerShriekBaseChangeIso Ab.{u + 1} sq).app M.X ≪≫
        (Mod.forget _).mapIso ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ g)).app
          (((g)^*[Ab.{u + 1}].mapMod _).obj ((j)_!open⟦Λ⟧.obj M))).symm⟩⟩

/-- For a cartesian square `g' ≫ j = j' ≫ g` of schemes with `j`, `j'` open immersions,
`Lg^* Dj_! K` lies in the essential image of `Dj'_!`: representing `K` by a complex `K₀`, it is
the class of the complex `g^* j_! K₀`, whose terms lie in the essential image of `j'_!`
(`ProEtale.CondensedRing.upperStar_obj_openImmersionLowerShriek_mem_essImage`). -/
lemma leftDerivedUpperStar_obj_derivedOpenImmersionLowerShriek_mem_essImage
    (sq : IsPullback g' j' j g)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    D((j')_!open⟦Λ⟧).essImage (L((g)^*⟦Λ⟧).obj (D((j)_!open⟦Λ⟧).obj K)) := by
  let K₀ := DerivedCategory.Q.objPreimage K
  let C := ((j)_!open⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj K₀
  refine Functor.essImage.ofIso ?_
    (Q_obj_mem_essImage_mapDerivedCategory_openImmersionLowerShriek Λ j'
      (((g)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj C)
      (fun n ↦ upperStar_obj_openImmersionLowerShriek_mem_essImage Λ sq (K₀.X n)))
  exact ((g)^*⟦Λ⟧.mapDerivedCategoryFactors.app C).symm ≪≫
    D((g)^*⟦Λ⟧).mapIso (((j)_!open⟦Λ⟧.mapDerivedCategoryFactors.app K₀).symm ≪≫
      D((j)_!open⟦Λ⟧).mapIso (DerivedCategory.Q.objObjPreimageIso K)) ≪≫
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ g).app _).symm

/-- **Base change for the extension by zero on module objects.** For a cartesian square
`g' ≫ j = j' ≫ g` of schemes with `j`, `j'` open immersions, the open-extension exchange
`b' : Dj'_! Lg'^* ⟶ Lg^* Dj_!` (`ProEtale.CondensedRing.derivedOpenImmersionLowerShriekExchange`)
is an isomorphism.

Both sides lie in the essential image of the fully faithful `Dj'_!`
(`ProEtale.CondensedRing.leftDerivedUpperStar_obj_derivedOpenImmersionLowerShriek_mem_essImage`),
so it suffices that `Lj'^* b'` is an isomorphism; and `Lj'^* b'` is the composite of `Lj'^*` of
the invertible unit of `Dj_! ⊣ Lj^*`, of the pullback comparison and of `Lj'^*` of the counit of
`Dj'_! ⊣ Lj'^*`, which is inverse to the invertible unit. -/
theorem isIso_derivedOpenImmersionLowerShriekExchange (sq : IsPullback g' j' j g) :
    IsIso (derivedOpenImmersionLowerShriekExchange Λ sq.toCommSq) := by
  obtain ⟨_, _⟩ := full_faithful_derivedOpenImmersionLowerShriek Λ j
  obtain ⟨_, _⟩ := full_faithful_derivedOpenImmersionLowerShriek Λ j'
  have e : derivedOpenImmersionLowerShriekExchange Λ sq.toCommSq =
      Adjunction.exchangeLeft (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j)
        (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j')
        (derivedPullbackSquareIso Λ sq.toCommSq.flip) := by
    unfold derivedOpenImmersionLowerShriekExchange
    rfl
  rw [e]
  have (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
      IsIso ((Adjunction.exchangeLeft
        (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j)
        (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j')
        (derivedPullbackSquareIso Λ sq.toCommSq.flip)).app K) :=
    Adjunction.isIso_exchangeLeft_app_of_mem_essImage _ _ _ K
      (leftDerivedUpperStar_obj_derivedOpenImmersionLowerShriek_mem_essImage Λ sq K)
  exact NatIso.isIso_of_isIso_app _

/-- The base change isomorphism `Dj_! ⋙ Lg^* ≅ Lg'^* ⋙ Dj'_!` for the extension by zero on module
objects along a cartesian square `g' ≫ j = j' ≫ g` with `j`, `j'` open immersions: the inverse of
the open-extension exchange `b'`
(`ProEtale.CondensedRing.isIso_derivedOpenImmersionLowerShriekExchange`). -/
noncomputable def derivedOpenImmersionLowerShriekBaseChangeIso (sq : IsPullback g' j' j g) :
    D((j)_!open⟦Λ⟧) ⋙ L((g)^*⟦Λ⟧) ≅ L((g')^*⟦Λ⟧) ⋙ D((j')_!open⟦Λ⟧) :=
  have := isIso_derivedOpenImmersionLowerShriekExchange Λ sq
  (asIso (derivedOpenImmersionLowerShriekExchange Λ sq.toCommSq)).symm

end Open

/-! ### The compact-support exchange -/

section Shriek

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Blueprint `pur713-def-shriek-exchange-module`: Compact-support exchange, module objects.

For a cartesian square `g' ≫ f = f' ≫ g`, a compactification `c = (j, p)` of `f` and its base
change `c' = (j', p')` along `g` (`Compactification.ofIsPullback`), a compactification of `f'`,
the compact-support exchange `Ex_{!,□} : Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*` of functors
`D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_{Y'}})`, between the derived lower shrieks
`Rf_!(c) = Rp_* ∘ Dj_!` of `ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification`.
Its component at `K` is the composite
```
Lg^* Rp_* Dj_! K ⟶ Rp'_* Lḡ^* Dj_! K ⟶ Rp'_* Dj'_! Lg'^* K
```
of the direct-image exchange `Ex_{*,□_p}` of the proper square
(`ProEtale.CondensedRing.derivedLowerStarExchange`) and of `Rp'_*` of the inverse `b` of the
open-extension exchange of the open square
(`ProEtale.CondensedRing.derivedOpenImmersionLowerShriekBaseChangeIso`), where
`ḡ : Z ×_Y Y' ⟶ Z` is the projection. No completed pullback is inserted. For `c` the chosen
compactification of `f` this is the exchange `Lg^* Rf_! ⟶ R_{c'} Lg'^*` of the blueprint. -/
noncomputable def derivedLowerShriekExchange (c : Compactification f) (sq : IsPullback g' f' f g) :
    Rf_!(c)⟦Λ⟧ ⋙ L((g)^*⟦Λ⟧) ⟶ L((g')^*⟦Λ⟧) ⋙ Rf_!(c.ofIsPullback sq)⟦Λ⟧ :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D((c.i)_!open⟦Λ⟧)
      (derivedLowerStarExchange Λ (c.isPullback_g_ofIsPullback sq).flip.toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (derivedOpenImmersionLowerShriekBaseChangeIso Λ (c.isPullback_i_ofIsPullback sq)).hom
      R(((c.ofIsPullback sq).g)_*⟦Λ⟧) ≫
    (Functor.associator _ _ _).hom

end Shriek

/-! ### The projection transformations -/

section Projection

variable {X Y : Scheme.{u}}

/-- Blueprint `pur713-def-star-projection-module`: Direct-image projection transformation, module
objects.

For `f : X ⟶ Y`, the projection map `P_{f,K,L} : Rf_* K ⊗ᴸ L ⟶ Rf_* (K ⊗ᴸ Lf^* L)` in
`D(Mod_{Λ_Y})`, natural in `K ∈ D(Mod_{Λ_X})` and `L ∈ D(Mod_{Λ_Y})`: the adjoint, under
`Lf^* ⊣ Rf_*`, of
```
Lf^* (Rf_* K ⊗ᴸ L) ⟶ Lf^* Rf_* K ⊗ᴸ Lf^* L ⟶ K ⊗ᴸ Lf^* L,
```
the monoidal comparison of `Lf^*` (`ProEtale.CondensedRing.leftDerivedUpperStarTensor`) followed
by the counit of `Lf^* ⊣ Rf_*` tensored with the identity
(`CategoryTheory.Adjunction.rightAdjointProjectionMap`). -/
noncomputable def derivedLowerStarProjection (f : X ⟶ Y) :
    R((f)_*⟦Λ⟧) ⋙ curriedTensor _ ⟶
      (Functor.postcompose₂.obj R((f)_*⟦Λ⟧)).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L((f)^*⟦Λ⟧)).obj (curriedTensor _)) :=
  (derivedUpperStarLowerStarAdjunction Λ f).rightAdjointProjectionMap
    (leftDerivedUpperStarTensor Λ f)

/-- Blueprint `pur713-def-shriek-projection-module`: Compact-support projection transformation,
module objects.

For a compactification `c = (j, p)` of `f : X ⟶ Y`, `K ∈ D(Mod_{Λ_X})` and
`L ∈ D(Mod_{Λ_Y})`, the projection map
`PF_{c,K,L} : Rf_!(c) K ⊗ᴸ L ⟶ Rf_!(c) (K ⊗ᴸ Lf^* L)` in `D(Mod_{Λ_Y})`, the composite
```
Rp_* Dj_! K ⊗ᴸ L ⟶ Rp_* (Dj_! K ⊗ᴸ Lp^* L) ⟶ Rp_* Dj_! (K ⊗ᴸ Lj^* Lp^* L)
  ⟶ Rp_* Dj_! (K ⊗ᴸ Lf^* L)
```
of the direct-image projection map `P_p` (`ProEtale.CondensedRing.derivedLowerStarProjection`),
of `Rp_*` of the inverse of the open-extension projection isomorphism `σ_j`
(`ProEtale.CondensedRing.openImmersionProjectionComparison`), and of the composition
isomorphism `Lj^* Lp^* ≅ L(j ≫ p)^* = Lf^*` (`ProEtale.CondensedRing.leftDerivedUpperStarComp`).
For `c` the chosen compactification of `f` this is `PF_f`. -/
noncomputable def derivedLowerShriekProjection {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (Rf_!(c)⟦Λ⟧).obj K ⊗ L ⟶ (Rf_!(c)⟦Λ⟧).obj (K ⊗ L((f)^*⟦Λ⟧).obj L) :=
  ((derivedLowerStarProjection Λ c.g).app (D((c.i)_!open⟦Λ⟧).obj K)).app L ≫
    R((c.g)_*⟦Λ⟧).map (inv (((openImmersionProjectionComparison Λ c.i).app K).app
      (L((c.g)^*⟦Λ⟧).obj L))) ≫
    (Rf_!(c)⟦Λ⟧).map (K ◁ ((leftDerivedUpperStarComp Λ c.i c.g).inv.app L ≫
      eqToHom (by rw [← c.comm])))

end Projection

end AlgebraicGeometry.ProEtale.CondensedRing
