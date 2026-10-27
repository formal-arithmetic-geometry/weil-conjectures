# CategoryTheory.ringedSite_cech_refinement_square_rest

## Reason

The old auxiliary theorem allowed an arbitrary cochain map gamma, omitting the tuple formula
that its DAG statement already requires. On the one-object identity site, with singleton
identity covers, constant integer coefficients and h the identity, gamma = 0 contradicts
the degree-zero square: normalized edges and the roof are identities. The Stacks 01FD
proof defines gamma by the tuple formula before asserting the square. Restore that missing
hypothesis. The parent theorem already constructs gamma with exactly this property.
No target signature or definition changes.

## Old

```lean
theorem ringedSite_cech_refinement_square_rest
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (u : C ⥤ D) [PreservesFiniteLimits u]
    (hcover : ∀ (Y : C) (S : Presieve Y), S ∈ J Y → S.map u ∈ K (u.obj Y))
    [u.IsContinuous J.toGrothendieck K.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    (R : Sheaf J.toGrothendieck RingCat.{u}) (R' : Sheaf K.toGrothendieck RingCat.{u})
    (ρ : R ⟶ (u.sheafPushforwardContinuous RingCat.{u}
      J.toGrothendieck K.toGrothendieck).obj R')
    [EnoughInjectives (ringedSiteModules.{u} R)]
    [EnoughInjectives (ringedSiteModules.{u} R')]
    (M : ringedSiteModules.{u} R) (N : ringedSiteModules.{u} R')
    (h : M ⟶ (SheafOfModules.pushforward.{u} ρ).obj N)
    {X : C} (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    {I₀ I₁ : Type u} [Finite I₀] [Finite I₁]
    (U : I₀ → C) (v : ∀ i, U i ⟶ X)
    (V : I₁ → D) (w : ∀ j, V j ⟶ u.obj X)
    (hU : Presieve.ofArrows U v ∈ J X)
    (hV : Presieve.ofArrows V w ∈ K (u.obj X))
    (S : SiteCechComplex U v) (T : SiteCechComplex V w)
    (r : I₁ → I₀) (a : ∀ j, V j ⟶ u.obj (U (r j)))
    (aTuple : ∀ (p : ℕ) (j : Fin (p + 1) → I₁),
      T.W p j ⟶ u.obj (S.W p (r ∘ j)))
    (haTuple : ∀ (p : ℕ) (j : Fin (p + 1) → I₁) (k : Fin (p + 1)),
      aTuple p j ≫ u.map (S.pr p (r ∘ j) k) = T.pr p j k ≫ a (j k))
    (γ : S.complex M.val.presheaf ⟶ T.complex N.val.presheaf) :
      ∀ q : ℕ,
        ∃! eM : (S.cohomologyFunctor q).obj M.val.presheaf ⟶ (((SheafOfModules.forget R ⋙
          PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
          X)).rightDerived q).obj M,
          S.IsNormalizedEdge (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) q eM ∧
          ∃! eN : (T.cohomologyFunctor q).obj N.val.presheaf ⟶ (((SheafOfModules.forget R' ⋙
            PresheafOfModules.toPresheaf R'.obj) ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj
            X))).rightDerived q).obj N,
            T.IsNormalizedEdge (SheafOfModules.forget R' ⋙ PresheafOfModules.toPresheaf R'.obj) q eN
              ∧
            ∃! hH : (((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation
              Cᵒᵖ AddCommGrpCat.{u}).obj (op X)).rightDerived q).obj M ⟶ (((SheafOfModules.forget R'
              ⋙ PresheafOfModules.toPresheaf R'.obj) ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op
              (u.obj X))).rightDerived q).obj N,
              (∀ (IM : InjectiveResolution M) (IN : InjectiveResolution N),
                ∃ (L : CochainComplex (ringedSiteModules.{u} R) ℕ)
                  (lam : ((SheafOfModules.pushforward.{u} ρ).mapHomologicalComplex (ComplexShape.up
                    ℕ)).obj IN.cocomplex ⟶ L)
                  (b : IM.cocomplex ⟶ L),
                  (∀ n : ℕ, Injective (L.X n)) ∧
                  (∀ n : ℕ, Mono (lam.f n)) ∧ QuasiIso lam ∧
                  IM.ι.f 0 ≫ b.f 0 = h ≫ (SheafOfModules.pushforward.{u} ρ).map (IN.ι.f 0) ≫ lam.f
                    0) ∧
              (∀ (IM : InjectiveResolution M) (IN : InjectiveResolution N)
                (L : CochainComplex (ringedSiteModules.{u} R) ℕ)
                (lam : ((SheafOfModules.pushforward.{u} ρ).mapHomologicalComplex (ComplexShape.up
                  ℕ)).obj IN.cocomplex ⟶ L)
                (b : IM.cocomplex ⟶ L),
                (∀ n : ℕ, Injective (L.X n)) →
                (∀ n : ℕ, Mono (lam.f n)) → QuasiIso lam →
                IM.ι.f 0 ≫ b.f 0 = h ≫ (SheafOfModules.pushforward.{u} ρ).map (IN.ι.f 0) ≫ lam.f 0 →
                IsIso (HomologicalComplex.homologyMap ((((SheafOfModules.forget R ⋙
                  PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
                  X)).mapHomologicalComplex (ComplexShape.up ℕ)).map lam) q) ∧
                hH ≫ (IN.isoRightDerivedObj ((SheafOfModules.forget R' ⋙
                  PresheafOfModules.toPresheaf R'.obj) ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op
                  (u.obj X))) q).hom ≫
                  HomologicalComplex.homologyMap ((((SheafOfModules.forget R ⋙
                    PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
                    X)).mapHomologicalComplex (ComplexShape.up ℕ)).map lam) q =
                (IM.isoRightDerivedObj ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf
                  R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)) q).hom ≫
                  HomologicalComplex.homologyMap ((((SheafOfModules.forget R ⋙
                    PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
                    X)).mapHomologicalComplex (ComplexShape.up ℕ)).map b) q) ∧
              eM ≫ hH = HomologicalComplex.homologyMap γ q ≫ eN
```

## New

```lean
theorem ringedSite_cech_refinement_square_rest
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (u : C ⥤ D) [PreservesFiniteLimits u]
    (hcover : ∀ (Y : C) (S : Presieve Y), S ∈ J Y → S.map u ∈ K (u.obj Y))
    [u.IsContinuous J.toGrothendieck K.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    (R : Sheaf J.toGrothendieck RingCat.{u}) (R' : Sheaf K.toGrothendieck RingCat.{u})
    (ρ : R ⟶ (u.sheafPushforwardContinuous RingCat.{u}
      J.toGrothendieck K.toGrothendieck).obj R')
    [EnoughInjectives (ringedSiteModules.{u} R)]
    [EnoughInjectives (ringedSiteModules.{u} R')]
    (M : ringedSiteModules.{u} R) (N : ringedSiteModules.{u} R')
    (h : M ⟶ (SheafOfModules.pushforward.{u} ρ).obj N)
    {X : C} (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    {I₀ I₁ : Type u} [Finite I₀] [Finite I₁]
    (U : I₀ → C) (v : ∀ i, U i ⟶ X)
    (V : I₁ → D) (w : ∀ j, V j ⟶ u.obj X)
    (hU : Presieve.ofArrows U v ∈ J X)
    (hV : Presieve.ofArrows V w ∈ K (u.obj X))
    (S : SiteCechComplex U v) (T : SiteCechComplex V w)
    (r : I₁ → I₀) (a : ∀ j, V j ⟶ u.obj (U (r j)))
    (aTuple : ∀ (p : ℕ) (j : Fin (p + 1) → I₁),
      T.W p j ⟶ u.obj (S.W p (r ∘ j)))
    (haTuple : ∀ (p : ℕ) (j : Fin (p + 1) → I₁) (k : Fin (p + 1)),
      aTuple p j ≫ u.map (S.pr p (r ∘ j) k) = T.pr p j k ≫ a (j k))
    (γ : S.complex M.val.presheaf ⟶ T.complex N.val.presheaf)
    (hγ : ∀ (p : ℕ) (s : S.cochains M.val.presheaf p) (j : Fin (p + 1) → I₁),
      (γ.f p s) j = N.val.presheaf.map (aTuple p j).op
        ((h.val.app (op (S.W p (r ∘ j)))) (s (r ∘ j)))) :
      ∀ q : ℕ,
        ∃! eM : (S.cohomologyFunctor q).obj M.val.presheaf ⟶ (((SheafOfModules.forget R ⋙
          PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
          X)).rightDerived q).obj M,
          S.IsNormalizedEdge (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) q eM ∧
          ∃! eN : (T.cohomologyFunctor q).obj N.val.presheaf ⟶ (((SheafOfModules.forget R' ⋙
            PresheafOfModules.toPresheaf R'.obj) ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj
            X))).rightDerived q).obj N,
            T.IsNormalizedEdge (SheafOfModules.forget R' ⋙ PresheafOfModules.toPresheaf R'.obj) q eN
              ∧
            ∃! hH : (((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation
              Cᵒᵖ AddCommGrpCat.{u}).obj (op X)).rightDerived q).obj M ⟶ (((SheafOfModules.forget R'
              ⋙ PresheafOfModules.toPresheaf R'.obj) ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op
              (u.obj X))).rightDerived q).obj N,
              (∀ (IM : InjectiveResolution M) (IN : InjectiveResolution N),
                ∃ (L : CochainComplex (ringedSiteModules.{u} R) ℕ)
                  (lam : ((SheafOfModules.pushforward.{u} ρ).mapHomologicalComplex (ComplexShape.up
                    ℕ)).obj IN.cocomplex ⟶ L)
                  (b : IM.cocomplex ⟶ L),
                  (∀ n : ℕ, Injective (L.X n)) ∧
                  (∀ n : ℕ, Mono (lam.f n)) ∧ QuasiIso lam ∧
                  IM.ι.f 0 ≫ b.f 0 = h ≫ (SheafOfModules.pushforward.{u} ρ).map (IN.ι.f 0) ≫ lam.f
                    0) ∧
              (∀ (IM : InjectiveResolution M) (IN : InjectiveResolution N)
                (L : CochainComplex (ringedSiteModules.{u} R) ℕ)
                (lam : ((SheafOfModules.pushforward.{u} ρ).mapHomologicalComplex (ComplexShape.up
                  ℕ)).obj IN.cocomplex ⟶ L)
                (b : IM.cocomplex ⟶ L),
                (∀ n : ℕ, Injective (L.X n)) →
                (∀ n : ℕ, Mono (lam.f n)) → QuasiIso lam →
                IM.ι.f 0 ≫ b.f 0 = h ≫ (SheafOfModules.pushforward.{u} ρ).map (IN.ι.f 0) ≫ lam.f 0 →
                IsIso (HomologicalComplex.homologyMap ((((SheafOfModules.forget R ⋙
                  PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
                  X)).mapHomologicalComplex (ComplexShape.up ℕ)).map lam) q) ∧
                hH ≫ (IN.isoRightDerivedObj ((SheafOfModules.forget R' ⋙
                  PresheafOfModules.toPresheaf R'.obj) ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op
                  (u.obj X))) q).hom ≫
                  HomologicalComplex.homologyMap ((((SheafOfModules.forget R ⋙
                    PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
                    X)).mapHomologicalComplex (ComplexShape.up ℕ)).map lam) q =
                (IM.isoRightDerivedObj ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf
                  R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)) q).hom ≫
                  HomologicalComplex.homologyMap ((((SheafOfModules.forget R ⋙
                    PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
                    X)).mapHomologicalComplex (ComplexShape.up ℕ)).map b) q) ∧
              eM ≫ hH = HomologicalComplex.homologyMap γ q ≫ eN
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.RingedSiteCechRefinementSquare | W2 | Sole direct declaration user. Pass the already proved tuple formula hγ to the auxiliary theorem; parent and abelian theorem signatures are unchanged. |

`tools/downstream.py Sheaf.CategoryTheory.RingedSiteCechRefinementSquare --uses
ringedSite_cech_refinement_square_rest` reports exactly this one declaration user.
There are 1938 transitive module importers. They all retain the same parent and abelian
interfaces; none uses the auxiliary declaration (confirmed by searching both Lean roots).
The auxiliary DAG statement already fixes gamma by the tuple formula; its wording needs
no correction. No other node lists this auxiliary in stmt_deps or proof_deps on the base.
The parent node's route now records the actual application explicitly.

## Status

landed 20261025T101719-L-3727611 2026-10-25 (merge of deliver/W2/Sheaf.CategoryTheory.RingedSiteCechRefinementSquare)
