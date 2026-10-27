# ordinaryFiniteP1Decomposition

## Reason

Avoid expensive kernel conversion between inferred projective-space endpoints and the
`ProjectiveLine` abbreviation. Supply those endpoints explicitly. The twisted map also
supplies its shifted ordinary finite-line argument explicitly. Every change is
definitionally equal to the original; hypotheses, mathematical maps, visibility,
attributes and public imports are preserved. No definition data comes from a new
unproved existence statement. These are performance repairs needed for the comparison
proof to compile within the existing limit.

## Old

```lean
theorem ordinaryFiniteP1Decomposition (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    ∃ c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
        (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧,
      ordinaryFiniteP1ChernSpec A N hA S
        ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
            hS.map (ProjectiveLine S ↘ S).appTop.hom) c ∧
      IsIso (p1DecompositionMap A N hN hA S hS c) ∧
      ∀ (S' : Scheme.{u}) (g : S' ⟶ S),
        ∃ c' : ordinaryFiniteUnit A (ProjectiveLine S') ⟶
            (ordinaryFiniteLine A N hA (ProjectiveLine S'))⟦(2 : ℤ)⟧,
          ordinaryFiniteP1ChernSpec A N hA S'
            ((map_natCast (ProjectiveLine S' ↘ S').appTop.hom N) ▸
              (((map_natCast g.appTop.hom N) ▸ hS.map g.appTop.hom).map
                (ProjectiveLine S' ↘ S').appTop.hom)) c' ∧
          IsIso (p1DecompositionMap A N hN hA S'
            ((map_natCast g.appTop.hom N) ▸ hS.map g.appTop.hom) c') ∧
          (ordinaryFinitePullback A g).map (p1DecompositionMap A N hN hA S hS c) ≫
              ordinaryFiniteP1Exchange A g (ordinaryFiniteUnit A (ProjectiveLine S)) ≫
              (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
                (ordinaryFiniteUnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom =
            p1DecompositionSourceMap A N hN hA g hS ≫
              p1DecompositionMap A N hN hA S'
                ((map_natCast g.appTop.hom N) ▸ hS.map g.appTop.hom) c' := by
  obtain ⟨t, d, _⟩ := exists_ordinaryFiniteP1Adjunction N hN A hA
  let c := (d S hS).chern
  have hc := (d S hS).chern_spec
  have hi : IsIso (p1DecompositionMap A N hN hA S hS c) := by
    apply isIso_p1DecompositionMap_of_twisted A N hN hA t S hS
    rw [← (d S hS).decomposition_hom]
    infer_instance
  refine ⟨c, hc, hi, ?_⟩
  intro S' g
  have : (ordinaryFinitePullback A g).Additive :=
    additive_leftDerivedUpperStar (ModuleCat.{u + 1} A) g
  let hS' : IsUnit (N : Γ(S', ⊤)) :=
    (map_natCast g.appTop.hom N) ▸ hS.map g.appTop.hom
  obtain ⟨c', hc', hu, hh⟩ :=
    ordinaryFiniteP1_components_baseChange A N hN hA g hS hS' c hc
  have he :
      (ordinaryFinitePullback A g).map (p1DecompositionMap A N hN hA S hS c) ≫
        ordinaryFiniteP1Exchange A g (ordinaryFiniteUnit A (ProjectiveLine S)) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteUnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom =
      p1DecompositionSourceMap A N hN hA g hS ≫
        p1DecompositionMap A N hN hA S' hS' c' := by
    exact biprodMap_desc (ordinaryFinitePullback A g)
      (p1DecompositionUnit A S) (p1DecompositionChernAdjoint A N hN hA S hS c)
      (p1DecompositionUnit A S') (p1DecompositionChernAdjoint A N hN hA S' hS' c')
      (ordinaryFiniteUnitPullback A g)
      (p1DecompositionTwistPullback A N hN hA g hS (-1) (-2)) _ hu hh
  have : IsIso (p1DecompositionSourceMap A N hN hA g hS) := by
    unfold p1DecompositionSourceMap p1DecompositionBiprodMap
    exact biprodMap_isIso (ordinaryFinitePullback A g) _ _ _ _
  have := isIso_ordinaryFiniteP1Exchange A g (ordinaryFiniteUnit A (ProjectiveLine S))
  have hi' : IsIso (p1DecompositionSourceMap A N hN hA g hS ≫
      p1DecompositionMap A N hN hA S' hS' c') := by
    rw [← he]
    infer_instance
  refine ⟨c', hc', ?_, he⟩
  simpa only [isIso_comp_left_iff] using hi'
```

## New

```lean
theorem ordinaryFiniteP1Decomposition (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    ∃ c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
        (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧,
      ordinaryFiniteP1ChernSpec A N hA S
        ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
            hS.map (ProjectiveLine S ↘ S).appTop.hom) c ∧
      IsIso (p1DecompositionMap A N hN hA S hS c) ∧
      ∀ (S' : Scheme.{u}) (g : S' ⟶ S),
        ∃ c' : ordinaryFiniteUnit A (ProjectiveLine S') ⟶
            (ordinaryFiniteLine A N hA (ProjectiveLine S'))⟦(2 : ℤ)⟧,
          ordinaryFiniteP1ChernSpec A N hA S'
            ((map_natCast (ProjectiveLine S' ↘ S').appTop.hom N) ▸
              (((map_natCast g.appTop.hom N) ▸ hS.map g.appTop.hom).map
                (ProjectiveLine S' ↘ S').appTop.hom)) c' ∧
          IsIso (p1DecompositionMap A N hN hA S'
            ((map_natCast g.appTop.hom N) ▸ hS.map g.appTop.hom) c') ∧
          (ordinaryFinitePullback A g).map (p1DecompositionMap A N hN hA S hS c) ≫
              ordinaryFiniteP1Exchange A g (ordinaryFiniteUnit A (ProjectiveLine S)) ≫
              (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
                (ordinaryFiniteUnitPullback A
                  (X := ProjectiveLine S') (Y := ProjectiveLine S)
                  (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom =
            p1DecompositionSourceMap A N hN hA g hS ≫
              p1DecompositionMap A N hN hA S'
                ((map_natCast g.appTop.hom N) ▸ hS.map g.appTop.hom) c' := by
  obtain ⟨t, d, _⟩ := exists_ordinaryFiniteP1Adjunction N hN A hA
  let c := (d S hS).chern
  have hc := (d S hS).chern_spec
  have hi : IsIso (p1DecompositionMap A N hN hA S hS c) := by
    apply isIso_p1DecompositionMap_of_twisted A N hN hA t S hS
    rw [← (d S hS).decomposition_hom]
    infer_instance
  refine ⟨c, hc, hi, ?_⟩
  intro S' g
  have : (ordinaryFinitePullback A g).Additive :=
    additive_leftDerivedUpperStar (ModuleCat.{u + 1} A) g
  let hS' : IsUnit (N : Γ(S', ⊤)) :=
    (map_natCast g.appTop.hom N) ▸ hS.map g.appTop.hom
  obtain ⟨c', hc', hu, hh⟩ :=
    ordinaryFiniteP1_components_baseChange A N hN hA g hS hS' c hc
  have he :
      (ordinaryFinitePullback A g).map (p1DecompositionMap A N hN hA S hS c) ≫
        ordinaryFiniteP1Exchange A g (ordinaryFiniteUnit A (ProjectiveLine S)) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteUnitPullback A
            (X := ProjectiveLine S') (Y := ProjectiveLine S)
            (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom =
      p1DecompositionSourceMap A N hN hA g hS ≫
        p1DecompositionMap A N hN hA S' hS' c' := by
    exact biprodMap_desc (ordinaryFinitePullback A g)
      (p1DecompositionUnit A S) (p1DecompositionChernAdjoint A N hN hA S hS c)
      (p1DecompositionUnit A S') (p1DecompositionChernAdjoint A N hN hA S' hS' c')
      (ordinaryFiniteUnitPullback A g)
      (p1DecompositionTwistPullback A N hN hA g hS (-1) (-2)) _ hu hh
  have : IsIso (p1DecompositionSourceMap A N hN hA g hS) := by
    unfold p1DecompositionSourceMap p1DecompositionBiprodMap
    exact biprodMap_isIso (ordinaryFinitePullback A g) _ _ _ _
  have := isIso_ordinaryFiniteP1Exchange A g (ordinaryFiniteUnit A (ProjectiveLine S))
  have hi' : IsIso (p1DecompositionSourceMap A N hN hA g hS ≫
      p1DecompositionMap A N hN hA S' hS' c') := by
    rw [← he]
    infer_instance
  refine ⟨c', hc', ?_, he⟩
  simpa only [isIso_comp_left_iff] using hi'
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition` | unclaimed | explicit arguments only; no mathematical change |
| `Sheaf.AlgebraicGeometry.SpP1NormalizedFamilyCore` | unclaimed | definitionally identical interface; no adaptation required |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | U8 | proof completed here |

## Status

landed 20261024T191435-L-356888 2026-10-24 (merge of deliver/U8/Sheaf.AlgebraicGeometry.GeoP1Cohomology)
