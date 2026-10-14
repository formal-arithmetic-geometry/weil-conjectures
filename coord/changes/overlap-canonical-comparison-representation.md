# overlapIteratedRestrictionIso, overlapDirectRestrictionIso and overlapConjugatedTransition

## Reason

The original concrete comparison proof exceeds the 60-second compiler limit during kernel checking. The iterated comparison now gives its chart maps explicitly. The direct restriction comparison uses pullbackCompOfEq with reflexive composite equality in its inverse composition factor, matching the generic single-chart comparison API. This avoids rewriting an equality of entire isomorphisms after substituting concrete pullback charts. The conjugated transition writes the two canonical composition factors explicitly, avoiding expansion of the descent-data constructor. These are the same canonical maps, with identical signatures.

## Old

```lean
def overlapIteratedRestrictionIso {X Y Z : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (d : U.I₀) :
    (Scheme.Modules.pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p d)).obj
      ((Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)) ≅
    (Scheme.Modules.pullback (overlapIteratedChartHom U q p t h d)).obj
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d)) :=
  (Scheme.Modules.pullbackComp _ _).app (N d) ≪≫
    (Scheme.Modules.pullbackCongr (pullback.lift_snd _ _ _).symm).app (N d) ≪≫
    ((Scheme.Modules.pullbackComp _ _).app (N d)).symm

def overlapDirectRestrictionIso {X Y Z H : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (a b d : U.I₀)
    (hd : H ⟶ (U.pullback₁ t).X d)
    (z : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ H)
    (r : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ ((U.pullback₁ q).pullback₁ p).X d)
    (hz : z ≫ hd = r ≫ overlapIteratedChartHom U q p t h d)
    (S : H.Modules)
    (τ : S ≅ (Scheme.Modules.pullback hd).obj
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d))) :
    (Scheme.Modules.pullback z).obj S ≅
      (Scheme.Modules.pullback r).obj
        ((Scheme.Modules.pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p d)).obj
          ((Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d))) :=
  (Scheme.Modules.pullback z).mapIso τ ≪≫
    pullbackCompOfEq z hd (r ≫ overlapIteratedChartHom U q p t h d) hz
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d)) ≪≫
    ((Scheme.Modules.pullbackComp r (overlapIteratedChartHom U q p t h d)).app _).symm ≪≫
    (Scheme.Modules.pullback r).mapIso (overlapIteratedRestrictionIso U q p t h N d).symm

def overlapConjugatedTransition {X Z H : Scheme.{u}} (U : X.OpenCover.{u})
    (t : Z ⟶ X) (N : (d : U.I₀) → (U.X d).Modules) (M : Z.Modules)
    (e : ∀ d, (Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f d)).obj M)
    (a b : U.I₀) (ν : H ⟶ Z)
    (ha : H ⟶ (U.pullback₁ t).X a) (hb : H ⟶ (U.pullback₁ t).X b)
    (hνa : ha ≫ (U.pullback₁ t).f a = ν) (hνb : hb ≫ (U.pullback₁ t).f b = ν)
    (S T : H.Modules)
    (τa : S ≅ (Scheme.Modules.pullback ha).obj
      ((Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a)))
    (τb : T ≅ (Scheme.Modules.pullback hb).obj
      ((Scheme.Modules.pullback (U.pullbackHom t b)).obj (N b))) : S ⟶ T :=
  let D := (modulesPseudofunctor.toDescentData (U.pullback₁ t).f).obj M
  τa.hom ≫ (Scheme.Modules.pullback ha).map (e a).hom ≫
    D.hom ν ha hb hνa hνb ≫ (Scheme.Modules.pullback hb).map (e b).inv ≫ τb.inv
```

## New

```lean
def overlapIteratedRestrictionIso {X Y Z : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (d : U.I₀) :
    (Scheme.Modules.pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p d)).obj
      ((Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)) ≅
    (Scheme.Modules.pullback (overlapIteratedChartHom U q p t h d)).obj
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d)) :=
by
  let V : Y.OpenCover.{u} := U.pullback₁ q
  let d' := overlapIteratedChartHom U q p t h d
  have hdq : d' ≫ U.pullbackHom t d = V.pullbackHom p d ≫ U.pullbackHom q d :=
    pullback.lift_snd _ _ _
  exact (Scheme.Modules.pullbackComp (V.pullbackHom p d) (U.pullbackHom q d)).app
      (N d) ≪≫
    (Scheme.Modules.pullbackCongr hdq.symm).app (N d) ≪≫
    ((Scheme.Modules.pullbackComp d' (U.pullbackHom t d)).app (N d)).symm

def overlapDirectRestrictionIso {X Y Z H : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (a b d : U.I₀)
    (hd : H ⟶ (U.pullback₁ t).X d)
    (z : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ H)
    (r : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ ((U.pullback₁ q).pullback₁ p).X d)
    (hz : z ≫ hd = r ≫ overlapIteratedChartHom U q p t h d)
    (S : H.Modules)
    (τ : S ≅ (Scheme.Modules.pullback hd).obj
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d))) :
    (Scheme.Modules.pullback z).obj S ≅
      (Scheme.Modules.pullback r).obj
        ((Scheme.Modules.pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p d)).obj
          ((Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d))) :=
  (Scheme.Modules.pullback z).mapIso τ ≪≫
    pullbackCompOfEq z hd (r ≫ overlapIteratedChartHom U q p t h d) hz
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d)) ≪≫
    (pullbackCompOfEq r (overlapIteratedChartHom U q p t h d)
      (r ≫ overlapIteratedChartHom U q p t h d) rfl
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d))).symm ≪≫
    (Scheme.Modules.pullback r).mapIso (overlapIteratedRestrictionIso U q p t h N d).symm

def overlapConjugatedTransition {X Z H : Scheme.{u}} (U : X.OpenCover.{u})
    (t : Z ⟶ X) (N : (d : U.I₀) → (U.X d).Modules) (M : Z.Modules)
    (e : ∀ d, (Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f d)).obj M)
    (a b : U.I₀) (ν : H ⟶ Z)
    (ha : H ⟶ (U.pullback₁ t).X a) (hb : H ⟶ (U.pullback₁ t).X b)
    (hνa : ha ≫ (U.pullback₁ t).f a = ν) (hνb : hb ≫ (U.pullback₁ t).f b = ν)
    (S T : H.Modules)
    (τa : S ≅ (Scheme.Modules.pullback ha).obj
      ((Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a)))
    (τb : T ≅ (Scheme.Modules.pullback hb).obj
      ((Scheme.Modules.pullback (U.pullbackHom t b)).obj (N b))) : S ⟶ T :=
  τa.hom ≫ (Scheme.Modules.pullback ha).map (e a).hom ≫
    ((pullbackCompOfEq ha ((U.pullback₁ t).f a) ν hνa M).hom ≫
      (pullbackCompOfEq hb ((U.pullback₁ t).f b) ν hνb M).inv) ≫
    (Scheme.Modules.pullback hb).map (e b).inv ≫ τb.inv
```

The additional congruence factor in pullbackCompOfEq r d (r ≫ d) rfl is the identity, so its composition with pullbackComp is the original composition isomorphism. This follows by Iso.ext and simplification of pullbackCongr rfl. The iterated comparison is the original three factors with all formerly inferred maps written explicitly. No theorem statement is changed or weakened.

The transition formula is unchanged by Pseudofunctor.DescentData.ofObj_hom and the two modulesPseudofunctor_mapComp'_app equations; the fully proved private canonical_descent_hom lemma checks this identification.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OverlapConjugateRestriction | Q2 | Identical canonical comparison isomorphisms; proof uses their composition formulas. |
| Sheaf.AlgebraicGeometry.OverlapPairModelTransport | unclaimed | Statement and canonical maps retain the same meaning; signature unchanged. |

| Sheaf.AlgebraicGeometry.OverlapStageModelRestriction | unclaimed | Same comparison maps and theorem statements; signature unchanged. |

The symbol-use check finds only the owned module for overlapIteratedRestrictionIso and all three rows above for overlapDirectRestrictionIso. overlapConjugatedTransition is used by the owned module and OverlapPairModelTransport. No target signature changes. Any statement review involving these definitions should confirm their identical canonical maps.

## Status

landed 20261014T052131-L-1876990 2026-10-14 (merge of deliver/Q2/Sheaf.AlgebraicGeometry.OverlapConjugateRestriction)
