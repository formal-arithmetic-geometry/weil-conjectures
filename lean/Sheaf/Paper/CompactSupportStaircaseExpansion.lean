/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.Paper.UnboundedProperOpenInterchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.Paper.DerivedCompactSupportCompositionCoherence

/-!
# Fixed-staircase expansion of compact-support comparisons

Source: Stacks Project, More on Étale Cohomology, Tag 0F7K, proof of
`lemma-pseudo-functor` (blueprint: lem-amb-compact-support-staircase-expansion).

## Main definitions and statement

* `compactSupportStaircaseInterchange`: the specified normalized interchange family.
* `compactSupportRawBinaryComparison`: the raw binary comparison on a proper/open tower.
* `compactSupportStaircaseTargetIso`: the common six-factor target identification.
* `compactSupportStaircaseExpansion`: the two fixed-staircase expansion identities.
-/


@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerStarComp
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryCompIso
  openImmersionLowerShriekComp Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek

/-- The complete normalization predicate for the specified derived interchange family.
Source: Stacks Project, Tags 0F7B--0F7F, as stated in
`unboundedProperOpenInterchange` (blueprint: lem-amb-compact-support-staircase-expansion).
This is the original predicate with the same chosen underived family. Naming it keeps
its large expression out of every use of classical choice. -/
noncomputable def compactSupportStaircaseInterchangeNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (Γ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (_sq : CommSq k r p i),
        R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
          D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A])) : Prop :=
  let θ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (_sq : CommSq k r p i),
        (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
          (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A] :=
    @Classical.choose _ _ (unboundedProperOpenInterchange A)
  (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (θ k r p i sq).hom.app F ≫
            (p)_*[ModuleCat.{u + 1} A].map
              ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F =
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
              ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F) ∧
      (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [J.IsKInjective]
        (I : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [I.IsKInjective]
        (ρ : ((k)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
        [QuasiIso ρ],
        D((i)_!open[ModuleCat.{u + 1} A]).map
            (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso J).hom ≫
          ((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app
            (((r)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (θ k r p i sq).hom (.up ℤ)).app J) ≫
          DerivedCategory.Q.map
            (((p)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).map ρ) =
        (Γ k r p i sq).hom.app (DerivedCategory.Q.obj J) ≫
          R((p)_*[ModuleCat.{u + 1} A]).map
            (((k)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J ≫
              DerivedCategory.Q.map ρ) ≫
          (((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).hom) ∧
      (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : IsPullback k r p i),
        ∃ lam : D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) ⋙
            D((i)^*[ModuleCat.{u + 1} A]) ≅ R((r)_*[ModuleCat.{u + 1} A]),
          (∀ K : DerivedCategoryModule A U,
            lam.hom.app K =
              (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
                  (D((k)_!open[ModuleCat.{u + 1} A]).obj K) ≫
                R((r)_*[ModuleCat.{u + 1} A]).map
                  (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction
                    (ModuleCat.{u + 1} A) k).unit.app K))) ∧
          ∀ K : DerivedCategoryModule A U,
            (Γ k r p i sq.toCommSq).hom.app K =
              D((i)_!open[ModuleCat.{u + 1} A]).map (lam.inv.app K) ≫
                (derivedOpenImmersionLowerShriekUpperStarAdjunction
                  (ModuleCat.{u + 1} A) i).counit.app
                    (R((p)_*[ModuleCat.{u + 1} A]).obj
                      (D((k)_!open[ModuleCat.{u + 1} A]).obj K))) ∧
      (∀ {U V W Z S T : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        [IsNoetherian S] [IsNoetherian T]
        (k : U ⟶ V) (r₁ : U ⟶ W) (p₁ : V ⟶ Z) (i₁ : W ⟶ Z)
        (r₂ : W ⟶ S) (p₂ : Z ⟶ T) (i₂ : S ⟶ T)
        [IsOpenImmersion k] [IsOpenImmersion i₁] [IsOpenImmersion i₂]
        [IsProper r₁] [IsProper p₁] [IsProper r₂] [IsProper p₂]
        (sq₁ : CommSq k r₁ p₁ i₁) (sq₂ : CommSq i₁ r₂ p₂ i₂)
        (K : DerivedCategoryModule A U),
        (Γ k (r₁ ≫ r₂) (p₁ ≫ p₂) i₂ (sq₁.vert_comp sq₂)).hom.app K =
          D((i₂)_!open[ModuleCat.{u + 1} A]).map
              ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) r₁ r₂).inv.app K) ≫
            (Γ i₁ r₂ p₂ i₂ sq₂).hom.app (R((r₁)_*[ModuleCat.{u + 1} A]).obj K) ≫
            R((p₂)_*[ModuleCat.{u + 1} A]).map ((Γ k r₁ p₁ i₁ sq₁).hom.app K) ≫
            (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p₁ p₂).hom.app
              (D((k)_!open[ModuleCat.{u + 1} A]).obj K)) ∧
      (∀ {U V T W Z S : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian T] [IsNoetherian W]
        [IsNoetherian Z] [IsNoetherian S]
        (k : U ⟶ V) (l : V ⟶ T) (r : U ⟶ W) (p : V ⟶ Z) (q : T ⟶ S)
        (i : W ⟶ Z) (j : Z ⟶ S)
        [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
        [IsProper r] [IsProper p] [IsProper q]
        (sq₁ : CommSq k r p i) (sq₂ : CommSq l p q j)
        (K : DerivedCategoryModule A U),
        (Γ (k ≫ l) r q (i ≫ j) (sq₁.horiz_comp sq₂)).hom.app K =
          (Functor.mapDerivedCategoryNatIso
              (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) i j) ≪≫
            Functor.mapDerivedCategoryCompIso _ _).hom.app
              (R((r)_*[ModuleCat.{u + 1} A]).obj K) ≫
            D((j)_!open[ModuleCat.{u + 1} A]).map ((Γ k r p i sq₁).hom.app K) ≫
            (Γ l p q j sq₂).hom.app (D((k)_!open[ModuleCat.{u + 1} A]).obj K) ≫
            R((q)_*[ModuleCat.{u + 1} A]).map
              ((Functor.mapDerivedCategoryNatIso
                  (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) k l) ≪≫
                Functor.mapDerivedCategoryCompIso _ _).inv.app K)) ∧
      (∀ {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
        (k : U ⟶ V) [IsOpenImmersion k] (K : DerivedCategoryModule A U),
        (Γ k (𝟙 U) (𝟙 V) k ⟨by simp⟩).hom.app K =
          D((k)_!open[ModuleCat.{u + 1} A]).map
              ((((𝟙 U)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorIsoMapDerivedCategory ≪≫
                Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) U) ≪≫
                Functor.mapDerivedCategoryIdIso _).hom.app K) ≫
            ((((𝟙 V)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorIsoMapDerivedCategory ≪≫
                Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) V) ≪≫
                Functor.mapDerivedCategoryIdIso _).inv.app
                  (D((k)_!open[ModuleCat.{u + 1} A]).obj K))) ∧
      (∀ {U W : Scheme.{u}} [IsNoetherian U] [IsNoetherian W]
        (r : U ⟶ W) [IsProper r] (K : DerivedCategoryModule A U),
        (Γ (𝟙 U) r r (𝟙 W) ⟨by simp⟩).hom.app K =
          (Functor.mapDerivedCategoryNatIso
              (Adjunction.leftAdjointIdIso
                (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 W))
                (upperStarId (ModuleCat.{u + 1} A) W)) ≪≫
            Functor.mapDerivedCategoryIdIso _).hom.app
              (R((r)_*[ModuleCat.{u + 1} A]).obj K) ≫
            R((r)_*[ModuleCat.{u + 1} A]).map
              ((Functor.mapDerivedCategoryNatIso
                  (Adjunction.leftAdjointIdIso
                    (openImmersionLowerShriekUpperStarAdjunction
                      (ModuleCat.{u + 1} A) (𝟙 U))
                    (upperStarId (ModuleCat.{u + 1} A) U)) ≪≫
                Functor.mapDerivedCategoryIdIso _).inv.app K)) ∧
      (∀ {U V W Z U₁ V₁ W₁ Z₁ : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        [IsNoetherian U₁] [IsNoetherian V₁] [IsNoetherian W₁] [IsNoetherian Z₁]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        (k₁ : U₁ ⟶ V₁) (r₁ : U₁ ⟶ W₁) (p₁ : V₁ ⟶ Z₁) (i₁ : W₁ ⟶ Z₁)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
        (sq : CommSq k r p i) (sq₁ : CommSq k₁ r₁ p₁ i₁)
        (a : V₁ ⟶ V) (b : Z₁ ⟶ Z) (c : W₁ ⟶ W) (d : U₁ ⟶ U)
        (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c)
        (si : IsPullback c i₁ i b) (sk : IsPullback d k₁ k a)
        (K : DerivedCategoryModule A U),
        D((b)^*[ModuleCat.{u + 1} A]).map ((Γ k r p i sq).hom.app K) ≫
            (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sp.toCommSq).app
              (D((k)_!open[ModuleCat.{u + 1} A]).obj K) ≫
            R((p₁)_*[ModuleCat.{u + 1} A]).map
              ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
                (ModuleCat.{u + 1} A) sk).inv.app K) =
          (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
              (ModuleCat.{u + 1} A) si).inv.app
                (R((r)_*[ModuleCat.{u + 1} A]).obj K) ≫
            D((i₁)_!open[ModuleCat.{u + 1} A]).map
              ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sr.toCommSq).app K) ≫
            (Γ k₁ r₁ p₁ i₁ sq₁).hom.app (D((d)^*[ModuleCat.{u + 1} A]).obj K))

/-- The normalized interchange family exists, with exactly the normalization supplied
by `unboundedProperOpenInterchange`. Source: Stacks Project, Tags 0F7B--0F7F
(blueprint: lem-amb-compact-support-staircase-expansion).
Proof: take the second existential witness of that theorem, after choosing its
underived family; the normalization predicate is definitionally the same one. -/
theorem compactSupportStaircaseInterchange_exists
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    ∃ Γ, compactSupportStaircaseInterchangeNormalization A Γ := by
  exact Classical.choose_spec (unboundedProperOpenInterchange A)

/-- The specified normalized interchange of Tags 0F7B--0F7F, used in Tag 0F7K
(blueprint: lem-amb-compact-support-staircase-expansion).
This selects the family supplied by `unboundedProperOpenInterchange`, with its complete
normalization. Its sheaf map is determined by its composite into the common direct image;
its derived map is determined on every K-injective representative and resolution. Thus this
choice determines the natural isomorphism up to equality, rather than choosing an arbitrary
isomorphism between the two functors. -/
noncomputable def compactSupportStaircaseInterchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : CommSq k r p i) :
    R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
      D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) :=
  (Classical.choose (compactSupportStaircaseInterchange_exists A)) k r p i sq

attribute [local irreducible] compactSupportStaircaseInterchange

/-- The raw binary comparison on a proper/open tower, before any compactification
independence. Source: Tag 0F7K, proof of `lemma-pseudo-functor`, using Tags 0F7C--0F7D
(blueprint: lem-amb-compact-support-staircase-expansion).
The four factors are the specified interchange, outer proper direct image, and the
canonical direct-image and open-extension composition isomorphisms. Associators only
parenthesize these functors. The candidates are exactly
`rightDerivedLowerShriekOfCompactification (ModuleCat A)` for the displayed factorizations. -/
noncomputable def compactSupportRawBinaryComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U V Y W Z : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian Y] [IsNoetherian W]
    (l : X ⟶ U) (a : U ⟶ V) (m : U ⟶ Y) (r : V ⟶ W) (d : Y ⟶ W) (q : W ⟶ Z)
    [IsOpenImmersion l] [IsOpenImmersion a] [IsOpenImmersion d]
    [IsProper m] [IsProper r] [IsProper q] (sq : CommSq a m r d) :
    (D((l)_!open[ModuleCat.{u + 1} A]) ⋙ R((m)_*[ModuleCat.{u + 1} A])) ⋙
        (D((d)_!open[ModuleCat.{u + 1} A]) ⋙ R((q)_*[ModuleCat.{u + 1} A])) ≅
      D((l ≫ a)_!open[ModuleCat.{u + 1} A]) ⋙ R((r ≫ q)_*[ModuleCat.{u + 1} A]) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (compactSupportStaircaseInterchange A a m r d sq) _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) r q)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) l a) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).symm _

set_option linter.unusedSimpArgs false

private lemma raw_hom_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U V Y W Z : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian Y] [IsNoetherian W]
    (l : X ⟶ U) (a : U ⟶ V) (m : U ⟶ Y) (r : V ⟶ W) (d : Y ⟶ W) (q : W ⟶ Z)
    [IsOpenImmersion l] [IsOpenImmersion a] [IsOpenImmersion d]
    [IsProper m] [IsProper r] [IsProper q] (sq : CommSq a m r d)
    (K : DerivedCategoryModule A X) :
    (compactSupportRawBinaryComparison A l a m r d q sq).hom.app K =
      R((q)_*[ModuleCat.{u + 1} A]).map
          ((compactSupportStaircaseInterchange A a m r d sq).hom.app
            (D((l)_!open[ModuleCat.{u + 1} A]).obj K)) ≫
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) r q).hom.app
          (D((a)_!open[ModuleCat.{u + 1} A]).obj
            (D((l)_!open[ModuleCat.{u + 1} A]).obj K)) ≫
        R((r ≫ q)_*[ModuleCat.{u + 1} A]).map
          ((Functor.mapDerivedCategoryNatIso
              (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) l a) ≪≫
            Functor.mapDerivedCategoryCompIso _ _).inv.app K) := by
  simp only [compactSupportRawBinaryComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj, Category.id_comp]

/-- The common target identification in Tag 0F7K, proof of `lemma-pseudo-functor`
(blueprint: lem-amb-compact-support-staircase-expansion).
It expands `R(tsp)_*D(bal)_!` into the six displayed factors. The proper factors are
expanded first and the open factors second. Both use the canonical composition maps,
with the left-associated scheme composites as the fixed parenthesization. -/
noncomputable def compactSupportStaircaseTargetIso
    (A : Type (u + 1)) [CommRing A]
    {X U V Xbar Ybar Zbar T : Scheme.{u}}
    (l : X ⟶ U) (a : U ⟶ V) (b : V ⟶ Xbar)
    (p : Xbar ⟶ Ybar) (s : Ybar ⟶ Zbar) (t : Zbar ⟶ T)
    [IsOpenImmersion l] [IsOpenImmersion a] [IsOpenImmersion b]
    (K : DerivedCategoryModule A X) :
    R(((p ≫ s) ≫ t)_*[ModuleCat.{u + 1} A]).obj
        (D(((l ≫ a) ≫ b)_!open[ModuleCat.{u + 1} A]).obj K) ≅
      R((t)_*[ModuleCat.{u + 1} A]).obj
        (R((s)_*[ModuleCat.{u + 1} A]).obj
          (R((p)_*[ModuleCat.{u + 1} A]).obj
            (D((b)_!open[ModuleCat.{u + 1} A]).obj
              (D((a)_!open[ModuleCat.{u + 1} A]).obj
                (D((l)_!open[ModuleCat.{u + 1} A]).obj K))))) :=
  (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) (p ≫ s) t).symm.app _ ≪≫
    R((t)_*[ModuleCat.{u + 1} A]).mapIso
      ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p s).symm.app _) ≪≫
    R((t)_*[ModuleCat.{u + 1} A]).mapIso
      (R((s)_*[ModuleCat.{u + 1} A]).mapIso
        (R((p)_*[ModuleCat.{u + 1} A]).mapIso
          ((Functor.mapDerivedCategoryNatIso
              (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) (l ≫ a) b) ≪≫
            Functor.mapDerivedCategoryCompIso _ _).app K ≪≫
            D((b)_!open[ModuleCat.{u + 1} A]).mapIso
              ((Functor.mapDerivedCategoryNatIso
                  (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) l a) ≪≫
                Functor.mapDerivedCategoryCompIso _ _).app K))))

@[reassoc] private lemma comp_iso_cancel
    {C D : Type*} [Category C] [Category D] {F G H : C ⥤ D}
    (e : F ≅ G) (f : G ≅ H) (K : C) :
    (e ≪≫ f).inv.app K ≫ e.hom.app K ≫ f.hom.app K = 𝟙 _ :=
  (e ≪≫ f).inv_hom_id_app K

attribute [local irreducible] compactSupportRawBinaryComparison
  compactSupportStaircaseTargetIso


/-- Expansion of the two iterated raw comparisons on the fixed cartesian staircase.
Source: Stacks Project, Tag 0F7K, proof of `lemma-pseudo-functor`
(blueprint: lem-amb-compact-support-staircase-expansion).

The first conjunct is the route `(g,f)` then `(h,gf)`, expanded as A, C, B.
The second is `(h,g)` then `(hg,f)`, expanded as C, A, B. Equations hold at every
unbounded derived input, and so are identities of natural transformations.

Proof plan:
1. Unfold `compactSupportRawBinaryComparison`. The candidates are `Dl_!Rm_*`,
   `Dd_!Rq_*`, `Di_!Rt_*`, `D(al)_!R(qr)_*`, `D(kd)_!R(ts)_*`, and
   `D(bal)_!R(tsp)_*`, in Lean's left-to-right functor notation. The four binary
   comparisons use A, C, the vertical rectangle B+C, and the horizontal rectangle A+B.
   This uses def-amb-etale-compact-support and lem-amb-unbounded-proper-open-interchange.
2. Identify both targets with the six factors using `compactSupportStaircaseTargetIso`.
   Open-extension associativity is the three-fold clause of
   lem-cbc-extension-zero-composition, applied degreewise. Proper associativity follows
   from the K-injective normalization of
   lem-weil-pbc-ringed-topoi-derived-pushforward-composition: both routes are represented
   by `t_*` applied to `s_*p_*I → s_*J → K` for successive resolutions.
   The uniqueness of the representing homotopy classes is
   lem-weil-pbc-kinjective-hom-derived. The `eqToHom` in the second route only changes
   the parenthesization of the scheme composites.
3. Apply vertical pasting from lem-amb-unbounded-proper-open-interchange to B+C and
   horizontal pasting to A+B. Whisker by the remaining factors, then use naturality of
   the composition isomorphisms. The resulting three factors are exactly those on the
   two right-hand sides. This proves the two expansion identities separately; no
   equality between them or compactification independence is asserted. -/
theorem compactSupportStaircaseExpansion
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U V Xbar Y W Ybar Z Zbar T : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian V] [IsNoetherian Xbar]
    [IsNoetherian Y] [IsNoetherian W] [IsNoetherian Ybar] [IsNoetherian Z]
    [IsNoetherian Zbar] [IsNoetherian T]
    (l : X ⟶ U) (a : U ⟶ V) (b : V ⟶ Xbar)
    (d : Y ⟶ W) (k : W ⟶ Ybar) (i : Z ⟶ Zbar)
    (m : U ⟶ Y) (r : V ⟶ W) (p : Xbar ⟶ Ybar)
    (q : W ⟶ Z) (s : Ybar ⟶ Zbar) (t : Zbar ⟶ T)
    [IsOpenImmersion l] [IsOpenImmersion a] [IsOpenImmersion b]
    [IsOpenImmersion d] [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper m] [IsProper r] [IsProper p] [IsProper q] [IsProper s] [IsProper t]
    (QA : IsPullback a m r d) (QB : IsPullback b r p k) (QC : IsPullback k q s i)
    (K : DerivedCategoryModule A X) :
    (R((t)_*[ModuleCat.{u + 1} A]).map
        (D((i)_!open[ModuleCat.{u + 1} A]).map
          ((compactSupportRawBinaryComparison A l a m r d q QA.toCommSq).hom.app K)) ≫
      (compactSupportRawBinaryComparison A (l ≫ a) b (r ≫ q) (p ≫ s) i t
        (QB.toCommSq.vert_comp QC.toCommSq)).hom.app K ≫
      (compactSupportStaircaseTargetIso A l a b p s t K).hom =
      R((t)_*[ModuleCat.{u + 1} A]).map
        (D((i)_!open[ModuleCat.{u + 1} A]).map
          (R((q)_*[ModuleCat.{u + 1} A]).map
            ((compactSupportStaircaseInterchange A a m r d QA.toCommSq).hom.app
              (D((l)_!open[ModuleCat.{u + 1} A]).obj K)))) ≫
      R((t)_*[ModuleCat.{u + 1} A]).map
        ((compactSupportStaircaseInterchange A k q s i QC.toCommSq).hom.app
          (R((r)_*[ModuleCat.{u + 1} A]).obj
            (D((a)_!open[ModuleCat.{u + 1} A]).obj
              (D((l)_!open[ModuleCat.{u + 1} A]).obj K)))) ≫
      R((t)_*[ModuleCat.{u + 1} A]).map
        (R((s)_*[ModuleCat.{u + 1} A]).map
          ((compactSupportStaircaseInterchange A b r p k QB.toCommSq).hom.app
            (D((a)_!open[ModuleCat.{u + 1} A]).obj
              (D((l)_!open[ModuleCat.{u + 1} A]).obj K))))) ∧
    ((compactSupportRawBinaryComparison A d k q s i t QC.toCommSq).hom.app
        (R((m)_*[ModuleCat.{u + 1} A]).obj
          (D((l)_!open[ModuleCat.{u + 1} A]).obj K)) ≫
      (compactSupportRawBinaryComparison A l (a ≫ b) m p (d ≫ k) (s ≫ t)
        (QA.toCommSq.horiz_comp QB.toCommSq)).hom.app K ≫
      eqToHom (by simp only [Category.assoc, Functor.comp_obj]) ≫
      (compactSupportStaircaseTargetIso A l a b p s t K).hom =
      R((t)_*[ModuleCat.{u + 1} A]).map
        ((compactSupportStaircaseInterchange A k q s i QC.toCommSq).hom.app
          (D((d)_!open[ModuleCat.{u + 1} A]).obj
            (R((m)_*[ModuleCat.{u + 1} A]).obj
              (D((l)_!open[ModuleCat.{u + 1} A]).obj K)))) ≫
      R((t)_*[ModuleCat.{u + 1} A]).map
        (R((s)_*[ModuleCat.{u + 1} A]).map
          (D((k)_!open[ModuleCat.{u + 1} A]).map
            ((compactSupportStaircaseInterchange A a m r d QA.toCommSq).hom.app
              (D((l)_!open[ModuleCat.{u + 1} A]).obj K)))) ≫
      R((t)_*[ModuleCat.{u + 1} A]).map
        (R((s)_*[ModuleCat.{u + 1} A]).map
          ((compactSupportStaircaseInterchange A b r p k QB.toCommSq).hom.app
            (D((a)_!open[ModuleCat.{u + 1} A]).obj
              (D((l)_!open[ModuleCat.{u + 1} A]).obj K))))) := by
  constructor
  · rw [raw_hom_app, raw_hom_app]
    simp only [compactSupportStaircaseTargetIso, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Functor.mapIso_hom, NatTrans.comp_app]
    simp only [NatTrans.naturality_assoc, Functor.comp_map, Functor.map_comp,
      Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id_app, Iso.inv_hom_id_app, Functor.map_id,
      Category.id_comp, Category.comp_id]
    simp only [← Functor.map_comp]
    congr 1
    simp only [NatTrans.naturality_assoc, Functor.comp_map, ← Functor.map_comp,
      Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id_app, Iso.inv_hom_id_app, Functor.map_id,
      Category.id_comp, Category.comp_id]
    simp only [comp_iso_cancel_assoc, comp_iso_cancel, Functor.map_comp]
    have hn := (compactSupportStaircaseInterchange A b (r ≫ q) (p ≫ s) i
      (QB.toCommSq.vert_comp QC.toCommSq)).hom.naturality
        ((Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) l a) ≪≫
            Functor.mapDerivedCategoryCompIso _ _).inv.app K)
    simp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    rw [(rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p s).inv.naturality_assoc]
    simp only [Functor.comp_map, ← Functor.map_comp, Category.assoc,
      comp_iso_cancel_assoc, comp_iso_cancel, Functor.map_id, Category.comp_id]
    have hv : (compactSupportStaircaseInterchange A b (r ≫ q) (p ≫ s) i
        (QB.toCommSq.vert_comp QC.toCommSq)).hom.app
          (D((a)_!open[ModuleCat.{u + 1} A]).obj
            (D((l)_!open[ModuleCat.{u + 1} A]).obj K)) =
      D((i)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) r q).inv.app _) ≫
      (compactSupportStaircaseInterchange A k q s i QC.toCommSq).hom.app _ ≫
      R((s)_*[ModuleCat.{u + 1} A]).map
        ((compactSupportStaircaseInterchange A b r p k QB.toCommSq).hom.app _) ≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p s).hom.app _ := by
      simpa only [compactSupportStaircaseInterchange] using
        ((Classical.choose_spec (compactSupportStaircaseInterchange_exists A)).2.2.2.1
        b r p k q s i QB.toCommSq QC.toCommSq
          (D((a)_!open[ModuleCat.{u + 1} A]).obj
            (D((l)_!open[ModuleCat.{u + 1} A]).obj K)))
    rw [hv]
    simp only [Functor.comp_obj, ← Functor.map_comp_assoc, ← Functor.map_comp,
      Category.assoc, Iso.hom_inv_id_app_assoc,
      Iso.hom_inv_id_app, Functor.map_id, Category.id_comp, Category.comp_id]
    rw [(D((b)_!open[ModuleCat.{u + 1} A])).map_id,
      (R((p)_*[ModuleCat.{u + 1} A])).map_id, Category.comp_id]
  · rw [raw_hom_app, raw_hom_app]
    simp only [compactSupportStaircaseTargetIso, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Functor.mapIso_hom, NatTrans.comp_app]
    simp only [NatTrans.naturality_assoc, Functor.comp_map, Functor.map_comp,
      Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id_app, Iso.inv_hom_id_app, Functor.map_id,
      Category.id_comp, Category.comp_id]
    have hh : (compactSupportStaircaseInterchange A (a ≫ b) m p (d ≫ k)
        (QA.toCommSq.horiz_comp QB.toCommSq)).hom.app
          (D((l)_!open[ModuleCat.{u + 1} A]).obj K) =
      (Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) d k) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).hom.app _ ≫
      D((k)_!open[ModuleCat.{u + 1} A]).map
        ((compactSupportStaircaseInterchange A a m r d QA.toCommSq).hom.app _) ≫
      (compactSupportStaircaseInterchange A b r p k QB.toCommSq).hom.app _ ≫
      R((p)_*[ModuleCat.{u + 1} A]).map
        ((Functor.mapDerivedCategoryNatIso
            (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) a b) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).inv.app _) := by
      simpa only [compactSupportStaircaseInterchange] using
        ((Classical.choose_spec (compactSupportStaircaseInterchange_exists A)).2.2.2.2.1
        a b m r p d k QA.toCommSq QB.toCommSq
          (D((l)_!open[ModuleCat.{u + 1} A]).obj K))
    rw [hh]
    simp only [Functor.map_comp, Category.assoc]
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Functor.map_id,
      Category.id_comp, Category.comp_id]
    simp only [Functor.map_comp, Category.assoc]
    rw [← (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) s t).hom.naturality_assoc,
      ← (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) s t).hom.naturality_assoc]
    simp only [Functor.comp_map]
    have hcoh := derivedCompactSupportComposition_cancel A l a b p s t K
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] at hcoh
    simp only [Functor.comp_obj] at hcoh ⊢
    rw [hcoh]
    simp only [Category.comp_id]

end AlgebraicGeometry.Etale
