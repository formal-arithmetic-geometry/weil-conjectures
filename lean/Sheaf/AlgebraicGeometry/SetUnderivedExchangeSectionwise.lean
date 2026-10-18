/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import Mathlib.CategoryTheory.Functor.Flat
import Sheaf.AlgebraicGeometry.ChosenCartesianSquare

/-!
# Sectionwise formula for the underived exchange of sheaves of sets

Source: Stacks Project, Étale Cohomology, Tag 0EZR, proof of lemma-base-change-local;
Sites, inverse-image representatives and the base-change mate
(blueprint: lem-sbc-sets-underived-exchange-sectionwise).

The exchange arrow is the existing `Etale.setBaseChangeArrow`, with the square transposed
so that the source is `g⁻¹ f_* F`. The helpers give the square comparison, the induced
map of test objects, and the actual sheafified presheaf representative.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Transpose the chosen Cartesian square by the canonical symmetry of its fibre product.
All fields are supplied by the original square and Mathlib's projection equations.
Source: Stacks Project, Tag 0EZR, Cartesian square
(blueprint: lem-sbc-sets-underived-exchange-sectionwise). -/
noncomputable def ChosenCartesianSquare.exchangeTranspose
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) :
    ChosenCartesianSquare f' g' g f where
  w := sq.w.symm
  isoPullback := sq.isoPullback ≪≫ pullbackSymmetry f g
  hom_fst := (Category.assoc _ _ _).trans
    ((congrArg (fun k => sq.isoPullback.hom ≫ k)
      (pullbackSymmetry_hom_comp_fst f g)).trans sq.hom_snd)
  hom_snd := (Category.assoc _ _ _).trans
    ((congrArg (fun k => sq.isoPullback.hom ≫ k)
      (pullbackSymmetry_hom_comp_snd f g)).trans sq.hom_fst)

/-- The set-valued square comparison is `c_{g,f'} ≫ c_{f,g'}⁻¹`, transported by
commutativity. The composition isomorphisms are the unit-normalized, uniquely determined
ones of `etaleSetInverseImageCompositionUnits`; no arbitrary comparison is selected.
Source: Stacks Project, Tag 0EZR, the inverse-image comparison in the base-change mate
(blueprint: lem-sbc-sets-underived-exchange-sectionwise). -/
noncomputable def ChosenCartesianSquare.setExchangeComparison
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (G : Sheaf Y.smallEtaleTopology (Type (u + 1))) :
    (Scheme.etaleSetPullback f').obj ((Scheme.etaleSetPullback g).obj G) ⟶
      (Scheme.etaleSetPullback g').obj ((Scheme.etaleSetPullback f).obj G) :=
  ((Classical.choose etaleSetInverseImageCompositionUnits.2.2 Y Y' X' g f').hom.app G) ≫
    eqToHom (congrArg (fun k : X' ⟶ Y => (Scheme.etaleSetPullback k).obj G) sq.w.symm) ≫
    ((Classical.choose etaleSetInverseImageCompositionUnits.2.2 Y X X' f g').inv.app G)

/-- The map `ℓ_a` from the base change of `V` to the iterated base change of `W`.
Base-change functors use `W ×_Y X`; their pullback-composition isomorphisms implement
exactly the scheme fibre-product map in the statement, including the canonical symmetries.
Source: Stacks Project, Tag 0EZR, restriction on representatives
(blueprint: lem-sbc-sets-underived-exchange-sectionwise). -/
noncomputable def ChosenCartesianSquare.setExchangeRestrictionMap
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (V : Y'.Etale) (W : Y.Etale)
    (a : V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj W) :
    (MorphismProperty.Over.pullback @Etale ⊤ f').obj V ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ g').obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W) :=
  (MorphismProperty.Over.pullback @Etale ⊤ f').map a ≫
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f' g).inv.app W ≫
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      g' f (f' ≫ g) sq.w.symm).hom.app W

/-- The sheafified class of `(W,a,s)`: apply the Kan-extension unit at `W`, restrict
along `a`, and apply the sheafification unit at `V`. This is actual construction data.
Source: Stacks Project, Sites, inverse image by sheafification; Tag 0EZR
(blueprint: lem-sbc-sets-underived-exchange-sectionwise). -/
noncomputable def setExchangeRepresentative
    {X Y' Y : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (V : Y'.Etale) (W : Y.Etale)
    (a : V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj W)
    (s : F.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))) :
    ((Scheme.etaleSetPullback g).obj ((Etale.lowerStar (Type (u + 1)) f).obj F)).obj.obj
      (op V) :=
  (toSheafify Y'.smallEtaleTopology
    ((MorphismProperty.Over.pullback @Etale ⊤ g).op.lan.obj
      ((Etale.lowerStar (Type (u + 1)) f).obj F).obj)).app (op V)
    (((MorphismProperty.Over.pullback @Etale ⊤ g).op.lan.obj
      ((Etale.lowerStar (Type (u + 1)) f).obj F).obj).map a.op
      (((MorphismProperty.Over.pullback @Etale ⊤ g).op.lanUnit.app
        ((Etale.lowerStar (Type (u + 1)) f).obj F).obj).app (op W) s))

/-- Apply the inverse-image unit for `g'` to `s`, then restrict along `ℓ_a`.
Source: Stacks Project, Tag 0EZR, restriction identities on presheaf representatives
(blueprint: lem-sbc-sets-underived-exchange-sectionwise). -/
noncomputable def ChosenCartesianSquare.setExchangeRepresentativeImage
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (V : Y'.Etale) (W : Y.Etale)
    (a : V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj W)
    (s : F.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))) :
    ((Scheme.etaleSetPullback g').obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f').obj V)) :=
  ((Scheme.etaleSetPullback g').obj F).obj.map
    (sq.setExchangeRestrictionMap V W a).op
    (((Etale.setUpperLowerAdjunction g').unit.app F).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)) s)

/-- The canonical set-valued exchange has the prescribed counit transpose, sends each
sheafified representative to unit followed by restriction along `ℓ_a`, is independent
of the representative, and is natural in the sheaf.

Source: Stacks Project, Étale Cohomology, Tag 0EZR, proof of lemma-base-change-local
(blueprint: lem-sbc-sets-underived-exchange-sectionwise).

Proof:
1. `lem-weil-pbc-sets-etale-inverse-image-composition-units` identifies inverse image
   with Kan extension followed by sheafification and direct image with evaluation on
   base change. Thus `(W,a,s)` is a presheaf representative. `def-pc-fibre-product`
   supplies `ℓ_a` and identifies target sections with sections over the base change of V.
2. Unit naturality in that node and functoriality of fibre products show that unit
   followed by `ℓ_a` restriction respects transitions in W and restrictions in V.
3. `def-weil-pbc-sheafification` extends this presheaf rule uniquely to the target sheaf.
   Equal sheafified classes have equal images; unit naturality gives naturality in F.
4. Compute its adjunct on identity representatives. The adjunction of
   `lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction` has unit the identity
   coprojection of `lem-weil-pbc-presheaf-pullback-sets-left-exact` followed by
   sheafification. The result is the unit for g' followed by the fibre-product comparison.
5. Transpose the square comparison followed by the pulled-back counit. The composition
   unit equation of `lem-weil-pbc-sets-etale-inverse-image-composition-units`, naturality
   of the g' unit, and the f triangle identity give the same adjunct. Injectivity of
   the g adjunction hom bijection identifies the rule with the existing exchange arrow. -/
theorem setUnderivedExchangeSectionwise
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) :
    (∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1))),
      Etale.setBaseChangeArrow sq.exchangeTranspose F =
        (Etale.setUpperLowerAdjunction f').homEquiv _ _
          (sq.setExchangeComparison ((Etale.lowerStar (Type (u + 1)) f).obj F) ≫
            (Scheme.etaleSetPullback g').map
              ((Etale.setUpperLowerAdjunction f).counit.app F))) ∧
    (∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (V : Y'.Etale) (W : Y.Etale)
      (a : V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj W)
      (s : F.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))),
      (Etale.setBaseChangeArrow sq.exchangeTranspose F).hom.app (op V)
        (setExchangeRepresentative f g F V W a s) =
          sq.setExchangeRepresentativeImage F V W a s) ∧
    (∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (V : Y'.Etale) (W₁ W₂ : Y.Etale)
      (a₁ : V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj W₁)
      (a₂ : V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj W₂)
      (s₁ : F.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W₁)))
      (s₂ : F.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W₂))),
      setExchangeRepresentative f g F V W₁ a₁ s₁ =
          setExchangeRepresentative f g F V W₂ a₂ s₂ →
        sq.setExchangeRepresentativeImage F V W₁ a₁ s₁ =
          sq.setExchangeRepresentativeImage F V W₂ a₂ s₂) ∧
    (∀ (F F₁ : Sheaf X.smallEtaleTopology (Type (u + 1))) (ψ : F ⟶ F₁),
      (Scheme.etaleSetPullback g).map ((Etale.lowerStar (Type (u + 1)) f).map ψ) ≫
          Etale.setBaseChangeArrow sq.exchangeTranspose F₁ =
        Etale.setBaseChangeArrow sq.exchangeTranspose F ≫
          (Etale.lowerStar (Type (u + 1)) f').map ((Scheme.etaleSetPullback g').map ψ)) := by
  sorry

end AlgebraicGeometry
