/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.CategoryTheory.Whiskering
import Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks

/-!
# A local right inverse of a charted logarithmic map

Source: Illusie--Laszlo--Orgogozo, Exposé VI 1.1 and 3.7(a), printed pp. 69 and 75,
final chart-extension sentence; the finite-generator inverse-lift extraction
(blueprint: lem-trf-charted-log-map-local-right-inverse).

Restrictions are expressed on the slice `Over V` of the small étale site. This is
the site of étale objects over `V.left`, with their given maps to `X`. Thus a
structure-compatible natural transformation on this slice is exactly a log
homomorphism between the restricted log structures. Stalk equations are written
on all pointed section representatives, in the original geometric stalks.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical map of geometric monoid stalks induced by a sheaf morphism.
It is the colimit map of the original pointed-neighbourhood diagrams.
Source: ILO VI 1.1, inverse chart lifting in 3.7(a)
(blueprint: lem-trf-charted-log-map-local-right-inverse). -/
noncomputable def EtalePrelogStructure.mapStalk {X : Scheme.{u}}
    (N M : EtalePrelogStructure X) (f : N.monoidSheaf ⟶ M.monoidSheaf)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) :
    N.stalk t ⟶ M.stalk t :=
  colimMap (Functor.whiskerLeft
    (CategoryOfElements.π (Scheme.pointSmallEtale t).fiber).op f.hom)

/-- Restriction of a global monoid chart by the sheaf's actual restriction map.
Source: ILO VI 1.1, inverse chart lifting in 3.7(a)
(blueprint: lem-trf-charted-log-map-local-right-inverse). -/
def EtaleLogStructure.restrictGlobalChart {X : Scheme.{u}} (M : EtaleLogStructure X)
    {Q : Type v} [CommMonoid Q]
    (q : Q →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 X)))) (V : X.Etale) :
    Q →* M.monoidSheaf.obj.obj (op V) :=
  (M.monoidSheaf.obj.map
    (MorphismProperty.Over.homMk V.hom (Category.comp_id V.hom) :
      V ⟶ Scheme.Etale.mk (𝟙 X)).op).hom.comp q

/-- A charted log map invertible at a geometric stalk has an affine pointed étale
local right inverse, with the prescribed inverse germs and unique chart extension.
Source: ILO VI 1.1 and the final chart-extension sentence of 3.7(a), printed pp. 69
and 75; the agent extraction of the inverse-lift argument
(blueprint: lem-trf-charted-log-map-local-right-inverse).

Proof:
1. Set `h = f_stalk⁻¹ q_stalk`. Apply the lifting clause of
`lem-trf-finite-monoid-stalk-data-spreading` to `Q` and the sheaf `N` at the
identity pointed neighbourhood. This produces an affine pointed neighbourhood
and a monoid map with germ `h`. No chart on `N` is used.
2. Apply the equality clause of that lemma to the maps `f k` and `q` into `M`.
Their germs agree, so they agree after a further affine pointed refinement.
Restriction preserves the specified germ. Structure compatibility of `f` gives
`alpha_N k = alpha_M q` without any finiteness of the unit sheaves.
3. By `lem-trf-associated-log-universal-stalks`, the restricted chart identifies
`M|V` with its associated log structure. Its universal property extends `k`
uniquely to a structure-compatible map `g : M|V → N|V`, fixing units.
4. The two log maps `f g` and the identity agree on the chart, so the injectivity
part of the same universal property identifies them. On the marked stalk this
says `f_stalk g_stalk = id`; cancellation by `f_stalk⁻¹` gives the final germ
formula. The earlier lift already gives `k_stalk = f_stalk⁻¹ q_stalk`.
-/
theorem EtaleLogStructure.exists_local_rightInverse_of_chart
    {X : Scheme.{max u v}} [IsLocallyNoetherian X]
    (N M : EtaleLogStructure X)
    (f : N.monoidSheaf ⟶ M.monoidSheaf) (hf : f.hom ≫ M.alpha = N.alpha)
    {Ω : Type (max u v)} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    {Q : Type v} [CommMonoid Q] (hQ : Monoid.FG Q)
    (q : Q →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (hq : M.IsChart (Scheme.Etale.mk (𝟙 X))
      (q.comp (MulEquiv.ulift : ULift.{u, v} Q ≃* Q).toMonoidHom))
    [IsIso (N.toEtalePrelogStructure.mapStalk M.toEtalePrelogStructure f t)] :
    ∃ (V : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj V)
      (k : Q →* N.monoidSheaf.obj.obj (op V)),
      IsAffine V.left ∧
      (N.alpha.app (op V)).hom.comp k =
        (M.alpha.app (op V)).hom.comp (M.restrictGlobalChart q V) ∧
      (f.hom.app (op V)).hom.comp k = M.restrictGlobalChart q V ∧
      (N.toEtalePrelogStructure.germ t V w).hom.comp k =
        (inv (N.toEtalePrelogStructure.mapStalk M.toEtalePrelogStructure f t)).hom.comp
          ((M.toEtalePrelogStructure.germ t V w).hom.comp
            (M.restrictGlobalChart q V)) ∧
      ∃ g : (Over.forget V).op ⋙ M.monoidSheaf.obj ⟶
          (Over.forget V).op ⋙ N.monoidSheaf.obj,
        (g ≫ Functor.whiskerLeft (Over.forget V).op N.alpha =
          Functor.whiskerLeft (Over.forget V).op M.alpha) ∧
        (g.app (op (Over.mk (𝟙 V)))).hom.comp (M.restrictGlobalChart q V) = k ∧
        (∀ g' : (Over.forget V).op ⋙ M.monoidSheaf.obj ⟶
            (Over.forget V).op ⋙ N.monoidSheaf.obj,
          g' ≫ Functor.whiskerLeft (Over.forget V).op N.alpha =
              Functor.whiskerLeft (Over.forget V).op M.alpha →
          (g'.app (op (Over.mk (𝟙 V)))).hom.comp (M.restrictGlobalChart q V) = k →
          g' = g) ∧
        g ≫ Functor.whiskerLeft (Over.forget V).op f.hom = 𝟙 _ ∧
        ∀ (W : X.Etale) (a : W ⟶ V)
          (z : (Scheme.pointSmallEtale t).fiber.obj W),
          (Scheme.pointSmallEtale t).fiber.map a z = w →
          ∀ s : M.monoidSheaf.obj.obj (op W),
            N.toEtalePrelogStructure.germ t W z (g.app (op (Over.mk a)) s) =
              inv (N.toEtalePrelogStructure.mapStalk M.toEtalePrelogStructure f t)
                (M.toEtalePrelogStructure.germ t W z s) := by
  sorry

end AlgebraicGeometry
