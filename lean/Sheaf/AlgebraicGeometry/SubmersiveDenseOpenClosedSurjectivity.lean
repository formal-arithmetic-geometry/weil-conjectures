module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Pullbacks

import Sheaf.AlgebraicGeometry.NoetherianImageBoundaryDvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Closed horizontal support under a universally submersive morphism

Source: Stacks Project, flat.tex, Tag 0ETT, proof of lemma-Noetherian-h-covering,
last paragraph, using limits.tex, Tag 0CM2, lemma-reach-point-closure-Noetherian.
(blueprint: lem-sfb-submersive-dense-open-closed-surjectivity)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A closed subset containing the inverse image of a dense open covers the integral
Noetherian base of a finite-type universally submersive morphism.

Source: Stacks Project, flat.tex, Tag 0ETT, proof of lemma-Noetherian-h-covering,
last paragraph; limits.tex, Tag 0CM2, lemma-reach-point-closure-Noetherian.
(blueprint: lem-sfb-submersive-dense-open-closed-surjectivity)

Proof:
1. The open inclusion j : U → Y is quasi-compact by
   lem-sfb-noetherian-open-closed-finite-presentation, applied with the identity closed
   immersion of U. It is of finite type by lem-weil-pbc-qc-open-immersion-finite-type.
   Its image has closure Y by density.
2. Fix y in Y. If y lies in U, surjectivity of f, obtained by identity base change,
   gives a point of Z over y. Otherwise lem-sfb-noetherian-image-boundary-dvr applied
   to j gives a DVR A and g : Spec A → Y whose generic point maps into U and whose
   closed point s maps to y.
3. Form W = X ×_Y Spec A with projections p and q. The closed subset C = p⁻¹(Z)
   contains q⁻¹({η}), since g(η) lies in U. Here η is the zero prime, the image of
   the fraction-field spectrum, by def-weil-affine-spectrum and the pullback square.
4. By lem-sc-dvr-dimension-one, def-weil-pbc-krull-dimension-ring and
   def-sc-discrete-valuation-ring, Spec A has exactly two points η and s. A third
   prime would give a strict chain of length two between zero and the maximal ideal.
   The singleton {η} is not closed: any Zariski closed V(I) containing zero has
   I = 0 and is all of Spec A, by def-weil-affine-spectrum.
5. If C contained no point over s, it would equal q⁻¹({η}). Its complement
   q⁻¹({s}) would then be open. Universal submersivity makes {s} open, contrary to
   step 4. Thus some w in C lies over s, and p(w) belongs to Z and maps to y.
   Together with the case y in U this proves f(Z) = Y. -/
theorem image_closed_eq_univ_of_universally_submersive
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y]
    (hsub : ∀ (T : Scheme.{u}) (g : T ⟶ Y),
      Function.Surjective (pullback.snd f g) ∧
        ∀ V : Set T, IsOpen V ↔ IsOpen ((pullback.snd f g) ⁻¹' V))
    (U : Y.Opens) (hU : closure (U : Set Y) = Set.univ)
    (Z : Set X) (hZ : IsClosed Z) (hUZ : f ⁻¹' (U : Set Y) ⊆ Z) :
    f '' Z = Set.univ := by
  sorry

end AlgebraicGeometry
