/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus
public import Sheaf.AlgebraicGeometry.EtaleSupportedSections
public import Sheaf.AlgebraicGeometry.ClosedSupportHom
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Category.Preorder
import Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity
import Sheaf.AlgebraicGeometry.NormalizedSupportTriangle
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Continuity of supported Kummer maps along preserved regular sequences

Source: ILO, Travaux de Gabber, Expose XVI, sections 2.1 and 2.3; Stacks Project,
Tag 03Q6 (blueprint: lem-per-transverse-gysin-limit).

Supported cohomology is written in its ordinary derived-Hom presentation from
`closedSupportHom`: Hom from the closed direct image of the constant coefficient
sheaf. The inverse closed exchange is extended by zero outside its isomorphism locus;
on every Cartesian closed pair it is the actual inverse of finite base change.
The continuity isomorphisms are expressed by descent and eventual vanishing, as in
`cohomology_continuity_of_isLimit`. All cohomological degrees and twists are integers.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The degree-zero realization of the existing signed Tate sheaf, with F_ell coefficients
at prime-power level one. Source: ILO XVI 2.3.1
(blueprint: lem-per-transverse-gysin-limit). -/
abbrev transverseTateObject (ℓ : ℕ) (X : Scheme.{u}) (m : ℤ) :=
  (DerivedCategory.singleFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1))) 0).obj
      (regularClassTwist ℓ 1 X m)

/-- Ordinary etale cohomology in its derived-Hom presentation, including negative degrees.
Source: Stacks 03Q6; ILO XVI 2.3.1 (blueprint: lem-per-transverse-gysin-limit). -/
abbrev transverseOrdinaryGroup (ℓ : ℕ) (X : Scheme.{u}) (q m : ℤ) :=
  transverseTateObject ℓ X 0 ⟶ (transverseTateObject ℓ X m)⟦q⟧

/-- Closed-supported cohomology in the presentation of `closedSupportHom`, equivalently
cohomology of `derivedSupportedEtaleSections` on the complementary open.
Source: Stacks 0A45; ILO XVI 2.3.1 (blueprint: lem-per-transverse-gysin-limit). -/
abbrev transverseSupportedGroup (ℓ : ℕ) {Z X : Scheme.{u}} (i : Z ⟶ X) (q m : ℤ) :=
  (DerivedCategory.singleFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1))) 0).obj
      ((lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)) i).obj
        (regularClassTwist ℓ 1 Z 0)) ⟶ (transverseTateObject ℓ X m)⟦q⟧

/-- Pull back a derived Hom and use the specified source and target coefficient maps.
Source: Stacks 03Q6, canonical cohomology pullback
(blueprint: lem-per-transverse-gysin-limit). -/
@[irreducible]
def transverseHomPullback (ℓ : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)))
    (P' : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)))
    (e : P' ⟶ (upperStar
      (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)) f).obj P)
    (q m : ℤ) (t : (upperStar
      (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)) f).obj
        (regularClassTwist ℓ 1 Y m) ⟶ regularClassTwist ℓ 1 X m)
    (x : (DerivedCategory.singleFunctor _ 0).obj P ⟶
      (transverseTateObject ℓ Y m)⟦q⟧) :
    (DerivedCategory.singleFunctor _ 0).obj P' ⟶
      (transverseTateObject ℓ X m)⟦q⟧ :=
  (DerivedCategory.singleFunctor _ 0).map e ≫
    ((upperStar
      (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)) f).mapDerivedCategorySingleFunctor
      0).inv.app P ≫
    (upperStar
      (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)) f).mapDerivedCategory.map x ≫
    ((upperStar
      (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)) f).mapDerivedCategory.commShiftIso
      q).hom.app (transverseTateObject ℓ Y m) ≫
    (((upperStar
      (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)) f).mapDerivedCategorySingleFunctor
      0).hom.app
      (regularClassTwist ℓ 1 Y m))⟦q⟧' ≫
    ((DerivedCategory.singleFunctor _ 0).map t)⟦q⟧'

/-- The ordinary pullback, using precisely the normalized signed Tate comparisons.
Source: Stacks 03Q6; ILO XVI 2.3 (blueprint: lem-per-transverse-gysin-limit). -/
@[irreducible]
def transverseOrdinaryPullback (ℓ : ℕ) (hℓ : ℓ.Prime)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit ((ℓ ^ 1 : ℕ) : Γ(Y, ⊤)))
    (hX : IsUnit ((ℓ ^ 1 : ℕ) : Γ(X, ⊤))) (q m : ℤ) :
    transverseOrdinaryGroup ℓ Y q m → transverseOrdinaryGroup ℓ X q m :=
  transverseHomPullback ℓ f _ _ (regularClassTwistPullback ℓ hℓ 1 f hY hX 0).inv q m
    (regularClassTwistPullback ℓ hℓ 1 f hY hX m).hom

/-- The canonical inverse closed exchange; the zero branch only makes it a total term
on non-Cartesian squares. Finite base change makes the first branch apply to the pairs
in the theorem. Source: ILO XVI 2.2.3.1 (blueprint: lem-per-transverse-gysin-limit). -/
@[irreducible]
def transverseClosedExchangeInverse (ℓ : ℕ) (hℓ : ℓ.Prime)
    {Z Z' X X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (v : X' ⟶ X) (w : Z' ⟶ Z) (sq : CommSq w i' i v)
    (hZ : IsUnit ((ℓ ^ 1 : ℕ) : Γ(Z, ⊤)))
    (hZ' : IsUnit ((ℓ ^ 1 : ℕ) : Γ(Z', ⊤))) :
    (lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)) i').obj
        (regularClassTwist ℓ 1 Z' 0) ⟶
      (upperStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)) v).obj
        ((lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)) i).obj
          (regularClassTwist ℓ 1 Z 0)) :=
  open Classical in
  if h : IsIso (regularClassExchange ℓ hℓ 1 i i' v w sq hZ hZ' 0) then
    @inv _ _ _ _ (regularClassExchange ℓ hℓ 1 i i' v w sq hZ hZ' 0) h
  else 0

/-- Supported pullback on the actual closed-derived-Hom presentation, through inverse
closed exchange and the normalized Tate comparison. Source: ILO XVI 2.2.3.1; Stacks 0A45
(blueprint: lem-per-transverse-gysin-limit). -/
@[irreducible]
def transverseSupportedPullback (ℓ : ℕ) (hℓ : ℓ.Prime)
    {Z Z' X X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (v : X' ⟶ X) (w : Z' ⟶ Z) (sq : CommSq w i' i v)
    (hX : IsUnit ((ℓ ^ 1 : ℕ) : Γ(X, ⊤)))
    (hX' : IsUnit ((ℓ ^ 1 : ℕ) : Γ(X', ⊤)))
    (hZ : IsUnit ((ℓ ^ 1 : ℕ) : Γ(Z, ⊤)))
    (hZ' : IsUnit ((ℓ ^ 1 : ℕ) : Γ(Z', ⊤))) (q m : ℤ) :
    transverseSupportedGroup ℓ i q m → transverseSupportedGroup ℓ i' q m :=
  transverseHomPullback ℓ v _ _
    (transverseClosedExchangeInverse ℓ hℓ i i' v w sq hZ hZ') q m
    (regularClassTwistPullback ℓ hℓ 1 v hX hX' m).hom

/-- The already specified canonical Kummer class family. Its existence theorem fixes
it uniquely by its normalization and composition laws; this selects no arbitrary class.
Source: ILO XVI 2.3.1--2.3.2 (blueprint: lem-per-transverse-gysin-limit). -/
@[irreducible]
def transverseClassFamily (ℓ : ℕ) (hℓ : ℓ.Prime) : RegularImmersionClassFamily.{u} ℓ :=
  Classical.choose (regular_immersion_class_calculus ℓ hℓ)

/-- The Kummer Gysin action: exact closed direct image of the input, followed by the
shifted supported class. The zero extension only applies outside the regular locus.
Source: ILO XVI 2.3.1--2.3.2 (blueprint: lem-per-transverse-gysin-limit). -/
@[irreducible]
def transverseGysin (ℓ : ℕ) (hℓ : ℓ.Prime)
    {Z X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ)
    (hX : IsUnit ((ℓ ^ 1 : ℕ) : Γ(X, ⊤))) (q : ℤ)
    (x : transverseOrdinaryGroup ℓ Z q 0) :
    transverseSupportedGroup ℓ i (q + 2 * (c : ℤ)) c :=
  open Classical in
  if h : IsStalkRegularClosedImmersion i c then
    ((lowerStar
      (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)) i).mapDerivedCategorySingleFunctor
      0).inv.app
      (regularClassTwist ℓ 1 Z 0) ≫
    (lowerStar
      (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)) i).mapDerivedCategory.map x ≫
    ((lowerStar
      (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)) i).mapDerivedCategory.commShiftIso
      q).hom.app (transverseTateObject ℓ Z 0) ≫
    (((lowerStar
      (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)) i).mapDerivedCategorySingleFunctor
      0).hom.app
      (regularClassTwist ℓ 1 Z 0))⟦q⟧' ≫
    ((transverseClassFamily ℓ hℓ 1 (Nat.le_refl 1) i c h hX 0).hom)⟦q⟧' ≫
    (shiftFunctorAdd' _ (2 * (c : ℤ)) q (q + 2 * (c : ℤ)) (add_comm _ _)).inv.app
      (transverseTateObject ℓ X c)
  else 0

/-- The elementwise criterion for a canonical directed-colimit comparison to be an
isomorphism: every class descends, and its kernel vanishes at a later stage. This is
also valid in negative degrees. Source: Stacks 03Q6
(blueprint: lem-per-transverse-gysin-limit). -/
def TransverseContinuity {I : Type u} [Preorder I]
    (H : I → Type (u + 1)) (HLimit : Type (u + 1))
    [∀ a : I, Zero (H a)] [Zero HLimit]
    (p : ∀ a : I, H a → HLimit) (t : ∀ a b : I, a ≤ b → H a → H b) : Prop :=
  (∀ x : HLimit, ∃ (a : I) (y : H a), p a y = x) ∧
    ∀ (a : I) (x : H a), p a x = 0 → ∃ (b : I) (h : a ≤ b), t a b h x = 0

/-- Invertibility of the coefficient order pulls back along the global-section ring map.
Source: ILO XVI 2.3.1 (blueprint: lem-per-transverse-gysin-limit). -/
abbrev transverseUnitPullback (ℓ : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit ((ℓ ^ 1 : ℕ) : Γ(Y, ⊤))) :
    IsUnit ((ℓ ^ 1 : ℕ) : Γ(X, ⊤)) :=
  (map_natCast f.appTop.hom (ℓ ^ 1)) ▸ hY.map f.appTop.hom

/-- The transition on the supported groups of a natural system of closed pairs.
The square is the naturality square of the immersion transformation.
Source: ILO XVI 2.2.3.1; Stacks 03Q6 (blueprint: lem-per-transverse-gysin-limit). -/
@[irreducible]
def transverseSupportedTransition (ℓ : ℕ) (hℓ : ℓ.Prime)
    {I : Type u} [Preorder I] {Z V : Iᵒᵖ ⥤ Scheme.{u}} (i : Z ⟶ V)
    (hV : ∀ a : I, IsUnit ((ℓ ^ 1 : ℕ) : Γ(V.obj (op a), ⊤)))
    (q m : ℤ) (a b : I) (h : a ≤ b) :
    transverseSupportedGroup ℓ (i.app (op a)) q m →
      transverseSupportedGroup ℓ (i.app (op b)) q m :=
  transverseSupportedPullback ℓ hℓ (i.app (op a)) (i.app (op b))
    (V.map (homOfLE h).op) (Z.map (homOfLE h).op)
    ⟨i.naturality (homOfLE h).op⟩ (hV a) (hV b)
    (transverseUnitPullback ℓ (i.app (op a)) (hV a))
    (transverseUnitPullback ℓ (i.app (op b)) (hV b)) q m

/-- The projection on supported groups from a stage to a compatible cone of closed pairs.
Source: ILO XVI 2.2.3.1; Stacks 03Q6 (blueprint: lem-per-transverse-gysin-limit). -/
@[irreducible]
def transverseSupportedProjection (ℓ : ℕ) (hℓ : ℓ.Prime)
    {I : Type u} [Preorder I] {Z V : Iᵒᵖ ⥤ Scheme.{u}} (i : Z ⟶ V)
    (z : Cone Z) (v : Cone V) (j : z.pt ⟶ v.pt)
    (hj : ∀ a : I, z.π.app (op a) ≫ i.app (op a) = j ≫ v.π.app (op a))
    (hV : ∀ a : I, IsUnit ((ℓ ^ 1 : ℕ) : Γ(V.obj (op a), ⊤)))
    (hLimit : IsUnit ((ℓ ^ 1 : ℕ) : Γ(v.pt, ⊤))) (q m : ℤ) (a : I) :
    transverseSupportedGroup ℓ (i.app (op a)) q m →
      transverseSupportedGroup ℓ j q m :=
  transverseSupportedPullback ℓ hℓ (i.app (op a)) j
    (v.π.app (op a)) (z.π.app (op a)) ⟨hj a⟩ (hV a) hLimit
    (transverseUnitPullback ℓ (i.app (op a)) (hV a))
    (transverseUnitPullback ℓ j hLimit) q m

/-- Simultaneous continuity for ordinary and closed-supported etale cohomology, and for
its specified Kummer Gysin actions, when transitions preserve the regular generators.
The two continuity predicates are the surjectivity and eventual-zero criterion for the
canonical colimit maps to be isomorphisms. The final two equations say respectively
that the Gysin actions form a directed-system map and that their colimit is the limit
immersion's action. Invertibility on the limit is derived from any fixed stage `a₀`;
no additional invertibility hypothesis on the limit or on the closed schemes is imposed.

Source: ILO XVI, sections 2.1 and 2.3, Definition 2.3.1, Theorem 2.3.2 and
Proposition 2.2.3.1; Stacks, Tag 03Q6 (blueprint: lem-per-transverse-gysin-limit).

Proof:
1. Restrict to the cofinal tail of a stage. Preservation of generators identifies each
   quotient by an initial segment and the complementary opens with their base changes.
   Quotients commute with the directed colimit of rings. Each initial quotient is
   Noetherian, and regularity makes successive flag inclusions effective Cartier divisors.
   The complements are finite unions of principal affine opens, hence qcqs; their
   transition maps are affine. For c = 0 the complement is empty.
2. Apply lem-asd-etale-finite-twist-pullback to descend every signed Tate coefficient.
   Apply lemma-weil-pbc-etale-cohomology-continuity on the ambient schemes, complements
   and closed schemes. Negative degrees vanish for these degree-zero sheaves.
3. The localization sequences of lem-pur-support-restriction-triangle are natural,
   by the shifted restriction cones in lem-amb-closed-support-hom. Filtered colimits are
   exact by lem-weil-pbc-filtered-colimit-abelian-groups-exact. Comparing the five terms
   H^(q-1)(V), H^(q-1)(U), H^q_Z(V), H^q(V), H^q(U) gives supported continuity:
   its kernel and cokernel vanish because the four ordinary comparisons are isomorphisms.
4. By lem-per-regular-immersion-class-calculus and the supported products of
   lem-per-noetherian-supported-product-calculus the Gysin action is the ordered
   composite of the positive supported Cartier Kummer operators along the generator
   flag. This identifies the actual specified class, including its sign; c = 0 is identity.
5. Every transition and projection preserves each Cartier flag and its conormal data.
   Apply the arbitrary Cartier-preserving pullback clause of
   lem-asd-ordinary-supported-kummer at each step, then the naturality of supported
   products and signed twists. Compose the resulting equalities. This gives both
   displayed Gysin equations without requiring flatness.
6. Every colimit class has a stage representative. The projection equation identifies
   the images of its Gysin image with the Gysin image of its limit pullback. Together
   with the two continuity isomorphisms, this identifies the colimit map with the
   Kummer Gysin map on the limit pair.
-/
theorem transverse_gysin_limit (ℓ : ℕ) (hℓ : ℓ.Prime)
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (a₀ : I)
    (Z V : Iᵒᵖ ⥤ Scheme.{u}) (i : Z ⟶ V)
    [∀ a : I, IsAffine (V.obj (op a))] [∀ a : I, IsAffine (Z.obj (op a))]
    [∀ a : I, IsNoetherian (V.obj (op a))]
    [∀ a : I, IsNoetherian (Z.obj (op a))]
    [∀ a : I, IsClosedImmersion (i.app (op a))]
    (z : Cone Z) (v : Cone V) (_hz : IsLimit z) (_hv : IsLimit v)
    [IsNoetherian z.pt] [IsNoetherian v.pt]
    (j : z.pt ⟶ v.pt) [IsClosedImmersion j]
    (hj : ∀ a : I, z.π.app (op a) ≫ i.app (op a) = j ≫ v.π.app (op a))
    (c : ℕ) (t : ∀ a : I, List Γ(V.obj (op a), ⊤)) (tLimit : List Γ(v.pt, ⊤))
    (_hlen : ∀ a : I, (t a).length = c) (_hlenLimit : tLimit.length = c)
    (_hreg : ∀ a : I, RingTheory.Sequence.IsRegular Γ(V.obj (op a), ⊤) (t a))
    (_hregLimit : RingTheory.Sequence.IsRegular Γ(v.pt, ⊤) tLimit)
    (_hcut : ∀ a : I, Ideal.ofList (t a) = RingHom.ker (i.app (op a)).appTop.hom)
    (_hcutLimit : Ideal.ofList tLimit = RingHom.ker j.appTop.hom)
    (_ht : ∀ (a b : I) (h : a ≤ b),
      (t a).map (V.map (homOfLE h).op).appTop.hom = t b)
    (_htLimit : ∀ a : I, (t a).map (v.π.app (op a)).appTop.hom = tLimit)
    (hV : ∀ a : I, IsUnit ((ℓ ^ 1 : ℕ) : Γ(V.obj (op a), ⊤))) :
    (∀ q m : ℤ,
      TransverseContinuity
        (fun a ↦ transverseSupportedGroup ℓ (i.app (op a)) q m)
        (transverseSupportedGroup ℓ j q m)
        (transverseSupportedProjection ℓ hℓ i z v j hj hV
          (transverseUnitPullback ℓ (v.π.app (op a₀)) (hV a₀)) q m)
        (transverseSupportedTransition ℓ hℓ i hV q m) ∧
      TransverseContinuity
        (fun a ↦ transverseOrdinaryGroup ℓ (Z.obj (op a)) q m)
        (transverseOrdinaryGroup ℓ z.pt q m)
        (fun a ↦ transverseOrdinaryPullback ℓ hℓ (z.π.app (op a))
          (transverseUnitPullback ℓ (i.app (op a)) (hV a))
          (transverseUnitPullback ℓ j
            (transverseUnitPullback ℓ (v.π.app (op a₀)) (hV a₀))) q m)
        (fun a b h ↦ transverseOrdinaryPullback ℓ hℓ (Z.map (homOfLE h).op)
          (transverseUnitPullback ℓ (i.app (op a)) (hV a))
          (transverseUnitPullback ℓ (i.app (op b)) (hV b)) q m)) ∧
    (∀ (q : ℤ) (a b : I) (h : a ≤ b)
      (x : transverseOrdinaryGroup ℓ (Z.obj (op a)) q 0),
      transverseSupportedTransition ℓ hℓ i hV (q + 2 * (c : ℤ)) c a b h
          (transverseGysin ℓ hℓ (i.app (op a)) c (hV a) q x) =
        transverseGysin ℓ hℓ (i.app (op b)) c (hV b) q
          (transverseOrdinaryPullback ℓ hℓ (Z.map (homOfLE h).op)
            (transverseUnitPullback ℓ (i.app (op a)) (hV a))
            (transverseUnitPullback ℓ (i.app (op b)) (hV b)) q 0 x)) ∧
    (∀ (q : ℤ) (a : I) (x : transverseOrdinaryGroup ℓ (Z.obj (op a)) q 0),
      transverseSupportedProjection ℓ hℓ i z v j hj hV
          (transverseUnitPullback ℓ (v.π.app (op a₀)) (hV a₀))
          (q + 2 * (c : ℤ)) c a
          (transverseGysin ℓ hℓ (i.app (op a)) c (hV a) q x) =
        transverseGysin ℓ hℓ j c
          (transverseUnitPullback ℓ (v.π.app (op a₀)) (hV a₀)) q
          (transverseOrdinaryPullback ℓ hℓ (z.π.app (op a))
            (transverseUnitPullback ℓ (i.app (op a)) (hV a))
            (transverseUnitPullback ℓ j
              (transverseUnitPullback ℓ (v.π.app (op a₀)) (hV a₀))) q 0 x)) := by
  sorry

end AlgebraicGeometry.Etale
