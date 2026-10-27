/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.AlgebraicGeometry.SchemeActionTorsorGroupoids
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids

/-! # The affine action quotient and its chosen scheme-torsor pullbacks

Source: Stacks Project, examples-stacks.tex, Situation 04WL and Proposition 04WM;
spaces-groupoids.tex, Tag 044Q (blueprint: def-sfb-affine-action-quotient-stack).

The total category and its projection reuse `SchemeAction.torsorGroupoid`.
The constructions below supply its specified fibre-product pullbacks, the canonical
map from the action scheme, and maps to algebraic spaces modulo vertical isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.SchemeAction

variable {S : Scheme.{u}} (G V : Over S) [GrpObj G] [ModObj G V]

/-- Compatibility needed to lift the action to the actual fibre product.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack).
Proof: invariance of the torsor projection removes the group coordinate; the
remaining equality is the pullback condition, precomposed with the second projection. -/
theorem pullback_action_compatible (X : TorsorObject G V) (T : Over S) (h : T ⟶ X.base) :
    (lift (fst G (pullback X.projection h))
      (snd G (pullback X.projection h) ≫ pullback.fst X.projection h) ≫
        ModObj.smul (M := G) (X := X.space)) ≫ X.projection =
      (snd G (pullback X.projection h) ≫ pullback.snd X.projection h) ≫ h := by
  sorry

/-- The induced action is `(g,(p,t)) ↦ (g • p,t)` on every test scheme.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack). -/
def torsorPullbackActionMap (X : TorsorObject G V) (T : Over S) (h : T ⟶ X.base) :
    G ⊗ pullback X.projection h ⟶ pullback X.projection h :=
  pullback.lift
    (lift (fst G (pullback X.projection h))
      (snd G (pullback X.projection h) ≫ pullback.fst X.projection h) ≫
        ModObj.smul (M := G) (X := X.space))
    (snd G (pullback X.projection h) ≫ pullback.snd X.projection h)
    (pullback_action_compatible G V X T h)

/-- The prescribed action on the fibre product is unital and associative.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack).
Proof: compose with the two pullback projections. On the first projection the
identities are the original action laws; on the second they are identities.
Joint monicity of the pullback projections proves both equations. -/
theorem pullback_action_laws (X : TorsorObject G V) (T : Over S) (h : T ⟶ X.base) :
    (MonObj.one (X := G) ▷ pullback X.projection h) ≫
        torsorPullbackActionMap G V X T h = (λ_ (pullback X.projection h)).hom ∧
    (MonObj.mul (X := G) ▷ pullback X.projection h) ≫
        torsorPullbackActionMap G V X T h =
      (α_ G G (pullback X.projection h)).hom ≫
        G ◁ torsorPullbackActionMap G V X T h ≫ torsorPullbackActionMap G V X T h := by
  sorry

/-- The action structure has the specified action morphism, not a chosen unknown map.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack). -/
@[instance_reducible]
def torsorPullbackAction (X : TorsorObject G V) (T : Over S) (h : T ⟶ X.base) :
    ModObj G (pullback X.projection h) where
  smul := torsorPullbackActionMap G V X T h
  one_smul := (pullback_action_laws G V X T h).1
  mul_smul := (pullback_action_laws G V X T h).2

/-- The specified pullback is again a torsor with an equivariant map to `V`.
Source: Stacks 04WM, 044Q (blueprint: def-sfb-affine-action-quotient-stack).
Proof: the second projection is unchanged by the action, proving invariance.
Pull back a covering sieve and each equivariant local trivialization of `X`;
fppf coverings are stable under base change, and pasting pullback squares gives
the required local trivializations. Equivariance of the map to `V` is the original
equivariance equation after composition with the first projection. -/
theorem pullback_object_laws (X : TorsorObject G V) (T : Over S) (h : T ⟶ X.base) :
    (∀ (W : Over S) (g : W ⟶ G) (p : W ⟶ pullback X.projection h),
      (lift g p ≫ torsorPullbackActionMap G V X T h) ≫ pullback.snd X.projection h =
        p ≫ pullback.snd X.projection h) ∧
    @IsLocallyTrivial S G _ T (pullback X.projection h)
      (torsorPullbackAction G V X T h) (pullback.snd X.projection h) ∧
    (∀ (W : Over S) (g : W ⟶ G) (p : W ⟶ pullback X.projection h),
      (lift g p ≫ torsorPullbackActionMap G V X T h) ≫
          (pullback.fst X.projection h ≫ X.map) =
        g • (p ≫ (pullback.fst X.projection h ≫ X.map))) := by
  sorry

/-- Chosen pullback `(P ×_T T',f ∘ pr_P)` with its induced action.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack). -/
def torsorPullback (X : TorsorObject G V) (T : Over S) (h : T ⟶ X.base) :
    TorsorObject G V where
  base := T
  space := pullback X.projection h
  action := torsorPullbackAction G V X T h
  projection := pullback.snd X.projection h
  invariant := (pullback_object_laws G V X T h).1
  local_trivial := (pullback_object_laws G V X T h).2.1
  map := pullback.fst X.projection h ≫ X.map
  equivariant := (pullback_object_laws G V X T h).2.2

/-- The first projection of the chosen pullback is equivariant.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack).
Proof: compose the defining pullback lift for the induced action with its first
projection. Its defining equation is precisely equivariance on every test scheme. -/
theorem pullback_projection_equivariant
    (X : TorsorObject G V) (T : Over S) (h : T ⟶ X.base) :
    ∀ (W : Over S) (g : W ⟶ G) (p : W ⟶ (torsorPullback G V X T h).space),
      (g • p) ≫ pullback.fst X.projection h =
        g • (p ≫ pullback.fst X.projection h) := by
  sorry

/-- Chosen cartesian arrow has torsor map exactly `pr_P` and base map exactly `h`.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack). -/
def torsorPullbackArrow (X : TorsorObject G V) (T : Over S) (h : T ⟶ X.base) :
    torsorPullback G V X T h ⟶ X :=
  ⟨h, pullback.fst X.projection h, IsPullback.of_hasPullback X.projection h,
    pullback_projection_equivariant G V X T h, rfl⟩

/-- Compatibility defining `r × id` for a vertical torsor arrow.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack).
Proof: use the commutativity of the cartesian square of `r`, then the two
pullback conditions and the hypothesis identifying the two maps to the base. -/
theorem pullback_map_compatible {X Y : TorsorObject G V} (r : X ⟶ Y)
    (T : Over S) (hX : T ⟶ X.base) (hY : T ⟶ Y.base) (w : hX ≫ r.base = hY) :
    (pullback.fst X.projection hX ≫ r.map) ≫ Y.projection =
      pullback.snd X.projection hX ≫ hY := by
  sorry

/-- Pullback on vertical arrows: the actual fibre-product map `r ×_T id`.
Allowing `hY = hX ≫ r.base` also supplies composition of pullback comparisons.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack). -/
def torsorPullbackMap {X Y : TorsorObject G V} (r : X ⟶ Y)
    (T : Over S) (hX : T ⟶ X.base) (hY : T ⟶ Y.base) (w : hX ≫ r.base = hY) :
    (torsorPullback G V X T hX).space ⟶ (torsorPullback G V Y T hY).space :=
  pullback.lift (pullback.fst X.projection hX ≫ r.map) (pullback.snd X.projection hX)
    (pullback_map_compatible G V r T hX hY w)

/-- The prescribed pullback map is a vertical arrow of torsors.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack).
Proof: pasting the square of `r` with the two fibre-product squares shows that
`r × id` is cartesian. Its equivariance follows after both pullback projections;
its compatibility with the maps to `V` follows from `r.commutes`.
The identity and composition formulas follow from these same two projections. -/
theorem pullback_map_laws {X Y : TorsorObject G V} (r : X ⟶ Y)
    (T : Over S) (hX : T ⟶ X.base) (hY : T ⟶ Y.base) (w : hX ≫ r.base = hY) :
    IsPullback (torsorPullbackMap G V r T hX hY w)
      (torsorPullback G V X T hX).projection
      (torsorPullback G V Y T hY).projection (𝟙 T) ∧
    (∀ (W : Over S) (g : W ⟶ G) (p : W ⟶ (torsorPullback G V X T hX).space),
      (g • p) ≫ torsorPullbackMap G V r T hX hY w =
        g • (p ≫ torsorPullbackMap G V r T hX hY w)) ∧
    torsorPullbackMap G V r T hX hY w ≫ (torsorPullback G V Y T hY).map =
      (torsorPullback G V X T hX).map := by
  sorry

/-- The induced arrow on the chosen pullbacks, over the identity of the new base.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack). -/
def torsorPullbackHom {X Y : TorsorObject G V} (r : X ⟶ Y)
    (T : Over S) (hX : T ⟶ X.base) (hY : T ⟶ Y.base) (w : hX ≫ r.base = hY) :
    torsorPullback G V X T hX ⟶ torsorPullback G V Y T hY :=
  ⟨𝟙 T, torsorPullbackMap G V r T hX hY w,
    (pullback_map_laws G V r T hX hY w).1,
    (pullback_map_laws G V r T hX hY w).2.1,
    (pullback_map_laws G V r T hX hY w).2.2⟩

/-- The actual fibre category, with vertical cartesian equivariant arrows.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack). -/
abbrev torsorFiber (T : Over S) := Functor.Fiber (torsorGroupoid G V).p T

/-- Every arrow of a fibre is invertible, rather than merely passing to a core.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack).
Proof: a cartesian square over the identity makes the torsor map an isomorphism.
Its inverse is equivariant by composing the equivariance equation with the inverse,
and it preserves the map to `V` by the commuting triangle. Both inverse equations
hold for scheme maps, hence for torsor arrows and their vertical subtypes. -/
theorem torsor_fiber_isGroupoid (T : Over S) : IsGroupoid (torsorFiber G V T) := by
  sorry

/-- Transport of the base equation of a vertical arrow.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack).
Proof: the hom-lift condition says the base map is the identity conjugated by
the two object equalities. Compose with `h` and cancel the equality transports. -/
theorem fiber_pullback_compatible {T T' : Over S} (h : T' ⟶ T)
    {X Y : torsorFiber G V T} (r : X ⟶ Y) :
    (h ≫ eqToHom X.property.symm) ≫ r.val.base = h ≫ eqToHom Y.property.symm := by
  sorry

/-- Pullback of a fibre object uses exactly the chosen fibre product.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack). -/
def torsorFiberPullbackObj {T T' : Over S} (h : T' ⟶ T) (X : torsorFiber G V T) :
    torsorFiber G V T' :=
  ⟨torsorPullback G V X.val T' (h ≫ eqToHom X.property.symm), rfl⟩

/-- Pullback of a fibre arrow uses exactly `r × id`.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack). -/
def torsorFiberPullbackMap {T T' : Over S} (h : T' ⟶ T)
    {X Y : torsorFiber G V T} (r : X ⟶ Y) :
    torsorFiberPullbackObj G V h X ⟶ torsorFiberPullbackObj G V h Y :=
  ⟨torsorPullbackHom G V r.val T'
      (h ≫ eqToHom X.property.symm) (h ≫ eqToHom Y.property.symm)
      (fiber_pullback_compatible G V h r),
    by
      apply IsHomLift.of_fac (torsorGroupoid G V).p (𝟙 T') _ rfl rfl
      rfl⟩

/-- Pullback preserves identities and composition in the fibre categories.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack).
Proof: compare the two maps after both pullback projections. The first gives
`id` or the composite of the original scheme maps, and the second gives the
identity of the new base. The pullback universal property and subtype extensionality
prove the equations. Equality transports cancel by proof irrelevance. -/
theorem fiber_pullback_functor_laws {T T' : Over S} (h : T' ⟶ T) :
    (∀ X : torsorFiber G V T, torsorFiberPullbackMap G V h (𝟙 X) =
      𝟙 (torsorFiberPullbackObj G V h X)) ∧
    (∀ {X Y Z : torsorFiber G V T} (r : X ⟶ Y) (s : Y ⟶ Z),
      torsorFiberPullbackMap G V h (r ≫ s) =
        torsorFiberPullbackMap G V h r ≫ torsorFiberPullbackMap G V h s) := by
  sorry

/-- The chosen pullback functor on fibres, on both objects and arrows.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack). -/
def torsorPullbackFunctor {T T' : Over S} (h : T' ⟶ T) :
    torsorFiber G V T ⥤ torsorFiber G V T' where
  obj := torsorFiberPullbackObj G V h
  map := torsorFiberPullbackMap G V h
  map_id := (fiber_pullback_functor_laws G V h).1
  map_comp := (fiber_pullback_functor_laws G V h).2

/-- The representable discrete groupoid maps to the action groupoid with identity labels.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack). -/
def schemeToActionGroupoid :
    BasedFunctor (discreteModuli (yoneda.obj V)) (actionGroupoid G V) where
  obj X := ⟨X.left, yoneda.preimage X.hom⟩
  map {X Y} a := ⟨a.left, 1, by
    rw [one_smul]
    apply yoneda.map_injective
    simp only [Functor.map_comp, Functor.map_preimage]
    exact (CostructuredArrow.w a).symm⟩
  map_id X := ActionHom.ext rfl rfl
  map_comp a b := ActionHom.ext rfl (by
    change (1 : _ ⟶ G) = (a.left ≫ (1 : _ ⟶ G)) * 1
    simp)
  w := rfl

/-- The canonical map sends `x` to `(G × T,(g,t) ↦ g • x(t))`.
On a base arrow it is `(g,t') ↦ (g,h(t'))`, since the action label is the identity.
Source: Stacks 04WM (blueprint: def-sfb-affine-action-quotient-stack). -/
def quotientAtlas :
    BasedFunctor (discreteModuli (yoneda.obj V)) (torsorGroupoid G V) :=
  (schemeToActionGroupoid G V).comp (trivialTorsorFunctor G V)

/-- Maps to an algebraic space are based functors modulo natural isomorphisms over the base.
Source: Stacks 04WM, 044Q (blueprint: def-sfb-affine-action-quotient-stack). -/
def quotientSpaceMapSetoid (Z : AlgebraicSpace S) :
    Setoid (BasedFunctor (torsorGroupoid G V) (discreteModuli Z.obj.obj)) where
  r F H := Nonempty (F ≅ H)
  iseqv := ⟨fun _ ↦ ⟨Iso.refl _⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩,
    fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩⟩

/-- The set of maps `[V/G] → Z`, retaining exactly the equivalence specified in the node.
Source: Stacks 04WM, 044Q (blueprint: def-sfb-affine-action-quotient-stack). -/
def quotientSpaceMaps (Z : AlgebraicSpace S) :=
  Quotient (quotientSpaceMapSetoid G V Z)

end AlgebraicGeometry.SchemeAction

namespace AlgebraicGeometry

/-- The affine `k`-scheme `Spec E` with its actual algebra structure morphism.
Source: Stacks 04WL (blueprint: def-sfb-affine-action-quotient-stack). -/
def affineActionScheme (k E : Type u) [Field k] [CommRing E] [Algebra k E] :
    Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k E)))

/-- The specified affine quotient is the existing scheme-torsor total category,
including its projection to the big fppf site. `ModObj` supplies precisely the
left action with its unit and associativity diagrams. Finite type is the
recorded conjunction of local finite type and quasi-compactness.
Source: Stacks 04WL, 04WM, 044Q (blueprint: def-sfb-affine-action-quotient-stack). -/
def affineActionQuotientStack (k E : Type u) [Field k] [CommRing E] [Algebra k E]
    [Algebra.FiniteType k E] (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
    [Smooth G.hom] [IsAffineHom G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [ModObj G (affineActionScheme k E)] : BasedCategory (Over (Spec (CommRingCat.of k))) :=
  SchemeAction.torsorGroupoid G (affineActionScheme k E)

end AlgebraicGeometry
