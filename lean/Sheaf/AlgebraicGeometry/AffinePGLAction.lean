/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.AlgebraicGeometry.PGLLinearizedPolarization
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Affine PGL actions and their invariant spectra

Source: Alper, arXiv:1005.2398v3, Theorem 9.1.4 and Remark 9.1.5;
Mumford--Fogarty--Kirwan, GIT, Chapter 1, §1
(blueprint: def-sfb-affine-pgl-action).

Natural GL actions with trivial scalar action descend along the fppf quotient
GL → PGL. Testing functions on every scheme detects the full coaction, including
nilpotents. No linearization or auxiliary line module is part of the data.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AffinePGL

variable (k : Type u) [Field k] (E : Type u) [CommRing E] [Algebra k E]

/-- Spec E with its given k-structure. Source: Alper, Remark 9.1.5
(blueprint: def-sfb-affine-pgl-action). -/
noncomputable def affineOver : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k E)))

/-- A PGL action by natural GL actions with trivial scalars. Descent along the
fppf epimorphism GL → PGL recovers exactly a scheme action, even when PGL test
points have no global lift. Source: MFK, GIT, Chapter 1, §1
(blueprint: def-sfb-affine-pgl-action). -/
structure Action (r : ℕ) where
  act : ∀ (T : Over (Spec (.of k))), PGLLinearization.Matrices k r T →
    (T ⟶ affineOver k E) → (T ⟶ affineOver k E)
  one_act : ∀ (T : Over (Spec (.of k))) (x : T ⟶ affineOver k E), act T 1 x = x
  mul_act : ∀ (T : Over (Spec (.of k))) (g h : PGLLinearization.Matrices k r T)
    (x : T ⟶ affineOver k E), act T (g * h) x = act T g (act T h x)
  scalar_act : ∀ (T : Over (Spec (.of k))) (a : Γ(T.left, ⊤)ˣ)
    (x : T ⟶ affineOver k E),
    act T (Matrix.GeneralLinearGroup.scalar (Fin r) a) x = x
  naturality : ∀ (T V : Over (Spec (.of k))) (f : V ⟶ T)
    (g : PGLLinearization.Matrices k r T) (x : T ⟶ affineOver k E),
    act V (Matrix.GeneralLinearGroup.map f.left.appTop.hom g) (f ≫ x) = f ≫ act T g x

variable {k E} {r : ℕ}

/-- Evaluation of a coordinate function at a scheme-valued point. Source:
Alper, Remark 9.1.5 (blueprint: def-sfb-affine-pgl-action). -/
noncomputable def evaluation {T : Over (Spec (.of k))} (x : T ⟶ affineOver k E) :
    E →+* Γ(T.left, ⊤) :=
  x.left.appTop.hom.comp (Scheme.ΓSpecIso (.of E)).inv.hom

/-- Equalities after all scheme-valued translations define the invariant subring.
This is the coaction equalizer E^G, since equality of regular functions is tested
on all schemes and GL → PGL is an fppf epimorphism. Source: Alper, Remark 9.1.5
(blueprint: def-sfb-affine-pgl-action). -/
noncomputable def Action.invariants (D : Action k E r) : Subring E :=
  ⨅ (T : Over (Spec (.of k))) (g : PGLLinearization.Matrices k r T)
    (x : T ⟶ affineOver k E),
    RingHom.eqLocus (evaluation (D.act T g x)) (evaluation x)

/-- Constants are invariant under a k-action. Source: Alper, Remark 9.1.5
(blueprint: def-sfb-affine-pgl-action).
Proof: the two translated points are morphisms over Spec k. Their composites
with the structure map coincide. Apply global sections, then the natural
Gamma-Spec identification, to obtain equality on every element of k. Membership
in each equalizer, and hence their intersection, follows. -/
theorem Action.constants_mem (D : Action k E r) (c : k) :
    algebraMap k E c ∈ D.invariants := by
  simp only [Action.invariants, Subring.mem_iInf, RingHom.mem_eqLocus]
  intro T g x
  have he (y : T ⟶ affineOver k E) :
      evaluation y (algebraMap k E c) =
        T.hom.appTop ((Scheme.ΓSpecIso (.of k)).inv c) := by
    change ((CommRingCat.ofHom (algebraMap k E) ≫
      (Scheme.ΓSpecIso (.of E)).inv) ≫ y.left.appTop) c = _
    rw [Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      ← Scheme.Hom.comp_appTop]
    change ((Scheme.ΓSpecIso (.of k)).inv ≫
      (y.left ≫ (affineOver k E).hom).appTop) c = _
    rw [Over.w y]
    rfl
  exact (he _).trans (he _).symm

/-- The coefficient map is the restriction of the specified algebra map.
Source: Alper, Remark 9.1.5 (blueprint: def-sfb-affine-pgl-action). -/
noncomputable def Action.constants (D : Action k E r) : k →+* D.invariants :=
  (algebraMap k E).codRestrict D.invariants D.constants_mem

/-- The invariant spectrum over k, using the specified constants. Source: Alper,
Remark 9.1.5 (blueprint: def-sfb-affine-pgl-action). -/
noncomputable def Action.quotientOver (D : Action k E r) : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom D.constants))

/-- The invariant inclusion respects the specified coefficient maps.
Source: Alper, Remark 9.1.5 (blueprint: def-sfb-affine-pgl-action).
Proof: by definition, including the restricted coefficient map into E is the
original algebra map. Contravariance of Spec gives the displayed triangle. -/
theorem Action.quotientMap_over (D : Action k E r) :
    Spec.map (CommRingCat.ofHom D.invariants.subtype) ≫ D.quotientOver.hom =
      (affineOver k E).hom := by
  change Spec.map (CommRingCat.ofHom D.invariants.subtype) ≫
    Spec.map (CommRingCat.ofHom D.constants) =
      Spec.map (CommRingCat.ofHom (algebraMap k E))
  rw [← Spec.map_comp]
  rfl

/-- The quotient arrow is Spec of the actual invariant inclusion. Source: Alper,
Remark 9.1.5 (blueprint: def-sfb-affine-pgl-action). -/
noncomputable def Action.quotientMap (D : Action k E r) :
    affineOver k E ⟶ D.quotientOver :=
  Over.homMk (Spec.map (CommRingCat.ofHom D.invariants.subtype)) D.quotientMap_over

/-- Invariance of maps to an arbitrary algebraic space is tested on all schemes.
Source: Alper, §8.1 (blueprint: def-sfb-affine-pgl-action). -/
def Action.IsInvariantMap (D : Action k E r) (B : AlgebraicSpace (Spec (.of k)))
    (f : yoneda.obj (affineOver k E) ⟶ B.obj.obj) : Prop :=
  ∀ (T : Over (Spec (.of k))) (g : PGLLinearization.Matrices k r T)
    (x : T ⟶ affineOver k E), f.app (op T) (D.act T g x) = f.app (op T) x

end AlgebraicGeometry.AffinePGL
