/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import WeilConjectures.AlgebraicGeometry.SmoothArtinianLiftingAtPoint

/-! # Pointwise smoothness from étale-local Artinian lifts

Source: Stacks Project, More on Morphisms of Spaces, Tags 0APN and 04AM
(blueprint: lem-sfb-space-artinian-etale-lift-smooth-point).

The scheme `S` is represented by `schemeSpace (Over.mk (𝟙 S))`. Test maps and their
restrictions live in `Over S`, which enforces compatibility with the maps to `S`.
Smoothness on the open subfunctor is written directly on its étale scheme charts.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Étale-local solutions of all centered Artinian square-zero lifting problems imply
smoothness on an open neighbourhood of the specified point.
Source: Stacks, Tags 0APN and 04AM
(blueprint: lem-sfb-space-artinian-etale-lift-smooth-point).

Proof:
1. A surjective ring map with square-zero kernel defines an affine first order thickening
   (def-sbc-first-order-thickening). For a centered test, apply
   lem-sfb-space-infinitesimal-lift-pseudotorsor to obtain the sheaf of compatible lifts and
   its simply transitive action by a quasi-coherent module. The hypothesized local lifts
   make this a torsor in the sense of def-sc-gm-torsor.
2. By lem-sc-etale-affine-qcoherent, its acting module has vanishing first étale cohomology
   on the affine test scheme. By lem-sc-torsor-h1, the torsor is trivial. Its zero section
   therefore gives a global compatible lift for each centered Artinian test.
3. Choose a surjective étale scheme chart and a point above the specified point, using
   def-trf-algebraic-space. Local finite presentation on charts gives local finite
   presentation for the composite to S. By lem-sfb-stack-chartwise-smooth-etale-calculus,
   this composite is locally of finite type and the étale chart is smooth.
4. Given an Artinian test at the chart point, compose with the chart and use step 2.
   Apply lem-sfb-smooth-space-affine-infinitesimal-lift to lift the resulting map through
   the smooth chart, compatibly with the original map on the closed test scheme.
5. In particular all small-extension tests lift. Apply
   lem-weil-pbc-smooth-artinian-lifting-at-point over the locally Noetherian base to obtain
   smoothness near the chart point. Then lem-sfb-space-smooth-source-point-locality descends
   it to the original point and supplies its smooth open neighbourhood. -/
theorem smooth_near_of_artinian_etale_lifting
    {S : Scheme.{u}} [IsLocallyNoetherian S] (X : AlgebraicSpace S)
    (f : X ⟶ schemeSpace (Over.mk (𝟙 S)))
    (hfp : MapIsLocallyOfFinitePresentation f) (x : Point X.obj.obj)
    (hlift : ∀ (B' B : Type u) [CommRing B'] [CommRing B]
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (φ : B' →+* B), Function.Surjective φ → (RingHom.ker φ) ^ 2 = ⊥ →
      ∀ (c : Spec (CommRingCat.of B') ⟶ S)
        (a : yoneda.obj (Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ c)) ⟶ X.obj.obj),
        schemePointMap a (IsLocalRing.closedPoint B) = x →
        ∃ (I : Type u) (T : I → Over S) (q : ∀ i, T i ⟶ Over.mk c),
          (∀ i, Etale (q i).left) ∧
          (∀ y : Spec (CommRingCat.of B'), ∃ (i : I) (z : (T i).left),
            (q i).left z = y) ∧
          ∀ i, ∃ b : yoneda.obj (T i) ⟶ X.obj.obj,
            yoneda.map (Limits.pullback.fst (q i)
              (Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl :
                Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ c) ⟶ Over.mk c)) ≫ b =
            yoneda.map (Limits.pullback.snd (q i)
              (Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl :
                Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ c) ⟶ Over.mk c)) ≫ a) :
    ∃ V : OpenSubspace X, x ∈ pointImage V.val.ι ∧
      ∀ (U : Over S) (a : yoneda.obj U ⟶ V.val.toFunctor), IsEtale a → Smooth U.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
