/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Exact.Basic
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomFinitePresentationKernel
import Sheaf.Algebra.Homology.ModuleStalkExact

/-!
# A local finite presentation and its internal-Hom stalk kernel

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`), third paragraph
(blueprint: lem-weil-pbc-finite-presentation-stalk-kernel).
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

/-- A local finite presentation supplies a presentation of the source stalk and
an injective coordinate map on the internal-Hom stalk, with the indicated kernel image.
It does not construct or assert bijectivity of the canonical stalk-Hom map.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`), third paragraph,
using Lemma 01CO (1) for the internal-Hom exact sequence.
(blueprint: lem-weil-pbc-finite-presentation-stalk-kernel)

Proof: Choose a finite free presentation on a neighborhood U of x from
IsFinitePresentation, with basis images s_i in F(U). Identify the stalks of the two
free modules with tuples over O_x by taking component germs. Finite tuples have
representatives on a common neighborhood, and equalities of their germs likewise
hold on a common neighborhood; this proves these identifications are bijective.
Exactness of module stalks gives maps a and b with b surjective and ker(b) = range(a).
Apply homObj_finitePresentation_kernel to the local presentation. Identify the stalk
of its finite product of copies of G with tuples in G_x by the same common-neighborhood
argument. The resulting map beta is injective, and its image is the kernel of
precomposition by a, transported through the finite free evaluation isomorphisms.
The displayed formula for beta follows by taking germs of the sectionwise evaluation
formula in homObj_finitePresentation_kernel. Restriction to U does not change any
stalk at x: its neighborhoods are cofinal among those in X, and restricting internal
Hom has the same local-morphism sections. Hence this formula holds for every W,
using the neighborhood U intersect W and the restricted basis sections. -/
theorem exists_finitePresentation_stalk_kernel
    (X : RingedSpace.{u})
    (F G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf))
    [SheafOfModules.IsFinitePresentation.{u} F] (x : X) :
    ∃ (U : Opens X) (hxU : x ∈ U) (m n : ℕ) (s : Fin n → F.val.obj (op U))
      (a : (Fin m → X.presheaf.stalk x) →ₗ[X.presheaf.stalk x]
        (Fin n → X.presheaf.stalk x))
      (b : (Fin n → X.presheaf.stalk x) →ₗ[X.presheaf.stalk x]
        (moduleStalkFunctor X x).obj F)
      (β : (moduleStalkFunctor X x).obj (F.homObj G) →ₗ[X.presheaf.stalk x]
        (Fin n → (moduleStalkFunctor X x).obj G)),
      Function.Surjective b ∧ Function.Exact a b ∧
      (∀ i, b (Pi.single i 1) = TopCat.Presheaf.germ F.val.presheaf U x hxU (s i)) ∧
      Function.Injective β ∧
      LinearMap.range β = LinearMap.ker
        (((LinearEquiv.piRing (X.presheaf.stalk x)
          ((moduleStalkFunctor X x).obj G) (Fin m) (X.presheaf.stalk x)).toLinearMap).comp
          ((LinearMap.lcomp (X.presheaf.stalk x) ((moduleStalkFunctor X x).obj G) a).comp
            (LinearEquiv.piRing (X.presheaf.stalk x)
              ((moduleStalkFunctor X x).obj G) (Fin n) (X.presheaf.stalk x)).symm.toLinearMap)) ∧
      (∀ (W : Opens X) (hxW : x ∈ W) (φ : (F.homObj G).val.obj (op W)) (i : Fin n),
        β (TopCat.Presheaf.germ (F.homObj G).val.presheaf W x hxW φ) i =
          TopCat.Presheaf.germ G.val.presheaf (U ⊓ W) x ⟨hxU, hxW⟩
            (φ.app (op (Over.mk (homOfLE inf_le_right : U ⊓ W ⟶ W)))
              (F.val.presheaf.map (homOfLE inf_le_left : U ⊓ W ⟶ U).op (s i)))) := by
  sorry

end AlgebraicGeometry.RingedSpace
