/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Exact.Basic
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.Topology.PresheafModuleStalkFunctor

/-! # Finite presentations of module stalks

Source: Stacks Project, Modules, Lemma 01CP, third paragraph.
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

/-- A finite local presentation gives a finite presentation of the source stalk,
with basis vectors sent to germs of the local generating sections.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`), third
paragraph, the last displayed right exact sequence; Definition 01BN.
(blueprint: lem-weil-pbc-finite-presentation-source-stalk)

Proof: Choose a finite presentation P of F on an open neighborhood U of x from
IsFinitePresentation.exists_quasicoherentData and its covering property. Reindex
its finite generator and relation sets by Fin n and Fin m. Let s_i be the values
at U of its generating sections. Restriction to U does not change stalks at x,
since the neighborhoods contained in U are cofinal. The component-germ maps
identify the stalk of a finite free sheaf with the corresponding finite power
of O_x: finitely many germs have simultaneous representatives, and finitely
many equalities of germs hold on a common neighborhood. Apply exactness of
module stalks to P.isColimit, transporting the resulting maps through these
finite free identifications. This gives a and b, surjectivity of b, and
exactness of a,b. The generator formula follows from functoriality of germs.
For an empty generator or relation set the same construction uses the zero
module, and no representatives need to be chosen. -/
theorem exists_finitePresentation_source_stalk
    (X : RingedSpace.{u})
    (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf))
    [SheafOfModules.IsFinitePresentation.{u} F] (x : X) :
    ∃ (U : Opens X) (hxU : x ∈ U) (m n : ℕ) (s : Fin n → F.val.obj (op U))
      (a : (Fin m → X.presheaf.stalk x) →ₗ[X.presheaf.stalk x]
        (Fin n → X.presheaf.stalk x))
      (b : (Fin n → X.presheaf.stalk x) →ₗ[X.presheaf.stalk x]
        (moduleStalkFunctor X x).obj F),
      Function.Surjective b ∧ Function.Exact a b ∧
      (∀ i, b (Pi.single i 1) = TopCat.Presheaf.germ F.val.presheaf U x hxU (s i)) := by
  sorry

end AlgebraicGeometry.RingedSpace
