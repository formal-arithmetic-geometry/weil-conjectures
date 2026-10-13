/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.Algebra.Homology.ModuleStalkFunctor

/-! # Spreading one linear map of stalks from a finitely presented source

Source: Stacks Project, Modules, Lemma 01CP, finite presentation argument.
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

/-- One specified stalk-linear map from a finitely presented source is induced
by a local morphism on a neighborhood. This only asserts existence of a lift;
it asserts neither uniqueness nor a comparison isomorphism.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`), third
paragraph, lifting an element of the displayed finite-coordinate kernel.
(blueprint: lem-weil-pbc-stalk-linear-map-local-lift-finite-presentation)

Proof: Choose a finite free presentation of F near x. Represent the images under
χ of its finitely many generator germs by sections of G on a common smaller
neighborhood. These sections define a morphism from the finite free generator
sheaf to G. Its composite with the finite free relation map has zero stalk,
since the generator-to-F map kills every relation. Each of its finitely many
basis images therefore vanishes after shrinking; intersect those neighborhoods.
The resulting composite is zero as a sheaf morphism. The cokernel universal
property of the presentation now descends this map to a local morphism φ from
F to G. Its stalk map agrees with χ on all generator germs, hence everywhere
because the presentation's stalk generator map is surjective. Naturality of
germs gives the displayed formula for every section over every subneighborhood.
Restriction does not change the stalk, by cofinality of subneighborhoods. Empty
finite sets require no shrinking, so zero source or zero target causes no exception. -/
theorem exists_local_internalHom_of_stalkLinearMap
    (X : RingedSpace.{u})
    (F G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf))
    [SheafOfModules.IsFinitePresentation.{u} F] (x : X)
    (χ : (moduleStalkFunctor X x).obj F →ₗ[X.presheaf.stalk x]
      (moduleStalkFunctor X x).obj G) :
    ∃ (U : Opens X) (hxU : x ∈ U) (φ : (F.homObj G).val.obj (op U)),
      ∀ (V : Opens X) (i : V ⟶ U) (hxV : x ∈ V) (s : F.val.obj (op V)),
        TopCat.Presheaf.germ G.val.presheaf V x hxV (φ.app (op (Over.mk i)) s) =
          χ (TopCat.Presheaf.germ F.val.presheaf V x hxV s) := by
  sorry

end AlgebraicGeometry.RingedSpace
