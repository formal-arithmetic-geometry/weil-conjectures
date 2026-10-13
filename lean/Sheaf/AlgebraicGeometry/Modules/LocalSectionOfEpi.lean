/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- Local section of an epimorphism onto a finite locally free module.

Source: Stacks Project, Tag 0EKP, proof of (2) to (3), finite-basis lifting.
(blueprint: new-sbc-local-section-of-epi)

The proof chooses a finite local basis of the target, lifts its members locally using
local surjectivity of an epimorphism, and intersects the resulting finitely many opens.
Restrict every lift to this intersection and extend linearly from the finite free sheaf
using its coproduct universal property. The composite `s ≫ f|_U` fixes each basis
section, hence is the identity by free-sheaf extensionality. For rank zero the family
is empty: keep the trivializing open and use the unique map out of the zero sheaf.
No quasi-coherence of the source is needed, and the empty scheme has no points.
-/
theorem exists_local_section_of_epi
    {X : Scheme.{u}} {P Q : X.Modules} (f : P ⟶ Q) [Epi f] [Q.IsFiniteLocallyFree] :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ s : (restrictFunctor U.ι).obj Q ⟶ (restrictFunctor U.ι).obj P,
        s ≫ (restrictFunctor U.ι).map f = 𝟙 _ := by sorry


end AlgebraicGeometry.Scheme.Modules
