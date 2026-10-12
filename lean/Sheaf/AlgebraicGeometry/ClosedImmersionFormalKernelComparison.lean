module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Whiskering

import Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Closed pushforward identifies the underlying inverse system of a categorical
formal kernel, without asserting that evaluation preserves kernels.

Source: Stacks Project, Tags 087T, 087W, 087X and proof of Theorem 088E.
(blueprint: aux-closed-immersion-formal-kernel-comparison)

Proof: On each Noetherian affine Spec A in X, write the closed inverse image as
Spec(A/J). The affine formal-module equivalence identifies systems with finite
modules over the completions of A and A/J. The latter completion is the quotient
of the former by the extended J. Termwise pushforward corresponds to restriction
of scalars: the inverse limits and their transition maps are unchanged as sets.
Restriction of scalars preserves kernels, and the kernel of a map of finite modules
is finite because the completed ring is Noetherian. Thus its reductions give the
same formal system before and after closed pushforward. The affine identifications
are canonical on kernels and commute with restriction to smaller affine opens;
local exactness glues them to the pushed kernel fork. The square supplied by e and d
identifies that fork with a kernel fork of a. Uniqueness of limiting kernel forks
then gives the stated inverse-system isomorphism. This uses only the kernel universal
property, so is independent of the chosen Abelian structure. -/
theorem closedImmersion_formalKernel_comparison
    {X Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Z]
    (j : Z ⟶ X) [IsClosedImmersion j] (Q : X.IdealSheafData)
    [Abelian (CoherentFormalModule X Q)]
    (M N : CoherentFormalModule X Q)
    (G D : CoherentFormalModule Z (Q.comap j))
    (a : M ⟶ N) (α : G ⟶ D)
    (e : M.obj ≅ G.obj ⋙ Scheme.Modules.pushforward j)
    (d : N.obj ≅ D.obj ⋙ Scheme.Modules.pushforward j)
    (hsquare : a.hom ≫ d.hom =
      e.hom ≫ Functor.whiskerRight α.hom (Scheme.Modules.pushforward j))
    (k : KernelFork α) (hk : IsLimit k) :
    Nonempty ((kernel a).obj ≅ k.pt.obj ⋙ Scheme.Modules.pushforward j) := by sorry

end AlgebraicGeometry
