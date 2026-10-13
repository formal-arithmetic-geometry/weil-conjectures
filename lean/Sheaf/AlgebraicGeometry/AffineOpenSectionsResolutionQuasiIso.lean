/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechTotalComplex
public import Sheaf.AlgebraicGeometry.Coherent

/-! # Affine sections of an unbounded quasi-coherent resolution

Source: Stacks Project, Cohomology, Lemma 08C2, with affine vanishing 01XB.
(blueprint: lem-sc-affine-open-sections-resolution-quasi-iso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The global-ring module presheaf functor is additive.
Source: Stacks Project, 08C2 (blueprint: lem-sc-affine-open-sections-resolution-quasi-iso).
Proof: its maps apply the given module map on each open; addition is componentwise. -/
instance alternatingCechModulePresheaf_additive (X : Scheme.{u}) :
    (alternatingCechModulePresheaf (X := X)).Additive where
  map_add := by
    intro F G f g
    ext V x
    rfl

/-- Evaluating a resolution map on an affine open gives a quasi-isomorphism of
complexes of modules over the global section ring.

Source: Stacks Project, Cohomology, Lemma 08C2, and Cohomology of Schemes, 01XB.
(blueprint: lem-sc-affine-open-sections-resolution-quasi-iso).

Proof: Restrict F, J and i to V. Open restriction is exact and preserves
K-injectivity (08BS), so the restricted i is still a K-injective resolution.
Restriction preserves quasi-coherence. Kernels, images and cokernels of maps
between quasi-coherent modules are quasi-coherent. On the basis of affine
opens of V, the terms, differential cokernels, and cohomology sheaves of F
therefore all have vanishing higher cohomology by 01XB. Apply 08C2 to this
basis and the singleton cover of V by itself: all three acyclicity conditions
in that lemma hold, including those on differential cokernels and cohomology.
For the unbounded case, use good truncations tau_ge(-n): the cokernel
vanishing verifies the bounded-below hypotheses. Choose the compatible
K-injective resolution tower of 08C2; its section cohomology is eventually
constant in each degree because the singleton Cech complex has only one
column. The Mittag-Leffler argument in 08C2 identifies the cohomology of
the inverse limit with that constant value. This proves the unbounded
comparison without assuming sections preserve arbitrary quasi-isomorphisms.
It identifies the ordinary section complex of F with its derived sections,
by the actual ordinary-to-derived comparison. Compute derived sections using
the restricted resolution J; compatibility with this comparison identifies
the map with the ordinary sections of i. One may first use a K-injective
resolution with injective terms, then compare it with J by a homotopy
equivalence; the additive section functor preserves that equivalence.
Finally restrict scalars along Gamma(X,O_X) to Gamma(V,O_X). This is exact
and preserves the underlying homology isomorphisms. This gives precisely the
presheaf evaluation in the conclusion. For empty V, both section complexes
are zero. No boundedness or quasi-coherence of the terms of J is needed. -/
theorem affineOpenSections_resolution_quasiIso
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    (F J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    [J.IsKInjective] (i : F ⟶ J) [QuasiIso i] :
    QuasiIso (((alternatingCechModulePresheaf (X := X) ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))).obj
          (op V)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map i) := by sorry

end AlgebraicGeometry
