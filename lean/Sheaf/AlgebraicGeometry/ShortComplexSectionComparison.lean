/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.Topology.RingedSpaceModuleCohomology
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence

/-! # The section comparison for a short complex

Source: Stacks Project, Tags 015B and 01E4.
(blueprint: lem-pc-short-complex-section-comparison)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

/-- First-cohomology vanishing of the incoming kernel and image suffices for the
canonical sheafification comparison of a short complex to be invertible on sections.
Source: Stacks Project, Tag 015B (degree-zero and degree-one exact sequence),
and Tag 01E4 (the canonical cocycle-to-sheaf-class comparison).
(blueprint: lem-pc-short-complex-section-comparison)

Proof: Put Z = ker(S.g), B = im(S.f), and L = ker(S.f). Restrict to V, which
preserves kernels, images and homology because open restriction is exact. In
0 -> L -> S.X1 -> B -> 0 the first-cohomology vanishing of L makes
Gamma(S.X1) -> Gamma(B) surjective. In 0 -> B -> Z -> S.homology -> 0 the
first-cohomology vanishing of B makes Gamma(Z) -> Gamma(S.homology) surjective
with kernel Gamma(B). Left exactness identifies Gamma(Z) with the kernel of
Gamma(S.g). Consequently Gamma(S.homology) is the cokernel of the incoming
map to that kernel, and the canonical homology comparison is an isomorphism.
Evaluation of a presheaf of modules followed by forgetting scalars is exact,
so its homology is precisely homology of the section short complex.
To identify the displayed arrow, commute exact sheafification with homology
using mapHomologyIso and apply the homology map of its counit at S. Under
the sheafification adjunction this sends a presheaf cycle class to the class
of the same cycle in S.homology: the unit sends the cycle to its sheafification,
and the counit returns it to S. This is also the map characterized by the
cokernel universal property above. Equality follows after precomposition with
the epimorphic homology projection from the cycles. Thus the displayed arrow,
including its specified adjunction normalization, is invertible. If S.f = 0,
its image is zero and the same proof applies; if V is empty all section groups
are zero. No boundedness or acyclicity of S.X2 or S.homology is required. -/
theorem shortComplex_sectionComparison_isIso
    {Y : Scheme.{u}} (S : ShortComplex (SheafOfModules.{u} Y.ringCatSheaf))
    (V : Y.Opens)
    (hkernel : IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace 1).obj
      ((restrictFunctor V.ι).obj (kernel S.f))))
    (himage : IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace 1).obj
      ((restrictFunctor V.ι).obj (image S.f)))) :
    IsIso (((PresheafOfModules.toPresheaf.{u} Y.ringCatSheaf.obj).map
      ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 Y.ringCatSheaf.obj)).homEquiv
        (S.map (SheafOfModules.forget.{u} Y.ringCatSheaf)).homology S.homology
        (((S.map (SheafOfModules.forget.{u} Y.ringCatSheaf)).mapHomologyIso
          (PresheafOfModules.sheafification.{u} (𝟙 Y.ringCatSheaf.obj))).inv ≫
          ShortComplex.homologyMap (S.mapNatTrans
            (PresheafOfModules.sheafificationAdjunction.{u}
              (𝟙 Y.ringCatSheaf.obj)).counit)))).app (op V)) := by sorry

end AlgebraicGeometry.Scheme.Modules
