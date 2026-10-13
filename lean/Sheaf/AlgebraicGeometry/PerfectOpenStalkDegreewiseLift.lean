/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor

/-! # Extending degreewise maps between perfect open-site stalks

Source: Stacks Project, Tags 09RE and 01CP.
(blueprint: lem-sc-perfect-open-stalk-degreewise-lift).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Degreewise stalk maps extend on a common affine neighbourhood, without any
chain equations.

Source: Stacks Project, Tag 09RE, affine finite-presentation calculation, and
Tag 01CP, finite-presentation internal-Hom stalk comparison.
(blueprint: lem-sc-perfect-open-stalk-degreewise-lift).

Proof: Pass from the slice site over U to the open subscheme U. The finite-free
retractions make every term of P finitely presented. Apply the internal-Hom stalk
comparison to each component and represent its preimage by a section of internal
Hom near x. Such a section is a local sheaf morphism, giving the required local
map without any finiteness assumption on its target. Outside the finite support interval of P,
use zero maps, since the source is zero.
Intersect the finitely many neighbourhoods, then take an affine neighbourhood W
of x inside the intersection. Restrict all representatives to W. Cofinality of
neighbourhoods inside W and the open-immersion stalk-ring isomorphisms give a
natural isomorphism between restriction followed by the W stalk and the U stalk;
apply it termwise to obtain e. The germ formulas give the stated component
identities. Empty source support intervals and zero ranks require no representatives
and give the zero family. No perfectness assumption on Q or affineness
assumption on U is needed. No differential compatibility is imposed or asserted. -/
theorem exists_affine_perfect_open_stalk_degreewise_lift
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P)
    (t : ∀ n : ℤ,
      (((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj P).X n ⟶
      (((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj Q).X n) :
    ∃ (W : X.Opens) (hxW : x ∈ W) (_hW : IsAffineOpen W) (hWU : W ≤ U),
      let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S := (openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ)
      let T := (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)
      ∃ (e : R ⋙ S ≅ T) (g : ∀ n : ℤ, (R.obj P).X n ⟶ (R.obj Q).X n),
        ∀ n : ℤ, (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g n) =
          (e.app P).hom.f n ≫ t n ≫ (e.app Q).inv.f n := by sorry

end
end AlgebraicGeometry.Scheme
