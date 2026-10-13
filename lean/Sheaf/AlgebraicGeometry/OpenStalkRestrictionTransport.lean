/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor

/-! # Transport of open-site stalk comparisons through further restriction

Source: Stacks Project, Sheaves Tag 00A0 (3), (5), and Tag 0096.
(blueprint: lem-sc-open-stalk-restriction-transport).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Choose comparison coordinates before any module or map. An arbitrary comparison
on an intermediate open can be transported through a further restriction.

Source: Stacks Project, Sheaves Tag 00A0 (3), (5), `lemma-restrict`, and Tag 0096,
`lemma-adjoint-pullback-pushforward-modules` (open-immersion pushforward).
(blueprint: lem-sc-open-stalk-restriction-transport).

Proof: Use the slice/open-subspace equivalences. The final functor of neighbourhoods
inside W gives the additive restriction-stalk isomorphism. Its germ formula,
checked on a common neighbourhood for a scalar and a vector, makes it linear
after the open-immersion stalk-ring scalar transports. The same formula proves
naturality. These canonical isomorphisms define e for every W, independently of
modules. The comparison c of two slice restrictions is the sectionwise identity;
associativity of inclusions gives its naturality. The canonical W-to-V stalk
comparison d0 satisfies the displayed law for the canonical V-to-U comparison e0:
both sides take a section germ to that same germ on U.

For an arbitrary comparison a on V, put R = restriction from U to V. Transport
open-immersion module pushforward back to the slice sites to obtain its right
adjoint P, with unit eta and invertible counit epsilon : R P --> Id. Define an
automorphism b of the V-stalk functor S by the composite
S(epsilon) inverse, e0 whiskered by P, a inverse whiskered by P, S(epsilon).
Naturality makes b a natural automorphism. Naturality of e0 and a at eta_F,
and the triangle identity R(eta_F) followed by epsilon_(R F) = identity, give
b_(R F) followed by a_F = e0_F. Thus d = d0 followed by b has the required law.
This argument applies to all module sheaves and all comparisons a: no free source,
finite presentation, local existence of a morphism, or prescribed stalk map is
used. If V=W the same counit calculation applies; the hypothesis x in W excludes
empty neighbourhoods. The canonical comparisons are determined by the germ formula;
d is adjusted to a by the explicit adjunction construction above.
-/
theorem exists_openStalk_restriction_transport
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U) :
    ∃ e : ∀ (W : X.Opens) (hxW : x ∈ W) (hWU : W ≤ U),
      SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hWU) ⋙
        openModuleStalkFunctor X W ⟨x, hxW⟩ ≅ openModuleStalkFunctor X U ⟨x, hxU⟩,
      ∀ (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U)
        (a : SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hVU) ⋙
          openModuleStalkFunctor X V ⟨x, hxV⟩ ≅ openModuleStalkFunctor X U ⟨x, hxU⟩)
        (W : X.Opens) (hxW : x ∈ W) (hWV : W ≤ V) (hWU : W ≤ U),
        let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hVU)
        let Q := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hWV)
        let P := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hWU)
        ∃ (c : R ⋙ Q ≅ P)
          (d : Q ⋙ openModuleStalkFunctor X W ⟨x, hxW⟩ ≅
            openModuleStalkFunctor X V ⟨x, hxV⟩),
          ∀ M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U),
            (openModuleStalkFunctor X W ⟨x, hxW⟩).map (c.hom.app M) ≫
                (e W hxW hWU).hom.app M =
              d.hom.app (R.obj M) ≫ a.hom.app M := by sorry

end
end AlgebraicGeometry.Scheme
