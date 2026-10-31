/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence

/-! # The direct-image square on Zariski opens

Source: Stacks Project, Descent, Tag 03FH (2).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Direct image and restriction to Zariski opens commute with their prescribed scalars.

Source: Stacks Project, Descent, Tag 03FH (2).
(blueprint: lem-trf-zariski-etale-right-adjoint-square).

Proof: the small-etale base-change functor is continuous. Its module direct image
has the tensor left adjoint obtained from module-presheaf pullback and sheafification
on the affine etale basis. On an open W, identify its scheme base change with the
inverse-image open by gabberPreimageEtaleIso. Apply the module presheaf to this
isomorphism. The structural ring maps agree by functoriality of pullback of regular
functions, so the resulting additive maps are linear. Naturality in W follows from
the pullback universal property, and naturality in G follows from G's morphism
naturality. Applying G to the inverse scheme isomorphism supplies the inverse.
This calculation uses no quasi-coherence, quasi-compactness or separatedness. -/
theorem zariskiEtale_rightAdjoint_square {U T : Scheme.{u}} (a : U ⟶ T)
    (cU : ZariskiEtaleModuleContext U) (cT : ZariskiEtaleModuleContext T) :
    ∃ (hp : (smallEtaleModulePushforward a).IsRightAdjoint)
      (r : smallEtaleModulePushforward a ⋙ cT.restriction ≅
        cU.restriction ⋙ pushforward a),
      ∀ (G : SmallEtaleModules U) (W : T.Opens),
        (r.hom.app G).app W =
          G.val.presheaf.map (AlgebraicGeometry.gabberPreimageEtaleIso a W).hom.op := by
  sorry

end AlgebraicGeometry.Scheme.Modules
