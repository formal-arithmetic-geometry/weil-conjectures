/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherent
import Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen
import Sheaf.AlgebraicGeometry.EtaleQuasiCoherentDescent
import Sheaf.AlgebraicGeometry.EtaleTensorSections
import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.CategoryTheory.SiteLerayDegenerate
import Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf
import Sheaf.Paper.ZariskiEtaleInclusionMorphismOfSites
import Sheaf.Paper.ZariskiModuleAbelianCohomologyAgree
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift

/-! # Étale and Zariski cohomology of quasi-coherent modules

Source: Stacks Project, Descent, Proposition 03DW (2), and Étale Cohomology,
Theorem 03P2 (blueprint: lem-sc-etale-zariski-qcoh-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- Étale and Zariski cohomology of quasi-coherent modules agree naturally in the module.
The morphisms `m` have exactly the prescribed components `Γ(U, u^*φ)`. The family `c`
is chosen simultaneously for all quasi-coherent modules and all nonnegative degrees.
In degree zero, its value on the canonical image of a global section is that section
pulled back to the terminal étale object, i.e. the identity under `id_X^*F ≅ F`.
We use the standard large Ext model of étale cohomology `Sheaf.H`; it computes the
right-derived global sections of `def-weil-pbc-etale-cohomology`. This changes no sheaf
or section group and places no smallness hypothesis on `X` or `F`.

Source: Stacks Project, Descent, Proposition 03DW (2), and Étale Cohomology, Theorem 03P2
(blueprint: lem-sc-etale-zariski-qcoh-comparison).

Proof:
1. The restrictions of `def-sc-etale-qcoherent-module` compose by
   `lem-sc-etale-qcoherent-presheaf-functorial` and satisfy descent by
   `lem-sc-etale-qcoherent-descent`. Naturality of tensor pullback in the module gives
   the morphism with components `Γ(U, u^*φ)`.
2. Use the site morphism of `lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites`.
   The unit-normalized open pullback identification of
   `lem-weil-pbc-open-immersion-module-pullback-restriction` identifies its direct image
   with the underlying abelian sheaf, compatibly with restrictions and module maps.
   Compose `lem-sc-zariski-module-abelian-cohomology-agree`, cohomology of this
   identification, and the pullback/counit map of `lem-weil-pbc-site-cohomology-pullback`.
3. On each affine open, `lem-weil-pbc-etale-cohomology-over-open` and
   `lem-sc-etale-affine-qcoherent` give vanishing in positive degrees. Sheafification
   on the affine basis and `lem-weil-pbc-site-higher-direct-image-sheafified-presheaf`
   show that all positive higher direct images vanish.
4. Apply `lem-weil-pbc-site-leray-degenerate`: the edge maps, hence the comparisons,
   are isomorphisms for every scheme, without a separatedness assumption.
5. Compose the naturality squares of the module/abelian comparison, the open pullback
   identification, site-cohomology pullback, and the adjunction counit. This proves the
   displayed naturality equality. In degree zero, the triangle identity and the
   degree-zero module/abelian comparison identify the result with section pullback
   along the identity. -/
theorem etale_zariski_qcoh_comparison (X : Scheme.{u}) :
    ∃ m : ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent],
        (F ⟶ G) → (etaleTensorSectionsSheaf F ⟶ etaleTensorSectionsSheaf G),
      (∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
          (φ : F ⟶ G) (U : X.Etale),
        (m F G φ).hom.app (op U) = ((tensorPullback U.hom).map φ).app ⊤) ∧
      ∃ c : ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
          ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≃+
            @Sheaf.H _ _ X.smallEtaleTopology (etaleTensorSectionsSheaf F)
              inferInstance (HasExt.standard _) q,
        (∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
            (φ : F ⟶ G) (q : ℕ)
            (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F),
          c G q (((RingedSpace.moduleCohomology X.toRingedSpace q).map φ).hom x) =
            @Sheaf.H.map _ _ X.smallEtaleTopology inferInstance (HasExt.standard _)
              _ _ (m F G φ) q (c F q x)) ∧
        (∀ (F : X.Modules) [F.IsQuasicoherent] (s : Γ(F, ⊤)),
          @Sheaf.H.equiv₀ _ _ X.smallEtaleTopology inferInstance (HasExt.standard _)
            (etaleTensorSectionsSheaf F) _ terminalIsTerminal
            (c F 0 (((@Functor.toRightDerivedZero _ _ _ _ _
              (@InjectiveResolution.instHasInjectiveResolutions _ _ _
                (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2) _
              (RingedSpace.globalSectionsFunctor X.toRingedSpace) _).app F).hom s)) =
          tensorSectionsUnit (⊤_ X.Etale).hom F s) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
