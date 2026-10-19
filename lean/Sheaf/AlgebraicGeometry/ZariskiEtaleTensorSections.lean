/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsMapNaturality
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.CategoryTheory.RingedToposMorphism
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites
import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-!
# Tensor sections and Zariski-to-étale change of topology

Source: Stacks Project, Descent, Tags 070S (2), 03FH (1), and the proof of 0GN7
(blueprint: lem-trf-zariski-etale-tensor-sections).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- For every module, the canonical ringed-site pullback is sheafified tensor sections.
The ring sheaf, its structural map, and restriction are the existing
`smallEtaleModuleRing`, `zariskiEtaleOpenRingMap`, and `c.restriction`:
the latter evaluates on open subschemes, with scalars restricted by the former map.
The inclusion preserves finite limits and is continuous (`c.continuous`), so this
is the ringed morphism of sites, with the structure map adjoint to the open ring map.
The presheaf identification `p` includes every restriction; its scalar equation
and map equation specify precisely the module presheaf and its action on morphisms.
The final equation fixes the comparison by the ordinary open-section unit.

Source: Stacks Project, Descent, Tags 070S (2), 03FH (1), and proof of 0GN7
(blueprint: lem-trf-zariski-etale-tensor-sections).

Proof, following the eight steps of the DAG:
1. The Zariski inclusion is a morphism of sites. Regular functions are an étale
   sheaf by additive descent, and their ring operations glue sectionwise. On opens
   the structure map is the usual identification with functions on the open scheme.
2. The recorded tensor-section restrictions are semilinear, preserve identities,
   and compose. The recorded map-naturality theorem supplies the functor P.
   Apply module sheafification, which is left adjoint to inclusion.
3. Restrict an étale module G to the opens of each étale V. Open covers are étale,
   giving a Zariski module G_V. Étale restriction gives G_V to a_*G_V' for each a.
4. From beta : M to epsilon_*G, restrict beta's sections to V times_T W on every
   open W of T. Transpose by the scheme-module adjunction to u^*M to G_V, and
   take global sections to obtain P(M)(V) to G(V).
5. The transposes of the two maps for a triangle agree by functoriality of
   restrictions. The normalized composition-unit equation therefore proves
   naturality on the site. The construction is natural in both modules.
6. Conversely restrict a presheaf map P(M) to G to open subschemes, using the
   unit-compatible tensor/open comparison to obtain M to epsilon_*G. Starting
   with beta recovers beta on every open.
7. Starting with a presheaf map, assemble its components on opens of each V.
   Its transpose is beta restricted to V times_T W by the composition-unit
   equation. The scheme-module adjunction therefore recovers the original map.
8. These inverse Hom bijections give P followed by sheafification as left adjoint
   to restriction. The ringed-site tensor adjunction has the same right adjoint.
   Uniqueness of left adjoints gives the natural isomorphism, normalized by their
   units; evaluated on an open this is the final equation. No quasi-coherence,
   affine generation of global sections, or separatedness is used. -/
theorem zariskiEtale_tensorSections (T : Scheme.{u}) :
    ∃ c : ZariskiEtaleModuleContext T,
      PreservesFiniteLimits (AlgebraicGeometry.gabberOpenEtale T) ∧
      ∃ P : T.Modules ⥤ _root_.PresheafOfModules.{u} (smallEtaleModuleRing T).obj,
        ∃ p : ∀ M : T.Modules, (P.obj M).presheaf ≅ etaleTensorSectionsPresheaf M,
          (∀ (M : T.Modules) (V : T.Etale)
              (r : Γ(V.left, ⊤)) (s : (P.obj M).obj (op V)),
            (p M).hom.app (op V) (r • s) =
              r • (@id (Γ((tensorPullback V.hom).obj M, ⊤))
                ((p M).hom.app (op V) s))) ∧
          (∀ (M N : T.Modules) (h : M ⟶ N) (V : T.Etale),
            ((_root_.PresheafOfModules.toPresheaf _).map (P.map h)).app (op V) ≫
                (p N).hom.app (op V) =
              (p M).hom.app (op V) ≫ ((tensorPullback V.hom).map h).app ⊤) ∧
          ∃ e : c.extension ≅
              P ⋙ _root_.PresheafOfModules.sheafification (𝟙 (smallEtaleModuleRing T).obj),
            ∀ (M : T.Modules) (W : T.Opens) (s : Γ(M, W)),
              (e.hom.app M).val.app (op ((AlgebraicGeometry.gabberOpenEtale T).obj W))
                  (((c.adjunction.unit.app M).app W) s) =
                ((_root_.PresheafOfModules.sheafificationAdjunction
                    (𝟙 (smallEtaleModuleRing T).obj)).unit.app (P.obj M)).app
                  (op ((AlgebraicGeometry.gabberOpenEtale T).obj W))
                  ((p M).inv.app (op ((AlgebraicGeometry.gabberOpenEtale T).obj W))
                    ((tensorOpenSectionIso T M W).inv s)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
