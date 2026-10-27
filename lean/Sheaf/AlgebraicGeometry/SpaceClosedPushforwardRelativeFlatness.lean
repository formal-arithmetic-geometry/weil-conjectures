/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Topology.ClosedPushforwardAbelianStalks
import Sheaf.TraceFormula.EtaleLocalRingFlatness
import Sheaf.AlgebraicGeometry.RelativeFlatnessSourceCover
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.TraceFormula.ZariskiEtaleFunctorComparisonSquare

/-! # Closed pushforward preserves and reflects relative flatness

Source: Stacks Project, Morphisms of Spaces, Tag 0DK1, lemma-stalk-push-closed;
Quot and Hilbert Spaces, Tag 0D00, lemma-hilb-is-quot, omitted flatness argument
(blueprint: lem-sfb-space-closed-pushforward-relative-flatness).

The existing chartwise relative-flatness predicate uses the actual Zariski module
restriction. For a scheme target its all-target-chart test agrees with the ordinary
base-local-ring stalk condition, by étale local-ring flatness (Tag 05BA).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-coherent module and its closed direct image are flat over precisely the
same scheme base; the structure-module case detects flatness of the closed subspace.

Source: Stacks, Tag 0DK1, lemma-stalk-push-closed (stalk at the image is the original
stalk); Tag 0D00, lemma-hilb-is-quot
(blueprint: lem-sfb-space-closed-pushforward-relative-flatness).

Proof:
1. Set F = i_*G. By lem-sfb-space-closed-immersion-quasi-coherent-modules, F is
   quasi-coherent. Over any étale scheme chart U of X, the closed base change V is
   a scheme. By lem-trf-space-etale-module-pushforward-restriction, restriction of F
   is the direct image from V. The Zariski/étale equivalence
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and the unrestricted first
   clause of lem-trf-zariski-etale-functor-comparison-square identify its Zariski
   module with the ordinary closed pushforward of the Zariski module on V.
2. Apply lem-sc-closed-pushforward-abelian-stalks. Outside V the stalk is zero;
   at the image of v it is the stalk at v. This germ identification is linear over
   the base local ring: a base germ acts by pullback through the same composite
   V → U → X → T on both sides. Zero modules are flat. The stalk criterion of
   def-pc-scheme-module-flat-over gives the equivalence on this pair of charts.
3. If G is flat over T, its restriction to every such V is flat. Step 2 proves
   flatness of F on every U, hence flatness over T.
4. Conversely choose a surjective étale atlas U → X and its pullback V → Z.
   Step 2 makes G flat over T on V. For any other chart W → Z, the scheme
   E = W ×_Z V is étale over V and surjective étale over W, by
   lem-trf-space-fibre-products-etale-covers. The pullback compatibility in the
   Zariski/étale equivalence and lem-trf-relative-flatness-source-cover first pull
   flatness to E and then descend it to W. Thus G is flat on every chart of Z.
5. Apply this equivalence to O_Z. Its chart module is the structure module, whose
   relative stalk flatness is exactly flatness of the chart scheme over T.
   The chart test def-sfb-space-morphism-properties includes id_T. Conversely,
   lem-trf-etale-local-ring-flatness changes O_{T,t} to the local ring of any
   étale target chart. This also identifies ModuleIsFlatOver with the stipulated
   base-stalk condition and gives the second equivalence. No finiteness is used. -/
theorem space_closed_pushforward_relative_flatness
    {S : Scheme.{u}} (T : Over S) {X Z : AlgebraicSpace S}
    (f : X ⟶ schemeSpace T) (i : Z ⟶ X)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom)
    (G : Z.Modules) [G.IsQuasicoherent] :
    (ModuleIsFlatOver (i ≫ f) G ↔
      ModuleIsFlatOver f ((moduleDirectImage i).obj G)) ∧
    (MapIsFlat (i ≫ f) ↔
      ModuleIsFlatOver f ((moduleDirectImage i).obj
        (SheafOfModules.unit Z.structureSheaf))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
