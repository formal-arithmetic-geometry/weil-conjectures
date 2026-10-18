/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.AlgebraicGeometry.TorsorComparisonGlue
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.SiteModuleSheafGluing
import Sheaf.AlgebraicGeometry.ConstructiblePartitionLocalClosedStratum
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingInverseImageComparison
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Constructible
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-! # Constructible pro-etale module sheaves are classical

Source: current Weil blueprint, sec-proetale-coefficients/sk-thm-pe-constructible-comparison,
`sk-thm-pe-constructible-comparison-classical.md`; Stacks Project, Tags 099Y and 09AK
(blueprint: det-pe-constructible-comparison-classical).

The global and Zariski-local assertions use intrinsic modules over the constant ring.
The stratum schemes are reduced, including when the ambient scheme is nonreduced.
Local models are finitely generated modules, with no finite-ring assumption.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- A finite constructible locally closed partition with finite constant local module models
makes a pro-etale module sheaf classical. Reduced immersed representatives realize the
reduced induced structure on each stratum. Constructibility, local closedness, disjointness
and covering are fields of `S.toStratification`; empty strata and zero strata are allowed.

Source: current blueprint, constructible-comparison-classical; Stacks, Tags 099Y and 09AK
(blueprint: det-pe-constructible-comparison-classical).

Proof, following the node's steps 1--9:
1. Over a Noetherian ring a finite module is finitely presented
   (lem-sc-noetherian-finite-module-finite-presentation). The local-system type decomposition
   (det-pe-finite-local-systems-type) reduces locally constant sheaves to one fixed model.
2. The sheaf Isom(M,F) is an Aut(M)-torsor: maps, inverses and linearity glue by the sheaf
   equalizer condition. Its automorphism group is the inverse image of the etale constant
   group (det-pe-finite-local-systems-hom). Torsor comparison
   (det-pe-torsor-comparison-glue) therefore supplies etale local trivializations.
3. Full faithfulness on modules (det-pe-classical-sheaves-modules), compatibility with
   scheme pullbacks (sk-thm-pe-direct-image-comparison), slice-site localization and constant
   restriction descend their transition isomorphisms and cocycle. Module-sheaf gluing
   (lem-weil-pbc-site-module-sheaf-gluing) gives an etale sheaf whose inverse image is F.
   This proves the locally constant case on every scheme.
4. Induct strongly on the number of nonempty strata. With none, X is empty and the zero
   sheaf is classical (det-pe-classical-derived-weak-serre). Around a point, choose an affine
   W on which its stratum Z is closed and constructible, with quasi-compact complement U
   (lem-sf-constructible-partition-local-closed-stratum). Affineness makes W and U qcqs and
   makes the open immersion j quasi-compact. Retain the reduced structure on Z, also for
   one stratum on a nonreduced scheme.
5. Use lem-weil-pbc-proetale-ringed-open-closed to form the short exact sequence
   0 -> j_!j^*F -> F -> i_*i^*F -> 0 over the restricted constant coefficient rings.
   The constant-ring comparison and scheme-pullback comparison identify those rings.
6. The other strata restrict to a constructible locally closed partition of U with fewer
   nonempty parts. Restrict the same constant models and apply induction to j^*F.
7. Adjunction identifies comparison inverse image of etale j_! with pro-etale j_!: their
   right adjoints agree sectionwise. Use localized restriction, extension-by-zero adjunction
   and uniqueness of left adjoints (lem-weil-pbc-conjugate-iso-unit-equation).
8. The sheaf i^*F on Z is classical by steps 1--3. The reduced closed immersion is qcqs.
   Direct-image comparison in degree zero identifies i_*i^*F with an etale inverse image;
   exact comparison inverse image and left exact i_* justify degree-zero cohomology.
9. Both ends of the short exact sequence are classical, so the extension clause of
   det-pe-classical-derived-weak-serre makes F|W classical. Zariski locality
   (det-pe-constructible-comparison-local) gives classicality on X. -/
theorem constructible_isClassicalModule (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ]
    (F : ringedSiteModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (Scheme.proEtaleConstantRing X Λ)))
    (S : Scheme.LocallyClosedStratification X)
    (_hred : ∀ k : Fin S.n, IsReduced (S.domain k))
    (_hmodels : ∀ k : Fin S.n,
      ∃ (I : Type (u + 1)) (V : I → (S.domain k).ProEt)
        (f : ∀ a : I, V a ⟶ Scheme.ProEt.mk (𝟙 (S.domain k))),
        Presieve.ofArrows V f ∈ (Scheme.ProEt.precoverage (S.domain k)).coverings _ ∧
        ∀ a : I, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ),
          Module.Finite (ULift.{u + 1, u} Λ) M ∧
          Nonempty ((Scheme.proEtaleConstantModulePullback (S.immersion k) Λ F).over (V a) ≅
            Scheme.proEtaleConstantModuleSheafOver (S.domain k) Λ (V a) M)) :
    IsClassicalModule Λ F := by
  sorry

/-- The finite constructible partition may exist only on Zariski neighborhoods of points.
Restriction to a stratum of an open is pullback along its composite immersion into X,
with the canonical constant-ring structure map.

Source: current blueprint, constructible-comparison-classical, last sentence;
Stacks, Tags 09AJ and 09AK (blueprint: det-pe-constructible-comparison-classical).

Proof, step 10 of the node: around each point choose a neighborhood with such a partition,
then refine it by affine opens (lem-weil-pbc-affine-opens-basis). Constructible locally
closed partitions restrict to these opens (lem-weil-pbc-constructible-open-restriction),
and the trivializing covers and their finite constant models pull back unchanged.
Every affine open is qcqs (lem-weil-pbc-affine-scheme-qcqs), so apply
constructible_isClassicalModule, proved by steps 1--9 above, on each affine open.
The resulting opens cover X, and det-pe-constructible-comparison-local gives the result. -/
theorem locallyConstructible_isClassicalModule (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ]
    (F : ringedSiteModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (Scheme.proEtaleConstantRing X Λ)))
    (_hlocal : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ S : Scheme.LocallyClosedStratification U.toScheme,
        (∀ k : Fin S.n, IsReduced (S.domain k)) ∧
        ∀ k : Fin S.n,
          ∃ (I : Type (u + 1)) (V : I → (S.domain k).ProEt)
            (f : ∀ a : I, V a ⟶ Scheme.ProEt.mk (𝟙 (S.domain k))),
            Presieve.ofArrows V f ∈ (Scheme.ProEt.precoverage (S.domain k)).coverings _ ∧
            ∀ a : I, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ),
              Module.Finite (ULift.{u + 1, u} Λ) M ∧
              Nonempty ((Scheme.proEtaleConstantModulePullback
                (S.immersion k ≫ U.ι) Λ F).over (V a) ≅
                  Scheme.proEtaleConstantModuleSheafOver (S.domain k) Λ (V a) M)) :
    IsClassicalModule Λ F := by
  sorry

end AlgebraicGeometry.ProEtale
