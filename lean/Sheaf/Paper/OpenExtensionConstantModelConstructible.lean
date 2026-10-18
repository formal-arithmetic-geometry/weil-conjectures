/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Paper.ModuleObjects
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Extension by zero and finite constant local models

Source: blueprint main-20261015, sec-six-functors/sk-lem-sf-open-ctf,
sk-prop-proper-image-localizing-open.proof.md, paragraph Constructibility
(blueprint: lem-sf-open-extension-zero-constant-model-constructible).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Extension by zero preserves constructibility with finite constant scalar models.
The supplied stratification witnesses the constructibility hypothesis. The equivalence
of indices identifies the extended stratification, as schemes over X, with precisely the
old strata and the reduced closed complement; empty strata are allowed.

Source: blueprint main-20261015, sk-prop-proper-image-localizing-open.proof.md,
paragraph Constructibility
(blueprint: lem-sf-open-extension-zero-constant-model-constructible).

Proof, following the node's five steps:
1. Finite-type schemes over a field are Noetherian (sk-def-sfb-dc-setting), so the
composites of the stratum immersions with j have constructible locally closed images
(def-weil-constructible-subset). Add the reduced induced closed complement
(lem-weil-pbc-reduced-induced-closed-subscheme) to obtain a finite disjoint cover
(def-constructible-stratification). Noetherianness also makes j quasi-compact.
2. Identify ring and module objects with sectionwise rings and modules using the
sheafified tensor (sk-def-sfb-ring-object, sk-def-sfb-module-objects,
def-weil-sheaf-of-modules-category). Inverse image and abelian upper star are the
same sheafified Kan extension (def-weil-proetale-inverse-image,
def-sfb-finite-upper-star). The ringed extension by zero and linear module-object
extension are isomorphic as left adjoints to this same inverse image
(lem-weil-pbc-conjugate-iso-unit-equation, def-sfb-module-linear-open-lower-shriek).
3. Apply lem-weil-pbc-proetale-ringed-open-closed. The canonical coefficient maps
are isomorphisms (sk-def-sfb-coefficient-morphisms), so extension and restriction
of scalars cancel (sk-def-sfb-change-of-scalars). The module-object definitions
(sk-def-sfb-module-lower-shriek, sk-def-sfb-module-pushforward-pullback) then give
j^* j_! M isomorphic to M and zero restriction to the complement. Pullback
composition gives the asserted isomorphism on each original stratum.
4. Pull those isomorphisms to the same covers and compose with the same scalar
models (det-def-sfb-constructible-local-model). On the complement use the identity
cover and the zero scalar module, with its rank-zero presentation. These models
and the extended stratification give sk-def-sfb-constructible.
5. If U is empty, the empty cover forces M to be zero and additive extension by
zero sends it to zero (def-weil-pbc-proetale-site, def-sfb-module-open-lower-shriek).
If j is an isomorphism, the complement is empty. Retaining the empty stratum also
handles X empty, without requiring a nonempty index set. -/
theorem constantModelConstructible_openImmersionLowerShriek
    (ℓ p : ℕ) [Fact ℓ.Prime] [Fact p.Prime] (_hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (S : Scheme.FiniteLocallyClosedStratification U)
    (_hS : ∀ a : Fin S.n, Topology.IsConstructible (S.stratum a))
    (_hM : ∀ a : Fin S.n, HasFiniteConstantLocalModel Λ (S.domain a)
      ((CondensedRing.upperStar Λ (S.immersion a)).obj M)) :
    IsConstantModelConstructible Λ X ((CondensedRing.openImmersionLowerShriek Λ j).obj M) ∧
    (∃ (T : Scheme.FiniteLocallyClosedStratification X)
        (e : Fin T.n ≃ Option (Fin S.n)),
      (∀ b : Fin T.n, Topology.IsConstructible (T.stratum b)) ∧
      (∀ b : Fin T.n, match e b with
        | none => Nonempty (Over.mk (T.immersion b) ≅ Over.mk j.closedComplement)
        | some a => Nonempty (Over.mk (T.immersion b) ≅ Over.mk (S.immersion a ≫ j)))) ∧
    (∀ a : Fin S.n,
      Nonempty ((CondensedRing.upperStar Λ (S.immersion a ≫ j)).obj
          ((CondensedRing.openImmersionLowerShriek Λ j).obj M) ≅
        (CondensedRing.upperStar Λ (S.immersion a)).obj M)) ∧
    IsZero ((CondensedRing.upperStar Λ j.closedComplement).obj
      ((CondensedRing.openImmersionLowerShriek Λ j).obj M)) ∧
    (IsEmpty U → IsZero M ∧ IsZero ((CondensedRing.openImmersionLowerShriek Λ j).obj M)) ∧
    (IsIso j → IsEmpty (Scheme.IdealSheafData.vanishingIdeal
      ⟨(j.opensRange : Set X)ᶜ, j.opensRange.isOpen.isClosed_compl⟩).subscheme) := by
  sorry

end AlgebraicGeometry.ProEtale
