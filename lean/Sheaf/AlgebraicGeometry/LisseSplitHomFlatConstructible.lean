/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.ConstantSheafSectionsLocallyConstant
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

/-!
# Hom from an étale locally split finite projective sheaf

Source: Weil conjectures blueprint, `sec-six-functors-basics/sk-rem-sf-matrix/`
`det-rem-sf-matrix-hom-devissage.proof.md`, Step 2, termwise flat constructibility
(blueprint: lem-sfb-lisse-split-hom-flat-constructible).

Flatness and internal Hom use the recorded ringed-site module declarations.
Constructibility uses the recorded module-valued sheaf declaration. The explicit
`etaleConstantCommRingComparison` and scalar restriction below identify these presentations
canonically; no equivalence or comparison map is chosen as extra data.

## Main declarations

- `etaleConstantCommRingComparison`: the canonical coefficient-ring comparison map.
- `hom_isFlat_constructible_of_etaleLocallySplit`: flatness and constructibility of Hom.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical map from the constant ring sheaf to the underlying ring sheaf of
the constant commutative ring sheaf. It is the adjoint transpose of the constant
commutative-ring sheafification unit after forgetting commutativity. Restriction
along this map followed by `etaleConstantModuleRestriction` restricts precisely to
the original constant A-scalars, with no choice of an abstract equivalence.

Source: Stacks, Modules on Sites, Sections 093I and 03CV, and the constant-coefficient
convention in `det-rem-sf-matrix-hom-devissage.proof.md`, Step 2
(blueprint: lem-sfb-lisse-split-hom-flat-constructible). -/
noncomputable def etaleConstantCommRingComparison
    (U : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    etaleConstantModuleRing U A ⟶
      (sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)) :=
  ((sheafificationAdjunction U.smallEtaleTopology RingCat.{u + 1}).homEquiv
    ((Functor.const U.Etaleᵒᵖ).obj (RingCat.of A)) _).symm
    (Functor.whiskerRight
      (toSheafify U.smallEtaleTopology
        ((Functor.const U.Etaleᵒᵖ).obj (CommRingCat.of A)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))

/-- Internal Hom from an étale locally split summand of a finite free constant-ring
module sheaf into a flat constructible sheaf is flat and constructible.

Source: Weil conjectures blueprint, `det-rem-sf-matrix-hom-devissage.proof.md`, Step 2;
Stacks, Modules on Sites, Tag 03ER(3), and Étale Cohomology, Tags 03RU and 095E(3)
(blueprint: lem-sfb-lisse-split-hom-flat-constructible).

Proof:
1. Put H = Hom(E,G). On each member V of the given étale cover choose splitting
   maps i : E|V → A_V^t and p : A_V^t → E|V with i ≫ p = id. Precomposition with
   p and i realizes H|V as a retract of Hom(A_V^t,G|V) = (G|V)^t, cut out by the
   idempotent e* induced by e = p ≫ i. The entries of e are sections of A_V.
   By lem-weil-pbc-constant-sheaf-sections-locally-constant (03P5), refine V by
   Zariski opens until all the finitely many entries are constant elements of A.
2. Restrict any short exact tensor-test sequence to these covering pieces. By
   prop-weil-pbc-inverse-image-modules-exact restriction is exact and identifies
   constant coefficients; lem-weil-pbc-ringed-topos-flat-module-pullback makes
   G|V flat. Tensor commutes with restriction by the sectionwise tensor formula
   and its sheafification (def-pur-sheaf-tensor-product). The tensor sequence for
   H|V is the image of the compatible idempotent 1 ⊗ e* on the exact tensor
   sequence for (G|V)^t. It is exact: apply the idempotent to local lifts. Every
   geometric point lifts to the cover; exact geometric stalks and
   lemma-weil-pbc-geometric-stalk-conservative detect vanishing of the kernel,
   middle homology and cokernel globally. This is def-pc-flat-sheaf-modules.
3. Keep G's finite constructible stratification. Base change the cover to each
   stratum and refine to make G the constant sheaf on a finite A-module M.
   Exact additive inverse image (prop-weil-pbc-inverse-image-modules-exact)
   carries the image presentation of H to the image of the same constant matrix
   on M^t. This image sheaf is constant with value N = im(e* : M^t → M^t):
   03P5 identifies sections with locally constant functions, and each value in N
   locally lifts to M^t. This is an A-linear identification and N is finite.
   Thus the inverse image of H on every original stratum is finite locally
   constant, precisely def-weil-pbc-etale-constructible-sheaf. This argument uses
   inverse image of an image, without assuming general Hom/pullback commutation.
4. The identifications are restrictions of the global sheaf Hom
   (def-pur-sheaf-hom), so steps 2 and 3 give its two asserted properties. -/
theorem hom_isFlat_constructible_of_etaleLocallySplit
    (A : Type (u + 1)) [CommRing A] [Finite A] (U : Scheme.{u}) [IsNoetherian U]
    (E G : SheafOfModules.{u + 1}
      ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))))
    (_hE : ∃ 𝒰 : Cover.{u} etalePrecoverage U, ∀ α : 𝒰.I₀, ∃ t : ℕ,
      ∃ i : E.over (𝒰.etalePrecoverageToEtale α) ⟶
        SheafOfModules.free
          (R := ((sheafCompose U.smallEtaleTopology
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj
              (CommRingCat.of A))).over (𝒰.etalePrecoverageToEtale α))
          (ULift.{u + 1} (Fin t)),
      ∃ p : SheafOfModules.free
          (R := ((sheafCompose U.smallEtaleTopology
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj
              (CommRingCat.of A))).over (𝒰.etalePrecoverageToEtale α))
          (ULift.{u + 1} (Fin t)) ⟶
        E.over (𝒰.etalePrecoverageToEtale α), i ≫ p = 𝟙 _)
    (_hflat : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := U.smallEtaleTopology)
      (R := (constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)) G)
    (_hconstructible : IsConstructibleEtaleModuleSheaf
      (etaleConstantModuleRestriction U A
        ((SheafOfModules.restrictScalars.{u + 1}
          (etaleConstantCommRingComparison U A)).obj G))) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := U.smallEtaleTopology)
      (R := (constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
      (SheafOfModules.homObj.{u + 1, u, u + 1, u + 1}
        (J := U.smallEtaleTopology)
        (R := (constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of A)) E G) ∧
    IsConstructibleEtaleModuleSheaf
      (etaleConstantModuleRestriction U A
        ((SheafOfModules.restrictScalars.{u + 1}
          (etaleConstantCommRingComparison U A)).obj
            (SheafOfModules.homObj.{u + 1, u, u + 1, u + 1}
              (J := U.smallEtaleTopology)
              (R := (constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj
                (CommRingCat.of A)) E G))) := by
  sorry

end AlgebraicGeometry.Scheme
