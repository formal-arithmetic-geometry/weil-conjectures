/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryEvaluationData
public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
public import Sheaf.Algebra.Homology.KFlat
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison
import Sheaf.AlgebraicGeometry.DerivedTensorSymmetry
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions

/-! # Ordinary models for evaluation on the open scheme

Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
(blueprint: lem-pc-exact-source-evaluation-open-models).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The standard localization is available on the open scheme independently of the
specified localization universe of the over-site.
Source: Stacks Project, Tag 05RU.
(blueprint: lem-pc-exact-source-evaluation-open-models). -/
local instance modelsEvaluationStandardDerived (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

/-- The ordinary evaluation calculation, entirely on the open scheme. The functor E
only changes from the over-site to its equivalent scheme site; it does not restrict
an object or an evaluation arrow from X.

Source: Stacks Project, cohomology.tex, Tag 08DJ (lemma-internal-hom),
Tag 08DM (lemma-Rhom-strictly-perfect), and Tag 08DQ (lemma-dual-perfect-complex),
ordinary representative computation without the perfectness-dependent inverse.
(blueprint: lem-pc-exact-source-evaluation-open-models).

Proof:
1. Transport the actual complexes P,F and f along the exact equivalence of module
   categories Modules.overEquiv. It preserves tensor, the unit, Hom complexes,
   their projections, and direct-sum totalization. Thus it preserves the given
   component equations, Hom preservation of quasi-isomorphisms, and K-flatness
   of the actual ordinary dual. Its localization factorization identifies E(QP)
   and E(QF) with the localized transported complexes.
2. Resolve the transported F and the degree-zero unit by the fixed functorial
   K-injective resolution on the open scheme. Hom preservation makes the two
   induced Hom maps quasi-isomorphisms. The derived Hom factorization, followed
   by their localized inverses and eK,eN, supplies the target and dual comparisons.
3. K-flatness of the ordinary dual makes its total tensor with the arbitrary F
   compute the derived tensor. Compose this model comparison with eN and the
   dual comparison to obtain a. In particular, a uses no inverse of f.
4. Replace tensor inputs by K-flat resolutions and use the fixed K-injective
   target. Uncurry the identity of the dual with the canonical representative
   formula. On a summand of degrees p,q followed by the Hom projection indexed
   by r, associativity and symmetry give the unit-action evaluation when r+q=0,
   and zero otherwise. These are exactly hf. Naturality with the resolution maps
   and detection by tensor inclusions and Hom projections identify the chain
   maps. Localization, and cancellation of the two Hom resolution isomorphisms,
   give g;b=a;E(Qf).
This is a local complex calculation: no global restriction compatibility is
asserted. Zero complexes and the empty open obey the same universal properties. -/
theorem exists_exactSource_evaluation_open_models (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory U.toScheme)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (_hhom : ∀ (M M' : CochainComplex (localEvaluationModules X U) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t))
    (_hdual : (localEvaluationDual X U P).IsKFlat)
    (_eK : (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj P) ≅ K)
    (_eN : (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj F) ≅ N)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (_hf : IsLocalOrdinaryEvaluation X U P F f) :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let H := derivedInternalHom
      (Opens.grothendieckTopology U.toScheme.toRingedSpace) U.toScheme.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory U.toScheme))
    let g := ((schemeDerivedTensorHomEquiv U.toScheme) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv U.toScheme) D K
          (𝟙_ (schemeDerivedCategory U.toScheme)) (𝟙 D)) ≫ (ρ_ N).hom)
    ∃ a : N ⊗ D ≅ E.obj (DerivedCategory.Q.obj (localEvaluationTensor X U P F)),
      ∃ b : H.obj (op K, N) ≅
          E.obj (DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F)),
        g ≫ b.hom = a.hom ≫ E.map (DerivedCategory.Q.map f) := by sorry

end AlgebraicGeometry
