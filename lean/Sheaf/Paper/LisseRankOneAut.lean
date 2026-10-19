/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.LocallyConstant.Algebra
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.ConstructibleSheaf.ConstantModuleLocallyConstant
import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
import WeilConjectures.ConstructibleSheaf.ConstantModuleLocallyConstant

/-!
# Scalars and automorphisms of finite rank-one local systems

Source: blueprint sec-smooth-purity/sk-prop-a1-inv/lem-pur-lisse-rank-one-aut.md,
order 1959 (blueprint: lem-pur-lisse-rank-one-aut).

The ordinary internal Hom is the recorded ringed-site construction. Ring and group
isomorphisms below are characterized by their scalar action on geometric stalks.
The equalities between isomorphisms are equalities of actual sheaf isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The canonical scalar map, sending 1 to the identity, obtained from the two
ordinary global-sections bijections. Its component sends r to multiplication by r
on the localized module sheaf. Source: blueprint order 1959, clause (1)
(blueprint: lem-pur-lisse-rank-one-aut). -/
def rankOneScalarMap {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max v w}}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max v w})]
    (L : SheafOfModules.{max v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{max v w})).obj R)) :
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat.{max v w})).obj R) ⟶
      SheafOfModules.homObj (R := R) L L :=
  (SheafOfModules.unitHomEquiv (SheafOfModules.homObj (R := R) L L)).symm
    ((SheafOfModules.homObjSectionsEquiv (R := R) L L).symm (𝟙 L))

/-- Rank-one finite local systems have scalar endomorphisms and locally constant
unit automorphisms; two given isomorphisms differ by a unique such unit. The last
clause retains the given phi and specifies both the global constant-unit multiple
and its action at the specified geometric point.

Source: blueprint sec-smooth-purity/sk-prop-a1-inv/lem-pur-lisse-rank-one-aut.md,
order 1959, clauses (1) and (2) (blueprint: lem-pur-lisse-rank-one-aut).

Proof:
1. The positive-level coefficient quotient in def-pur-conventions is finite by
   def-weil-l-adic-coefficient-extension. On a rank-one trivializing cover define
   the scalar map sectionwise by r acting as multiplication by r. Commutativity
   makes it linear and the global-sections bijections identify it with rankOneScalarMap.
2. Use def-pur-sheaf-hom and def-pur-localized-ringed-site to restrict ordinary Hom.
   On a free rank-one module every localized endomorphism h is multiplication by
   h(1): linearity gives h(x)=x*h(1), and naturality identifies h(1) on restrictions.
   This supplies inverse maps compatible with every further restriction.
3. On a pullback of the trivializing cover, the scalar preimages agree on overlaps
   by local injectivity. The sheaf axiom glues them uniquely and proves that the
   scalar map is an isomorphism, without choosing any global basis.
4. The comparison adjunction, sheafification and the constant-module functor identify
   the inverse image of the etale coefficient sheaf with the pro-etale coefficient
   sheaf. Maps out of either are determined by the image of the constant generator 1;
   the two Yoneda inverse identities give the comparison preserving constant labels.
5. The unit isomorphism of prop-weil-pbc-site-comparison-finite-level and the etale
   model of lem-weil-pbc-constant-module-locally-constant identify coefficient sections
   with locally constant functions on the underlying scheme. Open fibers give local
   constant representatives. The locally bijective sheafification criterion identifies
   the labels; products agree on intersections of open fibers and hence globally.
6. Global sections of ordinary Hom identify endomorphisms with these scalar sections.
   Composition is multiplication and identity is 1, giving eL and eM. An invertible
   scalar has a unique inverse section; conversely such inverse sections give inverse
   sheaf maps. Pointwise inversion preserves local constancy, giving gL and gM.
   The displayed stalk formulas follow from the representativewise module operations
   in def-weil-proetale-geometric-stalk.
7. For phi and psi take psi composed with phi inverse, apply the scalar description
   for M, and cancel phi to prove uniqueness. For a constant unit v take the actual
   composite phi followed by gM(const v); the stalk functor gives the displayed
   formula at every geometric point. No isomorphism between arbitrary L and M is assumed.
-/
theorem lisse_rank_one_aut (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] [IsSeparated (T ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (L M : proEtaleRingModules T (proEtaleConstantRing T P.Ring))
    (_hL : IsLocallyConstantProEtaleModuleSheaf T P.Ring L)
    (_hM : IsLocallyConstantProEtaleModuleSheaf T P.Ring M)
    [L.IsFiniteLocallyFreeOfRank 1] [M.IsFiniteLocallyFreeOfRank 1] :
    IsIso (rankOneScalarMap L) ∧
      ∃ (eL : LocallyConstant T P.Coefficient ≃+* End L)
        (eM : LocallyConstant T P.Coefficient ≃+* End M)
        (gL : LocallyConstant T P.Coefficientˣ ≃* Aut L)
        (gM : LocallyConstant T P.Coefficientˣ ≃* Aut M),
        (∀ (f : LocallyConstant T P.Coefficient) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (y : Spec (.of Ω) ⟶ T) (x : (finiteCoefficientModuleStalkFunctor y P.Ring).obj L),
          ((finiteCoefficientModuleStalkFunctor y P.Ring).map (eL f)).hom x =
            f (y (IsLocalRing.closedPoint Ω)) • x) ∧
        (∀ (f : LocallyConstant T P.Coefficient) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (y : Spec (.of Ω) ⟶ T) (x : (finiteCoefficientModuleStalkFunctor y P.Ring).obj M),
          ((finiteCoefficientModuleStalkFunctor y P.Ring).map (eM f)).hom x =
            f (y (IsLocalRing.closedPoint Ω)) • x) ∧
        (∀ u₀ : LocallyConstant T P.Coefficientˣ,
          (gL u₀).hom =
            eL (LocallyConstant.map (fun a : P.Coefficientˣ ↦ (a : P.Coefficient)) u₀)) ∧
        (∀ u₀ : LocallyConstant T P.Coefficientˣ,
          (gM u₀).hom =
            eM (LocallyConstant.map (fun a : P.Coefficientˣ ↦ (a : P.Coefficient)) u₀)) ∧
        (∀ φ ψ : L ≅ M, ∃! u₀ : LocallyConstant T P.Coefficientˣ, ψ = φ ≪≫ gM u₀) ∧
        (∀ (φ : L ≅ M) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (y : Spec (.of Ω) ⟶ T) (v₀ : P.Coefficientˣ),
          ∃ ψ : L ≅ M, ψ = φ ≪≫ gM (LocallyConstant.const T v₀) ∧
            ∀ x : (finiteCoefficientModuleStalkFunctor y P.Ring).obj L,
              ((finiteCoefficientModuleStalkFunctor y P.Ring).map ψ.hom).hom x =
                (v₀ : P.Coefficient) •
                  ((finiteCoefficientModuleStalkFunctor y P.Ring).map φ.hom).hom x) := by
  sorry

end WeilConjectures
