/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization
public import Sheaf.Paper.Pur9Invertible
public import Sheaf.Algebra.Homology.DerivedTensor
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.Paper.CoprojectionCompositionMate
import Sheaf.Paper.EtaleRhoMonoidalMate
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.PurityCoprojection
import Sheaf.Paper.StandingExceptionalComposition

/-!
# Étale co-projection compatibility with normalized exceptional pullback

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-thm-regular/sk-thm-regular.proof.md`, Step 4(ii)
(blueprint: lem-pur-etale-coprojection-rho-compatibility).

## Main definitions

* `coprojectionRhoComparison`: the five-arrow normalized exceptional comparison.
* `pullbackComposition`: the canonical comparison on the second tensor factor.
* `etaleCoprojectionProperty`: the projection/counit characterization in étale coordinates.
* `coprojectionTensorPullback`, `coprojectionTensorHom`: the specified tensor arrows.

## Main statements

* `etale_coprojection_rho_compatibility`: the square for characterized co-projections commutes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

/-- The explicit five-arrow comparison in the statement. Source: blueprint Step 4(ii)
(blueprint: lem-pur-etale-coprojection-rho-compatibility). -/
noncomputable def coprojectionRhoComparison
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X U V : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [U.Over (Spec (.of P.field.k))]
    [V.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    (i : Z ⟶ X) (e : U ⟶ X) (v : V ⟶ Z) (iU : V ⟶ U)
    [i.IsOver (Spec (.of P.field.k))] [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e]
    [v.IsOver (Spec (.of P.field.k))] [iU.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v] [Etale v]
    [IsSeparated iU] [LocallyOfFiniteType iU] [QuasiCompact iU]
    [IsClosedImmersion iU]
    (hcomp : iU ≫ e = v ≫ i)
    (K : Etale.DerivedCategoryModule P.Coefficient X) :
    (exceptional P iU).obj ((pull P e).obj K) ≅
      (pull P v).obj ((exceptional P i).obj K) := by
  let c₁ := (comp P iU e).app K
  let c₂ := (comp P v i).app K
  let q := congr P (iU ≫ e) (v ≫ i) hcomp
  exact ((exceptional P iU).mapIso ((rho P e).app K).symm) ≪≫
    c₁.symm ≪≫ q.app K ≪≫ c₂ ≪≫ (rho P v).app ((exceptional P i).obj K)

/-- The canonical pullback-composition identification on the tensor factor. Source:
blueprint Step 4(ii) (blueprint: lem-pur-etale-coprojection-rho-compatibility). -/
noncomputable def pullbackComposition
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X U V : Scheme.{u}}
    (i : Z ⟶ X) (e : U ⟶ X) (v : V ⟶ Z) (iU : V ⟶ U)
    (hcomp : iU ≫ e = v ≫ i)
    (L : Etale.DerivedCategoryModule P.Coefficient X) :
    (pull P iU).obj ((pull P e).obj L) ≅
      (pull P v).obj ((pull P i).obj L) := by
  exact ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) iU e).app L).symm ≪≫
    eqToIso (by rw [hcomp]) ≪≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) v i).app L

/-- A co-projection is characterized by its inverse being the specified exceptional
transpose of inverse projection followed by counit tensor identity. Equivalently,
PF(GK,L); F(co.inv); eps(K tensor L) = eps(K) tensor id(L).
This is the canonical-map equation of `lem-pur-coprojection` in the étale-origin
coordinates used by `FiniteEtaleNormalization.exceptional`.
Source: main-20261015, `sk-lem-coprojection/lem-pur-coprojection.md`, canonical-map
paragraph (blueprint: lem-pur-etale-coprojection-rho-compatibility). -/
noncomputable def etaleCoprojectionProperty
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z W : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))] [W.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
    (i : Z ⟶ W) [i.IsOver (Spec (.of P.field.k))]
    [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    (K L : Etale.DerivedCategoryModule P.Coefficient W)
    (co : (exceptional P i).obj
        (Etale.DerivedCategory.etaleDerivedTensor P.Coefficient W K L) ≅
      Etale.DerivedCategory.etaleDerivedTensor P.Coefficient Z
        ((exceptional P i).obj K) ((pull P i).obj L)) : Prop :=
  letI := compactification P i
  co.inv = Etale.rightDerivedUpperShriekDerivedTensorMap P.Coefficient i K L

/-- The specified derived pullback tensor comparison, with its endpoint objects
written using the recorded finite tensor wrapper. Source: main-20261015, Step 4(ii),
mu_e and mu_v (blueprint: lem-pur-etale-coprojection-rho-compatibility). -/
noncomputable def coprojectionTensorPullback
    (Λ : Type (u + 1)) [CommRing Λ]
    {S T : Scheme.{u}} (f : S ⟶ T)
    (K L : Etale.DerivedCategoryModule Λ T) :
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor).obj
        (Etale.DerivedCategory.etaleDerivedTensor Λ T K L) ≅
      Etale.DerivedCategory.etaleDerivedTensor Λ S
        (((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor).obj K)
        (((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor).obj L) :=
  Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) f K L

/-- Tensor the two specified morphisms with the existing derived tensor bifunctor.
Source: main-20261015, Step 4(ii), right edge B tensor can
(blueprint: lem-pur-etale-coprojection-rho-compatibility). -/
noncomputable def coprojectionTensorHom
    (Λ : Type (u + 1)) [CommRing Λ] (S : Scheme.{u})
    {K K' L L' : Etale.DerivedCategoryModule Λ S}
    (a : K ⟶ K') (b : L ⟶ L') :
    Etale.DerivedCategory.etaleDerivedTensor Λ S K L ⟶
      Etale.DerivedCategory.etaleDerivedTensor Λ S K' L' :=
  Etale.derivedTensorHom (ModuleCat.{u + 1} Λ) a b

/-- The normalized exceptional comparison commutes with the canonical co-projections.
Both co-projections are universally quantified under their projection/counit
characterizations; every other edge is the specified canonical expression.
Source: main-20261015, `sk-thm-regular/sk-thm-regular.proof.md`, Step 4(ii)
(blueprint: lem-pur-etale-coprojection-rho-compatibility).

Proof:
1. Base change makes v étale and iU a closed immersion. Preservation of Dctf puts
   all objects in the domain. The exceptional compositors are the mates
   (`lem-sf-mate`) of `thm-sf-comp-composition`; together with the invertible
   normalized rho of `lem-pur-finite-etale-dualizing-normalization`, they give the
   displayed five-arrow comparison B, naturally in K.
2. Apply `lem-pur-coprojection` at i and iU. Its projection/counit equation says
   co.inv is kappa, the adjoint transpose fixed in
   `lem-pur-coprojection-composition-mate`. Invert the top and bottom
   co-projections and the tensor comparisons. The square is equivalent to
   kappa_iU; iU!(mu_e.inv); B_KL =
   (B_K tensor can); mu_v.inv; v*(kappa_i).
3. Expand the left side of this equality. Apply
   `lem-pur-etale-rho-monoidal-mate` at e and naturality of kappa_iU, then
   `lem-pur-coprojection-composition-mate` at (e,iU). Identify eiU with iv and
   apply that composition mate at (i,v). Naturality moves rho_v past v!(kappa_i).
   The rho-monoidal mate identity at v converts its kappa to mu_v.inv.
   The two pullback compositors combine to exactly pullbackComposition, giving
   the right side. Every factor is a compositor or normalized rho; no Ex_! occurs.
4. Invert the rearrangement in Step 2 to obtain the square. The invertibility
   used in Step 1 is supplied by `lem-sf-mate`, `thm-sf-comp-composition`, and the
   rho-normalization theorem. Naturality in K and the invertible L applies in
   particular to Tate twists and shifts, component by component. -/
theorem etale_coprojection_rho_compatibility
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X U V : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [U.Over (Spec (.of P.field.k))]
    [V.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    [IsSeparated (U ↘ Spec (.of P.field.k))]
    [IsSeparated (V ↘ Spec (.of P.field.k))]
    (i : Z ⟶ X) (e : U ⟶ X) (v : V ⟶ Z) (iU : V ⟶ U)
    [i.IsOver (Spec (.of P.field.k))] [e.IsOver (Spec (.of P.field.k))]
    [IsClosedImmersion i] [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e]
    [v.IsOver (Spec (.of P.field.k))] [iU.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v] [Etale v]
    [IsSeparated iU] [LocallyOfFiniteType iU] [QuasiCompact iU]
    [IsClosedImmersion iU]
    (sq : IsPullback iU v e i)
    (K L : Etale.DerivedCategoryModule P.Coefficient X)
    (_hK : domain P X K) (_hL : domain P X L)
    (_hInv : Etale.DerivedCategory.isInvertible P.Coefficient X L)
    (co_i : (exceptional P i).obj
        (Etale.DerivedCategory.etaleDerivedTensor P.Coefficient X K L) ≅
      Etale.DerivedCategory.etaleDerivedTensor P.Coefficient Z
        ((exceptional P i).obj K) ((pull P i).obj L))
    (co_iU : (exceptional P iU).obj
        (Etale.DerivedCategory.etaleDerivedTensor P.Coefficient U
          ((pull P e).obj K) ((pull P e).obj L)) ≅
      Etale.DerivedCategory.etaleDerivedTensor P.Coefficient V
        ((exceptional P iU).obj ((pull P e).obj K))
        ((pull P iU).obj ((pull P e).obj L)))
    (_hco_i : etaleCoprojectionProperty P i K L co_i)
    (_hco_iU : etaleCoprojectionProperty P iU
      ((pull P e).obj K) ((pull P e).obj L) co_iU) :
    (exceptional P iU).map (coprojectionTensorPullback P.Coefficient e K L).hom ≫
        co_iU.hom ≫
        coprojectionTensorHom P.Coefficient V
          (coprojectionRhoComparison P i e v iU sq.w K).hom
          (pullbackComposition P i e v iU sq.w L).hom =
      (coprojectionRhoComparison P i e v iU sq.w
        (Etale.DerivedCategory.etaleDerivedTensor P.Coefficient X K L)).hom ≫
        (pull P v).map co_i.hom ≫
        (coprojectionTensorPullback P.Coefficient v ((exceptional P i).obj K)
          ((pull P i).obj L)).hom := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteEtaleNormalization
