/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalTateCoprojectionCoherence
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import Mathlib.FieldTheory.Perfect
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.CategoryTheory.Whiskering

/-! # Étale restriction of the regular comparison

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/
sk-thm-regular.proof.md, Steps 4(i)--(ii), with the specified comparison of
Steps 1--2; adjunction-normalized étale locality
(blueprint: lem-pur-regular-comparison-etale-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The specified smooth orientation in the ordered shifted-root presentation.
It is the ordinary witness of the unique normalized diagonal dualizing object.
The coordinate counit normalization fixes this witness, including its scalar;
no comparison with an abstract Tate datum is selected.
This is the orientation `Π_{a_T}` that `pur9-rg-def-phi` uses, and the `Π_f` from
which `smoothPurityMap` (def-pur-smooth-purity-map) builds `γ`. At the coefficient
unit `θ` is the unit constraint (`smoothPurityTheta_unit`,
lem-route-smooth-purity-theta-unit), so this is the node's `P_T = γ_{a_T,A_k}^{-1}`
after the canonical coefficient-unit identifications.
Source: `sk-thm-regular`, Steps 1 and 4(ii), and the coordinate normalization of
`thm-pur-diagonal-dualizing-object` (blueprint:
`lem-pur-regular-comparison-etale-restriction`). -/
noncomputable def regularCanonicalDualizingIso
    (P : WeilConjectures.PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (aT : T ⟶ Spec (.of P.field.k)) (d : ℕ)
    [HasCompactification aT] [HasInvertibleExponent P.Coefficient T]
    [QuasiCompact aT] [IsSeparated aT] [LocallyOfFiniteType aT]
    [SmoothOfRelativeDimension d aT] :
    dualizingComplex P.Coefficient aT ≅ P.diagonalTwistEtale T d := by
  let e := Classical.choose
    (P.existsUnique_diagonalDualizingObject d aT (𝟙 (Spec (.of P.field.k)))).exists.choose_spec
  exact eqToIso (by rfl) ≪≫ e

/-- The specified objectwise exceptional base-change map.  With
`G_h = R h^!`, `S_h = L h^*`, it is exactly
`ρ_v c_{i,v} c_{u,i_U}^{-1} G_{i_U}(ρ_u^{-1})`, where `ρ` and the
exceptional compositor are the recorded constructions.  The equality of the
Cartesian composites is used only through `congr`, so no arbitrary map is
introduced.
Source: Step 4(i) of `sk-thm-regular` (blueprint:
`lem-pur-regular-comparison-etale-restriction`). -/
noncomputable def regularRestrictionBaseChange
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X U V : Scheme.{u}}
    (i : Z ⟶ X) (uMap : U ⟶ X) (v : V ⟶ Z) (iU : V ⟶ U)
    (hcart : iU ≫ uMap = v ≫ i)
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
    [IsSeparated (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    [IsSeparated (V ↘ Spec (.of P.field.k))]
    [i.IsOver (Spec (.of P.field.k))] [uMap.IsOver (Spec (.of P.field.k))]
    [v.IsOver (Spec (.of P.field.k))] [iU.IsOver (Spec (.of P.field.k))]
    [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    [IsSeparated uMap] [LocallyOfFiniteType uMap] [QuasiCompact uMap]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [IsSeparated iU] [LocallyOfFiniteType iU] [QuasiCompact iU]
    [Etale uMap] [Etale v] [IsClosedImmersion i] [IsClosedImmersion iU]
    (K : Etale.DerivedCategoryModule P.Coefficient X) :
    (FiniteEtaleNormalization.exceptional P iU).obj ((FiniteEtaleNormalization.pull P uMap).obj K) ⟶
      (FiniteEtaleNormalization.pull P v).obj ((FiniteEtaleNormalization.exceptional P i).obj K) :=
  (FiniteEtaleNormalization.exceptional P iU).map
      ((FiniteEtaleNormalization.rho P uMap).inv.app K) ≫
    (FiniteEtaleNormalization.comp P iU uMap).inv.app K ≫
    (FiniteEtaleNormalization.congr P (iU ≫ uMap) (v ≫ i) hcart).hom.app K ≫
    (FiniteEtaleNormalization.comp P v i).hom.app K ≫
    (FiniteEtaleNormalization.rho P v).hom.app
      ((FiniteEtaleNormalization.exceptional P i).obj K)

/-- The same comparison as a natural isomorphism of derived functors.
Source: Step 4(i), the canonical adjunction-preserving base-change square in
`sk-thm-regular` (blueprint: `lem-pur-regular-comparison-etale-restriction`). -/
noncomputable def regularRestrictionBaseChangeIso
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X U V : Scheme.{u}}
    (i : Z ⟶ X) (uMap : U ⟶ X) (v : V ⟶ Z) (iU : V ⟶ U)
    (hcart : iU ≫ uMap = v ≫ i)
    [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [U.Over (Spec (.of P.field.k))] [V.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [IsSeparated (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    [i.IsOver (Spec (.of P.field.k))] [uMap.IsOver (Spec (.of P.field.k))]
    [v.IsOver (Spec (.of P.field.k))] [iU.IsOver (Spec (.of P.field.k))]
    [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    [IsSeparated uMap] [LocallyOfFiniteType uMap] [QuasiCompact uMap]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [IsSeparated iU] [LocallyOfFiniteType iU] [QuasiCompact iU]
    [Etale uMap] [Etale v] [IsClosedImmersion i] [IsClosedImmersion iU] :
    (FiniteEtaleNormalization.pull P uMap ⋙
      FiniteEtaleNormalization.exceptional P iU) ≅
      (FiniteEtaleNormalization.exceptional P i ⋙
        FiniteEtaleNormalization.pull P v) :=
  Functor.isoWhiskerRight
      (FiniteEtaleNormalization.rho P uMap).symm
      (FiniteEtaleNormalization.exceptional P iU) ≪≫
    (FiniteEtaleNormalization.comp P iU uMap).symm ≪≫
    FiniteEtaleNormalization.congr P (iU ≫ uMap) (v ≫ i) hcart ≪≫
    FiniteEtaleNormalization.comp P v i ≪≫
    Functor.isoWhiskerLeft (FiniteEtaleNormalization.exceptional P i)
      (FiniteEtaleNormalization.rho P v)

/-- The natural isomorphism has exactly the specified five-factor component.
Source: regular-immersion proof Step 4(i), expanding the displayed comparison
(blueprint: lem-pur-regular-restriction-comparison-data). -/
theorem regularRestrictionBaseChangeIso_hom_app
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X U V : Scheme.{u}}
    (i : Z ⟶ X) (uMap : U ⟶ X) (v : V ⟶ Z) (iU : V ⟶ U)
    (hcart : iU ≫ uMap = v ≫ i)
    [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [U.Over (Spec (.of P.field.k))] [V.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [IsSeparated (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    [IsSeparated (V ↘ Spec (.of P.field.k))]
    [i.IsOver (Spec (.of P.field.k))] [uMap.IsOver (Spec (.of P.field.k))]
    [v.IsOver (Spec (.of P.field.k))] [iU.IsOver (Spec (.of P.field.k))]
    [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    [IsSeparated uMap] [LocallyOfFiniteType uMap] [QuasiCompact uMap]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [IsSeparated iU] [LocallyOfFiniteType iU] [QuasiCompact iU]
    [Etale uMap] [Etale v] [IsClosedImmersion i] [IsClosedImmersion iU]
    (K : Etale.DerivedCategoryModule P.Coefficient X) :
    (regularRestrictionBaseChangeIso P i uMap v iU hcart).hom.app K =
      regularRestrictionBaseChange P i uMap v iU hcart K := by
  simp only [regularRestrictionBaseChangeIso, regularRestrictionBaseChange,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app]

/-- The oriented Step 1 comparison commutes with the specified restriction map
when its dualizing square and its two orientation squares commute. This is the
formal step before applying either co-projection or cancelling a Tate factor.
Source: regular-immersion proof Step 4(ii); naturality at the X-orientation,
followed by cancellation of the two coefficient comparisons and functoriality
(blueprint: lem-pur-regular-restriction-comparison-data). -/
theorem regularRestrictionOrientedComparison
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X U V : Scheme.{u}}
    (i : Z ⟶ X) (uMap : U ⟶ X) (v : V ⟶ Z) (iU : V ⟶ U)
    (hcart : iU ≫ uMap = v ≫ i)
    [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [U.Over (Spec (.of P.field.k))] [V.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [IsSeparated (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    [IsSeparated (V ↘ Spec (.of P.field.k))]
    [i.IsOver (Spec (.of P.field.k))] [uMap.IsOver (Spec (.of P.field.k))]
    [v.IsOver (Spec (.of P.field.k))] [iU.IsOver (Spec (.of P.field.k))]
    [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    [IsSeparated uMap] [LocallyOfFiniteType uMap] [QuasiCompact uMap]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [IsSeparated iU] [LocallyOfFiniteType iU] [QuasiCompact iU]
    [Etale uMap] [Etale v] [IsClosedImmersion i] [IsClosedImmersion iU]
    {WX TX : Etale.DerivedCategoryModule P.Coefficient X}
    {WU TU : Etale.DerivedCategoryModule P.Coefficient U}
    {WZ TZ : Etale.DerivedCategoryModule P.Coefficient Z}
    {WV TV : Etale.DerivedCategoryModule P.Coefficient V}
    (b : WZ ≅ (FiniteEtaleNormalization.exceptional P i).obj WX)
    (bU : WV ≅ (FiniteEtaleNormalization.exceptional P iU).obj WU)
    (Eu : WU ≅ (FiniteEtaleNormalization.pull P uMap).obj WX)
    (Ev : WV ≅ (FiniteEtaleNormalization.pull P v).obj WZ)
    (PX : WX ≅ TX) (PZ : WZ ≅ TZ) (PU : WU ≅ TU) (PV : WV ≅ TV)
    (Cu : (FiniteEtaleNormalization.pull P uMap).obj TX ≅ TU)
    (Cv : (FiniteEtaleNormalization.pull P v).obj TZ ≅ TV)
    (hb : bU.hom ≫ (FiniteEtaleNormalization.exceptional P iU).map Eu.hom ≫
        regularRestrictionBaseChange P i uMap v iU hcart WX =
      Ev.hom ≫ (FiniteEtaleNormalization.pull P v).map b.hom)
    (hu : PU.hom = Eu.hom ≫ (FiniteEtaleNormalization.pull P uMap).map PX.hom ≫ Cu.hom)
    (hv : PV.hom = Ev.hom ≫ (FiniteEtaleNormalization.pull P v).map PZ.hom ≫ Cv.hom) :
    PV.inv ≫ bU.hom ≫ (FiniteEtaleNormalization.exceptional P iU).map PU.hom ≫
        (FiniteEtaleNormalization.exceptional P iU).map Cu.inv ≫
        regularRestrictionBaseChange P i uMap v iU hcart TX =
      Cv.inv ≫ (FiniteEtaleNormalization.pull P v).map
        (PZ.inv ≫ b.hom ≫ (FiniteEtaleNormalization.exceptional P i).map PX.hom) := by
  simpa only [regularRestrictionBaseChangeIso_hom_app] using
    CategoryTheory.regularOrientedRestrictionNaturality
    (FiniteEtaleNormalization.pull P uMap) (FiniteEtaleNormalization.exceptional P i)
    (FiniteEtaleNormalization.exceptional P iU) (FiniteEtaleNormalization.pull P v)
    (regularRestrictionBaseChangeIso P i uMap v iU hcart).hom
    b bU Eu Ev PX PZ PU PV Cu Cv
    (by simpa only [regularRestrictionBaseChangeIso_hom_app] using hb) hu hv

/-- Pasting law for the actual exceptional restriction comparison.  For a further
étale square, this is the equality of the composite canonical maps after the
canonical derived-pullback composition isomorphisms.
Source: Step 4(ii), the further-étale restriction compatibility in
`sk-thm-regular` (blueprint: `lem-pur-regular-comparison-etale-restriction`). -/
noncomputable def regularRestrictionFurtherRestriction
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X U V : Scheme.{u}}
    (i : Z ⟶ X) (uMap : U ⟶ X) (v : V ⟶ Z) (iU : V ⟶ U)
    (hcart : iU ≫ uMap = v ≫ i)
    [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [U.Over (Spec (.of P.field.k))] [V.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [IsSeparated (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    [IsSeparated (V ↘ Spec (.of P.field.k))]
    [i.IsOver (Spec (.of P.field.k))] [uMap.IsOver (Spec (.of P.field.k))]
    [v.IsOver (Spec (.of P.field.k))] [iU.IsOver (Spec (.of P.field.k))]
    [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    [IsSeparated uMap] [LocallyOfFiniteType uMap] [QuasiCompact uMap]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [IsSeparated iU] [LocallyOfFiniteType iU] [QuasiCompact iU]
    [Etale uMap] [Etale v] [IsClosedImmersion i] [IsClosedImmersion iU] : Prop :=
  ∀ {U' V' : Scheme.{u}} (w : U' ⟶ U) (t : V' ⟶ V) (iU' : V' ⟶ U')
    (hw : iU' ≫ w = t ≫ iU)
    [U'.Over (Spec (.of P.field.k))] [V'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U' ↘ Spec (.of P.field.k))]
    [QuasiCompact (U' ↘ Spec (.of P.field.k))]
    [IsSeparated (U' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (V' ↘ Spec (.of P.field.k))]
    [QuasiCompact (V' ↘ Spec (.of P.field.k))]
    [IsSeparated (V' ↘ Spec (.of P.field.k))]
    [w.IsOver (Spec (.of P.field.k))] [t.IsOver (Spec (.of P.field.k))]
    [iU'.IsOver (Spec (.of P.field.k))]
    [IsSeparated w] [LocallyOfFiniteType w] [QuasiCompact w]
    [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]
    [IsSeparated (w ≫ uMap)] [IsSeparated (t ≫ v)]
    [IsSeparated iU'] [LocallyOfFiniteType iU'] [QuasiCompact iU']
    [Etale w] [Etale t] [IsClosedImmersion iU'] ,
    regularRestrictionBaseChangeIso P i (w ≫ uMap) (t ≫ v) iU'
        (by
          calc
            iU' ≫ w ≫ uMap = (iU' ≫ w) ≫ uMap := by simp only [Category.assoc]
            _ = (t ≫ iU) ≫ uMap := by rw [hw]
            _ = t ≫ (iU ≫ uMap) := by simp only [Category.assoc]
            _ = t ≫ (v ≫ i) := by rw [hcart]
            _ = (t ≫ v) ≫ i := by simp only [Category.assoc]) =
      Functor.isoWhiskerRight
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
            w uMap (w ≫ uMap) rfl) (FiniteEtaleNormalization.exceptional P iU') ≪≫
        Functor.isoWhiskerLeft (FiniteEtaleNormalization.pull P uMap)
          (regularRestrictionBaseChangeIso P iU w t iU' hw) ≪≫
        Functor.isoWhiskerRight
          (regularRestrictionBaseChangeIso P i uMap v iU hcart)
          (FiniteEtaleNormalization.pull P t) ≪≫
        Functor.isoWhiskerLeft (FiniteEtaleNormalization.exceptional P i)
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
            t v (t ≫ v) rfl).symm

/-- Étale restriction preserves the specified regular comparison.  Put
`V = Z ×_X U`, `v = pullback.fst i u`, and `i_U = pullback.snd i u`.
`regularDiagonalComparisonPhi` is the `Φ` of the recorded cancellation declaration,
and `regularRestrictionBaseChange` is the objectwise map
`B_K = ρ_v c_{i,v,K} c_{u,i_U,K}^{-1} G_{i_U}(ρ_u^{-1})`.
The second conjunct is the natural-transformation pasting law for a further
étale map, expressed using the same canonical `regularRestrictionBaseChangeIso`.

Proof (postponed): étale and closed-immersion base change gives `v` and `i_U`,
and smooth relative-dimension permanence gives the dimensions.  Expanding the
five factors of `B` gives the adjunction-normalized formula in Step 2.
Write C_u(d), C_v(d) for the normalized finite-root pullback maps, and
E_u = rho_u composed with the exceptional compositor at A_k (similarly E_v).
The four intermediate equations, in ordinary right-to-left composition order, are:
(1) B_omegaX o G_iU(E_u) o bU = S_v(b) o E_v;
(2) P_U = C_u(nX) o S_u(P_X) o E_u and
    P_V = C_v(m) o S_v(P_Z) o E_v;
(3) B_Tn o G_iU(C_u(nX)^-1) o r_U = C_v(m)^-1 o S_v(r_i),
    where r_i = G_i(P_X) o b o P_Z^-1;
(4) after co-projection and the same source/target coefficient identifications,
    (B_AX tensor 1) o q_U = S_v(q_i).
Tensor cancellation is uniquely characterized by its projection/counit equation,
so (4) gives the displayed Phi equality with these exact root pullback maps.
Expanding two successive five-factor words, using compositor associativity and
rho composition, gives B_uw,i = S_t(B_u,i) o B_w,iU under the two canonical
pullback-composition isomorphisms, which is the second conjunct.
All unit equations also apply when c = 0, m = 0, u is the identity, or a scheme
is empty. Negative twists occur only in the equivalent cancellation conclusion.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/
sk-thm-regular.proof.md, Steps 4(i)--(ii)
(blueprint: lem-pur-regular-comparison-etale-restriction). -/
def regularComparisonEtaleRestrictionStatement
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X U : Scheme.{u}}
    (i : Z ⟶ X) (uMap : U ⟶ X)
    [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [IsSeparated (U ↘ Spec (.of P.field.k))]
    [i.IsOver (Spec (.of P.field.k))] [uMap.IsOver (Spec (.of P.field.k))]
    [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    [IsSeparated uMap] [LocallyOfFiniteType uMap] [QuasiCompact uMap]
    [Etale uMap] [IsClosedImmersion i]
    [HasInvertibleExponent P.Coefficient X]
    [HasInvertibleExponent P.Coefficient Z]
    [HasInvertibleExponent P.Coefficient U]
    (nX m c : ℕ) (hdim : nX = m + c)
    [SmoothOfRelativeDimension nX (X ↘ Spec (.of P.field.k))]
    [SmoothOfRelativeDimension m (i ≫ (X ↘ Spec (.of P.field.k)))]
    [SmoothOfRelativeDimension nX (uMap ≫ (X ↘ Spec (.of P.field.k)))] : Prop :=
    let V := pullback i uMap
    letI : V.Over (Spec (.of P.field.k)) :=
      ⟨pullback.snd i uMap ≫ uMap ≫ (X ↘ Spec (.of P.field.k))⟩
    letI : HasInvertibleExponent P.Coefficient V :=
      HasInvertibleExponent.of_hom (pullback.fst i uMap)
    letI : LocallyOfFiniteType (V ↘ Spec (.of P.field.k)) := by
      change LocallyOfFiniteType
        (pullback.snd i uMap ≫ uMap ≫ (X ↘ Spec (.of P.field.k)))
      infer_instance
    letI : QuasiCompact (V ↘ Spec (.of P.field.k)) := by
      change QuasiCompact
        (pullback.snd i uMap ≫ uMap ≫ (X ↘ Spec (.of P.field.k)))
      infer_instance
    letI : IsSeparated (pullback i uMap ↘ Spec (.of P.field.k)) := by
      change IsSeparated
        (pullback.snd i uMap ≫ uMap ≫ (X ↘ Spec (.of P.field.k)))
      infer_instance
    let v := pullback.fst i uMap
    let iU := pullback.snd i uMap
    letI : (pullback.fst i uMap).IsOver (Spec (.of P.field.k)) := by
      refine ⟨?_⟩
      change pullback.fst i uMap ≫ (Z ↘ Spec (.of P.field.k)) =
        pullback.snd i uMap ≫ uMap ≫ (X ↘ Spec (.of P.field.k))
      calc
        pullback.fst i uMap ≫ (Z ↘ Spec (.of P.field.k)) =
            pullback.fst i uMap ≫ i ≫ (X ↘ Spec (.of P.field.k)) := by
              simpa only [Category.assoc] using congrArg
                (fun q => pullback.fst i uMap ≫ q)
                (comp_over i (Spec (.of P.field.k))).symm
        _ = pullback.snd i uMap ≫ uMap ≫ (X ↘ Spec (.of P.field.k)) := by
              simpa only [Category.assoc] using congrArg
                (fun q => q ≫ (X ↘ Spec (.of P.field.k)))
                (pullback.condition (f := i) (g := uMap))
    letI : (pullback.snd i uMap).IsOver (Spec (.of P.field.k)) := by
      refine ⟨?_⟩
      change pullback.snd i uMap ≫ (U ↘ Spec (.of P.field.k)) =
        pullback.snd i uMap ≫ uMap ≫ (X ↘ Spec (.of P.field.k))
      simpa only [Category.assoc] using congrArg
        (fun q => pullback.snd i uMap ≫ q)
        (comp_over uMap (Spec (.of P.field.k))).symm
    letI : Etale v := by
      dsimp [v]
      infer_instance
    letI : IsClosedImmersion iU := by
      dsimp [iU]
      infer_instance
    let aX := X ↘ Spec (.of P.field.k)
    let aZ := i ≫ aX
    let aU := uMap ≫ aX
    let aV := iU ≫ aU
    letI : SmoothOfRelativeDimension m aV := by
      haveI : SmoothOfRelativeDimension 0 v :=
        (Etale.iff_smoothOfRelativeDimension_zero v).mp inferInstance
      have hv : SmoothOfRelativeDimension m (v ≫ aZ) := by
        simpa using (smoothOfRelativeDimension_comp (n := 0) (m := m) v aZ)
      rw [show aV = v ≫ aZ by
        change (pullback.snd i uMap ≫ uMap) ≫ aX =
          (pullback.fst i uMap ≫ i) ≫ aX
        simpa only [Category.assoc] using congrArg (fun q => q ≫ aX)
          (pullback.condition (f := i) (g := uMap)).symm]
      exact hv
    letI : HasCompactification aX := inferInstance
    letI : HasCompactification aZ := inferInstance
    letI : HasCompactification aU := inferInstance
    letI : HasCompactification aV := inferInstance
    let W_X := dualizingComplex P.Coefficient aX
    let W_Z := dualizingComplex P.Coefficient aZ
    let W_U := dualizingComplex P.Coefficient aU
    let W_V := dualizingComplex P.Coefficient aV
    let P_X : W_X ≅ P.diagonalTwistEtale X nX := by
      simpa [W_X] using (regularCanonicalDualizingIso P aX nX)
    let P_Z : W_Z ≅ P.diagonalTwistEtale Z m := by
      simpa [W_Z] using (regularCanonicalDualizingIso P aZ m)
    let P_U : W_U ≅ P.diagonalTwistEtale U nX := by
      simpa [W_U] using (regularCanonicalDualizingIso P aU nX)
    let P_V : W_V ≅ P.diagonalTwistEtale V m := by
      simpa [W_V] using (regularCanonicalDualizingIso P aV m)
    let b := (WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition
      P.Coefficient i aX).app (constantComplex P.Coefficient (Spec (.of P.field.k)))
    let bU := (WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition
      P.Coefficient iU aU).app (constantComplex P.Coefficient (Spec (.of P.field.k)))
    (∀ t : OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates,
      regularDiagonalComparisonPhi P iU aU m nX c hdim W_U W_V bU P_U P_V ≫
        (FiniteEtaleNormalization.exceptional P iU).map
          ((vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates t uMap (P.diagonalExponent_isUnit aX) c).inv) ≫
        regularRestrictionBaseChange P i uMap v iU (pullback.condition (f := i) (g := uMap)).symm
          (P.diagonalTwistEtale X c) =
      (leftDerivedUpperStarConstantComplexIso P.Coefficient v).inv ≫
        (FiniteEtaleNormalization.pull P v).map
          (regularDiagonalComparisonPhi P i aX m nX c hdim W_X W_Z b P_X P_Z)) ∧
    regularRestrictionFurtherRestriction P i uMap v iU
        ((pullback.condition (f := i) (g := uMap)).symm)

end AlgebraicGeometry.Etale
