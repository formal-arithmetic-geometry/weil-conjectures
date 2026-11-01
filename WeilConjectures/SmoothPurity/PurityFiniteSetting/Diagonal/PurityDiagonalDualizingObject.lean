/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalOrdinaryOrientationGluing
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalOrdinaryOrientationNormalization
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalOrdinaryOrientationRigidity

/-! # The canonical smooth dualizing-object comparison

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation,
thm-pur-diagonal-dualizing-object.proof.md.
(blueprint: thm-pur-diagonal-dualizing-object).

The definitions are reexported unchanged from PurityDiagonalDualizingData so that
separate gluing, coordinate-normalization and rigidity lemmas can precede this theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The smooth dualizing object has its canonical Tate orientation on the full
finite-type k-domain, including nonseparated X and Y.
Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-prop-sp-orientation/thm-pur-diagonal-dualizing-object.md
(blueprint: thm-pur-diagonal-dualizing-object).

Proof:
1. Cover Y by finite-type affine opens V_i and put X_i = X times_Y V_i.
   The separated finite-type map X_i -> V_i makes X_i separated finite type
   over k. Smooth pure dimension d survives this base change.
2. Apply lem-pur-diagonal-base-change to obtain the specified comparison
   alpha_i:C(p1,Delta) -> omega_(f_i). The regular diagonal has normal bundle
   T_(X_i/V_i), of rank d, including rank zero.
3. thm-pur-dnc-invariance supplies the unique normalized map delta_i to the
   zero-section invariant of that normal bundle. cor-pur-vector-bundle-purity,
   normalized by the actual vector integration counit, restricts along zero
   to beta_i with target A_(X_i)(d)[2d]. Form beta_i delta_i alpha_i^-1.
   In etale coordinates this is exactly the ordered affine-space counit mate
   used in DiagonalOrientationNormalization; the Kummer class fixes its scalar.
4. On common affine refinements of target overlaps, all three canonical
   factors restrict to the same factors. Their coefficient comparisons send
   pure root tensors to their pullbacks. Thus the local orientations agree.
5. Put r=-2d and M=H^r(omega_f). Exact open restriction and the local comparisons
   make every other cohomology sheaf zero. Good truncation gives the natural
   roof omega_f <- tau_le_r omega_f -> M[-r]. Both arrows are quasi-isomorphisms.
   This argument applies on nonseparated X and does not use a separated-base
   concentration theorem globally.
6. Fully faithful single-complex embedding identifies the shifted local maps
   with maps of sheaves M -> A_X(d). Sheaf Hom gluing gives the global map and
   its inverse. Common refinements show independence of the affine cover.
   Every etale coordinate chart has the same affine counit normalization by
   the DNC and vector-bundle compatibility. Conversely these charts cover X;
   after removing the shift the sheaf axiom makes two normalized maps equal.
7. Finite etale/pro-etale comparison identifies the fixed root-line coefficients
   and the transported exceptional inverse image. Apply nu_X* to the normalized
   ordinary arrow and compose with diagonalDualizingComparison. Full faithfulness
   on these bounded-below etale-origin objects transports the same uniqueness.
   This is precisely the displayed comparison-unit equation, not bare Nonempty. -/
theorem existsUnique_diagonalDualizingObject (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :
    P.DiagonalDualizingConclusion d f aY := by
  let := isNoetherian_of_locallyOfFiniteType aY
  let := isNoetherian_of_locallyOfFiniteType (f ≫ aY)
  let : HasCompactification f := inferInstance
  obtain ⟨D, hD, _, _⟩ :=
    P.diagonalOrientationRefinement aY (f ≫ aY) f rfl d
  obtain ⟨e, he⟩ := P.diagonalOrdinaryOrientationGluing d f aY D
    (fun V V' hV hV' h ↦ (hD V V' hV hV' h).2)
  have hn := P.diagonalOrdinaryOrientationNormalization d f aY D e he
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  refine ⟨P.diagonalDualizingComparison f ≪≫ F.mapIso e, ⟨e, hn, rfl⟩, ?_⟩
  rintro θ ⟨e', hn', hθ⟩
  have he' := P.diagonalOrdinaryOrientationRigidity d f aY e' e hn' hn
  subst e'
  exact hθ

/-- The unique normalized comparison on the full finite-type k-domain.
Source: blueprint smooth dualizing object (blueprint: thm-pur-diagonal-dualizing-object).
The existence-and-uniqueness theorem fixes the arrow itself by coordinate counits;
choice is used only for this uniquely determined object, never for an arbitrary iso. -/
def diagonalDualizingObject (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  (P.existsUnique_diagonalDualizingObject d f aY).exists.choose

end WeilConjectures.PurityFiniteSetting
