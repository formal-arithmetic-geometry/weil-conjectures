/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic

import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.CategoryTheory.ScalarLocalizationTriangulated

import Mathlib.CategoryTheory.Triangulated.Triangulated
import Sheaf.Paper.SfScalarExtensionComposition
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom
import Mathlib.CategoryTheory.Shift.Localization
/-! # Exactness of intrinsic finite scalar extension

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
`sk-prop-sf-pf-reduction/lem-weil-scalar-extension-exact-triangulated.md`
(blueprint: lem-weil-scalar-extension-exact-triangulated).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe d u r v

open CategoryTheory

open scoped TensorProduct
open TensorProduct

private noncomputable def rawComparison
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [Limits.HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    ScalarLocalization R C p ⥤ Rationalization (Submonoid.powers p) C where
  obj X := (Rationalization.Q (Submonoid.powers p) C).obj X.obj
  map {X Y} f := Rationalization.tensorHomEquiv (Submonoid.powers p)
    (Localization.Away p) X.obj Y.obj f
  map_id X := by
    change Rationalization.tensorHomEquiv _ _ _ _ (1 ⊗ₜ[R] 𝟙 X.obj) = _
    simp
  map_comp {X Y Z} f g := by
    induction f using TensorProduct.induction_on with
    | zero => simp only [Limits.zero_comp, map_zero, Limits.zero_comp]
    | tmul a f =>
      induction g using TensorProduct.induction_on with
      | zero => simp only [Limits.comp_zero, map_zero, Limits.comp_zero]
      | tmul b g =>
        change Rationalization.tensorHomEquiv _ _ _ _
          (ScalarLocalization.composition R C p _ _ _ (b ⊗ₜ[R] g) (a ⊗ₜ[R] f)) = _
        rw [ScalarLocalization.composition_tmul]
        simp only [Rationalization.tensorHomEquiv_tmul, Functor.map_comp,
          Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]
      | add g h hg hh =>
        rw [Preadditive.comp_add X Y Z (a ⊗ₜ[R] f) g h]
        simp only [_root_.map_add]
        rw [hg, hh]
        exact (Preadditive.comp_add _ _ _ _ _ _).symm
    | add f h hf hh =>
      rw [Preadditive.add_comp X Y Z f h g]
      simp only [_root_.map_add]
      rw [hf, hh]
      exact (Preadditive.add_comp _ _ _ _ _ _).symm

private theorem rawLocalization
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [Limits.HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    (ScalarLocalization.localization R C p).IsLocalization
      (Rationalization.W (Submonoid.powers p) C) := by
  classical
  let M := Submonoid.powers p
  let E := rawComparison R C p
  have : E.Full := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).surjective⟩
  have : E.Faithful := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).injective⟩
  have : E.EssSurj := ⟨fun X ↦ by
    obtain ⟨Y, ⟨e⟩⟩ := Rationalization.exists_iso_obj X
    exact ⟨⟨Y⟩, ⟨e⟩⟩⟩
  have : E.IsEquivalence := {}
  let Q := ScalarLocalization.localization R C p
  have fac : Q ⋙ E ≅ Rationalization.Q M C :=
    NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      dsimp [Q, E, ScalarLocalization.localization, rawComparison]
      simp only [Category.comp_id, Category.id_comp,
        Rationalization.tensorHomEquiv_tmul, one_smul]
      rfl)
  exact Functor.IsLocalization.of_equivalence_target (Rationalization.Q M C)
    (Rationalization.W M C) Q E.asEquivalence.symm
    (Functor.isoWhiskerRight fac.symm E.inv ≪≫ (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft Q E.asEquivalence.unitIso.symm ≪≫ Q.rightUnitor)

namespace WeilConjectures

attribute [local irreducible] sfRationalTriangulationDatum

set_option linter.unusedVariables false in
/-- The completed rational scalar extension preserves shifts and distinguished triangles.
Source: blueprint order 1883; Stacks Tags 06XN, 05SE and 05R6
(blueprint: lem-weil-scalar-extension-exact-triangulated).

Proof, following every step of the DAG:

1. Use the completed coefficient sheaves, not discrete constant integral coefficients. Write
$B_m=(A_{L,m})_Y$, with the ring maps $\rho_m$ and restrictions $\operatorname{Res}^L_m$ of
[def-weil-integral-scalar-extension]. For any complex $P$ of $\widehat{\mathcal O}_{E,Y}$-modules,
set $V(P)=\prod_m\operatorname{Res}^L_m(P\otimes_{\widehat{\mathcal O}_{E,Y}}B_m)$ and
$h_P=1-s_P$, and define $H(P)=\operatorname{Cone}(h_P)[-1]$. These termwise products exist by
[lem-weil-proetale-countable-products-exact]. Thus $H(P)^n=V(P)^{n-1}\oplus V(P)^n$, with
differential $(y,x)\mapsto(-dy-h_Px,dx)$. On chain maps use the two diagonal product maps.
Additivity, identities and composition follow componentwise from tensor and product functoriality.
If $k$ is a chain homotopy between $u,v$, its product after tensoring is a degree $-1$ map $\bar
k$ commuting with the transition maps; the degree $-1$ map $k_H(y,x)=(-\bar k y,\bar k x)$ is a
homotopy between $H(u),H(v)$, since the off-diagonal terms cancel and the diagonal terms are
$V(u-v)$. Hence $H$ descends to homotopy categories.

2. The shift comparison $H(P[1])\longrightarrow H(P)[1]$ is $(y,x)\mapsto(-y,x)$ and is natural.
For a chain map $f:P\to Q$, termwise tensoring and products commute with the finite direct sums
defining its cone. Put the four coordinates of $H(C(f))^n$ in the order $(y_Q,y_P,x_Q,x_P)$. The
map $(y_Q,y_P,x_Q,x_P)\mapsto(y_Q,x_Q,-y_P,x_P)$ identifies it with $C(H(f))^n$. Indeed its
differential before this permutation is $(-d_Qy_Q-fy_P-h_Qx_Q,\ d_Py_P-h_Px_P,\ d_Qx_Q+fx_P,\
-d_Px_P)$, which after the permutation is exactly the cone differential of $H(f)$. Its inverse
sends $(a,b,c,d)$ to $(a,-c,b,d)$. This identification respects the cone inclusion. It also
respects the connecting arrow $-p$ using the displayed shift comparison: both maps on the $P$
coordinates are $(y_P,-x_P)$. Therefore $H$ carries cone triangles to cone triangles, including
the last arrow. By [lem-pur-homotopy-category-triangulated], every distinguished homotopy triangle
is isomorphic to such a cone triangle, and the target localization is exact. Consequently
$F=Q_LH:K(\widehat{\mathcal O}_{E,Y})\to D(\widehat{\mathcal O}_{L,Y})$ is exact.

3. Take as resolution class the K-flat complexes with flat terms over $\widehat{\mathcal
O}_{E,Y}$. Every complex admits a quasi-isomorphism from this class by [lem-pc-kflat-resolution].
For a quasi-isomorphism between two members, clause (1) of
[lem-weil-integral-scalar-extension-well-defined] says precisely that its $H$-image is a
quasi-isomorphism, hence $F$ inverts it. Apply [lem-pur-left-derived-from-kflat-class] to the
exact $F$ of step 2 and this class. Its everywhere defined left derived functor is exact and is
computed by $Q_LH(P)$ on every chosen K-flat resolution. This is the functor $K\mapsto
K\otimes_{\mathcal O_E}\mathcal O_L$ specified in [def-weil-integral-scalar-extension], with the
same induced maps and shift comparison; the comparison on resolutions is the natural
derived-functor comparison, not a choice of cones in the triangulated category.

4. The fixed prime satisfies $\ell\neq p$ by [def-weil-rationalization-karoubi], so the
coefficient hypotheses of both following lemmas hold. By
[lem-weil-integral-scalar-extension-constructible] this exact ambient functor maps
$D^b_c(Y,\mathcal O_E)$ into $D^b_c(Y,\mathcal O_L)$. Both are full triangulated subcategories
with the ambient distinguished triangles by [lem-weil-integral-constructible-triangulated],
applied for each coefficient field. Thus on these subcategories its shift comparison remains a
morphism, and the image of every distinguished triangle is still distinguished. Its $\mathcal
O_E$-linearity is clause (3) of [lem-weil-integral-scalar-extension-well-defined]. Denote this
restricted exact linear functor by $T$.

5. By [def-weil-rationalization-karoubi], the specified rational scalar-extension functor is
$T_{L/E}(K)=T(K)$ and $T_{L/E}(f\otimes a)=T(f)\otimes a$, where $a\in E\subset L$. Localize the
shift comparison of $T$ and its inverse. Naturality on $f\otimes a$ is the integral naturality
equation tensored with $a$, and extends to sums by additivity. The two inverse equations also
remain true after tensoring. This supplies a natural isomorphism $T_{L/E}(K[1])\simeq
T_{L/E}(K)[1]$; its iterates give all shifts. No identification of the $\mathcal O_E$- and
$\mathcal O_L$-localizations is needed.

6. Let $\Delta$ be distinguished in $D^b_c(Y,E)$. By
[lem-weil-linear-scalar-localization-triangulated] and [def-weil-rationalization-karoubi], it is
isomorphic to $Q_E(\Delta_0)$ for an integral distinguished triangle $\Delta_0$. With the shift
comparison of step 5, $T_{L/E}(Q_E(\Delta_0))=Q_L(T(\Delta_0))$: all three maps, including the
connecting map, are the integral images tensored with $1$. Step 4 makes $T(\Delta_0)$
distinguished and the cited localization theorem makes its $Q_L$-image distinguished. Applying
$T_{L/E}$ to the triangle isomorphism gives another triangle isomorphism. Hence $T_{L/E}(\Delta)$
is distinguished. Together with step 5 this proves both clauses of the item.
-/
theorem sfScalarExtension_exact_triangulated
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u}) :
    ∃ h : (sfRationalScalarExtension l E Y D.p hl L ι).CommShift ℤ,
      (fun [commShift : (sfRationalScalarExtension l E Y D.p hl L ι).CommShift ℤ] ↦
        (sfRationalScalarExtension l E Y D.p hl L ι).IsTriangulated) (commShift := h) := by
  classical
  let T := sfConstructibleIntegralScalarExtension D.p l hl E L ι Y
  let I := (sfIntegralConstructible l L Y).ι
  let H := (sfIntegralConstructible l E Y).ι ⋙ integralOrdinaryDerivedScalar l E L ι Y
  let e : T ⋙ I ≅ H :=
    (sfIntegralConstructible l L Y).liftCompιIso
      ((sfIntegralConstructible l E Y).ι ⋙ integralScalarExtension l E L ι Y)
      (fun X ↦ sfIntegralScalarExtension_constructible D.p l hl E L ι Y X.obj X.property) ≪≫
      (sfIntegralOrdinaryComparison l E L ι Y).symm
  let t : T.CommShift ℤ := Functor.CommShift.ofComp e ℤ
  have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  have : T.IsTriangulated := (Functor.isTriangulated_iff_comp_right e).2 inferInstance
  let Q := sfRationalConstructibleLocalization l E Y
  let Q' := sfRationalConstructibleLocalization l L Y
  let F := sfRationalScalarExtension l E Y D.p hl L ι
  have : Q.IsLocalization
      (Rationalization.W (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
        (sfIntegralConstructibleCategory l E Y)) :=
    rawLocalization (Padic.coefficientExtensionIntegers l E)
      (sfIntegralConstructibleCategory l E Y) (Padic.coefficientExtensionUniformizer l E)
  have hobj := (sfRationalScalarExtension_existsUnique l E Y D.p hl L ι).exists.choose_spec.2.1
  have hmap := (sfRationalScalarExtension_existsUnique l E Y D.p hl L ι).exists.choose_spec.2.2
  let c : Q ⋙ F ≅ T ⋙ Q' := NatIso.ofComponents
    (fun X ↦ eqToIso (hobj (Q.obj X))) (by
      intro X X' f
      change F.map (Q.map f) ≫ eqToHom (hobj (Q.obj X')) =
        eqToHom (hobj (Q.obj X)) ≫ Q'.map (T.map f)
      have hm := hmap X X' f 1
      have hm' : HEq (F.map (Q.map f)) (Q'.map (T.map f)) := by
        simp only [map_one] at hm
        exact hm
      exact eq_of_heq ((comp_eqToHom_heq _ _).trans
        (hm'.trans (eqToHom_comp_heq _ _).symm)))
  let W := Rationalization.W
    (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
    (sfIntegralConstructibleCategory l E Y)
  let : Localization.Lifting Q W (T ⋙ Q') F := ⟨c⟩
  let h : F.CommShift ℤ := Functor.commShiftOfLocalization Q W ℤ (T ⋙ Q') F
  refine ⟨h, ?_⟩
  have : NatTrans.CommShift c.hom ℤ :=
    inferInstanceAs (NatTrans.CommShift (Localization.Lifting.iso Q W (T ⋙ Q') F).hom ℤ)
  have : (Q ⋙ F).IsTriangulated := (Functor.isTriangulated_iff_of_iso c).2 inferInstance
  have : Q.mapArrow.EssSurj := Localization.essSurj_mapArrow Q W
  exact Functor.isTriangulated_of_precomp Q F

end WeilConjectures
