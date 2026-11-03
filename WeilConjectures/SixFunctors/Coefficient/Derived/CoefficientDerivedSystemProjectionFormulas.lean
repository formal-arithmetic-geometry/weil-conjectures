/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemGammaProjectionTransport
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemHomProjectionTransport
public import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
public import WeilConjectures.SixFunctors.Coefficient.CoefficientHomZeroClass

/-! # Actual finite projections of coefficient gamma

Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 08JA, 0D6E and 0941;
the evaluated enriched projection formula and its normalized degree-zero calculation
(blueprint: lem-coef-derived-system-projection-formulas).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The finite projection of the canonical enriched scalar comparison is the transpose
of the projected evaluation. Its action on derived morphisms is scalar extension
followed by the specified counit.

Source: blueprint `det-prop-scalar-six-tensor-hom`, proof (1) and the paragraph
"It is v": the comparisons retain the evaluation pairings, units and counits;
Stacks 07A6 and 08J9.
(blueprint: lem-coef-derived-system-projection-formulas).

Proof: apply the five defining Hom bijections to the map obtained by internal Hom of
q followed by the inverse canonical comparison. Postcomposition by the comparison
cancels its inverse. Undo the closed transpose and scalar transpose, then the tensor
comparison and the target closed transpose. This gives scalar extension of the
uncurried evaluation, followed by scalar extension of q and the scalar counit.
For an ordinary derived morphism h, the inverse scalar adjunction is F(h;q) followed
by the counit; functoriality gives the displayed formula. This is the degree-zero
formula under the recorded identification of H-zero global Hom with derived morphisms.
The argument allows zero objects, an empty site, identity coefficient changes, and
nonflat quotient changes; no preservation of K-injectives by evaluation is asserted. -/
theorem coefficientDerivedSystemProjectionFormulas (P L : A) (N : B) (q : L ⟶ U.obj N) :
    (∀ (X : A) (g : X ⟶ H.obj (op P, L)),
      (adj.homEquiv X (I.obj (op (F.obj P), N))).symm
          (g ≫ H.map (Prod.mkHom (𝟙 (op P)) q) ≫
            (ClosedScalarHom.iso S T adj μ).inv.app (op P, N)) =
        T.transpose (F.obj X) (F.obj P) N
          ((μ.app (X, P)).inv ≫
            F.map ((S.transpose X P L).symm g) ≫ F.map q ≫ adj.counit.app N)) ∧
    (∀ h : P ⟶ L, (adj.homEquiv P N).symm (h ≫ q) =
      F.map h ≫ F.map q ≫ adj.counit.app N) := by
  constructor
  · intro X g
    let z := g ≫ H.map (Prod.mkHom (𝟙 (op P)) q)
    let t := z ≫ (ClosedScalarHom.iso S T adj μ).inv.app (op P, N)
    have ht : ClosedScalarHom.bijection S T adj μ X P N t = z := by
      rw [ClosedScalarHom.representing]
      dsimp only [t]
      rw [Category.assoc, Iso.inv_hom_id_app]
      exact Category.comp_id z
    have hz : (S.transpose X P (U.obj N)).symm z =
        (S.transpose X P L).symm g ≫ q := by
      simpa [z, CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
        Prod.sectR] using (S.adjunction P).homEquiv_naturality_right_symm g q
    dsimp only [ClosedScalarHom.bijection, Equiv.trans_apply, Iso.homCongr,
      Equiv.coe_fn_mk, Iso.symm_inv, Iso.refl_hom] at ht
    simp only [Category.comp_id] at ht
    have ht' := (S.transpose X P (U.obj N)).eq_symm_apply.mpr ht
    rw [hz] at ht'
    have ht'' := (adj.homEquiv (S.tensor.obj (X, P)) N).eq_symm_apply.mpr ht'
    conv_rhs at ht'' => rw [adj.homEquiv_counit, F.map_comp]
    apply (T.transpose (F.obj X) (F.obj P) N).symm.injective
    rw [Equiv.symm_apply_apply]
    apply (cancel_epi (μ.app (X, P)).hom).mp
    simpa only [t, z, Category.assoc, Iso.hom_inv_id_assoc] using ht''
  · intro h
    rw [adj.homEquiv_counit, F.map_comp, Category.assoc]

/-- The actual zero-cycle normalization gives the same finite scalar adjunct.
Source: Stacks 08JA, 079P, and the scalar unit/counit calculation in the current
blueprint `det-prop-scalar-six-tensor-hom`.
(blueprint: lem-coef-derived-system-projection-formulas).

Proof: naturality of the uniquely normalized Hom-zero equivalence sends internal
Hom of q to postcomposition by q. Its inverse sends h to the recorded zero class.
The inverse scalar adjunction is extension followed by the specified counit;
functoriality gives the claimed composition. No arbitrary Hom equivalence is used. -/
theorem coefficientDerivedSystemProjectionFormulas_homZero
    {C : Type c} [Category.{d} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c d r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c d r}]
    (R : Sheaf J CommRingCat.{max c d r})
    [HasDerivedCategory.{z} (SheafOfModules.{max c d r}
      ((sheafCompose J (forget₂ CommRingCat.{max c d r} RingCat.{max c d r})).obj R))]
    {B : Type b} [Category.{w} B]
    {F : DerivedCategory (SheafOfModules.{max c d r}
      ((sheafCompose J (forget₂ CommRingCat.{max c d r} RingCat.{max c d r})).obj R)) ⥤ B}
    {U : B ⥤ DerivedCategory (SheafOfModules.{max c d r}
      ((sheafCompose J (forget₂ CommRingCat.{max c d r} RingCat.{max c d r})).obj R))}
    (adj : F ⊣ U)
    (P L : DerivedCategory (SheafOfModules.{max c d r}
      ((sheafCompose J (forget₂ CommRingCat.{max c d r} RingCat.{max c d r})).obj R)))
    (N : B) (q : L ⟶ U.obj N) (h : P ⟶ L) :
    (adj.homEquiv P N).symm
      (coefficientHomZeroEquiv.{r, c, d, z} J R P (U.obj N)
        (((@DerivedCategory.homologyFunctor AddCommGrpCat.{max c d r} _ _
          (HasDerivedCategory.standard _) 0).map
            ((coefficientGlobalSections.{r, c, d} J R).map
              ((derivedInternalHomOfUniverses.{c, d, r, z} J R).map
                (Prod.mkHom (𝟙 (op P)) q))))
          ((coefficientHomZeroEquiv.{r, c, d, z} J R P L).symm h))) =
      F.map h ≫ F.map q ≫ adj.counit.app N := by
  have he := (coefficientHomZeroEquiv_exists.{r, c, d, z} J R).choose_spec.1.1
  have hq := he P L P (U.obj N) (𝟙 P) q
    ((coefficientHomZeroEquiv.{r, c, d, z} J R P L).symm h)
  change coefficientHomZeroEquiv.{r, c, d, z} J R P (U.obj N) _ = _ at hq
  simp only [coefficientHomZeroEquiv, AddEquiv.apply_symm_apply, Category.id_comp] at hq
  simpa only [coefficientHomZeroEquiv, op_id, adj.homEquiv_counit,
    F.map_comp, Category.assoc] using congrArg (adj.homEquiv P N).symm hq

end WeilConjectures
