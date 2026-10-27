module

public import Sheaf.Paper.FramedProPredicate

/-! # Supported Kummer realization of a framed line bundle

Source: Stacks Tags 03AJ, 03PL and 0A45; blueprint main-20261015,
lem-pur-divisor-class, first sentence and final paragraph
(blueprint: def-pur-framed-pro-realization).

The integral torsor extension remembers the frame on the complementary open.
Scalar extension is performed on roots of unity, never on Gm as a Z/m-module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedIdentification_eq_injective
    {A : Type (u + 1)} [CommRing A] (S : SupportHomPair A)
    (B : Sheaf S.topology (ModuleCat.{u + 1} A))
    (rho : (constantSheaf S.topology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A) ⟶ B)
    (N : SupportedHomCocycleNormalization S.topology A S.isTerminal S.restriction B rho)
    (d : B ≅ S.supported) (hd : rho ≫ d.hom = S.constantRestriction)
    (χ ψ : S.Identification)
    (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] (a : ℤ)
    (x : S.group (DerivedCategory.Plus.Q.obj I) a) :
    χ.chi (DerivedCategory.Plus.Q.obj I) a x =
      ψ.chi (DerivedCategory.Plus.Q.obj I) a x := by
  let E := Sheaf.supportSequenceModelIso S.topology (ModuleCat.{u + 1} A) S.sections I
    (DerivedCategory.Plus.Q.obj I) (Iso.refl _) a
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective ((S.complex I).homologyπ a)).mp
    inferInstance (E.inv x)
  have hx : S.cycleClass I a y = x := by
    change E.hom ((S.complex I).homologyπ a y) = x
    rw [hy]
    exact ConcreteCategory.congr_hom E.inv_hom_id x
  obtain ⟨f, ⟨hf, hdf, _⟩, _⟩ := N.cocycle I I (𝟙 I) a y
  have hdf' : (d.inv ≫ f) ≫ I.obj.d a (a + 1) = 0 := by
    rw [Category.assoc, hdf, comp_zero]
  have heval : kernel.ι ((I.obj.X a).obj.map S.restriction.op)
      ((S.complex I).iCycles a y) =
      ((constantSheafAdj S.topology (ModuleCat.{u + 1} A) S.isTerminal).homEquiv _ _
        (S.constantRestriction ≫ (d.inv ≫ f))) 1 := by
    rw [← hf, N.evaluation, ← hd]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← hx]
  exact (χ.normalization I a (d.inv ≫ f) hdf' y heval).trans
    (ψ.normalization I a (d.inv ≫ f) hdf' y heval).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedIdentification_eq
    {A : Type (u + 1)} [CommRing A] (S : SupportHomPair A)
    (B : Sheaf S.topology (ModuleCat.{u + 1} A))
    (rho : (constantSheaf S.topology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A) ⟶ B)
    (N : SupportedHomCocycleNormalization S.topology A S.isTerminal S.restriction B rho)
    (d : B ≅ S.supported) (hd : rho ≫ d.hom = S.constantRestriction)
    (χ ψ : S.Identification)
    (K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ)
    (x : S.group K a) : χ.chi K a x = ψ.chi K a x := by
  obtain ⟨m, hm⟩ := K.2
  have : K.IsGE m := (K.isGE_ι_obj_iff m).mp hm
  obtain ⟨J, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K m
  let I := (InjectiveObject.ι (Sheaf S.topology (ModuleCat.{u + 1} A))).mapCochainComplexPlus.obj J
  have hi (n : ℤ) : Injective (I.obj.X n) := (J.obj.X n).2
  have h := normalizedIdentification_eq_injective S B rho N d hd χ ψ I a
    ((Sheaf.supportHypercohomologyFunctor S.topology (ModuleCat.{u + 1} A)
      S.restriction a).map e.inv x)
  rw [χ.naturality, ψ.naturality] at h
  exact (cancel_mono ((DerivedCategory.Plus.ι.map e.inv)⟦a⟧')).mp h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem proIdentification_eq
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i]
    (χ ψ : (proEtaleSupportHomPair P i).Identification)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} P.Coefficient))) (a : ℤ)
    (x : (proEtaleSupportHomPair P i).group K a) : χ.chi K a x = ψ.chi K a x := by
  obtain ⟨_, ⟨N⟩, _⟩ := supportedHom_cocycle_normalization P i
  let d := (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapIso
    (ProEtale.comparisonUpperStarUnitIso P.Coefficient Z).symm
  apply normalizedIdentification_eq (proEtaleSupportHomPair P i) _ _ N d _ χ ψ K a x
  rfl

end AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting
/-- The normalized pro-etale realization exists uniquely, for every integral extension.
Source: Stacks 0A45 and 099W; def-pur-frame-class, sigma rho
(blueprint: def-pur-framed-pro-realization).
Proof: exact site inverse image carries b_A to an Ext class. Precompose with the
inverse supported-constant comparison and apply the inverse normalized supported-Hom
bijection. Its cocycle normalization fixes the result independently of the chosen
identification and transport. The roots-tensor presentation identifies its coefficient
map with sigma rho. This uses the bounded-below etale witness B[0], without purity. -/
theorem divisorProRealization_existsUnique (P : PurityFiniteSetting.{u})
    {Z T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k))
    (i : Z ⟶ T) [IsClosedImmersion i]
    (β : Ext.{u + 1} ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
      (Etale.supportedIntegralConstant Z)) T.gmSheaf 1) :
    ∃! c : P.DivisorProGroup i,
      P.DivisorProRealizes i (P.divisorScalarRealization a i β) c := by
  classical
  obtain ⟨_, χ, _⟩ := supportedHom_pullback P
  let b := P.functorialCupCompare i 2 1
    (P.divisorEtaleHom i (P.divisorScalarRealization a i β))
  let c : P.DivisorProGroup i := (χ i |>.chi (P.divisorProCoefficient T) 2).symm b
  refine ⟨c, ?_, ?_⟩
  · unfold DivisorProRealizes divisorProHom
    intro ψ
    change ψ.chi (P.divisorProCoefficient T) 2 c = b
    rw [proIdentification_eq P i ψ (χ i)]
    exact (χ i |>.chi (P.divisorProCoefficient T) 2).apply_symm_apply b
  · intro c' hc'
    apply (χ i |>.chi (P.divisorProCoefficient T) 2).injective
    unfold DivisorProRealizes divisorProHom at hc'
    exact (hc' (χ i)).trans
      ((χ i |>.chi (P.divisorProCoefficient T) 2).apply_symm_apply b).symm

/-- The unique supported pro-etale Kummer class, in the existing right-derived support group.
Source: Stacks 0A45, 099W and the framed-line refinement
(blueprint: def-pur-framed-pro-realization). -/
@[irreducible] def divisorProRealization (P : PurityFiniteSetting.{u}) {Z T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k))
    (i : Z ⟶ T) [IsClosedImmersion i]
    (β : Ext.{u + 1} ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
      (Etale.supportedIntegralConstant Z)) T.gmSheaf 1) : P.DivisorProGroup i :=
  Classical.choose (P.divisorProRealization_existsUnique a i β)


end WeilConjectures.PurityFiniteSetting
