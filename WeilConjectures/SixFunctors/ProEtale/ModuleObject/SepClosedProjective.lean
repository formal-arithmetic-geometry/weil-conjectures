/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# The unit is projective on the pro-étale site of a separably closed field

Let `k` be a separably closed field. The final object `Spec k` of the pro-étale site of `Spec k`
is weakly contractible (`AlgebraicGeometry.Scheme.ProEt.isWeaklyContractible_self`): every
faithfully flat ind-étale `k`-algebra has a `k`-point. Hence taking sections over it is exact,
and the unit of the category of abelian sheaves, the sheafified constant sheaf `ℤ`, is projective
(`AlgebraicGeometry.ProEtale.projective_presheafToSheaf_const`). Consequently, for every
ring object `R` of abelian sheaves on `(Spec k)_proét`, the regular module `R`, the unit of the
category of `R`-modules, is projective
(`AlgebraicGeometry.ProEtale.projective_regular_of_isSepClosed`).

## Main results

- `AlgebraicGeometry.Scheme.ProEt.isTerminalSelf`: `S` is the final object of `S_proét`.
- `AlgebraicGeometry.Scheme.ProEt.isWeaklyContractible_self`: for `k` separably closed, the final
  object of `(Spec k)_proét` is weakly contractible.
- `AlgebraicGeometry.ProEtale.projective_presheafToSheaf_const`: the unit of the abelian
  sheaves on a site whose final object is weakly contractible is projective.
- `CategoryTheory.Mod.projective_regular`: the regular module over a ring object is projective
  when the unit is.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.ProEt

variable (S : Scheme.{u})

/-- The scheme `S` itself, as the final object `𝟙 S` of the pro-étale site of `S`. -/
noncomputable abbrev self : S.ProEt :=
  ProEt.mk (𝟙 S)

/-- `S` is the final object of the pro-étale site of `S`. -/
noncomputable def isTerminalSelf : IsTerminal (self S) :=
  IsTerminal.ofUniqueHom (fun U ↦ MorphismProperty.Over.homMk U.hom (Category.comp_id _))
    fun U f ↦ MorphismProperty.Over.Hom.ext
      ((Category.comp_id f.left).symm.trans (MorphismProperty.Over.w f))

variable (k : Type u) [Field k] [IsSepClosed k]

/-- For a separably closed field `k`, the final object `Spec k` of the pro-étale site of `Spec k`
is weakly contractible: a faithfully flat ind-étale `k`-algebra is weakly étale and nonzero, so
it has a `k`-point (`Algebra.WeaklyEtale.nonempty_algHom_of_isSepClosed`). -/
theorem isWeaklyContractible_self :
    (topology (Spec (.of k))).IsWeaklyContractible.{w} (self (Spec (.of k))) :=
  isWeaklyContractible_of_forall_exists_retraction (R := .of k) (fun T _ _ _ _ ↦ by
    have : Nontrivial (k ⊗[k] T) := Module.FaithfullyFlat.rTensor_nontrivial k T k
    have : Nontrivial T := (TensorProduct.lid k T).symm.toEquiv.nontrivial
    obtain ⟨φ⟩ := Algebra.WeaklyEtale.nonempty_algHom_of_isSepClosed (K := k) (R := T)
    exact ⟨φ.toRingHom, RingHom.ext fun x ↦ φ.commutes x⟩) (Iso.refl _)

end AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.ProEtale

variable {S : Scheme.{u}} {T : S.ProEt}

/-- If the final object `T` of a site is weakly contractible, the sheafified constant presheaf
`ℤ` is projective: sections over `T` of an epimorphism of abelian sheaves are surjective, and a
morphism from the constant presheaf `ℤ` is determined by the image of `1` over `T`. -/
theorem projective_presheafToSheaf_const (hT : IsTerminal T)
    (hW : (Scheme.ProEt.topology S).IsWeaklyContractible.{u + 1} T) :
    Projective ((presheafToSheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}).obj
      ((Functor.const S.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) := by
  refine ⟨fun {E X} f e he ↦ ?_⟩
  let adj := sheafificationAdjunction (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}
  let x' := adj.homEquiv _ _ f
  have hφ : Sheaf.IsLocallySurjective e := (Sheaf.isLocallySurjective_iff_epi' (φ := e)).2 he
  obtain ⟨s, hs⟩ : ∃ s : E.obj.obj (op T), e.hom.app (op T) s = x'.app (op T) (ULift.up 1) :=
    hW ((sheafCompose _ (forget AddCommGrpCat.{u + 1})).map e)
      ((Presheaf.isLocallySurjective_iff_whisker_forget _ _).1 hφ) (x'.app (op T) (ULift.up 1))
  let y' : (Functor.const S.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ E.obj :=
    { app U := AddCommGrpCat.ofHom ((zmultiplesHom _ (E.obj.map (hT.from U.unop).op s)).comp
        AddEquiv.ulift.toAddMonoidHom)
      naturality U V g := by
        ext n
        simp only [Functor.const_obj_obj, Functor.const_obj_map, AddCommGrpCat.hom_comp,
          AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_comp, Function.comp_apply,
          AddCommGrpCat.hom_id, AddMonoidHom.id_apply, zmultiplesHom_apply,
          AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_zsmul]
        rw [← Functor.map_comp_apply, show (hT.from U.unop).op ≫ g = (hT.from V.unop).op from
          Quiver.Hom.unop_inj (hT.hom_ext _ _)] }
  refine ⟨(adj.homEquiv _ _).symm y', ?_⟩
  rw [← Adjunction.homEquiv_naturality_right_symm, Equiv.symm_apply_eq]
  ext U n
  obtain ⟨n⟩ := n
  have hn : (ULift.up n : ULift.{u + 1} ℤ) = n • ULift.up 1 := by
    ext
    simp
  change e.hom.app U (n • E.obj.map (hT.from U.unop).op s) = x'.app U (ULift.up n)
  have h₁ := NatTrans.naturality_apply e.hom (hT.from U.unop).op s
  have h₂ := NatTrans.naturality_apply x' (hT.from U.unop).op (ULift.up 1)
  rw [hs] at h₁
  rw [hn, map_zsmul, map_zsmul, h₁]
  exact congrArg (n • ·) h₂.symm

end AlgebraicGeometry.ProEtale

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R : C} [MonObj R] [PreservesFiniteColimits (tensorLeft R)]

/-- The regular module `R` over a ring object `R` is projective when the unit is: a morphism
`R ⟶ N` is determined by the image of the unit, which lifts along any epimorphism. -/
theorem projective_regular [Projective (𝟙_ C)] : Projective (regular R) := by
  refine ⟨fun {M N} f e he ↦ ?_⟩
  have : (forget R : Mod C R ⥤ C).IsRightAdjoint := (freeForgetAdjunction R).isRightAdjoint
  have : (forget R : Mod C R ⥤ C).PreservesEpimorphisms :=
    NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels _
  have : Epi e.hom := (forget R).map_epi e
  obtain ⟨y, hy⟩ := Projective.factors ((MonObj.one : 𝟙_ C ⟶ R) ≫ f.hom) e.hom
  refine ⟨regularLift M y, regular_hom_ext ?_⟩
  rw [comp_hom', ← Category.assoc, one_comp_regularLift, hy]

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

variable {k : Type u} [Field k] [IsSepClosed k]

/-- For a separably closed field `k`, the unit of the abelian sheaves on `(Spec k)_proét` is
projective. -/
instance projective_tensorUnit_of_isSepClosed :
    Projective (𝟙_ (Sheaf (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1})) :=
  Projective.of_iso
    (asIso (Functor.LaxMonoidal.ε (presheafToSheaf (Scheme.ProEt.topology (Spec (.of k)))
      AddCommGrpCat.{u + 1}))).symm
    (projective_presheafToSheaf_const (Scheme.ProEt.isTerminalSelf _)
      (Scheme.ProEt.isWeaklyContractible_self k))

/-- For a separably closed field `k` and a ring object `R` of abelian sheaves on `(Spec k)_proét`,
the regular module `R` is projective. -/
instance projective_regular_of_isSepClosed
    (R : Sheaf (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1}) [MonObj R] :
    Projective (Mod.regular R) :=
  Mod.projective_regular

end AlgebraicGeometry.ProEtale
