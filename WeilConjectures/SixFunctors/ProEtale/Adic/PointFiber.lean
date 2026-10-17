/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedFieldExact
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionsHom
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseRank
public import WeilConjectures.SixFunctors.ProEtale.Adic.PointFiberAux
public import WeilConjectures.SixFunctors.ProEtale.Adic.Truncation

/-!
# Constructible `ℓ`-adic complexes over a geometric point

Let `k` be an algebraically closed field and `s = Spec k`. Unlike the finite coefficient stage
(`AlgebraicGeometry.Etale.pointFiberEquivalence`), the category of pro-étale `ℚ̄_ℓ`-sheaves on
`s` is not equivalent to the category of `ℚ̄_ℓ`-vector spaces. However the global sections functor
`Γ = Γ(s, -)` is exact (`AlgebraicGeometry.ProEtale.preservesEpimorphisms_Γ_of_isAlgClosed`), and
it has an exact left adjoint `L` (the free `ℚ̄_ℓ,s`-module on the constant sheaf; every additive
functor out of vector spaces is exact). The unit `ℚ̄_ℓ` corepresents `Γ`, from which:

- the counit `L Γ F ⟶ F` is an isomorphism for every constructible `F`, these being the finite
  direct sums `ℚ̄_ℓⁿ` (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_iso_biproduct_of_isAlgClosed`);
- the unit `V ⟶ Γ L V` is an isomorphism for every finite-dimensional `V`, which is `Γ(ℚ̄_ℓⁿ)`.

Since `D(Γ)` and `D(L)` commute with cohomology, the induced natural transformations on derived
categories are isomorphisms on `Dᵇc(s, ℚ̄_ℓ)` and on `Dᵇ_fd(ℚ̄_ℓ)` respectively, and `D(Γ)`
restricts to an equivalence `Fib_s : Dᵇc(s, ℚ̄_ℓ) ≌ Dᵇ_fd(ℚ̄_ℓ)`.

## Main definitions

- `DerivedCategory.boundedFiniteDimensional`: the object property `Dᵇ_fd(K)` of `D(K)`, for a
  field `K`.
- `AlgebraicGeometry.ProEtale.adicPointSections`: the global sections `Γ(Spec k, -)` of `ℓ`-adic
  sheaves, as `ℚ̄_ℓ`-vector spaces.
- `AlgebraicGeometry.ProEtale.adicPointConstant`: its left adjoint.
- `AlgebraicGeometry.ProEtale.adicPointFiber`: `Fib_s : Dᵇc(Spec k, ℚ̄_ℓ) ⥤ Dᵇ_fd(ℚ̄_ℓ)`.
- `AlgebraicGeometry.ProEtale.adicPointFiberEquivalence` (`def-weil-finite-coefficient-point`,
  `ℚ̄_ℓ` stage): `Fib_s` is an equivalence.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace DerivedCategory

variable (K : Type) [Field K]

/-- The object property `Dᵇ_fd(K)` of the derived category of vector spaces over a field `K`:
bounded complexes all of whose cohomology spaces are finite-dimensional. -/
noncomputable def boundedFiniteDimensional :
    ObjectProperty (DerivedCategory (ModuleCat.{u + 1} K)) :=
  DerivedCategory.TStructure.t.bounded ⊓
    fun X ↦ ∀ n : ℤ, FiniteDimensional K ((homologyFunctor (ModuleCat.{u + 1} K) n).obj X)

instance : (boundedFiniteDimensional.{u} K).IsClosedUnderIsomorphisms where
  of_iso e h :=
    ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e h.1, fun n ↦
      have := h.2 n
      LinearEquiv.finiteDimensional
        ((homologyFunctor (ModuleCat.{u + 1} K) n).mapIso e).toLinearEquiv⟩

/-- The full subcategory `Dᵇ_fd(K)` of `D(K)`. -/
noncomputable abbrev BoundedFiniteDimensional : Type _ :=
  (boundedFiniteDimensional.{u} K).FullSubcategory

end DerivedCategory

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] [IsAlgClosed k]

/-- The global sections `Γ(Spec k, -)` of `ℓ`-adic pro-étale sheaves on `Spec k`, as
`ℚ̄_ℓ`-vector spaces. -/
noncomputable abbrev adicPointSections :
    AdicSheaf l (Spec (.of k)) ⥤ ModuleCat.{u + 1} (PadicAlgCl l) :=
  AdicSheaf.forget _ ⋙ Sheaf.Γ (Scheme.ProEt.topology (Spec (.of k))) (WeilCoefficients.{u} l) ⋙
    WeilCoefficients.toModuleCat l

instance : (adicPointSections l k).Additive := by
  have : (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of k))) (WeilCoefficients.{u} l)).Additive :=
    Functor.additive_of_preserves_binary_products _
  infer_instance

instance : PreservesFiniteLimits (adicPointSections l k) :=
  comp_preservesFiniteLimits _ _

instance : PreservesFiniteColimits (adicPointSections l k) := by
  have : (adicPointSections l k).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- The `ℚ̄_ℓ`-vector spaces as modules over `ULift ℚ̄_ℓ`. -/
noncomputable abbrev weilCoefficientsEquivalence :
    WeilCoefficients.{u} l ≌ ModuleCat.{u + 1} (PadicAlgCl l) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv (ULift.ringEquiv (R := PadicAlgCl l)).symm

/-- The left adjoint of `Γ(Spec k, -)`: a `ℚ̄_ℓ`-vector space `V` goes to the free
`ℚ̄_ℓ`-module `ℚ̄_ℓ ⊗ V` on the constant sheaf with value `V`. -/
noncomputable def adicPointConstant :
    ModuleCat.{u + 1} (PadicAlgCl l) ⥤ AdicSheaf l (Spec (.of k)) :=
  (weilCoefficientsEquivalence l).inverse ⋙
    constantSheaf (Scheme.ProEt.topology (Spec (.of k))) (WeilCoefficients.{u} l) ⋙
      Mod.free (adicConstantSheaf l (Spec (.of k)))

/-- The adjunction `L ⊣ Γ(Spec k, -)`. -/
noncomputable def adicPointAdjunction : adicPointConstant l k ⊣ adicPointSections l k :=
  (weilCoefficientsEquivalence l).symm.toAdjunction.comp
    ((constantSheafΓAdj _ _).comp (Mod.freeForgetAdjunction _))

instance : (adicPointConstant l k).Additive := by
  have := (adicPointAdjunction l k).leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (adicPointConstant l k)
  exact Functor.additive_of_preservesBinaryBiproducts _

instance : PreservesFiniteLimits (adicPointConstant l k) :=
  Functor.preservesFiniteLimits_of_moduleCat _

instance : PreservesFiniteColimits (adicPointConstant l k) :=
  Functor.preservesFiniteColimits_of_moduleCat _

variable {l k}

/-- The unit `ℚ̄_ℓ` corepresents the global sections: `Γ` is bijective on morphisms out of
`ℚ̄_ℓ`, both sides being identified with the global sections of the target. -/
lemma bijective_adicPointSections_map_unit (G : AdicSheaf l (Spec (.of k))) :
    Function.Bijective ((adicPointSections l k).map :
      (AdicSheaf.unit l (Spec (.of k)) ⟶ G) → _) := by
  let s : (adicPointSections l k).obj (AdicSheaf.unit l (Spec (.of k))) :=
    oneGlobalSection (l := l) (Spec (.of k))
  let ev : ((adicPointSections l k).obj (AdicSheaf.unit l (Spec (.of k))) ⟶
      (adicPointSections l k).obj G) → (adicPointSections l k).obj G := fun f ↦ f.hom s
  have hb : Function.Bijective (ev ∘ (adicPointSections l k).map) := by
    convert bijective_globalSectionOfModHom G using 1
    funext v
    exact (globalSectionOfModHom_eq v).symm
  have hev : Function.Injective ev := by
    intro f g hfg
    have hs : s ≠ 0 := oneGlobalSection_ne_zero _
    have h₁ := finrank_globalSections_adicConstantSheaf (l := l) (Spec (.of k))
    ext x
    obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' s hs).1 h₁ x
    simp only [map_smul]
    exact congrArg (c • ·) hfg
  exact (Function.Bijective.of_comp_iff' ⟨hev, hb.2.of_comp⟩ _).1 hb

/-- A natural transformation to the identity of additive functors is an isomorphism at a finite
direct sum of objects at which it is an isomorphism. -/
lemma _root_.CategoryTheory.NatTrans.isIso_app_biproduct {C : Type*} [Category C]
    [Preadditive C] [HasFiniteBiproducts C] {F : C ⥤ C} [F.Additive] (τ : F ⟶ 𝟭 C)
    {J : Type} [Finite J] (f : J → C) (h : ∀ j, IsIso (τ.app (f j))) :
    IsIso (τ.app (⨁ f)) := by
  have : τ.app (⨁ f) = (F.mapBiproduct f).hom ≫ biproduct.map fun j ↦ τ.app (f j) := by
    refine biproduct.hom_ext _ _ fun j ↦ ?_
    simp only [Functor.mapBiproduct_hom, Category.assoc, biproduct.map_π,
      biproduct.lift_π_assoc]
    exact τ.naturality (biproduct.π f j)
  rw [this]
  have : IsIso (biproduct.map fun j ↦ τ.app (f j)) :=
    (biproduct.mapIso fun j ↦ asIso (τ.app (f j))).isIso_hom
  infer_instance

variable (l k) in
/-- `ℚ̄_ℓⁿ` is lisse, trivialised by the identity cover. -/
lemma isAdicLisseSheaf_biproduct_unit (X : Scheme.{u}) (n : ℕ) :
    IsAdicLisseSheaf (⨁ fun _ : Fin n ↦ AdicSheaf.unit l X) := by
  refine ⟨.singleton (𝟙 X), Precoverage.mem_coverings_of_isIso _, fun V f hf ↦ ?_⟩
  obtain ⟨⟩ := hf
  exact ⟨n, ⟨(adicUpperStarId l X).app _⟩⟩

/-- The counit `L Γ F ⟶ F` is an isomorphism for every constructible `ℓ`-adic sheaf `F` on
`Spec k`. -/
lemma isIso_adicPointAdjunction_counit_app {F : AdicSheaf l (Spec (.of k))}
    (hF : IsAdicConstructibleSheaf F) : IsIso ((adicPointAdjunction l k).counit.app F) := by
  obtain ⟨n, ⟨e⟩⟩ := hF.isAdicLisseSheaf_of_isField.exists_iso_biproduct_of_isAlgClosed
  rw [NatTrans.isIso_app_iff_of_iso _ e]
  exact NatTrans.isIso_app_biproduct _ _ fun _ ↦
    (adicPointAdjunction l k).isIso_counit_app_of_bijective _
      bijective_adicPointSections_map_unit

/-- The unit `V ⟶ Γ L V` is an isomorphism for every finite-dimensional `ℚ̄_ℓ`-vector space `V`:
`V ≅ Γ(ℚ̄_ℓⁿ)` and `Γ(ε) ∘ η_Γ = 𝟙`. -/
lemma isIso_adicPointAdjunction_unit_app (V : ModuleCat.{u + 1} (PadicAlgCl l))
    [FiniteDimensional (PadicAlgCl l) V] : IsIso ((adicPointAdjunction l k).unit.app V) := by
  set n := Module.finrank (PadicAlgCl l) V
  let F := ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (Spec (.of k))
  have hF : IsAdicConstructibleSheaf F :=
    (isAdicLisseSheaf_biproduct_unit l _ n).isAdicConstructibleSheaf
  have := hF.finiteDimensional_globalSections
  let e : V ≅ (adicPointSections l k).obj F :=
    (LinearEquiv.ofFinrankEq _ _ (finrank_globalSections_biproduct_unit k n).symm).toModuleIso
  rw [NatTrans.isIso_app_iff_of_iso _ e]
  have := isIso_adicPointAdjunction_counit_app hF
  have h := (adicPointAdjunction l k).right_triangle_components F
  have : IsIso ((adicPointAdjunction l k).unit.app ((adicPointSections l k).obj F) ≫
      (adicPointSections l k).map ((adicPointAdjunction l k).counit.app F)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((adicPointSections l k).map _)

/-- The constant sheaf `L V` on a finite-dimensional `V` is constructible. -/
lemma isAdicConstructibleSheaf_adicPointConstant_obj (V : ModuleCat.{u + 1} (PadicAlgCl l))
    [FiniteDimensional (PadicAlgCl l) V] :
    IsAdicConstructibleSheaf ((adicPointConstant l k).obj V) := by
  have := isIso_adicPointAdjunction_unit_app (k := k) V
  set n := Module.finrank (PadicAlgCl l) V
  let F := ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (Spec (.of k))
  have hF : IsAdicConstructibleSheaf F :=
    (isAdicLisseSheaf_biproduct_unit l _ n).isAdicConstructibleSheaf
  have := hF.finiteDimensional_globalSections
  let e : V ≅ (adicPointSections l k).obj F :=
    (LinearEquiv.ofFinrankEq _ _ (finrank_globalSections_biproduct_unit k n).symm).toModuleIso
  have := isIso_adicPointAdjunction_counit_app hF
  exact hF.of_iso ((asIso ((adicPointAdjunction l k).counit.app F)).symm ≪≫
    (adicPointConstant l k).mapIso e.symm)

open DerivedCategory in
/-- `D(Γ)` sends `Dᵇc(Spec k, ℚ̄_ℓ)` to `Dᵇ_fd(ℚ̄_ℓ)`. -/
lemma boundedFiniteDimensional_mapDerivedCategory_obj
    {K : _root_.DerivedCategory (AdicSheaf l (Spec (.of k)))}
    (hK : ProEtale.DerivedCategory.boundedAdicConstructible l (Spec (.of k)) K) :
    boundedFiniteDimensional.{u} (PadicAlgCl l)
      ((adicPointSections l k).mapDerivedCategory.obj K) := by
  refine ⟨(adicPointSections l k).bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
  have := IsAdicConstructibleSheaf.finiteDimensional_globalSections (hK.2 n)
  exact LinearEquiv.finiteDimensional
    (((adicPointSections l k).mapDerivedCategoryHomologyFunctorIso n).app K).toLinearEquiv

open DerivedCategory in
/-- `D(L)` sends `Dᵇ_fd(ℚ̄_ℓ)` to `Dᵇc(Spec k, ℚ̄_ℓ)`. -/
lemma boundedAdicConstructible_mapDerivedCategory_obj
    {V : _root_.DerivedCategory (ModuleCat.{u + 1} (PadicAlgCl l))}
    (hV : boundedFiniteDimensional.{u} (PadicAlgCl l) V) :
    ProEtale.DerivedCategory.boundedAdicConstructible l (Spec (.of k))
      ((adicPointConstant l k).mapDerivedCategory.obj V) := by
  refine ⟨(adicPointConstant l k).bounded_mapDerivedCategory_obj hV.1, fun n ↦ ?_⟩
  have := hV.2 n
  exact IsAdicConstructibleSheaf.of_iso
    (((adicPointConstant l k).mapDerivedCategoryHomologyFunctorIso n).app V)
    (isAdicConstructibleSheaf_adicPointConstant_obj _)

end AlgebraicGeometry.ProEtale
