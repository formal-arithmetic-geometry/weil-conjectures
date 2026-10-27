/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable

/-!
# Tensor products with locally free module objects

Let `Λ` be a commutative condensed ring and `X` a scheme. For a locally free module object `P`
over `Λ_X` (`ProEtale.IsLocallyFree`):

* the pullback `g^* P` along any morphism `g` is locally free
  (`ProEtale.IsLocallyFree.upperStar`);
* `P ⊗ N` is pro-étale locally finitely presented, resp. constructible, if `N` is
  (`ProEtale.IsLocallyFree.isLocallyFinitelyPresented_tensorObj`,
  `ProEtale.IsLocallyFree.isConstructibleModuleObject_tensorObj`);
* `P` is flat, so the derived tensor product `P[0] ⊗ᴸ N[n]` is `(P ⊗ N)[n]`
  (`ProEtale.IsLocallyFree.nonempty_singleFunctor_tensorObj_iso`);
* `P[q]` is dualizable in `D(Mod_{Λ_X})`, with dual `P'[-q]` for a locally free `P'`
  (`ProEtale.IsLocallyFree.exists_exactPairing_singleFunctor`).

This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, so that the
latter can use these statements.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

/-! ### Free module objects -/

namespace CategoryTheory.Mod

section Free

variable {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R : C} [MonObj R] [PreservesFiniteColimits (MonoidalCategory.tensorLeft R)]
  {D : Type*} [Category* D] [MonoidalCategory D] [Abelian D] [MonoidalPreadditive D]
  {S : D} [MonObj S] [PreservesFiniteColimits (MonoidalCategory.tensorLeft S)]

omit [PreservesFiniteColimits (MonoidalCategory.tensorLeft R)] in
/-- Being free of finite rank is invariant under isomorphism of module objects. -/
lemma IsFree.of_iso {M N : Mod C R} (e : M ≅ N) (h : IsFree R M) : IsFree R N := by
  obtain ⟨n, ⟨e'⟩⟩ := h
  exact ⟨n, ⟨e.symm ≪≫ e'⟩⟩

omit [PreservesFiniteColimits (MonoidalCategory.tensorLeft R)]
  [PreservesFiniteColimits (MonoidalCategory.tensorLeft S)] in
/-- An additive functor `F : Mod_R ⥤ Mod_S` with `F R ≅ S` preserves free module objects of
finite rank. -/
lemma IsFree.map (F : Mod C R ⥤ Mod D S) [F.Additive] (e : F.obj (regular R) ≅ regular S)
    {M : Mod C R} (h : IsFree R M) : IsFree S (F.obj M) := by
  obtain ⟨n, ⟨e'⟩⟩ := h
  exact ⟨n, ⟨F.mapIso e' ≪≫ finiteFreeIsoMap F e n⟩⟩

omit [PreservesFiniteColimits (MonoidalCategory.tensorLeft S)] in
variable (S) in
/-- A direct sum of `m` copies of `Sᵏ` is `S^{m k}`. -/
noncomputable def finiteFreeFiniteFreeIso (m k : ℕ) :
    (⨁ fun _ : Fin m ↦ finiteFree S k) ≅ finiteFree S (m * k) :=
  biproductBiproductIso (fun _ : Fin m ↦ Fin k) (fun _ _ ↦ regular S) ≪≫
    biproduct.whiskerEquiv (f := fun _ : (Σ _ : Fin m, Fin k) ↦ regular S)
      (g := fun _ : Fin (m * k) ↦ regular S)
      ((Equiv.sigmaEquivProd _ _).trans finProdFinEquiv) (fun _ ↦ Iso.refl _)

/-- An additive right exact functor `F : Mod_R ⥤ Mod_S` sending `R` to a free module object of
finite rank preserves finitely presented module objects: it sends a presentation
`Rᵐ ⟶ Rⁿ ⟶ M ⟶ 0` to a presentation `S^{m k} ⟶ S^{n k} ⟶ F M ⟶ 0`. -/
lemma IsFinitelyPresented.map_of_isFree (F : Mod C R ⥤ Mod D S) [F.Additive]
    [PreservesFiniteColimits F] (hF : IsFree S (F.obj (regular R))) {M : Mod C R}
    (h : IsFinitelyPresented R M) : IsFinitelyPresented S (F.obj M) := by
  obtain ⟨k, ⟨e⟩⟩ := hF
  let en (m : ℕ) : F.obj (finiteFree R m) ≅ finiteFree S (m * k) :=
    F.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ e) ≪≫ finiteFreeFiniteFreeIso S m k
  obtain ⟨n, m, f, ⟨e'⟩⟩ := h
  exact ⟨n * k, m * k, (en m).inv ≫ F.map f ≫ (en n).hom,
    ⟨F.mapIso e' ≪≫ PreservesCokernel.iso _ f ≪≫
      cokernel.mapIso _ _ (en m) (en n) (by simp)⟩⟩

end Free

/-- Restriction of scalars along an isomorphism of algebra objects preserves free module objects
of finite rank. -/
lemma IsFree.comap {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] [MonoidalClosed C] {R S : C} [MonObj R] [MonObj S]
    [PreservesFiniteColimits (MonoidalCategory.tensorLeft R)]
    [PreservesFiniteColimits (MonoidalCategory.tensorLeft S)] (φ : R ⟶ S) [IsMonHom φ]
    [IsIso φ] {N : Mod C S} (h : IsFree S N) : IsFree R ((comap φ).obj N) := by
  obtain ⟨n, ⟨e⟩⟩ := h
  exact ⟨n, ⟨(Mod.comap φ).mapIso e ≪≫ finiteFreeIsoComap φ n⟩⟩

end CategoryTheory.Mod

/-! ### Exact pairings of direct sums -/

namespace CategoryTheory

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]

/-- The binary biproduct of two objects with right duals is paired with the biproduct of the
duals. -/
@[instance_reducible]
noncomputable def exactPairingBiprod [HasBinaryBiproducts C] (X Y : C) [HasRightDual X]
    [HasRightDual Y] : ExactPairing (X ⊞ Y) (Xᘁ ⊞ Yᘁ) where
  coevaluation' := η_ X Xᘁ ≫ (biprod.inl ⊗ₘ biprod.inl) + η_ Y Yᘁ ≫ (biprod.inr ⊗ₘ biprod.inr)
  evaluation' := (biprod.fst ⊗ₘ biprod.fst) ≫ ε_ X Xᘁ + (biprod.snd ⊗ₘ biprod.snd) ≫ ε_ Y Yᘁ
  coevaluation_evaluation' := by
    simp only [MonoidalPreadditive.whiskerLeft_add, MonoidalPreadditive.add_whiskerRight,
      Preadditive.add_comp, Preadditive.comp_add, whiskerLeft_coevaluation_evaluation,
      biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
      MonoidalCategory.whiskerLeft_id, id_whiskerRight, MonoidalPreadditive.whiskerLeft_zero,
      MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero, add_zero, zero_add,
      Category.id_comp, ExactPairing.coevaluation_evaluation_assoc, whiskerRight_id,
      id_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Preadditive.comp_add, ← Category.assoc biprod.fst, ← Category.assoc biprod.snd,
      ← Preadditive.add_comp, biprod.total, Category.id_comp]
  evaluation_coevaluation' := by
    simp only [MonoidalPreadditive.whiskerLeft_add, MonoidalPreadditive.add_whiskerRight,
      Preadditive.add_comp, Preadditive.comp_add, whiskerRight_coevaluation_evaluation,
      biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
      MonoidalCategory.whiskerLeft_id, id_whiskerRight, MonoidalPreadditive.whiskerLeft_zero,
      MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero, add_zero, zero_add,
      Category.id_comp, ExactPairing.evaluation_coevaluation_assoc, whiskerRight_id,
      id_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Preadditive.comp_add, ← Category.assoc biprod.fst, ← Category.assoc biprod.snd,
      ← Preadditive.add_comp, biprod.total, Category.id_comp]

/-- A zero object is paired with itself, with zero evaluation and coevaluation. -/
@[instance_reducible]
noncomputable def exactPairingOfIsZero {Z : C} (hZ : IsZero Z) : ExactPairing Z Z where
  coevaluation' := 0
  evaluation' := 0
  coevaluation_evaluation' := (hZ.of_iso (ρ_ Z)).eq_of_src _ _
  evaluation_coevaluation' := (hZ.of_iso (λ_ Z)).eq_of_src _ _

/-- The direct sum `𝟙ʳ` of `r` copies of the unit is self-dual. -/
@[instance_reducible]
noncomputable def exactPairingBiproductUnit [HasFiniteBiproducts C] [HasBinaryBiproducts C] :
    (r : ℕ) → ExactPairing (⨁ fun _ : Fin r ↦ 𝟙_ C) (⨁ fun _ : Fin r ↦ 𝟙_ C)
  | 0 => exactPairingOfIsZero
      ((IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext' _ _ fun i ↦ i.elim0))
  | r + 1 =>
    letI : HasRightDual (⨁ fun _ : Fin r ↦ 𝟙_ C) :=
      { rightDual := ⨁ fun _ : Fin r ↦ 𝟙_ C, exact := exactPairingBiproductUnit r }
    letI : HasRightDual (⨁ fun _ : Fin 1 ↦ 𝟙_ C) :=
      { rightDual := ⨁ fun _ : Fin 1 ↦ 𝟙_ C
        exact := exactPairingCongr (biproductUniqueIso _) (biproductUniqueIso _) }
    letI := exactPairingBiprod (⨁ fun _ : Fin r ↦ 𝟙_ C) (⨁ fun _ : Fin 1 ↦ 𝟙_ C)
    exactPairingCongr (biprodBiproductFinIso _ r 1).symm (biprodBiproductFinIso _ r 1).symm

end CategoryTheory

/-! ### Pullbacks of free module objects -/

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Freeness of the pullback `f^* N` of a module object can be read either over `f^* Λ_X` or over
`Λ_W`, the two being identified by the isomorphism of ring objects `α_f : f^* Λ_X ⟶ Λ_W`. -/
lemma isFree_mapMod_iff {W X : Scheme.{u}} (f : W ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mod.IsFree ((f)^*[Ab.{u + 1}].obj (condensedRingObj Λ X))
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj N) ↔
      Mod.IsFree (condensedRingObj Λ W) ((f)^*⟦Λ⟧.obj N) := by
  let α := condensedPullbackHom Λ f
  refine ⟨fun h ↦ (h.comap (asIso α).inv).of_iso ?_, fun h ↦ (h.comap α).of_iso ?_⟩
  · exact ((Mod.extendScalarsIsoComapInv α).app _).symm
  · exact comapUpperStarObjIso Λ f N

/-- The pullback of module objects over `Λ` preserves free module objects of finite rank. -/
lemma IsFree.upperStar {W Y : Scheme.{u}} (g : W ⟶ Y)
    {N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    (hN : Mod.IsFree (condensedRingObj Λ Y) N) :
    Mod.IsFree (condensedRingObj Λ W) ((g)^*⟦Λ⟧.obj N) :=
  hN.map _ (upperStarObjRegularIso Λ g)

/-- Along a commutative square `a ≫ f = b ≫ g`, if `f^* M` is free, then so is
`b^* g^* M ≅ a^* f^* M`. -/
lemma isFree_upperStar_upperStar_of_comm {P U W X : Scheme.{u}} {a : P ⟶ U}
    {b : P ⟶ W} {f : U ⟶ X} {g : W ⟶ X} (h : a ≫ f = b ≫ g)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : Mod.IsFree (condensedRingObj Λ U) ((f)^*⟦Λ⟧.obj M)) :
    Mod.IsFree (condensedRingObj Λ P) ((b)^*⟦Λ⟧.obj ((g)^*⟦Λ⟧.obj M)) :=
  (IsFree.upperStar Λ a hM).of_iso (upperStarSquareIso Λ h M)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

/-! ### Local freeness and duals -/

/-- A right dual of a free module object of finite rank over a commutative ring object of
pro-étale sheaves is free: it is isomorphic to the self-dual `Sⁿ`. -/
lemma isFree_of_exactPairing {W : Scheme.{u}} {S : Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}}
    [MonObj S] [IsCommMonObj S] {M D : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) S}
    [ExactPairing M D] (hM : Mod.IsFree S M) : Mod.IsFree S D := by
  obtain ⟨n, ⟨e⟩⟩ := hM
  exact ⟨n, ⟨rightDualIso (exactPairingCongrLeft e.symm) (exactPairingBiproductUnit n)⟩⟩

/-- A right dual of a locally free module object is locally free: the restrictions to the
members of a cover are strong monoidal, hence preserve exact pairings. -/
lemma IsLocallyFree.of_exactPairing {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M D : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} [ExactPairing M D]
    (hM : IsLocallyFree R M) : IsLocallyFree R D := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰, fun i ↦ ?_⟩
  let _ := ExactPairing.map ((𝒰.f i)^*[Ab.{u + 1}].mapMod R) M D
  exact isFree_of_exactPairing (h𝒰 i)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable {Λ} in
/-- Local freeness over `Λ_X` read with the pullbacks of module objects over `Λ`. -/
lemma isLocallyFree_iff {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsLocallyFree (condensedRingObj Λ X) M ↔
      ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
        ∀ i : 𝒰.I₀, Mod.IsFree (condensedRingObj Λ (𝒰.X i)) ((𝒰.f i)^*⟦Λ⟧.obj M) :=
  exists_congr fun _ ↦ forall_congr' fun _ ↦ isFree_mapMod_iff Λ _ M

variable {Λ} in
/-- Pro-étale local finite presentation over `Λ_X` read with the pullbacks of module objects
over `Λ`. -/
lemma isLocallyFinitelyPresented_iff {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) M ↔
      ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
        ∀ i : 𝒰.I₀,
          Mod.IsFinitelyPresented (condensedRingObj Λ (𝒰.X i)) ((𝒰.f i)^*⟦Λ⟧.obj M) :=
  exists_congr fun _ ↦ forall_congr' fun _ ↦ isFinitelyPresented_mapMod_iff Λ _ M

variable {Λ} in
/-- A free module object of finite rank is locally free, for the trivial cover. -/
lemma isLocallyFree_of_isFree {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : Mod.IsFree (condensedRingObj Λ X) M) : IsLocallyFree (condensedRingObj Λ X) M :=
  ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _),
    fun _ ↦ (isFree_mapMod_iff Λ _ _).2 (IsFree.upperStar Λ _ hM)⟩

variable {Λ} in
/-- Pro-étale local finite presentation is local: if the pullbacks of `M` to the members of a
pro-étale cover are locally finitely presented, so is `M`. -/
lemma isLocallyFinitelyPresented_of_cover {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ i, IsLocallyFinitelyPresented (condensedRingObj Λ (𝒰.X i)) ((𝒰.f i)^*⟦Λ⟧.obj M)) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) M := by
  choose 𝒱 h𝒱 using h
  refine ⟨𝒰.bind 𝒱, fun i ↦ ?_⟩
  obtain ⟨i, j⟩ := i
  have h₁ : Mod.IsFinitelyPresented (condensedRingObj Λ ((𝒱 i).X j))
      (((𝒱 i).f j ≫ 𝒰.f i)^*⟦Λ⟧.obj M) :=
    ((isFinitelyPresented_mapMod_iff Λ _ _).1 (h𝒱 i j)).of_iso
      ((CondensedRing.upperStarComp Λ ((𝒱 i).f j) (𝒰.f i)).app M).symm
  exact (isFinitelyPresented_mapMod_iff Λ ((𝒱 i).f j ≫ 𝒰.f i) M).2 h₁

variable {Λ} in
/-- The tensor product of a free module object of finite rank and a finitely presented one is
finitely presented. -/
lemma isFinitelyPresented_tensorObj_of_isFree {X : Scheme.{u}}
    {P N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : Mod.IsFree (condensedRingObj Λ X) P)
    (hN : Mod.IsFinitelyPresented (condensedRingObj Λ X) N) :
    Mod.IsFinitelyPresented (condensedRingObj Λ X) (P ⊗ N) :=
  have hP' : Mod.IsFree (condensedRingObj Λ X) ((tensorLeft P).obj (Mod.regular _)) :=
    hP.of_iso (ρ_ P).symm
  hN.map_of_isFree (tensorLeft P) hP'

variable {Λ} in
/-- The tensor product of a free module object of finite rank and a pro-étale locally finitely
presented one is pro-étale locally finitely presented. -/
lemma isLocallyFinitelyPresented_tensorObj_of_isFree {X : Scheme.{u}}
    {P N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : Mod.IsFree (condensedRingObj Λ X) P)
    (hN : IsLocallyFinitelyPresented (condensedRingObj Λ X) N) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) (P ⊗ N) := by
  obtain ⟨𝒱, h𝒱⟩ := (isLocallyFinitelyPresented_iff N).1 hN
  exact (isLocallyFinitelyPresented_iff _).2 ⟨𝒱, fun j ↦
    (isFinitelyPresented_tensorObj_of_isFree (IsFree.upperStar Λ _ hP) (h𝒱 j)).of_iso
      (Functor.Monoidal.μIso ((𝒱.f j)^*⟦Λ⟧) P N)⟩

/-! ### Main statements -/

omit [IsCommMonObj Λ] in
variable {Λ} in
/-- Local freeness is invariant under isomorphism. -/
lemma IsLocallyFree.of_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsLocallyFree (condensedRingObj Λ X) M) :
    IsLocallyFree (condensedRingObj Λ X) N :=
  let ⟨𝒰, h𝒰⟩ := hM
  ⟨𝒰, fun i ↦ (h𝒰 i).of_iso (((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod _).mapIso e)⟩

/-- The pullback `g^*` of module objects over `Λ` preserves local freeness. -/
lemma IsLocallyFree.upperStar {W X : Scheme.{u}} (g : W ⟶ X)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLocallyFree (condensedRingObj Λ X) M) :
    IsLocallyFree (condensedRingObj Λ W) ((g)^*⟦Λ⟧.obj M) := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰.pullback₁ g, fun i ↦ ?_⟩
  let a : (𝒰.pullback₁ g).X i ⟶ 𝒰.X i := pullback.snd g (𝒰.f i)
  exact (isFree_mapMod_iff Λ _ _).2
    (isFree_upperStar_upperStar_of_comm Λ (a := a) (b := (𝒰.pullback₁ g).f i)
      pullback.condition.symm ((isFree_mapMod_iff Λ _ _).1 (h𝒰 i)))

variable {Λ} in
/-- The tensor product of a locally free and a pro-étale locally finitely presented module object
is pro-étale locally finitely presented. -/
lemma IsLocallyFree.isLocallyFinitelyPresented_tensorObj {X : Scheme.{u}}
    {P N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : IsLocallyFree (condensedRingObj Λ X) P)
    (hN : IsLocallyFinitelyPresented (condensedRingObj Λ X) N) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) (P ⊗ N) := by
  obtain ⟨𝒰, h𝒰⟩ := (isLocallyFree_iff P).1 hP
  exact isLocallyFinitelyPresented_of_cover 𝒰 fun i ↦
    (isLocallyFinitelyPresented_tensorObj_of_isFree (h𝒰 i)
      (IsLocallyFinitelyPresented.upperStar Λ _ hN)).of_iso
      (Functor.Monoidal.μIso ((𝒰.f i)^*⟦Λ⟧) P N)

variable {Λ} in
/-- The tensor product of a locally free and a constructible module object is constructible. -/
lemma IsLocallyFree.isConstructibleModuleObject_tensorObj {X : Scheme.{u}}
    {P N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : IsLocallyFree (condensedRingObj Λ X) P)
    (hN : IsConstructibleModuleObject (condensedRingObj Λ X) N) :
    IsConstructibleModuleObject (condensedRingObj Λ X) (P ⊗ N) := by
  obtain ⟨S, hS⟩ := hN
  refine ⟨S, fun a ↦ (isLocallyFinitelyPresented_mapMod_iff Λ _ _).2 ?_⟩
  exact (IsLocallyFree.isLocallyFinitelyPresented_tensorObj (hP.upperStar Λ _)
    ((isLocallyFinitelyPresented_mapMod_iff Λ _ _).1 (hS a))).of_iso
    (Functor.Monoidal.μIso ((S.immersion a)^*⟦Λ⟧) P N)

variable {Λ} in
/-- A locally free module object `P` is flat, so the derived tensor product of `P[0]` and
`N[n]` is `(P ⊗ N)[n]`. -/
lemma IsLocallyFree.nonempty_singleFunctor_tensorObj_iso {X : Scheme.{u}}
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : IsLocallyFree (condensedRingObj Λ X) P)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) (n : ℤ) :
    Nonempty ((DerivedCategory.singleFunctor _ 0).obj P ⊗
        (DerivedCategory.singleFunctor _ n).obj N ≅
      (DerivedCategory.singleFunctor _ n).obj (P ⊗ N)) :=
  ⟨tensorIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app P)
      ((DerivedCategory.singleFunctorIsoCompQ _ n).app N) ≪≫
    DerivedCategory.QObjTensorQObjIsoOfKFlatLeft _ _
      ((CochainComplex.kFlat_single_obj_iff_flat P 0).2
        (ObjectProperty.flat_of_isDualizable hP.isDualizable)) ≪≫
    DerivedCategory.Q.mapIso
      ((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor _) P).app _ ≪≫
        (HomologicalComplex.singleMapHomologicalComplex (tensorLeft P) (.up ℤ) n).app N) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ n).app (P ⊗ N)).symm⟩

variable {Λ} in
/-- A locally free module object `P` placed in degree `q` is dualizable in `D(Mod_{Λ_X})`: it has
a left dual `P'[-q]` with `P'` locally free. -/
lemma IsLocallyFree.exists_exactPairing_singleFunctor {X : Scheme.{u}}
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : IsLocallyFree (condensedRingObj Λ X) P) (q : ℤ) :
    ∃ P' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
      IsLocallyFree (condensedRingObj Λ X) P' ∧
        Nonempty (ExactPairing ((DerivedCategory.singleFunctor _ (-q)).obj P')
          ((DerivedCategory.singleFunctor _ q).obj P)) := by
  let C := (HomologicalComplex.single
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (ComplexShape.up ℤ) q).obj P
  have hC (m : ℤ) : IsDualizable (C.X m) := by
    by_cases hm : m = q
    · subst hm
      exact hP.isDualizable.of_iso (HomologicalComplex.singleObjXSelf _ _ P).symm
    · exact CategoryTheory.IsZero.isDualizable (HomologicalComplex.isZero_single_obj_X _ _ _ _ hm)
  let _ (m : ℤ) : HasRightDual (C.X m) := (hC m).some
  obtain ⟨_⟩ := DerivedCategory.nonempty_exactPairing_Q_obj C q q
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  let _ := BraidedCategory.exactPairing_swap (DerivedCategory.Q.obj C)
    (DerivedCategory.Q.obj (CochainComplex.rightDual C))
  obtain ⟨M, ⟨eM⟩⟩ := CochainComplex.exists_iso_single (CochainComplex.rightDual C) (-q)
  have h₁ : IsLocallyFree (condensedRingObj Λ X) (C.X (-(-q))) :=
    hP.of_iso (HomologicalComplex.singleObjXIsoOfEq _ q P (-(-q)) (neg_neg q)).symm
  refine ⟨M, (IsLocallyFree.of_exactPairing (D := (C.X (-(-q)))ᘁ) h₁).of_iso ?_, ⟨?_⟩⟩
  · exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) (-q)).mapIso eM ≪≫
      HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-q) M
  · exact exactPairingCongr (X' := DerivedCategory.Q.obj (CochainComplex.rightDual C))
      (Y' := DerivedCategory.Q.obj C)
      ((DerivedCategory.singleFunctorIsoCompQ _ (-q)).app M ≪≫ DerivedCategory.Q.mapIso eM.symm)
      ((DerivedCategory.singleFunctorIsoCompQ _ q).app P)

/-- The unit `Λ_X` of the module objects over `Λ_X` is locally free (indeed free of rank one). -/
lemma isLocallyFree_tensorUnit (X : Scheme.{u}) :
    IsLocallyFree (condensedRingObj Λ X)
      (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
  isLocallyFree_of_isFree
    ⟨1, ⟨(biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular (condensedRingObj Λ X))).symm⟩⟩

end AlgebraicGeometry.ProEtale
