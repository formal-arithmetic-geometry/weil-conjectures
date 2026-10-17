/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import WeilConjectures.AlgebraicGeometry.HypercoverResolutionLocal
public import WeilConjectures.AlgebraicGeometry.HypercoverHomotopyInvariance
public import WeilConjectures.AlgebraicGeometry.SplitEtaleHypercoverFreeComplex

/-!
# Verdier's hypercovering theorem for finite split étale hypercovers

For a sheaf `F` with injective resolution `F ⟶ L^•`, the cohomology `H^q(C(U, F))` of a finite
split étale hypercover `U` maps to `H^q(Γ(X, L)) = R^qΓ(F)` through the total complex
`Tot(U, L)` (`AlgebraicGeometry.FiniteSplitEtaleHypercover.cohomologyMap`). These maps are
natural in `F` and compatible with refinements; every class of `R^qΓ(F)` comes from some `U`,
and a class of `H^q(C(U, F))` mapping to zero dies on a refinement of `U`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

open SplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  {A : Type (u + 2)} [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type*} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [∀ X, AddCommGroup (CA X)] [∀ X Y, AddMonoidHomClass (FA X Y) (CA X) (CA Y)]
  (hA : ElementwiseAbelian A)
  [HasSheafify X.smallEtaleTopology A] [X.smallEtaleTopology.WEqualsLocallyBijective A]
  [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A]

section Resolution

variable {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F)

/-- The coaugmentation `F ⟶ L^0` of an injective resolution. -/
noncomputable abbrev resι : F ⟶ I.cocomplex.X 0 := I.ι.f 0

lemma resι_d : resι I ≫ I.cocomplex.d 0 1 = 0 := I.ι_f_zero_comp_complex_d

include hA in
lemma resι_glob (T : X.Etale) (s : ToType ((I.cocomplex.X 0).obj.obj (op T)))
    (hs : (I.cocomplex.d 0 1).hom.app (op T) s = 0) :
    ∃ w, (resι I).hom.app (op T) w = s :=
  exists_kernel_elem hA (w := I.ι_f_zero_comp_complex_d) I.isLimitKernelFork T s hs

include hA in
lemma resι_inj (T : X.Etale) : Function.Injective ((resι I).hom.app (op T)) := by
  have : Mono (resι I) := Fork.IsLimit.mono I.isLimitKernelFork
  have : Mono (resι I).hom := (sheafToPresheaf X.smallEtaleTopology A).map_mono (resι I)
  have : Mono ((resι I).hom.app (op T)) := (NatTrans.mono_iff_mono_app _).1 this _
  exact hA.injective_of_mono _

end Resolution

/-- Global sections over the final object. -/
noncomputable abbrev Γ' : Sheaf X.smallEtaleTopology A ⥤ A :=
  (sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale))

instance : (Γ' (X := X) (A := A)).Additive where
  map_add := rfl

section Main

variable (Free : Type (u + 1) ⥤ A) (adj : Free ⊣ CategoryTheory.forget A)
  (hfin : ∀ (S : Type (u + 1)) (x : ToType (Free.obj S)), ∃ F : Set S, F.Finite ∧
    x ∈ Set.range (Free.map (↾(Subtype.val : F → S))))
  [(presheafToSheaf X.smallEtaleTopology A).PreservesHomology]
  [(CategoryTheory.forget A).PreservesMonomorphisms]

include hA adj hfin

lemma rows_of_injective (U : SplitEtaleHypercover X) (L : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ)
    [∀ r, Injective (L.X r)] :
    (∀ r, Function.Injective (U.resTop (L.X r) 0)) ∧
      (∀ r (s : ToType (U.dObj L 0 r)), U.dHor L 0 r s = 0 →
        ∃ t, U.resTop (L.X r) 0 t = s) ∧
      (∀ p r (s : ToType (U.dObj L (p + 1) r)), U.dHor L (p + 1) r s = 0 →
        ∃ t, U.dHor L p r t = s) := by
  have H := fun r ↦ U.injective_section_cohomology Free hA.sub_apply hfin adj hA.exact_of_elem
    (L.X r)
  refine ⟨fun r ↦ (H r).1, fun r s hs ↦ ((H r).2.1 s).1 hs, fun p r s hs ↦ ?_⟩
  have hz := (H r).2.2 (p + 1) (Nat.succ_pos p)
  have hex := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 hz
  rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp)] at hex
  exact hA.elem_of_exact _ hex s hs

/-- For a complex of injective sheaves `L`, the augmentation `Γ(X, L) ⟶ Tot(U, L)` is an
isomorphism on cohomology. -/
noncomputable def augIso (U : SplitEtaleHypercover X)
    (L : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) [∀ r, Injective (L.X r)] (n : ℕ) :
    (gammaComplex L).homology n ≅ (U.totComplex L).homology n :=
  have h := rows_of_injective hA Free adj hfin U L
  have := U.isIso_homologyMap_totAug L hA h.1 h.2.1 h.2.2 n
  asIso (HomologicalComplex.homologyMap (U.totAug L) n)

lemma augIso_hom (U : SplitEtaleHypercover X)
    (L : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) [∀ r, Injective (L.X r)] (n : ℕ) :
    (augIso hA Free adj hfin U L n).hom = HomologicalComplex.homologyMap (U.totAug L) n := rfl

lemma augIso_inv_naturality (U : SplitEtaleHypercover X)
    {L L' : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ} [∀ r, Injective (L.X r)]
    [∀ r, Injective (L'.X r)] (φ : L ⟶ L') (n : ℕ) :
    (augIso hA Free adj hfin U L n).inv ≫
        HomologicalComplex.homologyMap ((Γ' (X := X) (A := A)).mapHomologicalComplex _ |>.map φ) n =
      HomologicalComplex.homologyMap (U.totMapL φ) n ≫ (augIso hA Free adj hfin U L' n).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, augIso_hom, augIso_hom,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    totAug_totMapL]

lemma augIso_inv_totMap {U V : SplitEtaleHypercover X} (f : U.simplicial ⟶ V.simplicial)
    (L : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) [∀ r, Injective (L.X r)] (n : ℕ) :
    HomologicalComplex.homologyMap (totMap L f) n ≫ (augIso hA Free adj hfin U L n).inv =
      (augIso hA Free adj hfin V L n).inv := by
  rw [Iso.comp_inv_eq, Iso.inv_comp_eq, augIso_hom, augIso_hom,
    ← HomologicalComplex.homologyMap_comp, totAug_totMap]

end Main

end AlgebraicGeometry.FiniteSplitEtaleHypercover
