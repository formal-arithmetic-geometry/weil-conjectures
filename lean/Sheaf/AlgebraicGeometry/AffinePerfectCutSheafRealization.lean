/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C9
-/
module

public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Finiteness.Projective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Sheaf.AlgebraicGeometry.AffinePrincipalModelComparison

/-! # Realizing a supplied affine cut on an open subscheme

Source: Stacks Project, More on Algebra, Tag 0A1U, conclusion;
Derived Categories of Schemes, Tags 06Z0 and 08EB.
(blueprint: lem-sc-affine-perfect-cut-sheaf-realization).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
  preservesBinaryBiproducts_of_preservesBinaryProducts

/-- A finite-projective module sent to finite-free retracts gives a flat sheaf. -/
private theorem flat_of_finiteFree_retract (Y : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (m : ℕ)
    (i : M ⟶ SheafOfModules.free
      (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m)))
    (p : SheafOfModules.free
      (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m)) ⟶ M)
    (h : i ≫ p = 𝟙 M) : SheafOfModules.IsFlat M := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  obtain ⟨⟨mp⟩, ⟨mc⟩, _⟩ := SheafOfModules.tensorClosed Y.sheaf
  let := mp
  let := mc
  have := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  have hf : ObjectProperty.flat
      (SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m))) :=
    ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _)
  exact (ObjectProperty.flat_of_retract ⟨i, p, h⟩ hf).2

private theorem map_finiteProjective_retract (A : Type u) [CommRing A]
    (Y : Scheme.{u})
    (F : ModuleCat.{u} A ⥤ SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (hF : ∀ m : ℕ, Nonempty (F.obj (ModuleCat.of A (ULift.{u} (Fin m) →₀ A)) ≅
      SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m))))
    (M : ModuleCat.{u} A) [Module.Finite A M] [Module.Projective A M] :
    ∃ (m : ℕ) (i : F.obj M ⟶ SheafOfModules.free
      (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m)))
      (p : SheafOfModules.free
        (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m)) ⟶ F.obj M),
      i ≫ p = 𝟙 (F.obj M) := by
  classical
  obtain ⟨m, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  let c := ((Pi.basisFun A (Fin m)).reindex Equiv.ulift.symm).repr.toModuleIso
  let e := F.mapIso c ≪≫ (hF m).some
  have hsplit : (ModuleCat.ofHom g) ≫ (ModuleCat.ofHom f) = 𝟙 M := by
    ext a
    exact congrArg (fun h : M →ₗ[A] M ↦ h a) hfg
  refine ⟨m, F.map (ModuleCat.ofHom g) ≫ e.hom,
    e.inv ≫ F.map (ModuleCat.ofHom f), ?_⟩
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp, hsplit, F.map_id]

private theorem positive_projective_sheaf_model (A : Type u) [CommRing A]
    (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (F : ModuleCat.{u} A ⥤ SheafOfModules.{u} (moduleRings Y.toRingedSpace)) [F.Additive]
    (hF : ∀ m : ℕ, Nonempty (F.obj (ModuleCat.of A (ULift.{u} (Fin m) →₀ A)) ≅
      SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m))))
    (T : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ)
    (hlo : T.IsStrictlyGE 1) (hhi : T.IsStrictlyLE b)
    (hp : ∀ i : ℤ, Module.Projective A (T.X i) ∧ Module.Finite A (T.X i)) :
    let L := (F.mapHomologicalComplex (.up ℤ)).obj T
    Scheme.IsPerfect Y (DerivedCategory.Q.obj L) ∧
      (∀ G : SheafOfModules.{u} (moduleRings Y.toRingedSpace), ∀ i : ℤ, i < 1 →
        schemeDerivedTensorCohomologyVanishes Y (DerivedCategory.Q.obj L) G i) := by
  classical
  let L := (F.mapHomologicalComplex (.up ℤ)).obj T
  have hb (n : ℤ) (hn : n < 1 ∨ b < n) : IsZero (L.X n) := by
    apply F.map_isZero
    rcases hn with hn | hn
    · exact (T.isStrictlyGE_iff 1).mp hlo n hn
    · exact (T.isStrictlyLE_iff b).mp hhi n hn
  have hr (n : ℤ) : ∃ (m : ℕ) (i : L.X n ⟶ SheafOfModules.free
      (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m)))
      (p : SheafOfModules.free
        (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m)) ⟶ L.X n),
      i ≫ p = 𝟙 (L.X n) := by
    have := (hp n).1
    have := (hp n).2
    exact map_finiteProjective_retract A Y F hF (T.X n)
  constructor
  · intro y
    let R := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) ⊤
    refine ⟨⊤, trivial, (R.mapHomologicalComplex (.up ℤ)).obj L,
      ⟨⟨1, b, fun n hn ↦ R.map_isZero (hb n hn)⟩, ?_⟩,
      ⟨R.mapDerivedCategoryFactors.app L⟩⟩
    intro n
    obtain ⟨m, i, p, hip⟩ := hr n
    let e := (SheafOfModules.mapFreeIso R (ULift.{u} (Fin m)) (Iso.refl _)).symm
    refine ⟨m, R.map i ≫ e.hom, e.inv ≫ R.map p, ?_⟩
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← R.map_comp, hip, R.map_id]
    rfl
  · have hflat (n : ℤ) : SheafOfModules.IsFlat (L.X n) := by
      obtain ⟨m, i, p, hip⟩ := hr n
      exact flat_of_finiteFree_retract Y (L.X n) m i p hip
    have hL := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
      Y.toRingedSpace L ⟨b, fun n hn ↦ hb n (Or.inr hn)⟩ hflat
    intro G n hn
    refine ⟨L, hL, ⟨Iso.refl _⟩, ?_⟩
    let := SheafOfModules.monoidalCategory Y.sheaf
    let Z := CochainComplex.mapBifunctor L
      ((HomologicalComplex.single _ (.up ℤ) 0).obj G)
      (MonoidalCategory.curriedTensor _)
    let e := CochainComplex.mapBifunctorSingle₂Iso
      (MonoidalCategory.curriedTensor _) G L
    have hz : IsZero (Z.X n) := IsZero.of_iso
      ((MonoidalCategory.tensorRight G).map_isZero (hb n (Or.inl hn)))
      ((HomologicalComplex.eval _ (.up ℤ) n).mapIso e)
    exact (Z.sc n).isZero_homology_of_isZero_X₂ hz

private theorem split_iso_truncLT
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K A B : DerivedCategory C) [A.IsLE 0] [B.IsGE 1] (e : K ≅ A ⊞ B) :
    Nonempty (K ≅ (DerivedCategory.TStructure.t.truncLT 1).obj K ⊞ B) := by
  let t := DerivedCategory.TStructure.t (C := C)
  have : IsIso ((t.truncLTι 1).app A) :=
    (t.isLE_iff_isIso_truncLTι_app 0 1 (by omega) A).mp inferInstance
  let eA : (t.truncLT 1).obj K ≅ A :=
    (t.truncLT 1).mapIso e ≪≫ (t.truncLT 1).mapBiprod A B ≪≫
      (isoBiprodZero (t.isZero_truncLT_obj_of_isGE 1 B)).symm ≪≫
      asIso ((t.truncLTι 1).app A)
  exact ⟨e ≪≫ biprod.mapIso eA.symm (Iso.refl B)⟩

set_option backward.isDefEq.respectTransparency false in
/-- An algebraic localization splitting, with a bounded positive finite-projective
model for its right summand, gives a sheaf splitting and a positive perfect summand.
Source: Stacks Project, Tag 0A1U, conclusion; Tags 06Z0 and 08EB.
(blueprint: lem-sc-affine-perfect-cut-sheaf-realization).

Proof: In the affine chart for U take the principal open D(f) and regard it as
an open V of X. The hypothesis f not in the prime implies s in V. Localization
and associated sheaf commute, so the given comparison for M identifies K|V
with the associated sheaf of M tensor R_f. Associated sheaf is exact and
additive, hence induces a functor on derived categories preserving biproducts.
Apply it to the supplied splitting. Exactness identifies the image of the
nonpositive truncation with tau_<1(K|V); this follows either from the
termwise kernel truncation or the universal property of the standard t-structure.
For the positive summand use its given bounded complex T of finite projectives.
Associated sheaf makes each T.X i a finite-free retract and preserves its bounds,
so Q(tilde T) is perfect on V. Its terms are flat and it is bounded above,
hence K-flat. Tensoring this complex with any module sheaf in degree zero
still has zero terms below one, and hence zero cohomology there. Transport
along the supplied positive-model isomorphism. These identifications give
the asserted splitting. The construction requires no Tor bound on M and no
fibre-map assumption; all algebraic cutting data are explicit hypotheses.
If T is zero or has upper bound below one the same argument gives the zero
positive summand; the condition at s excludes an empty principal open. -/
theorem affine_perfect_cut_sheaf_realization (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ (U : X.Opens) (V : U.toScheme.Opens),
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (K : schemeDerivedCategory X) (s : X)
    (U : X.Opens) (hsU : s ∈ U) (hU : IsAffineOpen U)
    [∀ f : X.presheaf.obj (.op U),
      HasDerivedCategory.{u} (ModuleCat.{u} (Localization.Away f))]
    (M : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op U))) ℤ)
    (eM : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj
          (((Scheme.affinePerfectSheafification X U hU).mapHomologicalComplex
            (.up ℤ)).obj M)))
    (f : X.presheaf.obj (.op U)) (hf : f ∉ (hU.isoSpec.hom ⟨s, hsU⟩).asIdeal)
    (esplit : Nonempty
      (DerivedCategory.Q.obj ((RingTensorCohomology.extend _ (Localization.Away f)).obj M) ≅
        DerivedCategory.Q.obj
          (((RingTensorCohomology.extend _ (Localization.Away f)).obj M).truncLE 0) ⊞
        DerivedCategory.Q.obj
          (((RingTensorCohomology.extend _ (Localization.Away f)).obj M).truncGE 1)))
    (hpos : ∃ (T : CochainComplex (ModuleCat.{u} (Localization.Away f)) ℤ) (b : ℤ),
      T.IsStrictlyGE 1 ∧ T.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Projective (Localization.Away f) (T.X i) ∧
        Module.Finite (Localization.Away f) (T.X i)) ∧
      Nonempty (DerivedCategory.Q.obj
        (((RingTensorCohomology.extend _ (Localization.Away f)).obj M).truncGE 1) ≅
          DerivedCategory.Q.obj T)) :
    ∃ V : X.Opens, s ∈ V ∧ ∃ P : schemeDerivedCategory V.toScheme,
      Scheme.IsPerfect V.toScheme P ∧
      (∀ F : SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace),
        ∀ i : ℤ, i < 1 → schemeDerivedTensorCohomologyVanishes V.toScheme P F i) ∧
      Nonempty
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V)).mapDerivedCategory.obj K ≅
          (DerivedCategory.TStructure.t.truncLT 1).obj
            (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V) ⋙
              Equivalence.functor
                (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
                (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv V)).mapDerivedCategory.obj K) ⊞ P) := by
  classical
  obtain ⟨V, hsV, F, hFadd, hFlim, hFcolim, hFfree, ⟨eV⟩⟩ :=
    affine_principal_model_comparison X K s U hsU hU M eM f hf
  let := hFadd
  let := hFlim
  let := hFcolim
  let A := Localization.Away f
  let N := (RingTensorCohomology.extend _ A).obj M
  let D := F.mapDerivedCategory
  obtain ⟨T, b, hlo, hhi, hp, ⟨eT⟩⟩ := hpos
  let L := (F.mapHomologicalComplex (.up ℤ)).obj T
  obtain ⟨hLp, hLa⟩ := positive_projective_sheaf_model A V.toScheme F hFfree T b hlo hhi hp
  let P := DerivedCategory.Q.obj L
  let left := D.obj (DerivedCategory.Q.obj (N.truncLE 0))
  have : left.IsLE 0 := F.isLE_mapDerivedCategory_obj _ 0
  have : P.IsGE 1 := by
    apply (DerivedCategory.isGE_iff _ 1).mpr
    intro i hi
    apply IsZero.of_iso (F.map_isZero ((T.sc i).isZero_homology_of_isZero_X₂
      ((T.isStrictlyGE_iff 1).mp hlo i hi)))
    exact (DerivedCategory.homologyFunctorFactors _ i).app L ≪≫
      (T.sc i).mapHomologyIso F
  let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V) ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
      (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv V)
  let e : R.mapDerivedCategory.obj K ≅ left ⊞ P :=
    eV ≪≫ (F.mapDerivedCategoryFactors.app N).symm ≪≫
      D.mapIso esplit.some ≪≫ D.mapBiprod _ _ ≪≫
      biprod.mapIso (Iso.refl _) (D.mapIso eT ≪≫ F.mapDerivedCategoryFactors.app T)
  obtain ⟨e'⟩ := split_iso_truncLT (R.mapDerivedCategory.obj K) left P e
  exact ⟨V, hsV, P, hLp, hLa, ⟨e'⟩⟩

end AlgebraicGeometry
