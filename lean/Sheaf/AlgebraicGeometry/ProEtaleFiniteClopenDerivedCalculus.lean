/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
public import Sheaf.Algebra.Homology.RingedDerivedTensorNative
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientData
public import Sheaf.AlgebraicGeometry.ProEtaleClopenMonoidalNormalization
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarData
import Sheaf.CategoryTheory.FiniteProductDerivedLocalization
import Sheaf.CategoryTheory.AdditiveFiniteProductCoordinates
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.CategoryTheory.PUnit

/-!
# Unbounded derived calculus for a finite clopen partition

Source: Stacks Project, derived.tex, Tags 015F and 05RU; sites-modules.tex, Tag 0GMW;
sites-cohomology.tex, Tags 06YN, 06YS, 0G7D and 06YU; finite-component application
(blueprint: lem-pur-finite-clopen-derived-calculus).

All restrictions are the sectionwise functors of the module-gluing node. Tensor products
and their constraints are the existing sheafification and K-flat localization constructions.
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenScalar.derived
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenScalar.sheafify
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenScalar.locallyBijective

-- The canonical public wrappers below provide these instances to consumers.
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.hasDerived
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.monoidal
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.symmetric
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.restrictionLimits
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.restrictionColimits

set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe t u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory
  DerivedCategory.Q Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard DerivedCategory.Qh DerivedCategory.quotientCompQhIso
  Functor.mapDerivedCategoryFactorsh Functor.mapHomotopyCategoryFactors
  RingedDerivedNative.monoidal RingedDerivedNative.symmetric
  coefficientTotalTensor
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.ModelNormalization

namespace AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor

/-- The recorded module category, with a coefficient universe containing the small site.
Source: Stacks 03D7 (blueprint: lem-pur-finite-clopen-derived-calculus). -/
abbrev Modules {X : Scheme.{t}} (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  clopenTensorModules.{t, u} R

/-- Restrict commutative rings by the same site composition as `clopenRingRestriction`.
Source: Stacks 04TR (blueprint: lem-pur-finite-clopen-derived-calculus). -/
abbrev rings {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j] :=
  clopenTensorRings.{t, u} j

/-- The module restriction of the recorded gluing theorem, without changing its data.
Source: Stacks 04TR (blueprint: lem-pur-finite-clopen-derived-calculus). -/
abbrev restriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    Modules.{t, u} R ⥤ Modules.{t, u} ((rings.{t, u} j).obj R) :=
  clopenTensorRestriction.{t, u} j R

/-- Exactness of component restriction, including the unbounded case.
Source: Stacks 015F and 04TR (blueprint: lem-pur-finite-clopen-derived-calculus).
Proof: identify the component site with the slice at the open immersion. Restriction
preserves kernels and sheafified cokernels by the exact module-gluing equivalence;
equivalently sheaf exactness is local on this slice. No exactness of sections is used. -/
theorem restriction_exact {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    PreservesFiniteLimits (restriction.{t, u} j R) ∧
      PreservesFiniteColimits (restriction.{t, u} j R) := by
  exact ⟨ClopenScalar.resLimits j R, ClopenScalar.resColimits j R⟩

/-- Exact restriction preserves finite limits.
Source: Stacks 015F (blueprint: lem-pur-finite-clopen-derived-calculus). -/
instance restrictionLimits {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    PreservesFiniteLimits (restriction.{t, u} j R) := (restriction_exact j R).1

/-- Exact restriction preserves finite colimits.
Source: Stacks 015F (blueprint: lem-pur-finite-clopen-derived-calculus). -/
instance restrictionColimits {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    PreservesFiniteColimits (restriction.{t, u} j R) := (restriction_exact j R).2

/-- Additivity is the already recorded sectionwise restriction additivity.
Source: Stacks 04TR (blueprint: lem-pur-finite-clopen-derived-calculus). -/
instance restrictionAdditive {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    (restriction.{t, u} j R).Additive :=
  clopenModuleRestriction_additive j _

/-- Standard localization in the fixed module universe, with no boundedness restriction.
Source: Stacks 05RU (blueprint: lem-pur-finite-clopen-derived-calculus). -/
@[instance_reducible]
instance hasDerived {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    HasDerivedCategory.{max (u + 1) (t + 2)} (Modules.{t, u} R) :=
  ClopenMonoidalDescent.hasDerived.{t, u} R

/-- Degreewise restriction followed by localization at quasi-isomorphisms.
Source: Stacks 015F, 05RU (blueprint: lem-pur-finite-clopen-derived-calculus). -/
abbrev derivedRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  ClopenMonoidalDescent.derivedRestriction.{t, u} j R

/-- The existing native K-flat derived tensor, with its prescribed constraints.
Source: Stacks 0FPT (blueprint: lem-pur-finite-clopen-derived-calculus). -/
instance derivedMonoidal {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    MonoidalCategory (DerivedCategory (Modules.{t, u} R)) :=
  ClopenMonoidalDescent.monoidal.{t, u} R

/-- Its existing Koszul symmetry.
Source: Stacks 0FPT (blueprint: lem-pur-finite-clopen-derived-calculus). -/
instance derivedSymmetric {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    SymmetricCategory (DerivedCategory (Modules.{t, u} R)) :=
  ClopenMonoidalDescent.symmetric.{t, u} R

/-- The pure tensor in the existing localization tensor of module sheaves.
Source: Stacks 0GMW (blueprint: lem-pur-finite-clopen-derived-calculus). -/
def pure {X : Scheme.{t}} (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (F H : Modules.{t, u} R) (U : X.ProEtᵒᵖ) (x : F.val.obj U) (y : H.val.obj U) :
    (F ⊗ H).val.obj U :=
  clopenTensorPure.{t, u} R F H U x y

/-- The inverse tensorator of a braided restriction functor.
Source: Stacks 0GMW (blueprint: lem-pur-finite-clopen-derived-calculus). -/
def tensorComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (restriction.{t, u} j R).Braided) (F H : Modules.{t, u} R) :
    (restriction.{t, u} j R).obj (F ⊗ H) ≅
      (restriction.{t, u} j R).obj F ⊗ (restriction.{t, u} j R).obj H :=
  clopenTensorComparison.{t, u} j R h F H

/-- The inverse tensorator on the prescribed native derived tensors.
Source: Stacks 06YU, 0FPT (blueprint: lem-pur-finite-clopen-derived-calculus). -/
def derivedTensorComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (derivedRestriction.{t, u} j R).Braided)
    (K L : DerivedCategory (Modules.{t, u} R)) :
    (derivedRestriction.{t, u} j R).obj (K ⊗ L) ≅
      (derivedRestriction.{t, u} j R).obj K ⊗ (derivedRestriction.{t, u} j R).obj L :=
  (ClopenMonoidalDescent.braidedComparison.{t, u} j R h).app (K, L)

private local instance piPreadditive {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] : Preadditive (∀ i, D i) :=
  CategoryTheory.FiniteProductCoordinates.piPreadditive D

private theorem equivalenceCoordinateDecomposition
    {C : Type*} [Category C] [Preadditive C] {J : Type*} [Finite J]
    (D : J → Type*) [∀ i, Category (D i)] [∀ i, Preadditive (D i)]
    [∀ i, HasZeroObject (D i)] (E : C ≌ ∀ i, D i) [E.inverse.Additive] :
    ∃ e : ∀ i, D i ⥤ C,
      (∀ i, Nonempty (e i ⋙ (E.functor ⋙ Pi.eval D i) ≅ 𝟭 _)) ∧
      (∀ i k, i ≠ k → ∀ M, IsZero ((e k ⋙ (E.functor ⋙ Pi.eval D i)).obj M)) ∧
      (∃ s : ∀ i, D i ⥤ ∀ k, D k,
        ∀ i, e i = s i ⋙ E.inverse ∧
          Nonempty (s i ⋙ Pi.eval D i ≅ 𝟭 _) ∧
          (∀ k, k ≠ i → ∀ M, IsZero ((s i).obj M k))) ∧
      (∃ b : Bicone (fun i ↦ (E.functor ⋙ Pi.eval D i) ⋙ e i),
        b.pt = 𝟭 _ ∧ Nonempty b.IsBilimit) ∧
      (∃ b : Bicone (fun i ↦ Pi.eval D i ⋙ e i),
        b.pt = E.inverse ∧ Nonempty b.IsBilimit) := by
  exact CategoryTheory.FiniteProductCoordinates.equivalenceCoordinateDecomposition D E

section DerivedPi

universe a b c d z
variable {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory A]
  {I : Type z} [Finite I] {B : I → Type c} [∀ i, Category.{d} (B i)]
  [∀ i, Abelian (B i)] [∀ i, HasDerivedCategory (B i)]
  (r : ∀ i, A ⥤ B i) [∀ i, (r i).Additive]
  [∀ i, PreservesFiniteLimits (r i)] [∀ i, PreservesFiniteColimits (r i)]
  (G : (∀ i, B i) ⥤ A)
  (hzero : ∀ (M N : ∀ i, B i), G.map (fun i ↦ (0 : M i ⟶ N i)) = 0)
  (η : 𝟭 A ≅ Functor.pi' r ⋙ G) (ε : G ⋙ Functor.pi' r ≅ 𝟭 _)

include G hzero η ε in
private theorem derivedPi_isEquivalence
    (hr : JointlyReflectIsomorphisms r) :
    (Functor.pi' (fun i ↦ (r i).mapDerivedCategory)).IsEquivalence := by
  exact CategoryTheory.FiniteProductDerived.derivedPi_isEquivalence r G hzero η ε hr

end DerivedPi

/-- Module gluing for an arbitrary finite index universe, with the recorded restrictions.
Source: Stacks Project, Tags 04TR and 04TS
(blueprint: lem-pur-finite-clopen-derived-calculus). -/
theorem moduleGluingCore
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hc : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    ∃ E : Modules.{t, u} R ≌ ∀ i, Modules.{t, u} ((rings (j i)).obj R),
      E.functor = Functor.pi' (fun i ↦ restriction (j i) R) := by
  classical
  obtain ⟨n, ⟨a⟩⟩ := Finite.exists_equiv_fin I
  let e := a.symm
  let S := (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R
  have hde : Pairwise (fun i k : Fin n ↦
      Disjoint (Set.range (j (e i))) (Set.range (j (e k)))) := by
    intro i k hik
    exact hd (fun h ↦ hik (e.injective h))
  have hce : ∀ x : X, ∃ i : Fin n, x ∈ Set.range (j (e i)) := by
    intro x
    obtain ⟨i, hi⟩ := hc x
    exact ⟨e.symm i, by rw [e.apply_symm_apply]; exact hi⟩
  obtain ⟨G, η, ε, _⟩ := clopen_ringed_module_gluing.{t, max u (t + 1), u, 0,
    max u (t + 1), max u (t + 1), 0, 0}
    X (Fin n) (fun i ↦ Y (e i)) (fun i ↦ j (e i)) hde hce S
    (by intro U a b; exact @mul_comm (R.obj.obj U) inferInstance a b)
  let E₀ := CategoryTheory.Equivalence.mk _ G η ε
  let T := Pi.equivalenceOfEquiv (fun i ↦ Modules.{t, u} ((rings (j i)).obj R)) e
  let r := Functor.pi' (fun i ↦ restriction (j i) R)
  let h : (E₀.trans T).functor ≅ r :=
    Functor.associator r T.inverse T.functor ≪≫
      Functor.isoWhiskerLeft r T.counitIso ≪≫ Functor.rightUnitor r
  exact ⟨(E₀.trans T).changeFunctor h, rfl⟩

private theorem emptyDerived (X : Scheme.{t}) [IsEmpty X]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    Nonempty (DerivedCategory (Modules.{t, u} R) ≌ Discrete PUnit) := by
  classical
  obtain ⟨E, he⟩ := moduleGluingCore X PEmpty.{1} (fun i ↦ PEmpty.elim i)
    (fun i ↦ PEmpty.elim i) (by intro i; exact PEmpty.elim i)
    (fun x ↦ isEmptyElim x) R
  have hz (M : Modules.{t, u} R) : IsZero M := by
    rw [IsZero.iff_id_eq_zero]
    apply E.functor.map_injective
    funext i
    exact PEmpty.elim i
  have hD (K : DerivedCategory (Modules.{t, u} R)) : IsZero K :=
    (DerivedCategory.isZero_iff K).mpr (fun n ↦ hz _)
  apply (equiv_punit_iff_unique _).mpr
  exact ⟨⟨HasZeroObject.zero.choose⟩,
    fun K L ↦ ⟨{ default := 0, uniq := fun f ↦ (hD K).eq_of_src f 0 }⟩⟩

/-- The unbounded derived equivalence, insertion identities, cohomology and detection.
Source: Stacks 015F, 05RU and finite-product localization
(blueprint: lem-pur-finite-clopen-derived-calculus).

Proof (node steps 1-3 and 12): apply the exact module equivalence and its sectionwise
product inverse degreewise, including differentials and homotopies. Cohomology commutes
with exact restriction, so quasi-isomorphisms are detected componentwise. The finite
product of the localization functors is a localization at the component quasi-isomorphisms;
descend the inverse through it. Descend the module unit, counit and triangle equations
using the faithful natural-transformation clause of localization. Cone matrices and
shifts commute with the additive exact functors, proving triangulatedness. Zero insertion
and its projection identities descend the same way; their finite bilimit bicone has
vertex the identity. Thus the inverse is naturally the finite sum of inserted components.
The equivalence detects zero objects and isomorphisms. An empty site has only zero
modules, hence zero complexes and a terminal derived category. For an empty partition
the covering condition forces the scheme empty. No nonempty-index hypothesis is used. -/
theorem finite_clopen_derived_calculus
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    ∃ E : DerivedCategory (Modules.{t, u} R) ≌
        (∀ i, DerivedCategory (Modules.{t, u} ((rings.{t, u} (j i)).obj R))),
      E.functor = Functor.pi' (fun i ↦ derivedRestriction (j i) R) ∧
      (∀ i, (derivedRestriction.{t, u} (j i) R).IsTriangulated) ∧
      (∀ i (m : ℤ), Nonempty
        (derivedRestriction (j i) R ⋙ DerivedCategory.homologyFunctor _ m ≅
          DerivedCategory.homologyFunctor _ m ⋙ restriction (j i) R)) ∧
      (∀ K : DerivedCategory (Modules.{t, u} R),
        IsZero K ↔ ∀ i, IsZero ((derivedRestriction.{t, u} (j i) R).obj K)) ∧
      (∀ (K L : DerivedCategory (Modules.{t, u} R)) (f : K ⟶ L),
        IsIso f ↔ ∀ i, IsIso ((derivedRestriction.{t, u} (j i) R).map f)) ∧
      (∃ e : ∀ i, DerivedCategory (Modules.{t, u} ((rings.{t, u} (j i)).obj R)) ⥤
          DerivedCategory (Modules.{t, u} R),
        (∀ i, Nonempty (e i ⋙ derivedRestriction (j i) R ≅ 𝟭 _)) ∧
        (∀ i k, i ≠ k → ∀ K, IsZero ((e k ⋙ derivedRestriction (j i) R).obj K)) ∧
        (∃ s : ∀ i, DerivedCategory (Modules.{t, u} ((rings.{t, u} (j i)).obj R)) ⥤
            (∀ k, DerivedCategory (Modules.{t, u} ((rings (j k)).obj R))),
          ∀ i, e i = s i ⋙ E.inverse ∧
            Nonempty (s i ⋙ Pi.eval
              (fun k ↦ DerivedCategory (Modules.{t, u} ((rings (j k)).obj R))) i ≅ 𝟭 _) ∧
            (∀ k, k ≠ i → ∀ K, IsZero ((s i).obj K k))) ∧
        (∃ b : Bicone (fun i ↦ derivedRestriction (j i) R ⋙ e i),
          b.pt = 𝟭 _ ∧ Nonempty b.IsBilimit) ∧
        (∃ b : Bicone (fun i ↦ Pi.eval
            (fun k ↦ DerivedCategory (Modules.{t, u} ((rings (j k)).obj R))) i ⋙ e i),
          b.pt = E.inverse ∧ Nonempty b.IsBilimit)) ∧
      (∀ i, IsEmpty (Y i) → Nonempty
        (DerivedCategory (Modules.{t, u} ((rings.{t, u} (j i)).obj R)) ≌ Discrete PUnit)) ∧
      (IsEmpty I → IsEmpty X ∧ Nonempty
        (DerivedCategory (Modules.{t, u} R) ≌ Discrete PUnit)) := by
  classical
  obtain ⟨E₀, hE₀⟩ := moduleGluingCore X I Y j hdisjoint hcover R
  have hA : E₀.functor.Additive := by
    constructor
    intro M N f g
    rw [hE₀]
    funext i
    exact (restriction (j i) R).map_add
  let := hA
  have hr : JointlyReflectIsomorphisms (fun i ↦ restriction (j i) R) := by
    constructor
    intro M N f hf
    have : IsIso (E₀.functor.map f) := by
      rw [hE₀]
      exact (isIso_pi_iff _).mpr hf
    exact isIso_of_reflects_iso f E₀.functor
  have hD := derivedPi_isEquivalence (fun i ↦ restriction (j i) R) E₀.inverse
    (fun M N ↦ E₀.inverse.map_zero M N)
    (by simpa only [hE₀] using E₀.unitIso)
    (by simpa only [hE₀] using E₀.counitIso) hr
  have hD' : (Functor.pi' (fun i ↦ derivedRestriction (j i) R)).IsEquivalence := hD
  let := hD'
  let rd := Functor.pi' (fun i ↦ derivedRestriction (j i) R)
  let E := rd.asEquivalence
  have hd := Functor.jointlyReflectIsomorphisms_mapDerivedCategory hr
  have : E.functor.Additive := by
    constructor
    intro M N f g
    funext i
    exact (derivedRestriction (j i) R).map_add
  obtain ⟨e, he, hz, hs, hb, hc⟩ := equivalenceCoordinateDecomposition
    (fun i ↦ DerivedCategory (Modules.{t, u} ((rings (j i)).obj R))) E
  refine ⟨E, rfl, (fun _ ↦ inferInstance), ?_, (fun _ ↦ hd.isZero_iff), ?_, ?_, ?_, ?_⟩
  · intro i n
    exact ⟨((restriction (j i) R).mapDerivedCategoryHomologyFunctorIso n).symm⟩
  · intro K L f
    exact hd.isIso_iff f
  · exact ⟨e, he, hz, hs, hb, hc⟩
  · intro i hi
    let := hi
    exact emptyDerived (Y i) _
  · intro hi
    have hX : IsEmpty X := ⟨fun x ↦ hi.false (hcover x).choose⟩
    let := hX
    exact ⟨hX, emptyDerived X R⟩


end AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor
