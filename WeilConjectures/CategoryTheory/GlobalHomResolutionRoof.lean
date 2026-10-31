/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-! # The ordinary-to-resolved global Hom roof

Source: Stacks Project, dga.tex, Example 09L9 (example-category-complexes),
derived.tex, Lemma 070I (lemma-K-injective), and sites-cohomology.tex, Section 0B6E.
(blueprint: lem-sf-global-hom-resolution-roof)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.HomComplex

namespace CategoryTheory

variable (B : Type v) [CommRing B] {A : Type u} [Category.{v} A] [Abelian A] [Linear B A]

/-- Product Hom with scalars retained, using Mathlib's cochains and exact signed differential.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalLinearHom (X Y : CochainComplex A ℤ) : CochainComplex (ModuleCat.{v} B) ℤ where
  X n := ModuleCat.of B (Cochain X Y n)
  d n m := ModuleCat.ofHom (δ_hom B X Y n m)
  shape n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_shape n m h z
  d_comp_d' n m k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_δ n m k z

/-- The degreewise pre/postcomposition map on the existing linear cochains.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalLinearHomMapTerm {X X' Y Y' : CochainComplex A ℤ}
    (a : X' ⟶ X) (b : Y ⟶ Y') (n : ℤ) :
    (globalLinearHom B X Y).X n ⟶ (globalLinearHom B X' Y').X n :=
  ModuleCat.ofHom
    { toFun := fun f ↦ (Cochain.ofHom a).comp (f.comp (Cochain.ofHom b) (add_zero n))
        (zero_add n)
      map_add' := by intros; simp
      map_smul' := by intros; simp }

/-- The pre/postcomposition maps commute with the Hom differential.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof).
Proof: expand both differentials as `d_Y f - (-1)^n f d_X`, and use the chain-map
identities for `a` and `b`. The two expressions agree componentwise. -/
theorem globalLinearHomMap_comm {X X' Y Y' : CochainComplex A ℤ}
    (a : X' ⟶ X) (b : Y ⟶ Y') (n m : ℤ) :
    globalLinearHomMapTerm B a b n ≫ (globalLinearHom B X' Y').d n m =
      (globalLinearHom B X Y).d n m ≫ globalLinearHomMapTerm B a b m := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change δ n m ((Cochain.ofHom a).comp
      (z.comp (Cochain.ofHom b) (add_zero n)) (zero_add n)) =
    (Cochain.ofHom a).comp
      ((δ n m z).comp (Cochain.ofHom b) (add_zero m)) (zero_add m)
  rw [δ_ofHom_comp, δ_comp_ofHom]

/-- Actual pre/postcomposition chain map, with its prescribed component formula.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalLinearHomMap {X X' Y Y' : CochainComplex A ℤ} (a : X' ⟶ X) (b : Y ⟶ Y') :
    globalLinearHom B X Y ⟶ globalLinearHom B X' Y' where
  f := globalLinearHomMapTerm B a b
  comm' n m _ := globalLinearHomMap_comm B a b n m

/-- A resolution is only a complex and its given quasi-isomorphism, with the usual
K-injectivity predicate; no linear or functorial choice is part of this input.
Source: Stacks 070I (blueprint: lem-sf-global-hom-resolution-roof). -/
structure GlobalHomResolution (X : CochainComplex A ℤ) where
  I : CochainComplex A ℤ
  ι : X ⟶ I
  injective : I.IsKInjective
  quasiIso : QuasiIso ι

attribute [instance] GlobalHomResolution.injective GlobalHomResolution.quasiIso

/-- The identity resolution of a K-injective complex.
Source: Stacks 070I (blueprint: lem-sf-global-hom-resolution-roof). -/
def GlobalHomResolution.self (X : CochainComplex A ℤ) [X.IsKInjective] :
    GlobalHomResolution X := ⟨X, 𝟙 X, inferInstance, inferInstance⟩

/-- Shift the actual augmentation, using the standard signed cochain shift.
Source: Stacks 09L9, 070I (blueprint: lem-sf-global-hom-resolution-roof). -/
def GlobalHomResolution.shift {X : CochainComplex A ℤ} (R : GlobalHomResolution X) (n : ℤ) :
    GlobalHomResolution (X⟦n⟧) :=
  ⟨R.I⟦n⟧, (shiftFunctor _ n).map R.ι, inferInstance, inferInstance⟩

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)]

/-- The resolved Hom object on the specified resolutions, exactly `q H(I_X,I_Y)`.
Source: Stacks 0B6E (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalResolvedHom {X Y : CochainComplex A ℤ}
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) :
    DerivedCategory (ModuleCat.{v} B) :=
  DerivedCategory.Q.obj (globalLinearHom B R.I S.I)

/-- The actual class of an abstract cycle in the cohomology of the localized complex.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalLinearHomClass (X Y : CochainComplex A ℤ) (n : ℤ)
    (z : (globalLinearHom B X Y).cycles n) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).obj
      (DerivedCategory.Q.obj (globalLinearHom B X Y)) :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} B) n).inv.app
    (globalLinearHom B X Y) ((globalLinearHom B X Y).homologyπ n z)

/-- The complete canonical resolution-roof assertion, with all maps specified on cochains.
The only data in the assertion are maps constrained by the displayed formulas; no
arbitrary comparison, tensor or resolution functor is an input.
Source: Stacks 09L9, 070I, 0B6E and 06XY; the resolution-roof extension in the node.
(blueprint: lem-sf-global-hom-resolution-roof). -/
structure GlobalHomResolutionRoof where
  /-- Precomposition by every resolution is a quasi-isomorphism into any K-injective. -/
  precomp_quasiIso : ∀ (X J : CochainComplex A ℤ) (R : GlobalHomResolution X),
    J.IsKInjective → QuasiIso (globalLinearHomMap B R.ι (𝟙 J))
  /-- The ordinary-to-resolved map, for every individual pair of resolutions. -/
  c : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X) (S : GlobalHomResolution Y),
    DerivedCategory.Q.obj (globalLinearHom B X Y) ⟶ globalResolvedHom B R S
  /-- The roof equation uniquely specifies `c`, since its right leg is invertible. -/
  roof : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X) (S : GlobalHomResolution Y),
    c X Y R S ≫ DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I)) =
      DerivedCategory.Q.map (globalLinearHomMap B (𝟙 X) S.ι)
  /-- Derived arrows of chain maps admit the required lifts, unique up to homotopy. -/
  lifts : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
    (S : GlobalHomResolution Y) (a : X ⟶ Y),
    ∃ a' : R.I ⟶ S.I, Nonempty (Homotopy (R.ι ≫ a') (a ≫ S.ι)) ∧
      ∀ a'' : R.I ⟶ S.I, Nonempty (Homotopy (R.ι ≫ a'') (a ≫ S.ι)) →
        Nonempty (Homotopy a' a'')
  /-- Joint naturality, for any representatives of the lifted chain maps. -/
  naturality : ∀ (X X' Y Y' : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (R' : GlobalHomResolution X')
    (S : GlobalHomResolution Y) (S' : GlobalHomResolution Y')
    (a : X' ⟶ X) (b : Y ⟶ Y') (a' : R'.I ⟶ R.I) (b' : S.I ⟶ S'.I),
    Nonempty (Homotopy (R'.ι ≫ a') (a ≫ R.ι)) →
    Nonempty (Homotopy (S.ι ≫ b') (b ≫ S'.ι)) →
    DerivedCategory.Q.map (globalLinearHomMap B a b) ≫ c X' Y' R' S' =
      c X Y R S ≫ DerivedCategory.Q.map (globalLinearHomMap B a' b')
  /-- Chain homotopies do not change either ordinary or resolved localized Hom arrows. -/
  homotopy_invariance : ∀ (X X' Y Y' : CochainComplex A ℤ)
    (a a' : X' ⟶ X) (b b' : Y ⟶ Y'),
    Nonempty (Homotopy a a') → Nonempty (Homotopy b b') →
    DerivedCategory.Q.map (globalLinearHomMap B a b) =
      DerivedCategory.Q.map (globalLinearHomMap B a' b')
  /-- The canonical comparison between any two pairs of resolutions. -/
  comparison : ∀ (X Y : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) (S S' : GlobalHomResolution Y),
    globalResolvedHom B R S ≅ globalResolvedHom B R' S'
  /-- Identity derived arrows are represented by homotopy equivalences of resolutions. -/
  comparison_lifts : ∀ (X : CochainComplex A ℤ) (R R' : GlobalHomResolution X),
    ∃ a : HomotopyEquiv R.I R'.I, Nonempty (Homotopy (R.ι ≫ a.hom) R'.ι)
  /-- Every such representative gives the same conjugation comparison. -/
  comparison_formula : ∀ (X Y : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) (S S' : GlobalHomResolution Y)
    (a : HomotopyEquiv R.I R'.I) (b : HomotopyEquiv S.I S'.I),
    Nonempty (Homotopy (R.ι ≫ a.hom) R'.ι) →
    Nonempty (Homotopy (S.ι ≫ b.hom) S'.ι) →
    (comparison X Y R R' S S').hom =
      DerivedCategory.Q.map (globalLinearHomMap B a.inv b.hom)
  /-- The comparison carries the old roof to the new roof. -/
  comparison_roof : ∀ (X Y : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) (S S' : GlobalHomResolution Y),
    c X Y R S ≫ (comparison X Y R R' S S').hom = c X Y R' S'
  /-- Identity normalization for resolution comparisons. -/
  comparison_refl : ∀ (X Y : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y),
    (comparison X Y R R S S).hom = 𝟙 _
  /-- The cocycle law for three choices. -/
  comparison_cocycle : ∀ (X Y : CochainComplex A ℤ)
    (R R' R'' : GlobalHomResolution X) (S S' S'' : GlobalHomResolution Y),
    (comparison X Y R R' S S').hom ≫ (comparison X Y R' R'' S' S'').hom =
      (comparison X Y R R'' S S'').hom
  /-- Identity resolutions give the identity roof. -/
  normalization : ∀ (X Y : CochainComplex A ℤ) [X.IsKInjective] [Y.IsKInjective],
    c X Y (GlobalHomResolution.self X) (GlobalHomResolution.self Y) = 𝟙 _
  /-- The signed target-shift isomorphism of ordinary Hom complexes. -/
  targetShift : ∀ (X Y : CochainComplex A ℤ) (n : ℤ),
    globalLinearHom B X (Y⟦n⟧) ≅ (globalLinearHom B X Y)⟦n⟧
  /-- The shift map is the actual family identification in every integer degree. -/
  targetShift_formula : ∀ (X Y : CochainComplex A ℤ) (n s : ℤ)
    (f : Cochain X (Y⟦n⟧) s),
    ((globalLinearHom B X Y).shiftFunctorObjXIso n s (s + n) rfl).hom
      ((targetShift X Y n).hom.f s f) = f.rightUnshift (s + n) rfl
  /-- Shifted augmentations commute with the roof; arbitrary choices use comparison_roof. -/
  targetShift_roof : ∀ (X Y : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) (n : ℤ),
    c X (Y⟦n⟧) R (S.shift n) ≫ DerivedCategory.Q.map (targetShift R.I S.I n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (globalLinearHom B R.I S.I) =
      DerivedCategory.Q.map (targetShift X Y n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (globalLinearHom B X Y) ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{v} B)) n).map (c X Y R S)
  /-- Ordinary composition out of the actual direct-sum total tensor complex. -/
  comp : ∀ (X Y Z : CochainComplex A ℤ),
    globalLinearHom B Y Z ⊗ globalLinearHom B X Y ⟶ globalLinearHom B X Z
  /-- On every homogeneous pure tensor composition is exactly `g ∘ f`. -/
  comp_formula : ∀ (X Y Z : CochainComplex A ℤ) (r s n : ℤ) (h : r + s = n)
    (g : Cochain Y Z r) (f : Cochain X Y s),
    (comp X Y Z).f n
        (HomologicalComplex.ιTensorObj (globalLinearHom B Y Z) (globalLinearHom B X Y)
          r s n h (g ⊗ₜ[B] f)) = f.comp g (by omega)
  /-- Localized ordinary composition, preceded by the canonical derived-to-ordinary
  comparison, is compatible with every roof. This is the stated equation for `m`. -/
  composition_roof : ∀ (X Y Z : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) (T : GlobalHomResolution Z),
    (c Y Z S T ⊗ₘ c X Y R S) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B S.I T.I)
          (globalLinearHom B R.I S.I) ≫ DerivedCategory.Q.map (comp R.I S.I T.I) =
      Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B Y Z)
        (globalLinearHom B X Y) ≫ DerivedCategory.Q.map (comp X Y Z) ≫ c X Z R T
  /-- The composition descends through all canonical resolution comparisons. -/
  composition_comparison : ∀ (X Y Z : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) (S S' : GlobalHomResolution Y)
    (T T' : GlobalHomResolution Z),
    ((comparison Y Z S S' T T').hom ⊗ₘ (comparison X Y R R' S S').hom) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B S'.I T'.I)
          (globalLinearHom B R'.I S'.I) ≫ DerivedCategory.Q.map (comp R'.I S'.I T'.I) =
      Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B S.I T.I)
        (globalLinearHom B R.I S.I) ≫ DerivedCategory.Q.map (comp R.I S.I T.I) ≫
        (comparison X Z R R' T T').hom
  /-- The identity cochain as an actual map from `B[0]`. -/
  unit : ∀ (X : CochainComplex A ℤ),
    (CochainComplex.singleFunctor (ModuleCat.{v} B) 0).obj (ModuleCat.of B B) ⟶
      globalLinearHom B X X
  /-- It sends a scalar to that scalar times the identity cochain. -/
  unit_formula : ∀ (X : CochainComplex A ℤ) (b : B),
    (unit X).f 0
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of B B)).inv b) =
      b • Cochain.ofHom (𝟙 X)
  /-- The roof preserves the identity. -/
  unit_roof : ∀ (X : CochainComplex A ℤ) (R : GlobalHomResolution X),
    DerivedCategory.Q.map (unit X) ≫ c X X R R = DerivedCategory.Q.map (unit R.I)
  /-- The natural cohomology/derived-arrow interpretation, with the specified source and target. -/
  cohomology : ∀ (X Y : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) (n : ℤ),
    (DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).obj (globalResolvedHom B R S) ≃+
      (DerivedCategory.Q.obj X ⟶ (DerivedCategory.Q.obj Y)⟦n⟧)
  /-- Its value on a resolved cocycle is conjugation by the two augmentations. -/
  cohomology_resolved : ∀ (X Y : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) (n : ℤ)
    (z : (globalLinearHom B R.I S.I).cycles n) (f : Cocycle R.I S.I n),
    (f : Cochain R.I S.I n) = (globalLinearHom B R.I S.I).iCycles n z →
    cohomology X Y R S n (globalLinearHomClass B R.I S.I n z) ≫
        (shiftFunctor (DerivedCategory A) n).map (DerivedCategory.Q.map S.ι) =
      DerivedCategory.Q.map R.ι ≫ DerivedCategory.Q.map (Cocycle.equivHomShift.symm f) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app S.I
  /-- On every ordinary cocycle, the map on cohomology is exactly `Q f`. -/
  cohomology_roof : ∀ (X Y : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) (n : ℤ)
    (z : (globalLinearHom B X Y).cycles n) (f : Cocycle X Y n),
    (f : Cochain X Y n) = (globalLinearHom B X Y).iCycles n z →
    cohomology X Y R S n
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).map (c X Y R S)
          (globalLinearHomClass B X Y n z)) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm f) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app Y
  /-- Naturality in both variables of the cohomology interpretation. -/
  cohomology_naturality : ∀ (X X' Y Y' : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (R' : GlobalHomResolution X')
    (S : GlobalHomResolution Y) (S' : GlobalHomResolution Y')
    (a : X' ⟶ X) (b : Y ⟶ Y') (a' : R'.I ⟶ R.I) (b' : S.I ⟶ S'.I),
    Nonempty (Homotopy (R'.ι ≫ a') (a ≫ R.ι)) →
    Nonempty (Homotopy (S.ι ≫ b') (b ≫ S'.ι)) →
    ∀ (n : ℤ) (z : (DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).obj
      (globalResolvedHom B R S)),
    cohomology X' Y' R' S' n
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).map
          (DerivedCategory.Q.map (globalLinearHomMap B a' b')) z) =
      DerivedCategory.Q.map a ≫ cohomology X Y R S n z ≫
        (shiftFunctor (DerivedCategory A) n).map (DerivedCategory.Q.map b)

/-- Canonical ordinary-to-resolved global Hom roof, including composition and cohomology.
Source: Stacks 09L9, 070I, 0B6E and 06XY; agent-formulated resolution-roof extension.
(blueprint: lem-sf-global-hom-resolution-roof).

Proof (the node's eleven steps):
1. The product cochains are B-modules. Expand the differential: its square is zero,
   and `d(gf) = d(g)f + (-1)^|g| g d(f)`. Composition therefore defines a map from
   the direct-sum total tensor, without any boundedness requirement.
2. By lem-sc-hom-cocycle-homotopy-quotient-formulas, Hom cohomology is maps to shifts
   modulo homotopy. Shifts preserve K-injectivity. Apply lem-weil-pbc-kinjective-hom-derived
   to conclude that precomposition by a quasi-isomorphism into a K-injective target
   is an isomorphism on every cohomology group, hence a quasi-isomorphism.
3. A homotopy `h` of target maps gives the Hom homotopy `f ↦ hf`; for source maps
   use `f ↦ (-1)^|f| fh`. Thus localized Hom arrows depend only on homotopy classes.
4. Define the roof by inverting its precomposition leg. The K-injective Hom bijection
   lifts derived arrows to chain maps uniquely up to homotopy, with augmentation squares.
5. For either variable, postcompose both naturality expressions with the invertible
   precomposition leg. The augmentation homotopies reduce both to the same map; cancel.
6. Lift identity derived arrows between two resolutions to homotopy equivalences.
   Conjugation on Hom is independent of representatives, preserves the roof, and
   satisfies the cocycle law by uniqueness of the lifted homotopy classes. Identities
   give the identity roof when both original complexes are K-injective.
7. The family identity gives `H(X,Y[n]) ≅ H(X,Y)[n]`: both differentials are
   `(-1)^n d_Y f - (-1)^s f d_X`. Shift the augmentation and use the preceding comparison.
8. Use lem-sfb-derived-tensor-modules-derived for the canonical lax localization map;
   the module Grothendieck and functorial-flat-resolution inputs are supplied by
   lem-weil-pbc-ring-modules-grothendieck-abelian and
   lem-sfb-abelian-functorial-flat-resolution. Define resolved composition by ordinary
   composition after this comparison.
9. For R=H(I,I), M=H(X,I), O=H(X,X), the three mixed-composition identities are
   `j comp_R = A(1 ⊗ j)`, `A(1 ⊗ p) = B(j ⊗ 1)`, `B(p ⊗ 1) = p comp_O`.
   Apply localization and naturality of the tensor comparison, substitute `j c = p`
   twice, and cancel the invertible final j. No tensor of a quasi-isomorphism with
   an arbitrary nonflat complex is inverted.
10. Both sides of the identity assertion map to the augmentation under j. Conjugation
    preserves composition: insert `b_Y a_Y - 1 = dh + hd`, and use the tensor homotopy
    `S(g ⊗ f) = (-1)^|g| a_Z g h f b_X`. Ordinary associativity and units and lax
    localization coherence give derived associativity and units.
11. Identify resolved Hom cohomology with derived arrows between the resolutions,
    then conjugate by the augmentations. The roof equation sends the class of an
    ordinary cocycle to exactly Qf. All constructions use products of sets only,
    with no flatness, boundedness or scalar-linear choice of resolutions. -/
theorem globalHom_resolution_roof
    (hres : ∀ X : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (uX : X ⟶ I), I.IsKInjective ∧ QuasiIso uX) :
    Nonempty (GlobalHomResolutionRoof.{u, v, w, t} B (A := A)) := by
  sorry

end CategoryTheory
