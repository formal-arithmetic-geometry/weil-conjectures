/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.CategoryTheory.SystemRingedSequenceSite
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Derived adjunction for the ringed sequence projection

Source: Stacks Project, Cohomology on Sites, Tags 0940, 0941, 06YY, 07A6;
Modules on Sites, Tag 03D7; Derived Categories, Tags 09T5 and 0FND.
(blueprint: lem-coef-sequence-projection-derived-adjunction).

The ordinary functors are characterized by their tensor generators and limit
projections. The derived adjunction is normalized on every chain map, so localization
extends precisely this ordinary correspondence to fractions. Index `n` means level `n+1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w d

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.SequenceProjection

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- The existing module category over the base ring sheaf, with coefficient universe `w`.
Source: Stacks 03CZ (blueprint: lem-coef-sequence-projection-derived-adjunction). -/
abbrev Modules (A : Sheaf J CommRingCat.{w}) :=
  ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A)

/-- The actual restriction from level `n+1` along its specified structural ring map.
Source: Stacks 03D7 (blueprint: lem-coef-sequence-projection-derived-adjunction). -/
abbrev restriction (A : Sheaf J CommRingCat.{w})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B) (n : ℕ) : systemLevel B n ⥤ Modules A :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
    (α.app (op n)))

/-- The image of the local tensor `b ⊗ x` in the existing sheafified scalar extension.
Source: Stacks 03EK (blueprint: lem-coef-sequence-projection-derived-adjunction).
The scalar-first convention is the symmetry of the node's notation `x ⊗ b`. -/
def tensorSection {A S : Sheaf J CommRingCat.{w}} (φ : A ⟶ S)
    (M : Modules A) (U : Cᵒᵖ) (b : S.obj.obj U) (x : M.val.obj U) :
    (changeOfRings φ M).val.obj U :=
  @SMul.smul (S.obj.obj U) ((changeOfRings φ M).val.obj U) inferInstance b
    ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
      (((ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app (M.val.obj U)) x))

/-- The sequence projection has the canonical unbounded derived adjunction, its ordinary
limit direct image, and its simultaneous flat-term K-flat tensor model.
Source: Stacks 0940/0941, 06YY, 07A6, 03D7, 09T5 and 0FND
(blueprint: lem-coef-sequence-projection-derived-adjunction).

Proof plan:
1. Use `strictSystemSequenceEquivalence` (lem-pur-system-ringed-sequence-site).
Vertical covers give componentwise kernels, sheafified cokernels and quasi-isomorphisms
(def-weil-sheaf-of-modules-category).
2. The compatible families of sections form an A-module sheaf. Componentwise gluing
proves the limit universal property for the scalar restrictions (def-pc-sheaf-restrict-scalars).
3. Apply lem-weil-pbc-ringed-topoi-module-adjunction. At each level the tensor is the
sheafification of sectionwise scalar extension. The transpose of h sends b tensor x to
b times pi_n(h(x)); the inverse evaluates at 1 tensor x. These formulas are balanced,
natural, and compatible with the actual transitions of B.
4. Apply prop-pur-kinjective-resolutions-exist on the sequence site, then
lem-weil-pbc-kinjective-total-derived to obtain the universal right derived pair.
5. Apply lem-weil-pbc-ringed-topoi-derived-pullback and lem-pc-kflat-resolution.
One flat-term K-flat Q supplies every level, with transitions 1 tensor rho. The
left comparison is invertible on Q; its naturality gives the comparison for any
quasi-isomorphism Q to P and compatibility with all maps of representatives.
6. Apply lem-sfb-resolving-derived-adjunction-normalization to these universal pairs,
using lem-weil-pbc-termwise-adjunction-homotopy. Its chain-map normalization is the
last equation below. Naturality and inversion of quasi-isomorphisms extend that equation
to all derived fractions, including further denominators; no fixed representative is
assumed to represent every derived morphism by a chain map. -/
theorem derivedAdjunction
    (A : Sheaf J CommRingCat.{w}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    [HasDerivedCategory.{d} (Modules A)] [HasDerivedCategory.{d} (StrictRingSystem B)] :
    ∃ (G : Modules A ⥤ StrictRingSystem B) (F : StrictRingSystem B ⥤ Modules A)
      (_ : G.Additive) (_ : F.Additive)
      (e : ∀ (M : Modules A) (n : ℕ),
        (G.obj M).level n ≅ changeOfRings (α.app (op n)) M)
      (π : ∀ (N : StrictRingSystem B) (n : ℕ),
        F.obj N ⟶ (restriction A B α n).obj (N.level n))
      (adj : G ⊣ F),
      (∀ {M M' : Modules A} (f : M ⟶ M') (n : ℕ),
        (G.map f).app n ≫ (e M' n).hom =
          (e M n).hom ≫ changeOfRingsHom (α.app (op n)) M f) ∧
      (∀ (M : Modules A) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
        (b : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
        ((G.obj M).transition h).val.app U
            ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
          (e M m).inv.val.app U (tensorSection (α.app (op m)) M U
            ((B.map (homOfLE h).op).hom.app U b) x)) ∧
      (∀ {N N' : StrictRingSystem B} (f : N ⟶ N') (n : ℕ),
        F.map f ≫ π N' n = π N n ≫ (restriction A B α n).map (f.app n)) ∧
      (∀ (N : StrictRingSystem B) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
        (x : (F.obj N).val.obj U),
        (π N m).val.app U x =
          (N.transition h).val.app U ((π N n).val.app U x)) ∧
      (∀ (M : Modules A) (N : StrictRingSystem B)
        (f : ∀ n : ℕ, M ⟶ (restriction A B α n).obj (N.level n)),
        (∀ {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) (x : M.val.obj U),
          (f m).val.app U x = (N.transition h).val.app U ((f n).val.app U x)) →
        ∃! h : M ⟶ F.obj N, ∀ n : ℕ, h ≫ π N n = f n) ∧
      (∀ (M : Modules A) (N : StrictRingSystem B) (h : M ⟶ F.obj N)
        (n : ℕ) (U : Cᵒᵖ) (b : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
        (((adj.homEquiv M N).symm h).app n).val.app U
            ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
          @SMul.smul ((B.obj (op n)).obj.obj U) ((N.level n).val.obj U) inferInstance b
            ((π N n).val.app U (h.val.app U x))) ∧
      ∃ (L : DerivedCategory.{d} (Modules A) ⥤ DerivedCategory.{d} (StrictRingSystem B))
        (R : DerivedCategory.{d} (StrictRingSystem B) ⥤ DerivedCategory.{d} (Modules A))
        (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
        (derivedAdj : L ⊣ R),
        L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Modules A) (.up ℤ)) ∧
        R.IsRightDerivedFunctor η
          (HomologicalComplex.quasiIso (StrictRingSystem B) (.up ℤ)) ∧
        (∀ (Q : CochainComplex (Modules A) ℤ), Q.IsKFlatIndependentCoefficients →
          (∀ i : ℤ, (Q.X i).IsFlatOnSite) → IsIso (ε.app Q)) ∧
        (∀ (I : CochainComplex (StrictRingSystem B) ℤ), I.IsKInjective →
          IsIso (η.app I)) ∧
        (∀ (P Q : CochainComplex (Modules A) ℤ) (q : Q ⟶ P),
          Q.IsKFlatIndependentCoefficients → (∀ i : ℤ, (Q.X i).IsFlatOnSite) →
          QuasiIso q →
          ∃ c : L.obj (DerivedCategory.Q.obj P) ≅
            DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj Q),
            L.map (DerivedCategory.Q.map q) ≫ c.hom = ε.app Q) ∧
        (∀ (Q : CochainComplex (Modules A) ℤ)
          (I : CochainComplex (StrictRingSystem B) ℤ)
          (f : (G.mapHomologicalComplex (.up ℤ)).obj Q ⟶ I),
          derivedAdj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
              (ε.app Q ≫ DerivedCategory.Q.map f) =
            DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
              η.app I) := by
  sorry

end SheafOfModules.SequenceProjection
