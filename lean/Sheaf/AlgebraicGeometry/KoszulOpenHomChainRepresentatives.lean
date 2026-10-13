/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Sheaf.Algebra.Homology.ModuleHomComplex
import Sheaf.AlgebraicGeometry.KoszulOpenSystem

/-! # Normalized chain representatives for Koszul derived Hom

Source: Stacks Project, Tags 06Z0 and 08DD.
(blueprint: lem-sc-koszul-open-hom-chain-representatives).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

noncomputable section

/-- The class of a chain map in the module-valued Hom complex.
Source: Stacks Project, Tag 0A8H; cycles are chain maps and boundaries are homotopies.
(blueprint: lem-sc-koszul-open-hom-chain-representatives). -/
def koszulHomChainClass {A : Type u} [CommRing A]
    {L M : CochainComplex (ModuleCat.{u} A) ℤ} (t : L ⟶ M) :
    (CochainComplex.moduleHomComplex L M).homology 0 :=
  let S := (CochainComplex.moduleHomComplex L M).sc 0
  (S.moduleCatCyclesIso.inv ≫ S.homologyπ)
    ⟨CochainComplex.HomComplex.Cochain.ofHom t, by
      change CochainComplex.HomComplex.δ 0 _
        (CochainComplex.HomComplex.Cochain.ofHom t) = 0
      exact CochainComplex.HomComplex.δ_ofHom t⟩

/-- Transpose a sheaf chain map through the ordinary affine tilde/sections adjunction.
Source: Stacks Project, Tag 06Z0.
(blueprint: lem-sc-koszul-open-hom-chain-representatives). -/
def koszulOpenHomTranspose (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (e : ℕ) (t : koszulOpenSheafComplex A r f e ⟶ F) :
    (koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat ⟶
      ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F :=
  letI : (tilde.functor (.of A)).Additive :=
    ⟨fun {_ _} g h ↦ tilde.map_add g h⟩
  letI : (moduleSpecΓFunctor (R := .of A)).Additive :=
    ⟨fun {_ _} _ _ ↦ rfl⟩
  ((tilde.adjunction (R := .of A)).mapHomologicalComplex (.up ℤ)).homEquiv _ _ t

/-- The chain-map class in the specified stage of the derived Hom diagram.
This is constructed from the cycle, the homology projection, and the specified object iso.
Source: Stacks Project, Tags 0A8H and 08D1.
(blueprint: lem-sc-koszul-open-hom-chain-representatives). -/
def koszulOpenHomStageClass (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (e : ℕ) (t : koszulOpenSheafComplex A r f e ⟶ F) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      (DerivedCategory.Q.obj ((koszulCechHomDiagram A r f
        (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F)).obj e)) :=
  let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F
  let K := CochainComplex.moduleHomComplex
    ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  H.map (DerivedCategory.Q.map (koszulCechHomObjIso A r f M e).inv)
    (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).app K).inv
      (koszulHomChainClass (koszulOpenHomTranspose A r f F e t)))

/-- Normalized stage identifications and chain representability, before restriction to U.
Source: Stacks Project, Proposition 36.9.5, Tag 08DD, the derived-Hom identification;
Lemma 36.3.5, Tag 06Z0, and More on Algebra, Lemma 15.75.2.
(blueprint: lem-sc-koszul-open-hom-chain-representatives).

Proof: Let L be the extended module Koszul tail and M the top-sections complex of F.
Each term of L is a finite free exterior power, or zero outside the negative tail.
Thus L is bounded above with projective terms and is K-projective. Its derived maps
into M are homotopy classes of chain maps. The affine equivalence identifies these
with maps from Q(tilde L) into Q(F): the termwise tilde/sections counit is an iso
because every F.X n is quasi-coherent. The ordinary adjunction on complexes takes
a sheaf chain map t to exactly koszulOpenHomTranspose t. Degree-zero cycles of the
module Hom complex are chain maps and boundaries are null-homotopic maps. Quotient
by boundaries, then transport through koszulCechHomObjIso and the localization/homology
iso. This gives a, with the displayed normalization, and also proves surjectivity of
Q on maps from this tail to F. For r=0 the positive exterior powers are zero; both
Hom and Hom-complex homology vanish. Zero rings and zero complexes give the same
identification, without any nonzero or boundedness assumption on F. -/
theorem koszulOpenHom_chain_representatives
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent) :
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
    let D := koszulCechHomDiagram A r f
      (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F)
    ∃ a : ∀ e : ℕ, (koszulOpenObject A r f e ⟶ DerivedCategory.Q.obj F) ≃
        H.obj (DerivedCategory.Q.obj (D.obj e)),
      (∀ (e : ℕ) (t : koszulOpenSheafComplex A r f e ⟶ F),
        a e (DerivedCategory.Q.map t) = koszulOpenHomStageClass A r f F e t) ∧
      ∀ (e : ℕ) (φ : koszulOpenObject A r f e ⟶ DerivedCategory.Q.obj F),
        ∃ t : koszulOpenSheafComplex A r f e ⟶ F, DerivedCategory.Q.map t = φ := by
  sorry

end
end AlgebraicGeometry
