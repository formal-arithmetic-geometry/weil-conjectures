/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The prime-to-ell alteration category and topology

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II, Definitions 1.1.2,
1.1.8, 1.2.2, §§2.1.1--2.1.2 and 2.3.1, printed pp. 23--28
(blueprint: def-per-prime-to-ell-alteration-topology).

The topology is an infimum of Grothendieck topologies, rather than a claim that the
specified generating families already form a pretopology (Remark 2.3.2).

## Main definitions

* `Alt`: reduced finite-type, maximally dominant, generically finite schemes over `S`.
* `IsMaximallyPrimeToEllFinite`: the condition on generic residue fields.
* `IsPrimeToEllDecomposedEtaleFamily` and `IsCompletelyDecomposedEtaleFamily`.
* `topology`, `IsCoveringFamily` and `Refines`: the topology and its family language.
-/

@[expose] public section

set_option autoImplicit false

universe u w w'

open CategoryTheory

namespace AlgebraicGeometry.PrimeToEllAlteration

/-- The category `alt/S`, with all morphisms over `S`. A maximal point means that its
singleton closure is an irreducible component. Source: ILO II 1.1.2, 1.1.7 and 1.2.2
(blueprint: def-per-prime-to-ell-alteration-topology). -/
abbrev Alt (S : Scheme.{u}) [IsNoetherian S] :=
  ObjectProperty.FullSubcategory (fun T : Over S ↦
    LocallyOfFiniteType T.hom ∧ QuasiCompact T.hom ∧ IsReduced T.left ∧
      ∀ t : T.left, closure ({t} : Set T.left) ∈ irreducibleComponents T.left →
        closure ({T.hom t} : Set S) ∈ irreducibleComponents S ∧
          (T.hom.residueFieldMap t).hom.Finite)

/-- Maximal prime-to-ell finiteness imposes finiteness at every source maximal point and
one prime-to-ell lift for each target maximal point in the image. Source: ILO II 1.1.8
(blueprint: def-per-prime-to-ell-alteration-topology). -/
def IsMaximallyPrimeToEllFinite (ell : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  (∀ x : X, closure ({x} : Set X) ∈ irreducibleComponents X →
    (f.residueFieldMap x).hom.Finite) ∧
  ∀ y : Y, closure ({y} : Set Y) ∈ irreducibleComponents Y → y ∈ Set.range f →
    ∃ x : X, closure ({x} : Set X) ∈ irreducibleComponents X ∧ f x = y ∧
      Nat.Coprime (f.residueDegree x) ell

/-- A prime-to-ell decomposed étale family has a finite prime-to-ell residue-field lift
of every point. Source: ILO II 2.1.1
(blueprint: def-per-prime-to-ell-alteration-topology). -/
def IsPrimeToEllDecomposedEtaleFamily (ell : ℕ) {S : Scheme.{u}} [IsNoetherian S]
    {I : Type w} {T : Alt S} (U : I → Alt S) (f : ∀ i, U i ⟶ T) : Prop :=
  (∀ i, Etale (f i).hom.left) ∧
    ∀ t : T.obj.left, ∃ (i : I) (x : (U i).obj.left),
      (f i).hom.left x = t ∧ ((f i).hom.left.residueFieldMap x).hom.Finite ∧
        Nat.Coprime ((f i).hom.left.residueDegree x) ell

/-- Completely decomposed étale families lift every point with an isomorphism of residue
fields. Source: ILO II 2.1.1, the case `ell = ∞`
(blueprint: def-per-prime-to-ell-alteration-topology). -/
def IsCompletelyDecomposedEtaleFamily {S : Scheme.{u}} [IsNoetherian S]
    {I : Type w} {T : Alt S} (U : I → Alt S) (f : ∀ i, U i ⟶ T) : Prop :=
  (∀ i, Etale (f i).hom.left) ∧
    ∀ t : T.obj.left, ∃ (i : I) (x : (U i).obj.left),
      (f i).hom.left x = t ∧ IsIso ((f i).hom.left.residueFieldMap x)

/-- The prime-to-ell decomposed étale generators, expressed as presieves to include families
of every index size without choosing an index universe. Source: ILO II 2.1.1--2.1.2
(blueprint: def-per-prime-to-ell-alteration-topology). -/
def IsPrimeToEllDecomposedEtalePresieve (ell : ℕ) {S : Scheme.{u}} [IsNoetherian S]
    {T : Alt S} (R : Presieve T) : Prop :=
  (∀ (U : Alt S) (f : U ⟶ T), R f → Etale f.hom.left) ∧
    ∀ t : T.obj.left, ∃ (U : Alt S) (f : U ⟶ T) (x : U.obj.left),
      R f ∧ f.hom.left x = t ∧ (f.hom.left.residueFieldMap x).hom.Finite ∧
        Nat.Coprime (f.hom.left.residueDegree x) ell

/-- The least topology containing decomposed étale families and proper surjective maximally
prime-to-ell finite singleton families. Source: ILO II 2.3.1 and Remark 2.3.2
(blueprint: def-per-prime-to-ell-alteration-topology). -/
noncomputable def topology (S : Scheme.{u}) [IsNoetherian S]
    (ell : ℕ) [Fact ell.Prime] : GrothendieckTopology (Alt S) :=
  sInf {J | (∀ (T : Alt S) (R : Presieve T),
      IsPrimeToEllDecomposedEtalePresieve ell R → Sieve.generate R ∈ J T) ∧
    ∀ (T U : Alt S) (f : U ⟶ T),
      IsProper f.hom.left → Surjective f.hom.left →
        IsMaximallyPrimeToEllFinite ell f.hom.left →
          Sieve.generate (Presieve.singleton f) ∈ J T}

/-- A family is covering exactly when its generated sieve is covering; `Sieve.ofArrows`
consists of arrows factoring through a member. Source: ILO II 2.3.1
(blueprint: def-per-prime-to-ell-alteration-topology). -/
def IsCoveringFamily {S : Scheme.{u}} [IsNoetherian S] (ell : ℕ) [Fact ell.Prime]
    {I : Type w} {T : Alt S} (U : I → Alt S) (f : ∀ i, U i ⟶ T) : Prop :=
  Sieve.ofArrows U f ∈ topology S ell T

/-- Refinement chooses, for each member of the first family, a factorization through a member
of the second, all over the target. Source: ILO II §3 (standard forms of covering families)
(blueprint: def-per-prime-to-ell-alteration-topology). -/
def Refines {S : Scheme.{u}} [IsNoetherian S] {T : Alt S}
    {I : Type w} {J : Type w'} (A : I → Alt S) (a : ∀ i, A i ⟶ T)
    (B : J → Alt S) (b : ∀ j, B j ⟶ T) : Prop :=
  ∀ i : I, ∃ (j : J) (h : A i ⟶ B j), h ≫ b j = a i

end AlgebraicGeometry.PrimeToEllAlteration
