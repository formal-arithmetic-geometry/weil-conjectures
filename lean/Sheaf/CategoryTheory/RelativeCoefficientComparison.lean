/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.CategoryTheory.RelativeCyclicTotal



/-! # RelativeCoefficientComparison

Source: main-20261015, six-functors direct-images proof, paragraph (3),
agent-formulated relative rank-one input (exact combined reference wanted).
(blueprint: def-sfb-relative-coefficient-comparisons)

## Main definitions and statements

The primary declaration is `HasCoefficientComparison`.
The accompanying definitions fix the canonical maps, coordinates and normalization equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar
open Profinite.CondensedAction (inflate ProductInvariants)
namespace CategoryTheory.RelativeCyclic
variable (A : CondensedBar.Ring.{u}) (G J : Type u)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {A' : CondensedBar.Ring.{u}}
variable {J}
variable {A G}

/-- Coefficient restriction for relative invariants. The underived map is fixed by the
actual section-module inclusions, and the derived map by the computation-unit equation.
This is a specification of the canonical comparison, not an arbitrary isomorphism.
Source: paragraph (3), steps 13--14
(blueprint: def-sfb-relative-coefficient-comparisons). -/
def HasCoefficientComparison (a : A ⟶ A') (G J : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group J] [TopologicalSpace J] [IsTopologicalGroup J] : Prop :=
  ∃ underived : (CondensedDerivedRestriction.scalarAction (G := G × J) a).functor ⋙
      (invariants A G J).functor ≅
    (invariants A' G J).functor ⋙ (CondensedDerivedRestriction.scalarAction (G := G) a).functor,
    (∀ N,
    (underived.hom.app N).val ≫
        (CondensedDerivedRestriction.scalarAction a).underlying.hom.app
          ((invariants A' G J).functor.obj N) ≫
        (Mod.comap a.hom.hom).map ((invariants A' G J).inclusion.app N) =
      (invariants A G J).inclusion.app
          ((CondensedDerivedRestriction.scalarAction a).functor.obj N) ≫
        (CondensedDerivedRestriction.scalarAction a).underlying.hom.app N) ∧
    ∃ iso : CondensedDerivedRestriction.scalarDerived a (G × J) ⋙ derived A G J ≅
    derived A' G J ⋙ CondensedDerivedRestriction.scalarDerived a G,
      (∀ N : CochainComplex (Equivariant A' (G × J)) ℤ,
    (unit A G J)
        (((CondensedDerivedRestriction.scalarAction a).functor.mapHomologicalComplex
          (.up ℤ)).obj N) ≫
      (derived A G J).map
        ((CondensedDerivedRestriction.scalarAction a).functor.mapDerivedCategoryFactors.inv.app N) ≫
      iso.hom.app (DerivedCategory.Q.obj N) =
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex underived (.up ℤ)).hom.app N) ≫
      (CondensedDerivedRestriction.scalarAction a).functor.mapDerivedCategoryFactors.inv.app
        (((invariants A' G J).functor.mapHomologicalComplex (.up ℤ)).obj N) ≫
      (CondensedDerivedRestriction.scalarDerived a G).map
        ((unit A' G J) N)) ∧ NatTrans.CommShift iso.hom ℤ

/-- Relative coefficient maps exist for every ring map, without a flatness hypothesis.
Source: paragraph (3), step 13
(blueprint: def-sfb-relative-coefficient-comparisons).
Proof: scalar restriction is direct image along the identity ringed topos. The commuting
scalar/projection square and normalized derived-pushforward composition give the unique
comparison with the displayed derived-unit equation. Shift compatibility follows from
the derived scalar-extension adjunction, without assuming restriction preserves injectives. -/
theorem coefficientComparison (a : A ⟶ A') :
    HasCoefficientComparison a G J := by
  sorry

/-- The invariant-inclusion-normalized underived scalar comparison.
Source: paragraph (3) (blueprint: def-sfb-relative-coefficient-comparisons). -/
def HasCoefficientComparison.underived {a : A ⟶ A'} (C : HasCoefficientComparison a G J) :
    (CondensedDerivedRestriction.scalarAction (G := G × J) a).functor ⋙
      (invariants A G J).functor ≅
    (invariants A' G J).functor ⋙
      (CondensedDerivedRestriction.scalarAction (G := G) a).functor := Classical.choose C

/-- The derived scalar comparison fixed by its all-complex computation-unit equation.
Source: paragraph (3) (blueprint: def-sfb-relative-coefficient-comparisons). -/
def HasCoefficientComparison.iso {a : A ⟶ A'} (C : HasCoefficientComparison a G J) :
    CondensedDerivedRestriction.scalarDerived a (G × J) ⋙ derived A G J ≅
    derived A' G J ⋙ CondensedDerivedRestriction.scalarDerived a G :=
  Classical.choose (Classical.choose_spec C).2

/-- Compose the ordinary derived map with the normalized scalar comparison.
Source: paragraph (3) (blueprint: def-sfb-relative-coefficient-comparisons). -/
def coefficientMap (a : A ⟶ A')
    {N : DerivedCategory.{u + 1} (Equivariant A (G × J))}
    {N' : DerivedCategory.{u + 1} (Equivariant A' (G × J))}
    (f : N ⟶ (CondensedDerivedRestriction.scalarDerived a (G × J)).obj N') :
    (derived A G J).obj N ⟶
      (CondensedDerivedRestriction.scalarDerived a G).obj ((derived A' G J).obj N') :=
  (derived A G J).map f ≫ (coefficientComparison a).iso.hom.app N'

/-- Restriction and arbitrary coefficient maps commute before taking cohomology.
Source: paragraph (3), step 13
(blueprint: def-sfb-relative-coefficient-comparisons).
Proof: transpose both composites through the canonical derived projection adjunctions.
The two transposes are restriction of the H-counit followed by restriction of f. Mate
pasting identifies the arrows, and the canonical shifts identify their triangle boundaries. -/
theorem coefficientBeta (a : A ⟶ A') (v : J →ₜ* H)
    {N : DerivedCategory.{u + 1} (Equivariant A (G × H))}
    {N' : DerivedCategory.{u + 1} (Equivariant A' (G × H))}
    (f : N ⟶ (CondensedDerivedRestriction.scalarDerived a (G × H)).obj N') :
    (beta (A := A) (G := G) v).app N ≫
        coefficientMap a
          ((inflate (productMap (G := G) v)).mapDerivedCategory.map f ≫
            (CondensedDerivedRestriction.scalarGroupDerived a (productMap (G := G) v)).hom.app N') =
      coefficientMap a f ≫ (CondensedDerivedRestriction.scalarDerived a G).map
        ((beta (A := A') (G := G) v).app N') := by
  sorry





/-- Additive scalar restriction preserves the actual binary biproducts.
Source: paragraph (3) (blueprint: def-sfb-relative-coefficient-comparisons). -/
instance scalarBinaryBiproducts (a : A ⟶ A') :
    PreservesBinaryBiproducts (CondensedDerivedRestriction.scalarAction (G := G) a).functor :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- Scalar restriction of the explicit total is the termwise total, with its comparison
fixed by the two coordinates and the recorded scalar/group restriction comparisons.
Source: paragraph (3), step 14
(blueprint: def-sfb-relative-coefficient-comparisons).
Proof: restrict each of the two columns. The generator and d_N are unchanged on underlying
modules, so the coordinate maps intertwine both differentials with their stated signs.
The biproduct universal property gives uniqueness in every degree and naturality. -/
theorem coefficientTotalExist (a : A ⟶ A') (K : TotalModel A G) (K' : TotalModel A' G)
    (N : CochainComplex (Equivariant A' (G × Z.{u})) ℤ) :
    ∃! k : K.functor.obj
        (((CondensedDerivedRestriction.scalarAction (G := G × Z) a).functor.mapHomologicalComplex
          (.up ℤ)).obj N) ≅
      ((CondensedDerivedRestriction.scalarAction (G := G) a).functor.mapHomologicalComplex
        (.up ℤ)).obj (K'.functor.obj N),
      ∀ n : ℤ, k.hom.f n ≫
          (CondensedDerivedRestriction.scalarAction (G := G) a).functor.map
            (K'.coordinates N n).hom ≫
          ((CondensedDerivedRestriction.scalarAction (G := G) a).functor.mapBiprod
            ((retainResidual A' G Z).obj (N.X n))
            ((retainResidual A' G Z).obj (N.X (n - 1)))).hom =
        (K.coordinates
          (((CondensedDerivedRestriction.scalarAction (G := G × Z) a).functor.mapHomologicalComplex
            (.up ℤ)).obj N) n).hom ≫
          biprod.map
            ((CondensedDerivedRestriction.scalarGroup a
              (ContinuousMonoidHom.inl G Z)).hom.app (N.X n))
            ((CondensedDerivedRestriction.scalarGroup a
              (ContinuousMonoidHom.inl G Z)).hom.app (N.X (n - 1))) := by
  sorry

/-- The uniquely coordinate-normalized scalar comparison of cyclic totals.
Source: paragraph (3) (blueprint: def-sfb-relative-coefficient-comparisons). -/
def coefficientTotal (a : A ⟶ A') (K : TotalModel A G) (K' : TotalModel A' G)
    (N : CochainComplex (Equivariant A' (G × Z.{u})) ℤ) :
    K.functor.obj
        (((CondensedDerivedRestriction.scalarAction (G := G × Z) a).functor.mapHomologicalComplex
          (.up ℤ)).obj N) ≅
      ((CondensedDerivedRestriction.scalarAction (G := G) a).functor.mapHomologicalComplex
        (.up ℤ)).obj (K'.functor.obj N) :=
  Classical.choose (coefficientTotalExist a K K' N)

/-- The cyclic derived isomorphism is natural under arbitrary coefficient restriction,
without assuming that a restricted injective is injective.
Source: paragraph (3), step 14
(blueprint: def-sfb-relative-coefficient-comparisons).
Proof: take a bounded-below equivariant injective resolution over A'. Every augmented
cyclic row is a quasi-isomorphism. Exact restriction preserves those rows and the two
columns, so the same is true over A. The derived-mate model equation for the scalar square
identifies its unit on this common acyclic model. The two equations theta alpha = Qb
then give this square; naturality handles every coefficient map. The scalar comparison
commutes with canonical shifts, so the square respects the triangle boundaries. -/
theorem coefficientLambda (a : A ⟶ A') {K : TotalModel A G} {K' : TotalModel A' G}
   
    (C : HasComparison A G K) (C' : HasComparison A' G K')
    (N : CochainComplex.Plus (Equivariant A' (G × Z.{u}))) :
    (lambda A G C
        ((CondensedDerivedRestriction.scalarAction (G := G × Z) a).functor.mapCochainComplexPlus.obj
          N)).hom ≫
      (derived A G Z).map
        ((CondensedDerivedRestriction.scalarAction (G := G × Z)
          a).functor.mapDerivedCategoryFactors.inv.app N.obj) ≫
      (coefficientComparison (G := G) (J := Z) a).iso.hom.app (DerivedCategory.Q.obj N.obj) =
    DerivedCategory.Q.map (coefficientTotal a K K' N.obj).hom ≫
      (CondensedDerivedRestriction.scalarAction (G := G)
        a).functor.mapDerivedCategoryFactors.inv.app (K'.functor.obj N.obj) ≫
      (CondensedDerivedRestriction.scalarDerived a G).map (lambda A' G C' N).hom := by
  sorry


end CategoryTheory.RelativeCyclic
