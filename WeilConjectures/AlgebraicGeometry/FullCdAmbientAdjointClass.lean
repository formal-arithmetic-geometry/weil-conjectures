/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleOriginAdjointClass
public import WeilConjectures.AlgebraicGeometry.SfClassFullCohomologicalDimension

/-!
# FullCD and exceptional adjoints on the bounded-below comparison class

Source: Weil blueprint, `thm-sf-ambient-adjoint-class.md`, clauses 1--3, and the
proper-part specialization in `cor-exc-base-change-open-immersion-general.proof.md`
(blueprint: lem-sp-fullcd-ambient-adjoint).

The coefficient level is the stated positive integer `n`. The scalar `ULift` is the
recorded fixed-module size convention, with no change to the coefficient ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open AlgebraicGeometry Scheme

/--
The proper part satisfies FullCD on all etale-origin sheaves. Its ordinary etale
right adjoint, transported by comparison, gives natural Hom bijections on the
bounded-below comparison class. The given compactification has the same relative
adjunction, normalized on etale representatives, with coherent canonical comparisons.

Source: Weil blueprint, `thm-sf-ambient-adjoint-class.md`, clauses 1--3; proper-part
specialization in `cor-exc-base-change-open-immersion-general.proof.md`, final paragraph
(blueprint: lem-sp-fullcd-ambient-adjoint).

Proof: apply thm-sf-fullcd-class to the proper part `c.g`. Both schemes are of finite
type over the fixed algebraically closed field, the coefficient level is positive,
and the residue characteristic is invertible. The dimension bound gives vanishing
above `2*d`, uniformly after every pro-etale base change for restrictions of every
original etale-origin sheaf, including the empty-source case.
Apply thm-sf-ambient-adjoint-class to `c.g` and its identity-open compactification.
Extension by zero along the identity is canonically the identity, so the two left
functors identify with the ordinary etale and pro-etale derived direct images.
Transport the etale adjunction and the natural class Hom bijections along these
identifications. This gives `Gp`, the displayed right composite, its bounded-below
preservation, and both naturality equations.
Finally apply thm-sf-ambient-adjoint-class to `f` and `c`. The normalized datum gives
its etale adjunction, bounded-below preservation, and Hom equivalences. The input
property is the essential image of bounded-below etale complexes; hence the Hom
equivalence depends only on the input object, independently of any retained witness.
The normalization identifies the comparisons with the canonical etale comparisons
on every representative. Their identity and cocycle laws, and their compatibility
with the transported Hom chain, give the remaining fields. -/
theorem fullCDAmbientAdjointClass
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of D.k)) (aY : Y ⟶ Spec (.of D.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hf : f ≫ aY = aX) (c : Compactification f) (d : ℕ)
    (_hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)) :
    let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
    letI : Finite (Padic.coefficientExtensionRing l E n) :=
      Padic.finite_coefficientExtensionRing l E n hn
    sfClassFullCohomologicalDimension c.g (Padic.coefficientExtensionRing l E n)
        (2 * d) ∧
      (∃ Gp :
          DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
            DerivedCategory (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)),
        ∃ _adjp : (Etale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor ⊣ Gp,
          (∀ (L : DerivedCategory
                (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)))
              (_hL : DerivedCategory.TStructure.t.plus L),
            DerivedCategory.TStructure.t.plus
              ((R(ν_*(Y)[ModuleCat.{u + 1} A]) ⋙ Gp ⋙
                D(ν^*(c.Z)[ModuleCat.{u + 1} A])).obj L)) ∧
          ∃ e : ∀ (H : DerivedCategory
                (Sheaf (ProEt.topology c.Z) (ModuleCat.{u + 1} A)))
              (_hH : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) c.Z H)
              (L : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)))
              (_hL : DerivedCategory.TStructure.t.plus L),
            (((lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.obj H) ⟶ L) ≃
              (H ⟶ (R(ν_*(Y)[ModuleCat.{u + 1} A]) ⋙ Gp ⋙
                D(ν^*(c.Z)[ModuleCat.{u + 1} A])).obj L),
            (∀ (H H' : DerivedCategory (Sheaf (Scheme.ProEt.topology c.Z)
                (ModuleCat.{u + 1} A)))
                (hH : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) c.Z H)
                (hH' : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) c.Z H')
                (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
                  (ModuleCat.{u + 1} A)))
                (hL : DerivedCategory.TStructure.t.plus L) (a : H ⟶ H')
                (b : (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.obj H' ⟶ L),
              e H hH L hL
                  ((lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map a ≫ b) =
                a ≫ e H' hH' L hL b) ∧
            ∀ (H : DerivedCategory (Sheaf (Scheme.ProEt.topology c.Z)
                (ModuleCat.{u + 1} A)))
                (hH : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) c.Z H)
                (L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
                  (ModuleCat.{u + 1} A)))
                (hL : DerivedCategory.TStructure.t.plus L)
                (hL' : DerivedCategory.TStructure.t.plus L')
                (a : (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.obj H ⟶ L)
                (b : L ⟶ L'),
              e H hH L' hL' (a ≫ b) = e H hH L hL a ≫
                (R(ν_*(Y)[ModuleCat.{u + 1} A]) ⋙ Gp ⋙
                  D(ν^*(c.Z)[ModuleCat.{u + 1} A])).map b) ∧
      (∃ Gf :
          DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
            DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
        ∃ adjf : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ Gf,
          Nonempty (ComparisonClassAdjunction A f c Gf adjf
            (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X)
            DerivedCategory.TStructure.t.plus)) := by
  sorry

end AlgebraicGeometry.ProEtale
