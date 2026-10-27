/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.Paper.RingOpenRefinement

/-! # Scalar naturality of the ordinary proper/open refinement word

Source: Stacks 0F7B and 0F7I; Zheng Section 5, Lemma 5.13 and Constructions 5.14--5.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
attribute [local instance] constructionInclusionShift
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Completed scalar extension preserves the normalized proper/open refinement word.
The input is an ordinary open-unit comparison, before any chosen exceptional operation.
Source: Zheng 5.13--5.15; Stacks 0F7B and 0F7I, coefficient mate pasting
(blueprint: lem-sf-ring-refinement-scalar-word).

Proof: use a finite integral basis for the extension of coefficient fields, with
its compatible reductions on the ramified en subsystem. On the coefficient-system
site the proper scalar map is the counit-tensor mate and the open scalar map is
normalized by the open unit. Pasting these squares with the normalized open
refinement gives the same open transpose in either order. The adjunction bijection
makes the system maps equal. Whisker by the outer proper image and paste the proper
compositor; its counit formula respects these same coefficient squares. Invert the
open refinement maps. Apply normalized cofinal realization to this equality of
actual system maps, using the primitive proper, open and generator-map identities.
This gives the ordinary scalar square with target the scalar extension of K.
The supplied open comparisons are the constructed ones: open full faithfulness
makes the unit invertible, and the transpose of an invertible comparison is then
invertible too. Its normalization forces refinementRestriction to be invertible.
Postcomposition with that restriction and the Hom adjunction are injective, so
two normalized components coincide.
Finally transport that vertex to K' by e: insert e.inv before the refinement and
e.hom after it, using naturality. Finite-Tor bounds ensure the normalized tower
realization applies. The argument uses only the relative proper/open refinement;
absolute separatedness of X or Y is not needed. No equality of system arrows is
inferred from equality at finite reductions. -/
theorem ring_refinement_scalar_word
  (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (hi : ∀ s : RingStage.{max u v} l, (s.coefficients l).pull (c.i ≫ r.hom) =
        proEtaleRingCompositeCoefficients c.i r.hom
          ((s.coefficients l).ring d.Z) ((s.coefficients l).ring c.Z)
          ((s.coefficients l).ring X)
          ((s.coefficients l).pull r.hom) ((s.coefficients l).pull c.i))
    (hg : ∀ s : RingStage.{max u v} l, (s.coefficients l).pull (r.hom ≫ d.g) =
        proEtaleRingCompositeCoefficients r.hom d.g
          ((s.coefficients l).ring Y) ((s.coefficients l).ring d.Z)
          ((s.coefficients l).ring c.Z)
          ((s.coefficients l).pull d.g) ((s.coefficients l).pull r.hom))
    (ε : ∀ s : RingStage.{max u v} l, RingStage.inclusion.{u, v} l Ω X s ⋙
          (PurCompactSupport.openExtension (s.coefficients l) d.i).mapDerivedCategory ≅
        RingStage.inclusion.{u, v} l Ω X s ⋙
          ((PurCompactSupport.openExtension (s.coefficients l) c.i).mapDerivedCategory ⋙
            PurCompactSupport.push (s.coefficients l) r.hom))
    (hε : ∀ (s : RingStage.{max u v} l) (K : C.{u, v} l Ω X (s.stage l)),
        (PurCompactSupport.openDerivedAdjunction (s.coefficients l) d.i).homEquiv _ _
            ((ε s).hom.app K) ≫
            PurCompactSupport.refinementRestriction (s.coefficients l) r (hi s)
              ((RingStage.inclusion.{u, v} l Ω X s).obj K) =
          (PurCompactSupport.openDerivedAdjunction (s.coefficients l) c.i).unit.app
            ((RingStage.inclusion.{u, v} l Ω X s).obj K))
    (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (K : C.{u, v} l Ω X (.integral E)) (K' : C.{u, v} l Ω X (.integral L))
    (e : (RingStage.inclusion.{u, v} l Ω X (.integral L)).obj K' ≅
      (pbcDerivedExtend ((PurCompactSupport.completedChange l E.carrier L.carrier i).map X)).obj
        ((RingStage.inclusion.{u, v} l Ω X (.integral E)).obj K)) :
    let a := PurCompactSupport.completedChange l E.carrier L.carrier i
    let Hc := PurCompactSupport.image ((RingStage.integral L).coefficients l) c
    let Hd := PurCompactSupport.image ((RingStage.integral L).coefficients l) d
    (pbcDerivedExtend (a.map Y)).map
        ((ringRefinementWord.{u, v} l Ω r (.integral E) (hg _) (ε _)).hom.app K) ≫
        (PurCompactSupport.comparison a d).app K.obj =
      (PurCompactSupport.comparison a c).app K.obj ≫ Hc.map e.inv ≫
        (ringRefinementWord.{u, v} l Ω r (.integral L) (hg _) (ε _)).hom.app K' ≫
        Hd.map e.hom := by sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
