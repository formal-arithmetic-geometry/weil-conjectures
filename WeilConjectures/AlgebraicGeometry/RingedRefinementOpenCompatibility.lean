/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedRefinementData

/-! # Scalar compatibility of normalized ringed open comparisons

This is the scalar part of coefficient supplement Steps 5--6.  It is independent of
constructing the open-comparison object itself.
(blueprint: new-ringed-refinement-open-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization
namespace SheafOfModules.RingedRefinement

attribute [local irreducible] Calculus.openAdjunction Calculus.shriek
  AlgebraicGeometry.Scheme.ProjectionRestriction.Operation.left
  Spatial.square Spatial.openFactor Spatial.sectionPull


/-- The four normalized constituent equations of scalar-compatible open refinement.
Source: coefficient supplement Steps 1, 5--7; Stacks 03EL, 07A6 and 0D6D.

Proof: identify the supplied geometric/scalar comparisons with the normalized
balanced comparison on flat-term K-flat representatives, using the representative
counit equations and universal localization. The sectionwise identity equations
fix the ordinary restriction squares and the geometric compositors. Their derived
scalar comparisons therefore preserve composition and identities. Transpose the
base-change equation under the open adjunction: both sides become the same paste
of the open unit and that scalar composition equation. For the projector equation,
restrict to the distinguished clopen and its complement. The first restriction is
the defining scalar/open unit equation; the other restriction is zero. Binary
clopen decomposition detects equality on the whole derived category. For the
section equation apply the scalar composition and identity laws to s followed by
q. For the open-factor equation transpose under the composite open adjunction;
the composite-unit formula and the scalar composition law identify both sides.
All localizations are of the whole ordinary or vertical module category, so these
arguments impose neither flatness of the coefficient map nor boundedness of input.
(blueprint: new-ringed-refinement-open-compatibility).
-/
theorem ringedRefinementOpenFactorCompatibility {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} (o : Calculus c) (p : Spatial o)
    (sc : ScalarComparisons o) (e : OpenComparisons p)
    {X Y Z : Over T} {u : Y ⟶ Z} {j₁ : X ⟶ Y} {j₂ : X ⟶ Z}
    [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    (d : Shape u j₁ j₂) {A B : Rings m T} (a : A ⟶ B) (M : category c X A) :
    ((sc.pull u a).hom.app ((o.shriek j₂ A).obj M) ≫
          (o.scalar Y a).T.map ((e.beta d.b d.q u j₂ d.pullback A).hom.app M) ≫
          (sc.delta d.b a).hom.app ((o.operation d.q A).left.obj M) ≫
          (o.shriek d.b B).map ((sc.pull d.q a).inv.app M) =
        (o.operation u B).left.map ((sc.delta j₂ a).hom.app M) ≫
          (e.beta d.b d.q u j₂ d.pullback B).hom.app ((o.scalar X a).T.obj M)) ∧
    (∀ N : category c d.V A,
      (o.scalar d.V a).T.map ((e.pi d.s d.clopen A).app N) ≫
          (sc.delta d.s a).hom.app ((o.operation d.s A).left.obj N) =
        (e.pi d.s d.clopen B).app ((o.scalar d.V a).T.obj N) ≫
          (o.shriek d.s B).map ((sc.pull d.s a).hom.app N)) ∧
    ((sc.pull d.s a).inv.app ((o.operation d.q A).left.obj M) ≫
          (o.operation d.s B).left.map ((sc.pull d.q a).inv.app M) ≫
          (p.sectionPull d B).hom.app ((o.scalar X a).T.obj M) =
        (o.scalar X a).T.map ((p.sectionPull d A).hom.app M)) ∧
    (∀ N : category c X A,
      (o.scalar Y a).T.map ((p.openFactor d.s d.b j₁ d.openFactor A).hom.app N) ≫
          (sc.delta j₁ a).hom.app N =
        (sc.delta d.b a).hom.app ((o.shriek d.s A).obj N) ≫
          (o.shriek d.b B).map ((sc.delta d.s a).hom.app N) ≫
          (p.openFactor d.s d.b j₁ d.openFactor B).hom.app ((o.scalar X a).T.obj N)) := by
  sorry

end SheafOfModules.RingedRefinement
