/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalCompositorData
import WeilConjectures.AlgebraicGeometry.ConstructibleLeftCompositorCoherence
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Exceptional composition from canonical compact-support composition -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
universe u v u' v'

section
variable {C : Type u} {D : Type v} [Category.{u'} C] [Category.{v'} D]
  {F₁ F₂ : C ⥤ D} {G₁ G₂ : D ⥤ C}
  (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂) (α : F₁ ≅ F₂)

private theorem mate_counit (L : D) :
    α.hom.app (G₁.obj L) ≫
      F₂.map ((conjugateIsoEquiv a₁ a₂ α.symm).hom.app L) ≫ a₂.counit.app L =
        a₁.counit.app L := by
  rw [conjugateIsoEquiv_apply_hom, Iso.symm_hom,
    conjugateEquiv_counit, Iso.hom_inv_id_app_assoc]

private theorem mate_hom (K : C) (L : D) (u : K ⟶ G₁.obj L) :
    u ≫ (conjugateIsoEquiv a₁ a₂ α.symm).hom.app L =
      a₂.homEquiv K L (α.inv.app K ≫ (a₁.homEquiv K L).symm u) := by
  apply (a₂.homEquiv K L).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc, conjugateIsoEquiv_apply_hom, Iso.symm_hom,
    conjugateEquiv_counit, ← Category.assoc, α.inv.naturality,
    Category.assoc, Adjunction.homEquiv_counit]

private theorem mate_unique (L : D) (t : G₁.obj L ⟶ G₂.obj L) :
    (α.hom.app (G₁.obj L) ≫ F₂.map t ≫ a₂.counit.app L = a₁.counit.app L) ↔
      t = (conjugateIsoEquiv a₁ a₂ α.symm).hom.app L := by
  constructor
  · intro ht
    apply (a₂.homEquiv (G₁.obj L) L).symm.injective
    simp only [Adjunction.homEquiv_counit]
    apply (cancel_epi (α.hom.app (G₁.obj L))).1
    exact ht.trans (mate_counit a₁ a₂ α L).symm
  · rintro rfl
    exact mate_counit a₁ a₂ α L
end

section Square
variable {C D E : Type*} [Category C] [Category D] [Category E]
  {F F' : C ⥤ D} {R R' : D ⥤ C}
  {G G' : D ⥤ E} {T T' : E ⥤ D}
  {H H' : C ⥤ E} {U U' : E ⥤ C}
  (a : F ⊣ R) (a' : F' ⊣ R') (b : G ⊣ T) (b' : G' ⊣ T')
  (c : H ⊣ U) (c' : H' ⊣ U')
  (af : F ≅ F') (ag : G ≅ G') (ah : H ≅ H')
  (α : F ⋙ G ≅ H) (α' : F' ⋙ G' ≅ H')

private theorem mate_refinement_square
    (h : α ≪≫ ah =
      Functor.isoWhiskerLeft F ag ≪≫ Functor.isoWhiskerRight af G' ≪≫ α') :
    Functor.isoWhiskerLeft T' (conjugateIsoEquiv a' a af) ≪≫
        Functor.isoWhiskerRight (conjugateIsoEquiv b' b ag) R ≪≫
        conjugateIsoEquiv (a.comp b) c α.symm =
      conjugateIsoEquiv (a'.comp b') c' α'.symm ≪≫ conjugateIsoEquiv c' c ah := by
  have he : α.symm ≪≫
      (Functor.isoWhiskerLeft F ag ≪≫ Functor.isoWhiskerRight af G') =
        ah ≪≫ α'.symm := by
    apply Iso.ext
    apply (cancel_epi α.hom).1
    apply (cancel_mono α'.hom).1
    simpa [Category.assoc] using congrArg Iso.hom h.symm
  have hc := congrArg (conjugateIsoEquiv (a'.comp b') c) he
  rw [conjugateIsoEquiv_trans (a'.comp b') (a.comp b) c,
    conjugateIsoEquiv_trans (a'.comp b') (a.comp b') (a.comp b),
    conjugateIsoEquiv_isoWhiskerRight a' a b',
    conjugateIsoEquiv_isoWhiskerLeft b' b a,
    conjugateIsoEquiv_trans (a'.comp b') c' c] at hc
  simpa only [Iso.trans_assoc] using hc
end Square

namespace WeilConjectures.ConstructibleExceptionalCompositor
open ConstructibleExceptionalCoefficients
variable {D : FiniteFieldDatum.{u}} (B : D.CoefficientDatum)

private theorem mate_properties {X Y Z : AlgebraicGeometry.Scheme.{u}}
    {s : Stage.{u} B.l}
    (A : Operation.{u, u} B.l B.Qbar X Y s)
    (G : Operation.{u, u} B.l B.Qbar Y Z s)
    (H : Operation.{u, u} B.l B.Qbar X Z s)
    (alpha : A.F ⋙ G.F ≅ H.F) (h : alpha.hom.CommShift ℤ) :
    MateProperties B A G H alpha := by
  let : A.adjunction.CommShift ℤ := ⟨A.unitShift, A.counitShift⟩
  let : G.adjunction.CommShift ℤ := ⟨G.unitShift, G.counitShift⟩
  let : H.adjunction.CommShift ℤ := ⟨H.unitShift, H.counitShift⟩
  let := h
  refine ⟨?_, ?_, ?_, h, ?_⟩
  · intro K L v
    exact mate_hom (A.adjunction.comp G.adjunction) H.adjunction alpha K L v
  · intro L
    simpa only [exceptionalIso, Adjunction.comp_counit_app] using
      mate_counit (A.adjunction.comp G.adjunction) H.adjunction alpha L
  · intro L t
    simpa only [exceptionalIso, Adjunction.comp_counit_app] using
      mate_unique (A.adjunction.comp G.adjunction) H.adjunction alpha L t
  · dsimp only [exceptionalIso]
    rw [conjugateIsoEquiv_apply_hom, Iso.symm_hom]
    infer_instance

private theorem refinement_conjugate
    {X Y : AlgebraicGeometry.Scheme.{u}} {s : Stage.{u} B.l}
    {A A' : Operation.{u, u} B.l B.Qbar X Y s}
    (r : RefinementComparison.{u, u} B.l B.Qbar A A') :
    conjugateIsoEquiv A'.adjunction A.adjunction r.left = r.right := by
  apply Iso.ext
  rw [conjugateIsoEquiv_apply_hom]
  exact conjugateEquiv_eq_of_unit A'.adjunction A.adjunction r.left.hom r.right.hom
    r.unit

section Refinement
variable {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
  [AlgebraicGeometry.IsSeparated f.hom.left]
  [AlgebraicGeometry.LocallyOfFiniteType f.hom.left]
  [AlgebraicGeometry.QuasiCompact f.hom.left]
  [AlgebraicGeometry.IsSeparated g.hom.left]
  [AlgebraicGeometry.LocallyOfFiniteType g.hom.left]
  [AlgebraicGeometry.QuasiCompact g.hom.left]
  (P : System.{u, u} B.l B.Qbar D B.different (f := f.hom.left))
  (Q : System.{u, u} B.l B.Qbar D B.different (f := g.hom.left))
  (R : System.{u, u} B.l B.Qbar D B.different (f := (f ≫ g).hom.left))
  {S : ∀ (E : FieldStage.{u} B.l) (n : ℕ+),
    SixFunctorOperationDatum D B E.carrier n n.pos}
  (A : LeftCompositors B f g P Q R S)

private theorem refinement_of_left
    (h : ∀ (cf df : Compactification f.hom.left)
      (rf : cf.Refinement df)
      (cg dg : Compactification g.hom.left)
      (rg : cg.Refinement dg)
      (cx dx : Compactification (f ≫ g).hom.left)
      (rx : cx.Refinement dx) (s : Stage.{u} B.l),
      A.alpha cf cg cx s ≪≫ (R.refinements.refinement rx s).left =
        Functor.isoWhiskerLeft (P.ring.operation cf s).F
          (Q.refinements.refinement rg s).left ≪≫
        Functor.isoWhiskerRight (P.refinements.refinement rf s).left
          (Q.ring.operation dg s).F ≪≫ A.alpha df dg dx s) :
    RefinementIndependent B f g P Q R A := by
  intro cf df rf cg dg rg cx dx rx s L
  have ht := mate_refinement_square
    (P.ring.operation cf s).adjunction (P.ring.operation df s).adjunction
    (Q.ring.operation cg s).adjunction (Q.ring.operation dg s).adjunction
    (R.ring.operation cx s).adjunction (R.ring.operation dx s).adjunction
    (P.refinements.refinement rf s).left (Q.refinements.refinement rg s).left
    (R.refinements.refinement rx s).left
    (A.alpha cf cg cx s) (A.alpha df dg dx s) (h cf df rf cg dg rg cx dx rx s)
  rw [refinement_conjugate B, refinement_conjugate B, refinement_conjugate B] at ht
  exact congrArg (fun e ↦ e.hom.app L) ht

end Refinement

/-- Canonical exceptional composition on the actual constructible finite-Tor categories
at every finite, integral, raw rational and common finite-field stage.
Source: blueprint main-20261015, Verdier-exchange proof Step 1
(blueprint: lem-sf-constructible-exceptional-compositor).

Proof:
1. Use the constructible exceptional-adjunction coefficient theorem for f, g and
   their composite, retaining its actual operations, shifts and refinement maps.
   The compactified-tower comparison theorem supplies the canonical left maps.
   Lift the finite ones through the full finite-Tor inclusions. The integral
   presentation equality gives exactly the completed integral maps. Rational
   transport and coherent-pair descent give the displayed field normalizations.
2. Compose the f and g adjunctions. Its Hom bijection is their successive Hom
   bijections and its counit is F_g(epsilon_f) followed by epsilon_g. Conjugate
   inverse alpha using this composite adjunction and the direct one. Mathlib's
   conjugateIsoEquiv gives the specified natural isomorphism exceptionalIso.
3. Its transpose equation is F_x(c) epsilon_x = alpha^{-1} epsilon_composite.
   Precompose with alpha to obtain the displayed pasted-counit equation. For
   any component t, cancel alpha and apply injectivity of the direct adjunction
   Hom bijection. This proves the stated componentwise uniqueness.
4. Apply that equation to u:K -> G_f G_g L. Naturality of inverse alpha rewrites
   its transpose as inverse alpha at K followed by the composite inverse
   transpose of u. Applying the direct Hom bijection gives precisely the chain.
5. The compactified-tower left maps commute with the specified refinements, and
   the right refinement maps preserve counits. Both sides of the refinement
   equation therefore have the same transpose; Step 3 makes them equal.
6. The finite structural-map shift theorem gives the shift of finite alpha.
   Integral realization-shift coherence applies to the actual strict words and
   their Roos normalizations. There is a common cohomological and Tor interval
   for the finite list of their intermediate finite-Tor objects. Rational
   transport and coherent-pair descent carry these equations to field stages.
   No faithfulness of finite evaluation is assumed.
7. The composite counit, inverse alpha and the direct unit all commute with
   the specified integer shifts. The explicit conjugation formula and the
   composition/whiskering shift theorem give the shift of exceptionalIso.
No exceptional adjoint on an unrestricted ambient category is used. -/
theorem constructibleExceptionalCompositor
    {D : FiniteFieldDatum.{u}} (B : D.CoefficientDatum)
    (S : ∀ (E : FieldStage.{u} B.l) (n : ℕ+),
      SixFunctorOperationDatum D B E.carrier n n.pos)
    {X Y Z : SixFunctorSpace D}
    [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom] [IsSeparated Z.obj.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left] :
    ∃ (P : System.{u, u} B.l B.Qbar D B.different (f := f.hom.left))
      (Q : System.{u, u} B.l B.Qbar D B.different (f := g.hom.left))
      (R : System.{u, u} B.l B.Qbar D B.different (f := (f ≫ g).hom.left))
      (A : LeftCompositors B f g P Q R S),
      (∀ (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
        (cx : Compactification (f ≫ g).hom.left) (s : Stage.{u} B.l),
        MateProperties B (P.ring.operation cf s) (Q.ring.operation cg s)
          (R.ring.operation cx s) (A.alpha cf cg cx s)) ∧
      RefinementIndependent B f g P Q R A := by
  obtain ⟨P, Q, R, A, hs, hr⟩ := constructibleLeftCompositorCoherence B S f g
  refine ⟨P, Q, R, A, ?_, refinement_of_left B f g P Q R A ?_⟩
  · intro cf cg cx s
    exact mate_properties B _ _ _ (A.alpha cf cg cx s) (hs cf cg cx s)
  · intro cf df rf cg dg rg cx dx rx s
    exact Iso.ext (hr cf df rf cg dg rg cx dx rx s)

end WeilConjectures.ConstructibleExceptionalCompositor
