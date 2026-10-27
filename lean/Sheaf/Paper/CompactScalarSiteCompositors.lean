/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.CompactScalarSiteWords

/-! # Normalized inverse-image compositors and their adjoint conjugates
Source: Stacks 0E46 and 0E47; blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-compositors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option linter.checkUnivs false
universe u v w z
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.CompactScalarSite

/-- Paste of two specified inverse-image identifications, with associators inserted.
Source: Stacks 0E46 and 0E47
(blueprint: def-pur-compact-scalar-site-compositors). -/
def pasteInverseIso {C₀ C₁ C₂ D₀ D₁ D₂ : Type w}
    [Category.{z} C₀] [Category.{z} C₁] [Category.{z} C₂]
    [Category.{z} D₀] [Category.{z} D₁] [Category.{z} D₂]
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {G₀₁ : D₀ ⥤ D₁} {G₁₂ : D₁ ⥤ D₂}
    {N₀ : C₀ ⥤ D₀} {N₁ : C₁ ⥤ D₁} {N₂ : C₂ ⥤ D₂}
    (a₀₁ : N₀ ⋙ G₀₁ ≅ F₀₁ ⋙ N₁) (a₁₂ : N₁ ⋙ G₁₂ ≅ F₁₂ ⋙ N₂) :
    N₀ ⋙ (G₀₁ ⋙ G₁₂) ≅ (F₀₁ ⋙ F₁₂) ⋙ N₂ :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight a₀₁ _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ a₁₂ ≪≫
    (Functor.associator _ _ _).symm

/-- A composition identification is the specified set comparison on all underlying
module sections. This pins down the ordinary map before localization.
Source: Stacks 03D2 and 0E46
(blueprint: def-pur-compact-scalar-site-compositors). -/
def NormalizedComposite {X Y Z : Presentation.{u, v}} {R : Type (max u v)} [CommRing R]
    {p : GeometricMorphism (Sheaf X.J (Type (max u v))) (Sheaf Y.J (Type (max u v)))}
    {q : GeometricMorphism (Sheaf Y.J (Type (max u v))) (Sheaf Z.J (Type (max u v)))}
    {r : GeometricMorphism (Sheaf X.J (Type (max u v))) (Sheaf Z.J (Type (max u v)))}
    (Lp : InverseModel X Y R p) (Lq : InverseModel Y Z R q) (Lr : InverseModel X Z R r)
    (s : r.inverse ≅ q.inverse ⋙ p.inverse)
    (c : Lr.lift.modules ≅ Lq.lift.modules ⋙ Lp.lift.modules) : Prop :=
  ∀ M : modules Z R,
    (underlying X R).map (c.hom.app M) ≫
        Lp.lift.moduleUnderlying.hom.app (Lq.lift.modules.obj M) ≫
        p.inverse.map (Lq.lift.moduleUnderlying.hom.app M) =
      Lr.lift.moduleUnderlying.hom.app M ≫ s.hom.app ((underlying Z R).obj M)

variable {A B : Type (max u v)} [CommRing A] [CommRing B] (φ : A →+* B)

/-- Composition in the two geometric diagrams. The set cube is the canonical
composition compatibility; the four module maps are fixed by this same set data.
Source: Stacks 0E46 and 0E47
(blueprint: def-pur-compact-scalar-site-compositors). -/
structure CompositionIdentification {X Y Z : Vertex.{u, v} φ}
    (p : InverseSquare φ X Y) (q : InverseSquare φ Y Z) (r : InverseSquare φ X Z) where
  sets : r.p.inverse ≅ q.p.inverse ⋙ p.p.inverse
  tildeSets : r.tildeP.inverse ≅ q.tildeP.inverse ⋙ p.tildeP.inverse
  cube : r.sets.hom ≫ Functor.whiskerRight sets.hom X.ν.inverse =
    Functor.whiskerLeft Z.ν.inverse tildeSets.hom ≫ (pasteInverseIso q.sets p.sets).hom
  A : r.LA.lift.modules ≅ q.LA.lift.modules ⋙ p.LA.lift.modules
  B : r.LB.lift.modules ≅ q.LB.lift.modules ⋙ p.LB.lift.modules
  tildeA : r.tildeLA.lift.modules ≅ q.tildeLA.lift.modules ⋙ p.tildeLA.lift.modules
  tildeB : r.tildeLB.lift.modules ≅ q.tildeLB.lift.modules ⋙ p.tildeLB.lift.modules
  normalizedA : NormalizedComposite p.LA q.LA r.LA sets A
  normalizedB : NormalizedComposite p.LB q.LB r.LB sets B
  tildeNormalizedA : NormalizedComposite p.tildeLA q.tildeLA r.tildeLA tildeSets tildeA
  tildeNormalizedB : NormalizedComposite p.tildeLB q.tildeLB r.tildeLB tildeSets tildeB

/-- A direct-image letter with both normalized derived right adjoints.
Source: Stacks 09T5 (blueprint: def-pur-compact-scalar-site-compositors). -/
structure DirectLetter (X Y : Vertex.{u, v} φ) where
  square : InverseSquare φ X Y
  RA : DirectModel square.LA
  RB : DirectModel square.LB
  tildeRA : DirectModel square.tildeLA
  tildeRB : DirectModel square.tildeLB

/-- The value of the direct letter, retaining its specified maps.
Source: Stacks 07A7 (blueprint: def-pur-compact-scalar-site-compositors). -/
def DirectLetter.value {X Y : Vertex.{u, v} φ} (p : DirectLetter φ X Y) : Value φ X Y :=
  directValue φ p.square p.RA p.RB p.tildeRA p.tildeRB

/-- Four actual isomorphisms of word values.
Source: Stacks 0E46 and 0E47 (blueprint: def-pur-compact-scalar-site-compositors). -/
structure IsoComparison {X Y : Vertex.{u, v} φ} (H H' : Value φ X Y) where
  A : H.FA ≅ H'.FA
  B : H.FB ≅ H'.FB
  tildeA : H.tildeFA ≅ H'.tildeFA
  tildeB : H.tildeFB ≅ H'.tildeFB

/-- The transformation underlying an isomorphism comparison.
Source: Stacks 0E46 (blueprint: def-pur-compact-scalar-site-compositors). -/
def IsoComparison.hom {X Y : Vertex.{u, v} φ} {H H' : Value φ X Y}
    (θ : IsoComparison φ H H') : Comparison φ H H' :=
  ⟨θ.A.hom, θ.B.hom, θ.tildeA.hom, θ.tildeB.hom⟩

/-- The direct compositor is the counit-compatible conjugate of the actual
exact inverse-image compositor, including the exact-functor descent compositor.
Source: Stacks 0E46 (blueprint: def-pur-compact-scalar-site-compositors). -/
def directCompositor {X Y Z : Vertex.{u, v} φ}
    (p : DirectLetter φ X Y) (q : DirectLetter φ Y Z) (r : DirectLetter φ X Z)
    (c : CompositionIdentification φ p.square q.square r.square) :
    IsoComparison φ (composeValue φ p.value q.value) r.value where
  A := conjugateIsoEquiv (q.RA.adj.comp p.RA.adj) r.RA.adj
    (Functor.mapDerivedCategoryNatIso c.A ≪≫ Functor.mapDerivedCategoryCompIso _ _)
  B := conjugateIsoEquiv (q.RB.adj.comp p.RB.adj) r.RB.adj
    (Functor.mapDerivedCategoryNatIso c.B ≪≫ Functor.mapDerivedCategoryCompIso _ _)
  tildeA := conjugateIsoEquiv (q.tildeRA.adj.comp p.tildeRA.adj) r.tildeRA.adj
    (Functor.mapDerivedCategoryNatIso c.tildeA ≪≫ Functor.mapDerivedCategoryCompIso _ _)
  tildeB := conjugateIsoEquiv (q.tildeRB.adj.comp p.tildeRB.adj) r.tildeRB.adj
    (Functor.mapDerivedCategoryNatIso c.tildeB ≪≫ Functor.mapDerivedCategoryCompIso _ _)

/-- The open compositor is the open-unit-compatible conjugate of the actual
restriction compositor, with the inverse directions fixed by the open adjunctions.
Source: Stacks 0E47 (blueprint: def-pur-compact-scalar-site-compositors). -/
def openCompositor {X Y Z : Vertex.{u, v} φ}
    (p : OpenSquare φ X Y) (q : OpenSquare φ Y Z) (r : OpenSquare φ X Z)
    (c : CompositionIdentification φ p.square q.square r.square) :
    IsoComparison φ (composeValue φ (openValue φ p) (openValue φ q)) (openValue φ r) where
  A := ((conjugateIsoEquiv (p.IA.adj.comp q.IA.adj) r.IA.adj).symm
    (Functor.mapDerivedCategoryNatIso c.A ≪≫
      Functor.mapDerivedCategoryCompIso _ _).symm).symm
  B := ((conjugateIsoEquiv (p.IB.adj.comp q.IB.adj) r.IB.adj).symm
    (Functor.mapDerivedCategoryNatIso c.B ≪≫
      Functor.mapDerivedCategoryCompIso _ _).symm).symm
  tildeA := ((conjugateIsoEquiv (p.tildeIA.adj.comp q.tildeIA.adj) r.tildeIA.adj).symm
    (Functor.mapDerivedCategoryNatIso c.tildeA ≪≫
      Functor.mapDerivedCategoryCompIso _ _).symm).symm
  tildeB := ((conjugateIsoEquiv (p.tildeIB.adj.comp q.tildeIB.adj) r.tildeIB.adj).symm
    (Functor.mapDerivedCategoryNatIso c.tildeB ≪≫
      Functor.mapDerivedCategoryCompIso _ _).symm).symm

end CategoryTheory.CompactScalarSite
