/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RhoSectionModuleData
public import WeilConjectures.AlgebraicGeometry.Modules.Coherent
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Associated character line bundles and regular semi-invariants

Source: Milne, Algebraic Groups (2017), Section 18c, pp.389--390,
Definition 22.21, p.468, and proof of Theorem 22.48, p.479.
(blueprint: def-sfb-associated-character-line-bundle)

The quotient is specified by an fpqc atlas and its exact orbit relation on all
scheme-valued points. The sheaf of sections is specified by its representing
property on every scheme over the base, with pullback naturality. The chosen
trivialization and the geometric left actions are part of the presentation.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped MonObj

namespace AlgebraicGeometry.AssociatedCharacterLineBundle

/-- The affine-line point with the specified regular coordinate, by Spec--Γ adjunction.
Source: Milne, Section 18c, p.390.
(blueprint: def-sfb-associated-character-line-bundle) -/
def linePoint {F : Type u} [Field F] (S : Over (Spec (.of F))) (z : RhoSection.Coordinate S) :
    S ⟶ StandardGroupSchemes.additive F :=
  (algΓAlgSpecAdjunction (.of F)).homEquiv S (op (CommAlgCat.of F (Polynomial F)))
    (CommAlgCat.ofHom (Polynomial.aeval z)).op

/-- The scalar χ(b)⁻¹, evaluated by the Laurent coordinate after group inversion.
This avoids an inverse operation on arbitrary nonunits in a test algebra.
Source: Milne, Section 18c, p.390, displayed right action.
(blueprint: def-sfb-associated-character-line-bundle) -/
def inverseCharacter {F : Type u} [Field F] (B : Grp (Over (Spec (.of F))))
    (χ : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    {S : Over (Spec (.of F))} (b : S ⟶ B.X) : RhoSection.Coordinate S :=
  ((b ≫ χ.hom.hom)⁻¹).left.appTop
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv (LaurentPolynomial.T 1))

/-- Global sections of an O_Q-module as an F-module, by the structural scalar map.
Source: Milne, Theorem 22.48, p.479.
(blueprint: def-sfb-associated-character-line-bundle) -/
def sections {F : Type u} [Field F] (Q : Over (Spec (.of F))) (L : Q.left.Modules) :
    ModuleCat F :=
  (ModuleCat.restrictScalars
    (((Scheme.ΓSpecIso (.of F)).inv ≫ Q.hom.appTop).hom)).obj
      (ModuleCat.of Γ(Q.left, ⊤) Γ(L, ⊤))

/-- Pull a global section back and write its coordinate in the specified trivialization.
Source: Milne, proof of Theorem 22.48, p.479.
(blueprint: def-sfb-associated-character-line-bundle) -/
def pullbackCoordinate {F : Type u} [Field F]
    {G Q : Over (Spec (.of F))} (π : G ⟶ Q) (L : Q.left.Modules)
    (θ : (Scheme.Modules.pullback π.left).obj L ≅ Scheme.Modules.unit G.left)
    (σ : sections Q L) : RhoSection.Coordinate G :=
  θ.hom.app ⊤
    (((Scheme.Modules.pullback π.left).obj L).presheaf.map
      (homOfLE π.left.preimage_top.ge).op (Scheme.Modules.pullbackSection π.left σ))

/-- The specified trivialization after pullback to any point of G.
Source: Milne, Section 18c, p.390, and proof of Theorem 22.48, p.479.
(blueprint: def-sfb-associated-character-line-bundle) -/
def trivializationAt {F : Type u} [Field F]
    {G Q : Over (Spec (.of F))} (π : G ⟶ Q) (L : Q.left.Modules)
    (θ : (Scheme.Modules.pullback π.left).obj L ≅ Scheme.Modules.unit G.left)
    {S : Over (Spec (.of F))} (g : S ⟶ G) :
    (Scheme.Modules.pullback (g ≫ π).left).obj L ≅ Scheme.Modules.unit S.left :=
  ((Scheme.Modules.pullbackComp g.left π.left).app L).symm ≪≫
    (Scheme.Modules.pullback g.left).mapIso θ ≪≫ Scheme.Modules.pullbackObjUnitIso g.left

/-- Pullback of a section on the whole scheme, including the preimage-top transport.
Source: Milne, Section 18c, p.389, descent of line bundles.
(blueprint: def-sfb-associated-character-line-bundle) -/
def pullTopSection {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) (σ : Γ(L, ⊤)) :
    Γ((Scheme.Modules.pullback f).obj L, ⊤) :=
  ((Scheme.Modules.pullback f).obj L).presheaf.map (homOfLE f.preimage_top.ge).op
    (Scheme.Modules.pullbackSection f σ)

/-- Pullback of a section with the canonical composition isomorphism.
Source: Milne, Section 18c, p.389, descent of line bundles.
(blueprint: def-sfb-associated-character-line-bundle) -/
def pullSection {F : Type u} [Field F]
    {Q S R : Over (Spec (.of F))} (f : R ⟶ S) (x : S ⟶ Q) (L : Q.left.Modules)
    (σ : Γ((Scheme.Modules.pullback x.left).obj L, ⊤)) :
    Γ((Scheme.Modules.pullback (f ≫ x).left).obj L, ⊤) :=
  ((Scheme.Modules.pullbackComp f.left x.left).hom.app L).app ⊤
    (pullTopSection f.left ((Scheme.Modules.pullback x.left).obj L) σ)

/-- A presentation of the associated homogeneous line bundle for a character χ.
The map q is an fpqc atlas with exactly the relation (g,z)b = (gb,χ(b)⁻¹z).
The module L is its sheaf of sections, specified on all schemes by a natural
representing equivalence. Its pullback trivialization sends the coordinate z to
[g,z]. The left actions are geometric morphisms and send [g,z] to [sg,z], so they
are fibrewise linear with respect to that sheaf of sections. Invertibility and
coherence are asserted by the existence theorem, rather than assumed here.
Source: Milne, Section 18c, pp.389--390, and proof of Theorem 22.48, p.479.
(blueprint: def-sfb-associated-character-line-bundle) -/
structure Presentation {F : Type u} [Field F]
    (G B : Grp (Over (Spec (.of F)))) (iB : B ⟶ G)
    (Q : Over (Spec (.of F))) (π : G.X ⟶ Q)
    (χ : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) where
  /-- The sheaf of sections. -/
  L : Q.left.Modules
  /-- Its specified trivialization on G. -/
  trivialization : (Scheme.Modules.pullback π.left).obj L ≅ Scheme.Modules.unit G.X.left
  /-- The geometric total space. -/
  V : Over (Spec (.of F))
  /-- Bundle projection. -/
  projection : V ⟶ Q
  /-- Quotient map from G × A¹. -/
  quotientMap : G.X ⊗ StandardGroupSchemes.additive F ⟶ V
  flat_quotientMap : Flat quotientMap.left
  surjective_quotientMap : Surjective quotientMap.left
  quasiCompact_quotientMap : QuasiCompact quotientMap.left
  quotientMap_over : quotientMap ≫ projection = fst G.X (StandardGroupSchemes.additive F) ≫ π
  /-- The exact orbit relation, including on nonreduced test schemes. -/
  quotient_relation : ∀ (S : Over (Spec (.of F))) (g₁ g₂ : S ⟶ G.X)
    (z₁ z₂ : RhoSection.Coordinate S),
    lift g₁ (linePoint S z₁) ≫ quotientMap = lift g₂ (linePoint S z₂) ≫ quotientMap ↔
      ∃ b : S ⟶ B.X, g₂ = g₁ * (b ≫ iB.hom.hom) ∧ z₂ = inverseCharacter B χ b * z₁
  /-- L represents the sections of the total space on every base scheme. -/
  sectionRepresentation : ∀ (S : Over (Spec (.of F))) (x : S ⟶ Q),
    Γ((Scheme.Modules.pullback x.left).obj L, ⊤) ≃
      {s : S ⟶ V // s ≫ projection = x}
  /-- The representation is natural under arbitrary base change. -/
  sectionRepresentation_natural : ∀ (S R : Over (Spec (.of F))) (f : R ⟶ S)
    (x : S ⟶ Q) (σ : Γ((Scheme.Modules.pullback x.left).obj L, ⊤)),
    (sectionRepresentation R (f ≫ x) (pullSection f x L σ)).val =
      f ≫ (sectionRepresentation S x σ).val
  /-- The given trivialization is the one furnished by the quotient atlas. -/
  sectionRepresentation_coordinate : ∀ (S : Over (Spec (.of F))) (g : S ⟶ G.X)
    (z : RhoSection.Coordinate S),
    (sectionRepresentation S (g ≫ π)
      ((trivializationAt π L trivialization g).inv.app ⊤ z)).val =
      lift g (linePoint S z) ≫ quotientMap
  /-- The natural left G-action on the flag quotient. -/
  baseAction : ModObj G.X Q
  /-- Its lift to the total space. -/
  totalAction : ModObj G.X V
  /-- The bundle projection is equivariant. -/
  projection_equivariant : totalAction.smul ≫ projection =
    (𝟙 G.X ⊗ₘ projection) ≫ baseAction.smul
  /-- The base action is induced by left multiplication on G. -/
  baseAction_coordinate : ∀ (S : Over (Spec (.of F))) (s g : S ⟶ G.X),
    lift s (g ≫ π) ≫ baseAction.smul = (s * g) ≫ π
  /-- The total action is induced by (s,g,z) ↦ (sg,z).
  Together with sectionRepresentation_coordinate this specifies the natural
  action on sections, whose regular-function formula is f(s⁻¹g). -/
  totalAction_coordinate : ∀ (S : Over (Spec (.of F))) (s g : S ⟶ G.X)
    (z : RhoSection.Coordinate S),
    lift s (lift g (linePoint S z) ≫ quotientMap) ≫ totalAction.smul =
      lift (s * g) (linePoint S z) ≫ quotientMap

end AlgebraicGeometry.AssociatedCharacterLineBundle
