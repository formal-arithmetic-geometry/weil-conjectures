/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.CategoryTheory.PresheafBarResolution
public import Sheaf.CategoryTheory.DerivedColimitBar
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.DerivedCategory.RepresentableSumShriekAcyclic
import Sheaf.CategoryTheory.ContinuousCocontinuousDerivedShriek
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! # Ordinary Kan image of the presheaf bar resolution

Source: Stacks Project, Cohomology on Sites, Tags 08PG, 08PH and 08PK,
comma-chain reindexing, faces and restrictions
(blueprint: lem-trf-shriek-bar-comma-reindexing).

The bar complexes are the recorded dependency models, with their specified coordinates.
All maps below are normalized on generators. No complex or map is selected from the
postponed existence theorem. Singleton identity coverings give the bottom topology,
so the module sheaves in the statement are precisely these module presheaves.
-/

@[expose] public noncomputable section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.PresheafBar

variable {E D : Type u} [SmallCategory E] [SmallCategory D]
  {R : Type u} [CommRing R]

/-- The ordinary Kan generator `(a : V → f(U_n), c, x)`. The identity generator
of the actual presheaf bar term is mapped by the canonical Kan unit and then restricted
along `a`. This is exactly the generator in the normalized representable Kan formula.
Source: Stacks 08PG and 08PH (blueprint: lem-trf-shriek-bar-comma-reindexing). -/
def lanGenerator (P : Resolution.{u, u, u} E R) (f : E ⥤ D)
    (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (V : D) (n : ℕ)
    (c : ComposableArrows E n) (a : V ⟶ f.obj c.left) :
    F.obj (op c.right) ⟶ (f.op.lan.obj ((P.B.obj F).X (-(n : ℤ)))).obj (op V) :=
  ι F n c.left c (𝟙 c.left) ≫ (P.termIso F n c.left).hom ≫
    ((f.op.lanAdjunction (ModuleCat.{u} R)).unit.app
      ((P.B.obj F).X (-(n : ℤ)))).app (op c.left) ≫
    (f.op.lan.obj ((P.B.obj F).X (-(n : ℤ)))).map a.op

/-- The individual face on the recorded category bar model, constructed from its
coproduct coordinates. The first face deletes the initial vertex, internal faces compose
arrows, and the last applies the coefficient restriction.
Source: Stacks 08PG (blueprint: lem-trf-shriek-bar-comma-reindexing). -/
def commaFace {I : Type u} [SmallCategory I] (K : CategoryColimitBarModel I R)
    (F : Iᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ) (j : Fin (n + 2)) :
    (K.bar.obj F).X (-((n + 1 : ℕ) : ℤ)) ⟶ (K.bar.obj F).X (-(n : ℤ)) :=
  (K.coordinates F (n + 1)).hom ≫ Sigma.desc (fun c : ComposableArrows I (n + 1) ↦
    categoryBarFaceCoefficient F c j ≫ K.generator F n (categoryBarDelete c j))

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The specified chain comparison and restriction maps, with both generator directions,
individual faces, and the two naturalities. `StructuredArrow V f` is `(V ↓ f)`:
its arrow equation forces every later `t_j` from the first one. Thus quantifying over
its chains specifies exactly the recursion in the statement, without choosing arrows.
The inverse formula explicitly forgets all but the initial comma arrow.
Source: Stacks 08PG, 08PH and 08PK
(blueprint: lem-trf-shriek-bar-comma-reindexing). -/
structure CommaReindexing (P : Resolution.{u, u, u} E R)
    (B : CategoryColimitBarSystem.{u}) (f : E ⥤ D) where
  /-- The chain isomorphism from the ordinary Kan image, evaluated at V. -/
  beta : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (V : D),
    (((evaluation Dᵒᵖ (ModuleCat.{u} R)).obj (op V)).mapHomologicalComplex
      (.up ℤ)).obj ((f.op.lan.mapHomologicalComplex (.up ℤ)).obj (P.B.obj F)) ≅
        (B.models (StructuredArrow V f) R).bar.obj ((StructuredArrow.proj V f).op ⋙ F)
  /-- Every generator is carried to its comma chain with unchanged coefficient. -/
  forward : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (V : D) (n : ℕ)
    (c : ComposableArrows (StructuredArrow V f) n),
    lanGenerator P f F V n (c ⋙ StructuredArrow.proj V f) c.left.hom ≫
      (beta F V).hom.f (-(n : ℤ)) =
        (B.models (StructuredArrow V f) R).generator
          ((StructuredArrow.proj V f).op ⋙ F) n c
  /-- The inverse forgets the other comma arrows and keeps the coefficient. -/
  backward : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (V : D) (n : ℕ)
    (c : ComposableArrows (StructuredArrow V f) n),
    (B.models (StructuredArrow V f) R).generator
        ((StructuredArrow.proj V f).op ⋙ F) n c ≫ (beta F V).inv.f (-(n : ℤ)) =
      lanGenerator P f F V n (c ⋙ StructuredArrow.proj V f) c.left.hom
  /-- Intertwining every face separately includes both end faces and every internal face. -/
  faces : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (V : D) (n : ℕ) (j : Fin (n + 2)),
    (f.op.lan.map ((P.faces n j).app F)).app (op V) ≫
        (beta F V).hom.f (-(n : ℤ)) =
      (beta F V).hom.f (-((n + 1 : ℕ) : ℤ)) ≫
        commaFace (B.models (StructuredArrow V f) R)
          ((StructuredArrow.proj V f).op ⋙ F) n j
  /-- Restriction is a cochain map, not just a map on homology. -/
  rho : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) {V W : D} (_s : W ⟶ V),
    (B.models (StructuredArrow V f) R).bar.obj ((StructuredArrow.proj V f).op ⋙ F) ⟶
      (B.models (StructuredArrow W f) R).bar.obj ((StructuredArrow.proj W f).op ⋙ F)
  /-- On generators, replace each t_j by s ≫ t_j and retain x. -/
  rho_formula : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) {V W : D} (s : W ⟶ V)
    (n : ℕ) (c : ComposableArrows (StructuredArrow V f) n),
    (B.models (StructuredArrow V f) R).generator
        ((StructuredArrow.proj V f).op ⋙ F) n c ≫ (rho F s).f (-(n : ℤ)) =
      (B.models (StructuredArrow W f) R).generator
        ((StructuredArrow.proj W f).op ⋙ F) n (c ⋙ StructuredArrow.map s)
  /-- Naturality in the evaluation object, as an equality of chain maps. -/
  restriction : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) {V W : D} (s : W ⟶ V),
    (NatTrans.mapHomologicalComplex ((evaluation Dᵒᵖ (ModuleCat.{u} R)).map s.op)
        (.up ℤ)).app ((f.op.lan.mapHomologicalComplex (.up ℤ)).obj (P.B.obj F)) ≫
      (beta F W).hom = (beta F V).hom ≫ rho F s
  /-- Naturality in the coefficient presheaf. Its comma map has components q_U. -/
  coefficient : ∀ {F G : Eᵒᵖ ⥤ ModuleCat.{u} R} (q : F ⟶ G) (V : D),
    (((evaluation Dᵒᵖ (ModuleCat.{u} R)).obj (op V)).mapHomologicalComplex
        (.up ℤ)).map ((f.op.lan.mapHomologicalComplex (.up ℤ)).map (P.B.map q)) ≫
      (beta G V).hom = (beta F V).hom ≫
        (B.models (StructuredArrow V f) R).bar.map
          (Functor.whiskerLeft (StructuredArrow.proj V f).op q)
  /-- Restriction along an identity is the identity chain map. -/
  rho_id : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (V : D), rho F (𝟙 V) = 𝟙 _
  /-- The restriction maps compose contravariantly. -/
  rho_comp : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) {V W Z : D} (s : W ⟶ V) (t : Z ⟶ W),
    rho F s ≫ rho F t = rho F (t ≫ s)
  /-- Restriction commutes with coefficient maps as actual chain maps. -/
  rho_coefficient : ∀ {F G : Eᵒᵖ ⥤ ModuleCat.{u} R} (q : F ⟶ G)
    {V W : D} (s : W ⟶ V),
    (B.models (StructuredArrow V f) R).bar.map
        (Functor.whiskerLeft (StructuredArrow.proj V f).op q) ≫ rho G s =
      rho F s ≫ (B.models (StructuredArrow W f) R).bar.map
        (Functor.whiskerLeft (StructuredArrow.proj W f).op q)

/-- Localizing the specified chain isomorphism gives the specified isomorphism in D(R).
All chain-map equations in `CommaReindexing` pass to D(R) by applying Q.map.
Source: Stacks 08PG and 08PK (blueprint: lem-trf-shriek-bar-comma-reindexing). -/
def CommaReindexing.derivedBeta {P : Resolution.{u, u, u} E R}
    {B : CategoryColimitBarSystem.{u}} {f : E ⥤ D} (M : CommaReindexing P B f)
    (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (V : D) :=
  DerivedCategory.Q.mapIso (M.beta F V)

/-- Ordinary lower shriek of the specific presheaf bar resolution is the comma bar
complex, with its specified chain identification, face compatibility and naturalities.
Source: Stacks Project, Cohomology on Sites, Tags 08PG, 08PH and 08PK
(blueprint: lem-trf-shriek-bar-comma-reindexing).

Proof:
1. Apply lem-trf-augmented-presheaf-bar-resolution in degree -n, and the normalized
ordinary Kan formula of lem-trf-representable-sum-shriek-acyclic. The resulting terms
are sums over (c, t : V → f(c.left)), with coefficient F(c.right). The Kan unit in
`lanGenerator` is the identity-summand normalization of that formula. Restrictions
precompose t and coefficient maps apply q at c.right. Smallness ensures these sums exist.
The identity-cover functor is continuous and cocontinuous, so the canonical derived
setup is supplied by lem-trf-continuous-cocontinuous-derived-shriek; derived colimits
are supplied by lem-trf-derived-colimit-bar. The present comparison uses only ordinary Kan.
2. Starting with t, define all later comma arrows by composing f of the successive
arrows of c. The comma equation forces this recursion uniquely. Forgetting the other
comma arrows is inverse. Extend this index bijection by the identity on coefficients.
For n = 0 it is (t,U,x) ↔ ((U,t),x). Positive degrees are zero on both sides.
3. The first face composes t with f of the first chain arrow, exactly deleting the
initial comma object. Hence it agrees under the bijection.
4. Internal faces compose adjacent arrows, and functoriality of f preserves the comma
equations. The last face applies F of the final arrow, which is also the comma coefficient
restriction. Their alternating signs agree. Summing proves differential compatibility;
the outgoing degree-zero differential is zero. The inverse also commutes with d.
5. Precomposing every comma arrow with s preserves the comma equations, all deletions,
all compositions and the last coefficient restriction. It therefore defines rho as a
chain map. The same recursion starting with s ≫ t gives these precomposed arrows,
proving the restriction equation on every generator.
6. Naturality of q makes q_V a coefficient natural transformation. Both routes in the
coefficient equation keep the chain and apply q at its terminal vertex. Thus they agree
on the direct-sum generators, as in lem-trf-derived-colimit-bar.
7. Associativity of precomposition proves rho_comp and identities prove rho_id.
Changing coefficients commutes with changing only comma arrows, giving rho_coefficient.
8. Apply Q of def-weil-abstract-derived-category to the inverse chain maps. Functoriality
preserves their inverse equations and every equation in steps 5--7. This gives derivedBeta
and all the stated equations in D(R), without any derived evaluation acyclicity argument. -/
theorem commaReindexing_exists (P : Resolution.{u, u, u} E R)
    (B : CategoryColimitBarSystem.{u}) (f : E ⥤ D) : Nonempty (CommaReindexing P B f) := by
  sorry

end CategoryTheory.PresheafBar
