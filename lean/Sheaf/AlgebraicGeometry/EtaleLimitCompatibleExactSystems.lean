/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Compatible short exact systems of etale sheaves

Source: Stacks Project, Tags 0EXZ, 09YP and 0739.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
/-- Compatible stage short exact sequences and their limit sequence, in continuation form.
Source: Stacks Project, Tags 0EXZ and 09YP, construction of the injective system and
its cokernel; exactness of filtered sheaf colimits.
(blueprint: lem-weil-pbc-etale-limit-compatible-exact-systems).

Proof: For each k take the canonical injective embedding F_k into Injective.under F_k.
At i take the product of the direct images of these injectives over all arrows i to k.
The adjunction transposes the coefficient transitions into product components. The
identity component makes the induced embedding monic. Exact inverse image makes each
factor injective and products preserve injectivity. Composition of arrows defines the
product transitions; the canonical adjunction comparisons prove the identity and
composition laws. Take the actual stage cokernels of the embeddings. Exact inverse
image preserves their cokernel property, so cancelling the quotient epimorphisms proves
the quotient transition laws. Pull all three systems to X using the cone comparisons,
then take their actual filtered colimits. Exact filtered sheaf colimits give the limit
short exact sequence. The stage coprojections induce the displayed morphisms of short
complexes. More explicitly, transport the pulled-back embeddings and quotients
through eG, eGI and eGR to natural transformations between the three diagrams.
The coefficient squares and the cone comparisons prove their naturality. Their
composite is zero objectwise. Exact inverse image gives stagewise short exactness,
hence objectwise exactness gives a short exact sequence in the functor category.
Apply the exact filtered colimit functor. Identify colimit G with the supplied
L.pt by the unique colimit isomorphism. Compose the three object-identification
inverses with the coprojections to obtain t. Naturality of the coprojections
and the definitions of the induced colimit maps prove its two squares.
The stage compatibility of the embedding and quotient makes the triples
(phi, psi, phiR) morphisms r of short complexes. The middle component of each
limit comparison t is the pulled-back middle coprojection, just as its outer
components are the prescribed coprojections. This is only the construction:
no vanishing or cohomology boundary is asserted. The product construction
works for a singleton index and zero or empty-scheme systems as well.
-/
theorem etale_limit_compatible_exact_systems
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L) (result : Prop)
    (continuation : ∀ (FR : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φR : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (FR i) ⟶ FR j)
    (hidentityR : ∀ i : I, φR (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (FR i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (FR i))
    (hcompositionR : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φR (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (FR i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φR f) ≫ φR g)
    (GR : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eGR : ∀ i : I, GR.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (FR i))
    (hGR : ∀ (i j : I) (f : i ⟶ j), GR.map f =
      (eGR i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (FR i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φR f) ≫ (eGR j).inv)
    (LR : Cocone GR) (hLR : IsColimit LR)
    (FI : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (ψ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (FI i) ⟶ FI j)
    (hidentityI : ∀ i : I, ψ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (FI i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (FI i))
    (hcompositionI : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      ψ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (FI i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (ψ f) ≫ ψ g)
    (GI : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eGI : ∀ i : I, GI.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (FI i))
    (hGI : ∀ (i j : I) (f : i ⟶ j), GI.map f =
      (eGI i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (FI i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (ψ f) ≫ (eGI j).inv)
    (LI : Cocone GI) (hLI : IsColimit LI)
    (a : L.pt ⟶ LI.pt) (b : LI.pt ⟶ LR.pt) (w : a ≫ b = 0)
    (hE : (ShortComplex.mk a b w).ShortExact)
    (ai : ∀ i : I, F i ⟶ FI i) (bi : ∀ i : I, FI i ⟶ FR i)
    (wi : ∀ i : I, ai i ≫ bi i = 0)
    (hi : ∀ i : I, (ShortComplex.mk (ai i) (bi i) (wi i)).ShortExact)
    (t : ∀ i : I,
      (ShortComplex.mk (ai i) (bi i) (wi i)).map
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))) ⟶ ShortComplex.mk a b w)
    (r : ∀ (i j : I) (f : i ⟶ j),
      (ShortComplex.mk (ai i) (bi i) (wi i)).map
        (upperStar AddCommGrpCat.{u + 1} (D.map f.op)) ⟶
      ShortComplex.mk (ai j) (bi j) (wi j)),
      (∀ (i j : I) (f : i ⟶ j), (r i j f).τ₁ = φ f) ∧
      (∀ (i j : I) (f : i ⟶ j), (r i j f).τ₂ = ψ f) ∧
      (∀ (i j : I) (f : i ⟶ j), (r i j f).τ₃ = φR f) ∧
      (∀ i : I, (t i).τ₂ = (eGI i).inv ≫ LI.ι.app i) ∧
      (∀ i : I, Injective (FI i)) ∧
      (∀ i : I, (t i).τ₁ = (eG i).inv ≫ L.ι.app i) ∧
      (∀ i : I, (t i).τ₃ = (eGR i).inv ≫ LR.ι.app i) → result) : result := by sorry

end AlgebraicGeometry.Etale
