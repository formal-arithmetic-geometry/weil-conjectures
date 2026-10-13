/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.ModuleCupResolutionData

/-! # Compatible computing resolutions for coefficient morphisms

Source: Stacks Project, Section 20.31 (Tag 0FKU), and the functorial Godement
construction in Section 20.30 (Tag 0FKR).
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Coefficient maps lift simultaneously to computing resolution pairings.
The three lifted maps commute with the section pairing in every bidegree and
induce the coefficient maps under the resolution class identifications. This is
resolution-level data; no cup product on cohomology is assumed.
Source: Stacks Project, Sections 20.30 and 20.31, Tags 0FKR and 0FKU.
(blueprint: lem-sc-module-cup-coefficient-resolution-maps)
Proof: use the functorial cosimplicial Godement resolution for the six sheaves
F, G, F1, G1, F tensor G, and F1 tensor G1. Apply its functorial action to phi,
psi and phi tensor psi. The natural stalkwise tensor pairing commutes with
these maps. In the Alexander--Whitney formula the same front/back face maps
are used on both sides; their naturality proves the pairing equation in every
bidegree and on every open set. Restrict the resulting complexes to natural
indices and equip them with injective comparisons as in the computing-flasque
resolution construction. Each comparison induces an isomorphism on global
homology because its terms are flasque. A lifted coefficient map and an
injective-resolution lift agree over the degree-zero augmentation. The
comparison theorem makes their composites into the target injective complex
homotopic; applying global sections and homology makes them equal.
InjectiveResolution.isoRightDerivedObj_inv_naturality then gives the class
map equation for every degree and every pair of cycles with the stated
underlying-section equality. This proves all three class equations. No
quasi-coherence or flatness is used. For zero maps, zero sheaves, and the empty
scheme the same additive functor and tensor pairing apply. -/
theorem moduleCup_coefficient_resolution_maps (X : Scheme.{v})
    (F G F₁ G₁ : X.Modules) (φ : F ⟶ F₁) (ψ : G ⟶ G₁) :
    ∃ (D : CupResolutionPairing F G) (E : CupResolutionPairing F₁ G₁)
      (l : D.left.K ⟶ E.left.K) (r : D.right.K ⟶ E.right.K)
      (t : D.target.K ⟶ E.target.K),
      (∀ (n : ℕ)
        (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc n).moduleCatLeftHomologyData.K)
        (a' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.left.K).sc n).moduleCatLeftHomologyData.K),
        a'.val = (l.f n).val.app (op ⊤) a.val →
          E.left.class n a' =
            (RingedSpace.moduleCohomology X.toRingedSpace n).map φ (D.left.class n a)) ∧
      (∀ (n : ℕ)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc n).moduleCatLeftHomologyData.K)
        (b' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.right.K).sc n).moduleCatLeftHomologyData.K),
        b'.val = (r.f n).val.app (op ⊤) b.val →
          E.right.class n b' =
            (RingedSpace.moduleCohomology X.toRingedSpace n).map ψ (D.right.class n b)) ∧
      (∀ (n : ℕ)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc n).moduleCatLeftHomologyData.K)
        (c' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.target.K).sc n).moduleCatLeftHomologyData.K),
        c'.val = (t.f n).val.app (op ⊤) c.val →
          E.target.class n c' =
            (RingedSpace.moduleCohomology X.toRingedSpace n).map
              (@id (F ⊗ G ⟶ F₁ ⊗ G₁) (φ ⊗ₘ ψ)) (D.target.class n c)) ∧
      (∀ (p q : ℕ) (V : X.Opens)
        (a : Γ(D.left.K.X p, V)) (b : Γ(D.right.K.X q, V)),
        (t.f (p + q)).val.app (op V) (D.pair p q V a b) =
          E.pair p q V ((l.f p).val.app (op V) a) ((r.f q).val.app (op V) b)) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
