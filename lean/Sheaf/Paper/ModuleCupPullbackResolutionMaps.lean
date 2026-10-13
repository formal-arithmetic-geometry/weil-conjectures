/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.ModuleCupResolutionData
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
public import Sheaf.AlgebraicGeometry.ModulePullbackTensor

/-! # Compatible computing resolutions across a scheme morphism

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

/-- Global section maps between computing pairings lift the pullback of coefficients.
They commute with differentials and with the naive tensor pairing; their class
maps are the ordinary cohomology pullbacks, with the tensor comparison on the
target. This asserts no identity between cup products on cohomology.
Source: Stacks Project, Sections 20.14, 20.15, 20.30 and 20.31,
Tags 01FB, 01EZ, 01FD, 0FKR and 0FKU; the relative cup product in Remark 20.28.7.
(blueprint: lem-sc-module-cup-pullback-resolution-maps)
Proof: take the functorial Godement resolutions on X and X' for F, G and their
tensor products. The maps on stalks given by the tensor-pullback adjunction unit
induce maps from the Godement resolution on X to the direct image of the one
on X'. Iterate these maps through the stalk-products construction. Naturality
of the unit and the Godement multiplication makes them commute with cofaces
and codegeneracies, hence with the alternating differential. The stalkwise
tensor pairing commutes with these maps after applying the canonical tensor
pullback comparison; naturality of the front/back faces then proves the
Alexander--Whitney pairing equation, with the same signs on both sides.
Take global sections and restrict to nonnegative degrees to obtain l, r, t
and the three differential equations. Equip the six flasque complexes with
computing injective comparisons. To identify a map on global homology, work
on X with the map from its Godement complex to f_* of the complex on X'.
Pushforward preserves flasque sheaves, so the latter complex and f_* of its
injective comparison complex both have global-section-acyclic terms. Replace
the latter bounded-below complex by an injective complex on X. The replacement
and the pushed-forward comparison induce isomorphisms on global homology,
by the acyclic-complex comparison theorem. The two composites from the source
resolution to this injective complex extend the same adjunction unit, hence
are homotopic by resolution comparison. Apply global sections and homology
and cancel the computing isomorphisms. This is the resolution ladder defining
the usual cohomology pullback, and proves the left and right class equations.
For the target the unit is followed by the tensor-pullback comparison, so the
same ladder and coefficient naturality give exactly the stated target class
equation. This argument does not assert that f_* preserves injective modules;
that would require a hypothesis absent here. The statement only needs additive
global maps, so no identification of the two rings of global sections is
assumed. The empty-scheme, zero-sheaf, identity-morphism, and degree-zero cases
use the same formulas. -/
theorem moduleCup_pullback_resolution_maps (X X' : Scheme.{v}) (f : X' ⟶ X)
    (F G : X.Modules) :
    ∃ (D : CupResolutionPairing F G)
      (E : CupResolutionPairing ((tensorPullback f).obj F) ((tensorPullback f).obj G))
      (l : ∀ n : ℕ, Γ(D.left.K.X n, ⊤) →+ Γ(E.left.K.X n, ⊤))
      (r : ∀ n : ℕ, Γ(D.right.K.X n, ⊤) →+ Γ(E.right.K.X n, ⊤))
      (t : ∀ n : ℕ, Γ(D.target.K.X n, ⊤) →+ Γ(E.target.K.X n, ⊤)),
      (∀ (n : ℕ) (a : Γ(D.left.K.X n, ⊤)),
        (E.left.K.d n (n + 1)).val.app (op ⊤) (l n a) =
          l (n + 1) ((D.left.K.d n (n + 1)).val.app (op ⊤) a)) ∧
      (∀ (n : ℕ) (a : Γ(D.right.K.X n, ⊤)),
        (E.right.K.d n (n + 1)).val.app (op ⊤) (r n a) =
          r (n + 1) ((D.right.K.d n (n + 1)).val.app (op ⊤) a)) ∧
      (∀ (n : ℕ) (a : Γ(D.target.K.X n, ⊤)),
        (E.target.K.d n (n + 1)).val.app (op ⊤) (t n a) =
          t (n + 1) ((D.target.K.d n (n + 1)).val.app (op ⊤) a)) ∧
      (∀ (n : ℕ)
        (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc n).moduleCatLeftHomologyData.K)
        (a' : ((((RingedSpace.globalSectionsFunctor X'.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.left.K).sc n).moduleCatLeftHomologyData.K),
        a'.val = l n a.val →
          E.left.class n a' =
            moduleCohomologyPullback f F n (D.left.class n a)) ∧
      (∀ (n : ℕ)
        (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc n).moduleCatLeftHomologyData.K)
        (a' : ((((RingedSpace.globalSectionsFunctor X'.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.right.K).sc n).moduleCatLeftHomologyData.K),
        a'.val = r n a.val →
          E.right.class n a' =
            moduleCohomologyPullback f G n (D.right.class n a)) ∧
      (∀ (n : ℕ)
        (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc n).moduleCatLeftHomologyData.K)
        (a' : ((((RingedSpace.globalSectionsFunctor X'.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.target.K).sc n).moduleCatLeftHomologyData.K),
        a'.val = t n a.val →
          E.target.class n a' =
            (RingedSpace.moduleCohomology X'.toRingedSpace n).map
              ((Classical.choose (module_pullback_tensor f)) F G).hom
              (moduleCohomologyPullback f (@id X.Modules (F ⊗ G)) n
                (D.target.class n a))) ∧
      (∀ (p q : ℕ) (a : Γ(D.left.K.X p, ⊤)) (b : Γ(D.right.K.X q, ⊤)),
        t (p + q) (D.pair p q ⊤ a b) = E.pair p q ⊤ (l p a) (r q b)) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
