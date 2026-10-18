/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.SixFunctors.BaseChange.Square
import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.ProperGeometricPointExchange
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Proper-surjective descent equalizer for small étale sections

Source: Stacks Project, Étale Cohomology, Tag 0DDW (lemma-describe-pullback-pi-ph).
(blueprint: lem-trf-proper-surjection-etale-section-equalizer).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

open AlgebraicGeometry Scheme

/-- Source: Stacks Project, Étale Cohomology, Tag 0DDW (lemma-describe-pullback-pi-ph).
(blueprint: lem-trf-proper-surjection-etale-section-equalizer).

For a proper surjective morphism of schemes, sections of the inverse image of an
arbitrary abelian small étale sheaf are exactly the sections whose two pullbacks
to the double fibre product agree.  The first conjunct records uniqueness of the
descended section; the second records existence and compatibility, with the
canonical inverse-image unit and the two projection restrictions.  This is the
abelian-group equalizer formulation of the source statement.

Proof (the node's eight steps):
1. Put H = p_* p⁻¹G and J = q_* q⁻¹G. The two projection units give maps
   α₁, α₂ : H → J. The composition rule for adjunction units makes the unit
   η : G → H equalize them. Let E = ker(α₁ - α₂); sectionwise limits of
   abelian sheaves give the factorization θ : G → E.
2. Both projections rᵢ : Q → V are proper by proper base change, and q is
   proper by composition. For a geometric point s : P = Spec k → U, write
   W = V ×_U P and R = Q ×_U P. The pullback universal property identifies
   R with W ×_P W, compatibly with both projections ρᵢ and the maps to P.
3. With L = s⁻¹G, proper geometric-point exchange identifies H_s and J_s
   with Γ(W, a⁻¹L) and Γ(R, b⁻¹L), and G_s with Γ(P, L). This holds for
   arbitrary abelian coefficients: the integer-module structure requires
   no torsion hypothesis.
4. These identifications take η_s to a-pullback and (αᵢ)_s to ρᵢ-pullback.
   Check the proper exchange map on a section represented over an étale
   neighbourhood of s: both orders of pullback are the same morphism to
   V times that neighbourhood. For η, inverse-image germ compatibility
   identifies the unit germ with the original germ.
5. Surjectivity survives base change, so W is nonempty. Since W is proper
   of finite type over the algebraically closed field k, the Jacobson
   closed-point and residue-field results give a k-rational point, hence
   a section e : P → W of a. No section of p over U is asserted.
6. If z in Γ(W, a⁻¹L) equalizes ρ₁ and ρ₂, pull that equality back along
   (id_W, e a) : W → W ×_P W to get z = a-pullback(e-pullback(z)).
   Conversely an a-pullback equalizes them, and e-pullback after a-pullback
   is the identity. Thus Γ(P, L) is precisely the fibre-section equalizer.
7. Exact geometric stalks compute E_s as that equalizer. Therefore θ_s is
   an isomorphism at every geometric point, and stalk conservativity makes
   θ an isomorphism. If U is empty the same conservativity argument is
   vacuous and all three section groups are zero.
8. Taking terminal sections preserves the sheaf equalizer and identifies
   H(U) and J(U) with the sections on V and Q. The specified first map is
   η and the specified parallel arrows are the two restrictions, giving
   precisely injectivity and the displayed compatibility/image criterion.
-/
theorem properSurjectiveEtaleSectionEqualizer
    {U V : Scheme.{u}} (p : V ⟶ U) [IsProper p] [Surjective p]
    (G : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Injective
      (pullSection p G (V := Scheme.Etale.mk (𝟙 V)) (U := Scheme.Etale.mk (𝟙 U)) p
        ((Category.comp_id _).trans (Category.id_comp _).symm)) ∧
      ∀ σ' : ((p)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj
          (op (Scheme.Etale.mk (𝟙 V))),
        restrictAlong p G (pullback.fst p p) (pullback.fst p p ≫ p) rfl
            (V := Scheme.Etale.mk (𝟙 V))
            (V' := Scheme.Etale.mk (𝟙 (pullback p p))) (pullback.fst p p)
            ((Category.comp_id _).trans (Category.id_comp _).symm) σ' =
          restrictAlong p G (pullback.snd p p) (pullback.fst p p ≫ p) pullback.condition
            (V := Scheme.Etale.mk (𝟙 V))
            (V' := Scheme.Etale.mk (𝟙 (pullback p p))) (pullback.snd p p)
            ((Category.comp_id _).trans (Category.id_comp _).symm) σ' ↔
        ∃ σ : G.obj.obj (op (Scheme.Etale.mk (𝟙 U))),
          pullSection p G (V := Scheme.Etale.mk (𝟙 V)) (U := Scheme.Etale.mk (𝟙 U)) p
            ((Category.comp_id _).trans (Category.id_comp _).symm) σ = σ' := by
  sorry

end AlgebraicGeometry.Etale
