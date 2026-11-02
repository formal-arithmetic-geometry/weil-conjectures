/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfExistence
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

/-!
# Restriction of exceptional inverse image to bounded constructible finite-Tor objects

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sec-i-heart/sk-thm-restriction/
_section.md and sk-thm-restriction.proof.md, both conclusion clauses;
standing field convention resolved by Wei Yang #1412, answers 1/18
(blueprint: sk-thm-restriction).

The ambient right adjoint is the witness of the recorded Brown-existence theorem.
The restricted functors are full-subcategory lifts of those same ambient functors.
Their Hom equivalence is required to be the restriction of the ambient equivalence.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- For `O_E`, `E`, or the finite-subextension-valued algebraic closure, the Brown right
adjoint `f^!` preserves `Dctf`, and its restriction is right adjoint to `Rf_!` on `Dctf`.
The three alternatives name the existing condensed coefficient rings, up to ring isomorphism.
A finite extension is represented inside the fixed algebraic closure; no choice of embedding
is a hypothesis on the schemes. The right adjoint `G` and its adjunction are part of the
conclusion (Brown existence, `sk_prop_sf_existence`), not hypotheses; since right adjoints are
unique up to isomorphism and `SX`, `SY` are closed under isomorphisms, this is the Brown `f^!`.
The predicates `SX`, `SY` are exactly the recorded bounded constructible finite-Tor predicates;
`iX`, `iY` are their canonical full inclusions into the recorded localizing closures.

Source: latest blueprint part-six-operations/sec-constructibility-upper-shriek/
sec-ladic-summary/sec-i-heart/sk-thm-restriction, entire statement (_section.md) and
sk-thm-restriction.proof.md (blueprint: sk-thm-restriction).

Proof, following the node's nine steps:
1. The finite or algebraically closed base has ell-cohomological dimension at most one
   or zero. Thus sk-prop-sf-existence supplies the ambient adjunction. For these three
   coefficients sk-prop-n-ctf-equals-bc identifies Dctf with Dbc.
2. Choose finite affine covers of source and target and factor each chart as a closed
   immersion into affine space followed by its projection. The composition and open
   clauses of sk-lem-sf-mate identify the restricted exceptional image with i^! p^! v^*.
3. For E and Qbar, projective-line duality, the standard affine chart, and coordinate
   induction give p_d^! = p_d^*(d)[2d], including d = 0. Pullback preserves constant-model
   constructibility; rank-one Tate twists and shifts preserve bounded constructibility.
4. For O_E use only the projection clauses of det-thm-int-restriction-line. The diagonal
   tower, proper base change and the integral projection formula give projective-line
   duality; the same chart and induction give the affine-space formula. Integral inverse
   image and tensor preserve Dbc. No general integral restriction theorem is used.
5. For a closed immersion i with open complement j, formal closed support is i^* of the
   fibre of K -> Rj_* j^* K. The complement is quasi-compact since the ambient scheme is
   Noetherian. Open-coefficient finiteness and the triangulated Dbc predicate put the
   fibre in Dbc; pullback along i preserves it as well.
6. The support adjunction restricts to the localizing closures: i_* = Ri_! preserves them
   by compactification coherence, and step 5 places the support object in Dbc. Uniqueness
   of the right adjoint therefore identifies the given Brown i^! with closed support.
7. Apply the projection and closed-immersion conclusions to each affine chart. Its open
   pullback of f^! K is bounded constructible by the mate identification of step 2.
8. The finite cover gives a global cohomological interval. Refine the finitely many local
   stratifications to a finite global constructible stratification. This glues Dbc; for
   the empty source the sheaf category is zero and no minimum or maximum is needed.
9. Transfer Dbc preservation to Dctf by step 1. Compactification coherence also gives
   Rf_! preservation of Dctf. Lift both original functors to these full subcategories and
   restrict the original adjunction. Its natural Hom equivalences are unchanged, which
   is exactly the final equality below.
-/
theorem sk_thm_restriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : Finite k ∨ IsAlgClosed k)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    let SX := constantModelBoundedConstructible Λ X ⊓
      _root_.DerivedCategory.finiteTorAmplitude _
    let SY := constantModelBoundedConstructible Λ Y ⊓
      _root_.DerivedCategory.finiteTorAmplitude _
    let iX : SX.FullSubcategory ⥤
        (localizingClosureProEtale Λ X).FullSubcategory :=
      ObjectProperty.ιOfLE (fun K hK _P _hP hS ↦ hS K hK)
    let iY : SY.FullSubcategory ⥤
        (localizingClosureProEtale Λ Y).FullSubcategory :=
      ObjectProperty.ιOfLE (fun K hK _P _hP hS ↦ hS K hK)
    ∀ c : Compactification.BoundaryCompactification f,
      ∃ (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
          ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)),
        ∃ (hF : ∀ M : SX.FullSubcategory,
            SY ((localizingLowerShriek Λ c.obj.obj h).obj (iX.obj M)).obj),
          ∃ (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
              (localizingClosureProEtale Λ X).FullSubcategory),
            ∃ (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G),
              (∀ N : (localizingClosureProEtale Λ Y).FullSubcategory,
                SY N.obj → SX (G.obj N).obj) ∧
              ∃ (hG : ∀ N : SY.FullSubcategory, SX (G.obj (iY.obj N)).obj),
                let F₀ : SX.FullSubcategory ⥤ SY.FullSubcategory :=
                  SY.lift (iX ⋙ localizingLowerShriek Λ c.obj.obj h ⋙
                    (localizingClosureProEtale Λ Y).ι) hF
                let G₀ : SY.FullSubcategory ⥤ SX.FullSubcategory :=
                  SX.lift (iY ⋙ G ⋙ (localizingClosureProEtale Λ X).ι) hG
                ∃ (adj₀ : F₀ ⊣ G₀),
                  (F₀ ⋙ iY = iX ⋙ localizingLowerShriek Λ c.obj.obj h) ∧
                  (G₀ ⋙ iX = iY ⋙ G) ∧
                  ∀ (M : SX.FullSubcategory) (N : SY.FullSubcategory)
                    (a : (localizingLowerShriek Λ c.obj.obj h).obj
                      (iX.obj M) ⟶ iY.obj N),
                    (adj₀.homEquiv M N (ObjectProperty.homMk a.hom)).hom =
                      (adj.homEquiv (iX.obj M) (iY.obj N) a).hom
              := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
