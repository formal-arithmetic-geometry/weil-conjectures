/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.BrownHypothesesSmall

/-!
# Transport along an isomorphism of condensed coefficient rings

This is the coefficient-presentation transport clause of
`lem-route-sfb-admissible-coefficient-iso-transport`.

Source: blueprint latest, `sec-six-functors-basics/sk-prop-scalar-six`,
`det-prop-scalar-six-ctf.proof.md`, clause (3), coefficient-presentation reduction
(blueprint: lem-route-sfb-admissible-coefficient-iso-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/--
The restriction functor is written explicitly as `Mod.comap` along the pullback
of the ring-object isomorphism.  The statement records the exact equivalence,
its termwise derived functor, preservation of bounded constant-model
constructibility, the unchanged cohomological interval (degreewise vanishing),
the transport of every finite constant model along each map `g : Z ⟶ T` (cover
members of strata and of affine opens) with its finitely presented scalar
module restricted along `e`, and the resulting triangulated/retract-closure
equivalences.

Source: blueprint latest, `sec-six-functors-basics/sk-prop-scalar-six`,
`det-prop-scalar-six-ctf.proof.md`, clause (3)
(blueprint: lem-route-sfb-admissible-coefficient-iso-transport).

Proof in words: pull `e` back along the point-to-`T` inverse-image functor.
Restriction of scalars is the identity on underlying sheaves and morphisms;
the inverse restriction is obtained from `e.inv`, and the change-of-scalars
equivalence supplies exactness and the two-sided inverse data.  Termwise
application therefore induces the displayed derived functor and its
equivalence.  On every finite constant local model, restriction changes only
the scalar action: the same cover, stratum, and finite presentation work after
carrying its scalar matrix along `e.inv`, and the converse uses `e`.  Precisely,
for `g : Z ⟶ T`, restriction commutes with `g^*` and with `p_Z^*` (the pullback
comparison), so a model `g^* M ≅ p_Z^* P` gives `g^* (R_e M) ≅ p_Z^* (Res_e P)`,
and `Res_e P` is finitely presented because `Res_e` is an exact equivalence
carrying the regular module of `Λ'` to that of `Λ`.  Exactness gives the
canonical cohomology comparison `H^n(D(R_e) K) ≅ R_e(H^n K)` in every degree;
since `R_e` is an equivalence, `H^n K` vanishes exactly when `H^n(D(R_e) K)`
does, so the cohomological interval is unchanged, and the constructibility
predicate is preserved and reflected.
Finally the derived equivalence commutes with shifts and mapping cones and
carries retract diagrams to retract diagrams; transporting these properties
in both directions gives the two final equivalences.  The argument includes
the identity isomorphism, the zero ring, empty schemes, and coefficient
automorphisms.
-/
theorem sfbAdmissibleCoefficientIsoTransport
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    let φ := e.hom.hom
    let R_e : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ' T) ⥤
        Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj Λ T) :=
      Mod.comap ((upperStarFromPoint T).map φ)
    let R_e_inv : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T) ⥤
        Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj Λ' T) :=
      Mod.comap ((upperStarFromPoint T).map e.inv.hom)
    (PreservesFiniteLimits R_e ∧ PreservesFiniteColimits R_e ∧ R_e.IsEquivalence ∧
      R_e.mapDerivedCategory.IsEquivalence) ∧
      (∃ E :
          Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj Λ' T) ≌
            Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj Λ T),
        E.functor = R_e ∧ E.inverse = R_e_inv) ∧
      (∀ K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
            (condensedRingObj Λ' T)),
        constantModelBoundedConstructible Λ' T K ↔
          constantModelBoundedConstructible Λ T (R_e.mapDerivedCategory.obj K)) ∧
      (∀ (K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
            (condensedRingObj Λ' T))) (n : ℤ),
        IsConstantModelConstructible Λ' T
            ((DerivedCategory.homologyFunctor _ n).obj K) ↔
          IsConstantModelConstructible Λ T
            ((DerivedCategory.homologyFunctor _ n).obj
              (R_e.mapDerivedCategory.obj K))) ∧
      (∀ K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
            (condensedRingObj Λ' T)),
        DerivedCategory.TStructure.t.bounded K ↔
          DerivedCategory.TStructure.t.bounded (R_e.mapDerivedCategory.obj K)) ∧
      (∀ (K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
            (condensedRingObj Λ' T))) (n : ℤ),
        IsZero ((DerivedCategory.homologyFunctor _ n).obj K) ↔
          IsZero ((DerivedCategory.homologyFunctor _ n).obj
            (R_e.mapDerivedCategory.obj K))) ∧
      (∀ (Z : Scheme.{u}) (g : Z ⟶ T)
          (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ' T))
          (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ'),
        Mod.IsFinitelyPresented Λ' P →
        Nonempty ((CondensedRing.upperStar Λ' g).obj M ≅
          ((upperStarFromPoint Z).mapMod Λ').obj P) →
        Mod.IsFinitelyPresented Λ ((Mod.comap φ).obj P) ∧
          Nonempty ((CondensedRing.upperStar Λ g).obj (R_e.obj M) ≅
            ((upperStarFromPoint Z).mapMod Λ).obj ((Mod.comap φ).obj P))) ∧
      ((constantModelBoundedConstructible Λ' T).IsTriangulated ↔
        (constantModelBoundedConstructible Λ T).IsTriangulated) ∧
      ((constantModelBoundedConstructible Λ' T).IsStableUnderRetracts ↔
        (constantModelBoundedConstructible Λ T).IsStableUnderRetracts) := by
  sorry

end AlgebraicGeometry.ProEtale
