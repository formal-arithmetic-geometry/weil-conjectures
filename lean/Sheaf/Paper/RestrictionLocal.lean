/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.UnboundedLocalizingPullback
public import Sheaf.SixFunctors.CompactificationOverField
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.Paper.AffineSpaceRationalInduction
import Sheaf.Paper.ClosedAdjointConstructibleYoneda
import Sheaf.Paper.ClosedSupportConstructible
import Sheaf.Paper.CompactificationCoherenceCocycle
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.Paper.LocalizingLowerShriekComposition
import Sheaf.Paper.MateOpenRestriction
import Sheaf.Paper.RationalClosedSupportConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

/-!
# Local factorization of the exceptional inverse image

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-thm-restriction/sk-thm-restriction-local.md (blueprint: det-thm-restriction-local).

The right adjoints below are the localizing exceptional right adjoints supplied by
`sk-prop-sf-existence`; the pullbacks are the canonical derived pullback lifts.  Thus the
statement does not introduce a second exceptional inverse image or a second pullback.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Local factorization of `f^!` on affine charts, together with bounded constructibility.

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-restriction/
sk-thm-restriction-local (blueprint: det-thm-restriction-local).

The exceptional inverse images are the right adjoints of `sk-prop-sf-existence`: for
`f`, the projection `p` and the closed immersion `i`, an arbitrary boundary
compactification, its localizing-closure preservation proof and an arbitrary right
adjoint (`Ff`, `Fp`, `Fi`) of the corresponding `localizingLowerShriek` are taken as
arguments, so the factorization holds for every choice.  The pullbacks are the canonical
derived pullback lifts `huStar`, `hvStar`.

Proof (the steps of the blueprint proof):
1. `k` is Noetherian; `X`, `Y` are Noetherian, quasi-compact and quasi-separated, and
   affine opens of them are of finite type over `k`.
2. `A^d_V` is separated of finite type over `k`; `U`, `V`, `A^d_V` stay in the standing
   setting.
3. `Dctf = Dbc` and their localizing closures agree (det-def-localizing-closure-ctf-equals-bc);
   the closed immersion `i` is proper, so `u, v, i, p` satisfy the adjunction hypotheses.
4. Finitely many affine `V_β` cover `Y`, and finite affine covers `U_{βα}` of `f⁻¹(V_β)`
   by finitely generated algebras cover `X`.
5. Generators `b_1, …, b_d` give a surjection `A[t_1, …, t_d] → B`, hence the closed
   immersion `i` with `f u = v p i` (also for `d = 0`): the finite-cover clause.
6. `Rb_! Ra_! ≅ R(ba)_!` on the localizing closures
   (lem-sfb-localizing-lower-shriek-composition).
7. Composite adjunctions and uniqueness of right adjoints give `(ba)^! ≅ a^! b^!`.
8. `u^! ≅ u^*`, `v^! ≅ v^*` (det-sf-mate-open-restriction), whence
   `u^* f^! ≅ (f u)^! = (v p i)^! ≅ i^! p^! v^*`.
9. For `K ∈ Dbc(Y)`, `v^* K ∈ Dbc(V)` and `H = p^! v^* K ≅ p^* v^* K (d)[2d] ∈ Dbc(A^d_V)`.
10. `i^! H ≅ RΓ_U H` (closed-immersion normalization, det-prop-closed-adjoint-constructible-yoneda),
    and `RΓ_U H ∈ Dbc(U)` (lem-sfb-rational-closed-support-constructible).
11. Evaluating step 8 at `K` gives `u^* f^! K ∈ Dbc(U)`. -/
theorem restrictionLocal
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ :
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (cf : Compactification.BoundaryCompactification f)
    (hf : ∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      localizingClosureProEtale Λ X K →
        localizingClosureProEtale Λ Y
          ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ cf.obj.obj).obj K))
    (Ff : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (_adjf : CondensedRing.localizingLowerShriek Λ cf.obj.obj hf ⊣ Ff) :
    (∀ {V U : Scheme.{u}} (v : V ⟶ Y) (u : U ⟶ X)
        (hV : IsAffine V) (hU : IsAffine U)
        (hv : IsOpenImmersion v) (hu : IsOpenImmersion u)
        (d : ℕ)
        (i : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
        (hi : IsClosedImmersion i)
        (q : U ⟶ V)
        (hqi : i ≫ (AffineSpace.over (ULift.{u} (Fin d)) V).hom = q)
        (hq : q ≫ v = u ≫ f)
        (cp : Compactification.BoundaryCompactification
          ((AffineSpace.over (ULift.{u} (Fin d)) V).hom))
        (hp : ∀ K : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology (AffineSpace
              (ULift.{u} (Fin d)) V)) Ab.{u + 1})
              (condensedRingObj Λ (AffineSpace (ULift.{u} (Fin d)) V))),
          localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V) K →
            localizingClosureProEtale Λ V
              ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ cp.obj.obj).obj K))
        (Fp : (localizingClosureProEtale Λ V).FullSubcategory ⥤
          (localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V)).FullSubcategory)
        (adjp : CondensedRing.localizingLowerShriek Λ cp.obj.obj hp ⊣ Fp)
        (ci : Compactification.BoundaryCompactification i)
        (hi' : ∀ K : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
              (condensedRingObj Λ U)),
          localizingClosureProEtale Λ U K →
            localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V)
              ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ ci.obj.obj).obj K))
        (Fi : (localizingClosureProEtale Λ (AffineSpace
            (ULift.{u} (Fin d)) V)).FullSubcategory ⥤
          (localizingClosureProEtale Λ U).FullSubcategory)
        (adji : CondensedRing.localizingLowerShriek Λ ci.obj.obj hi' ⊣ Fi),
        ∃ (huStar : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
            localizingClosureProEtale Λ U
              (((localizingClosureProEtale Λ X).ι ⋙
                (CondensedRing.upperStar Λ u).leftDerivedFunctor).obj K))
          (hvStar : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
            localizingClosureProEtale Λ V
              (((localizingClosureProEtale Λ Y).ι ⋙
                (CondensedRing.upperStar Λ v).leftDerivedFunctor).obj K)),
          Nonempty
            ((Ff ⋙
                (localizingClosureProEtale Λ U).lift
                  ((localizingClosureProEtale Λ X).ι ⋙
                    (CondensedRing.upperStar Λ u).leftDerivedFunctor) huStar) ≅
              ((localizingClosureProEtale Λ V).lift
                  ((localizingClosureProEtale Λ Y).ι ⋙
                    (CondensedRing.upperStar Λ v).leftDerivedFunctor) hvStar ⋙
                Fp ⋙ Fi)) ∧
          (∀ K : DerivedCategory
              (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
                (condensedRingObj Λ Y)),
            constantModelBoundedConstructible Λ Y K →
              ∃ hK : localizingClosureProEtale Λ Y K,
                constantModelBoundedConstructible Λ U
                  (((localizingClosureProEtale Λ U).lift
                      ((localizingClosureProEtale Λ X).ι ⋙
                        (CondensedRing.upperStar Λ u).leftDerivedFunctor) huStar).obj
                    (Ff.obj ⟨K, hK⟩)).obj)) ∧
      ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (u : ∀ a, U a ⟶ X),
        (∀ a, IsAffine (U a) ∧ IsOpenImmersion (u a)) ∧
        (∀ x : X, ∃ a : Fin n, ∃ y : U a, (u a).base y = x) ∧
        (∀ a, ∃ (V : Scheme.{u}) (v : V ⟶ Y),
          IsAffine V ∧ IsOpenImmersion v ∧
          ∃ (d : ℕ) (i : U a ⟶ AffineSpace (ULift.{u} (Fin d)) V)
            (hi : IsClosedImmersion i) (q : U a ⟶ V),
            i ≫ (AffineSpace.over (ULift.{u} (Fin d)) V).hom = q ∧ q ≫ v = u a ≫ f) := by
  sorry

end AlgebraicGeometry.ProEtale
