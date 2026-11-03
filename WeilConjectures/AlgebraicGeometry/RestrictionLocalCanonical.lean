/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.SixFunctors.RestrictionLocal

/-!
# Local exceptional inverse image with the canonical rational coefficients

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sec-i-heart/
sk-thm-restriction/sk-thm-restriction-local.md and its proof
(blueprint: det-thm-restriction-local).

The coefficient is the canonical condensed finite extension or the canonical
finite-subextension-valued algebraic closure. The equality in `hΛ` selects these
existing ring objects; it introduces no comparison with another presentation.
Each restricted lower shriek is the defining `ObjectProperty.lift` expression of the
existing `localizingLowerShriek`, using the actual recorded derived compactification
functor. No lower-shriek construction is defined again. The exceptional functors are
arbitrary right adjoints of these restricted compactification lower shrieks. The open
pullbacks are lifts of the total derived module pullbacks.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option linter.unusedVariables false in
/-- On every affine chart, `u^* f^!` is isomorphic to `i^! p^! v^*` and takes bounded
constructible objects to bounded constructible objects; finitely many such charts cover `X`.
The compactifications and right adjoints for `f`, `p` and `i` are universally quantified.
Thus the formula applies to the chosen exceptional inverse images, independently of choices.
The canonical coefficient objects are those of `det-def-sfb-condensed-ring` and
`det-def-sfb-qlbar-condensed`. The notation `Loc(Dbc)` is implemented by the existing
`localizingClosureProEtale`; `det-def-localizing-closure-ctf-equals-bc` identifies it with
this closure of bounded constructible finite-Tor objects for these coefficients.

Source: blueprint latest, det-thm-restriction-local, complete statement and the proof's
three paragraphs (blueprint: det-thm-restriction-local).

Proof:
1. Finite type over the field makes `X` and `Y` Noetherian and quasi-compact. Choose a
   finite affine cover of `Y` and a finite affine cover of each inverse image. A finite
   list of algebra generators on each chart gives a surjection from a polynomial ring,
   hence a closed immersion into `A^d_V`. These give the final finite covering clause.
   This is `lem-sf-affine-chart-factorization-gluing` and includes dimension zero.
2. On an open immersion, extension by zero is left adjoint to restriction, so its
   exceptional inverse image is the derived pullback. Apply `sk-lem-sf-mate` to the
   equality `fu = vpi`: `u^* f^! ≅ u^! f^! ≅ (fu)^! ≅ i^! p^! v^! ≅ i^! p^! v^*`.
   The open pullbacks preserve the localizing categories by
   `det-proper-base-change-unbounded-pullback`. Composition and uniqueness of right
   adjoints give the natural isomorphism for every choice of the three right adjoints.
3. For `K` bounded constructible, `v^* K` remains bounded constructible.
   `det-cor-affine-space-rational-induction` gives
   `p^! v^* K ≅ p^* v^* K(d)[2d]`, again bounded constructible. Closed-immersion
   normalization and `det-prop-closed-adjoint-constructible-yoneda` identify `i^!` with
   closed support; `lem-sfb-rational-closed-support-constructible` preserves bounded
   constructibility. Evaluate the isomorphism from step 2 at `K` to conclude.
-/
theorem restrictionLocalCanonical
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ :
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj E.1)) ∨
      Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
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
    (_adjf : (localizingClosureProEtale Λ Y).lift
      ((localizingClosureProEtale Λ X).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ cf.obj.obj)
      (fun K ↦ hf K.obj K.property) ⊣ Ff) :
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
        (adjp : (localizingClosureProEtale Λ V).lift
          ((localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V)).ι ⋙
            CondensedRing.rightDerivedLowerShriekOfCompactification Λ cp.obj.obj)
          (fun K ↦ hp K.obj K.property) ⊣ Fp)
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
        (adji : (localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V)).lift
          ((localizingClosureProEtale Λ U).ι ⋙
            CondensedRing.rightDerivedLowerShriekOfCompactification Λ ci.obj.obj)
          (fun K ↦ hi' K.obj K.property) ⊣ Fi),
        ∃ (huStar : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
            localizingClosureProEtale Λ U
              (((localizingClosureProEtale Λ X).ι ⋙
                CondensedRing.moduleObjectDerivedPullback Λ u).obj K))
          (hvStar : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
            localizingClosureProEtale Λ V
              (((localizingClosureProEtale Λ Y).ι ⋙
                CondensedRing.moduleObjectDerivedPullback Λ v).obj K)),
          Nonempty
            ((Ff ⋙
                (localizingClosureProEtale Λ U).lift
                  ((localizingClosureProEtale Λ X).ι ⋙
                    CondensedRing.moduleObjectDerivedPullback Λ u) huStar) ≅
              ((localizingClosureProEtale Λ V).lift
                  ((localizingClosureProEtale Λ Y).ι ⋙
                    CondensedRing.moduleObjectDerivedPullback Λ v) hvStar ⋙
                Fp ⋙ Fi)) ∧
          (∀ K : DerivedCategory
              (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
                (condensedRingObj Λ Y)),
            constantModelBoundedConstructible Λ Y K →
              ∃ hK : localizingClosureProEtale Λ Y K,
                constantModelBoundedConstructible Λ U
                  (((localizingClosureProEtale Λ U).lift
                      ((localizingClosureProEtale Λ X).ι ⋙
                        CondensedRing.moduleObjectDerivedPullback Λ u) huStar).obj
                    (Ff.obj ⟨K, hK⟩)).obj)) ∧
      ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (u : ∀ a, U a ⟶ X),
        (∀ a, IsAffine (U a) ∧ IsOpenImmersion (u a)) ∧
        (∀ x : X, ∃ a : Fin n, ∃ y : U a, (u a).base y = x) ∧
        (∀ a, ∃ (V : Scheme.{u}) (v : V ⟶ Y),
          IsAffine V ∧ IsOpenImmersion v ∧
          ∃ (d : ℕ) (i : U a ⟶ AffineSpace (ULift.{u} (Fin d)) V)
            (hi : IsClosedImmersion i) (q : U a ⟶ V),
            i ≫ (AffineSpace.over (ULift.{u} (Fin d)) V).hom = q ∧ q ≫ v = u a ≫ f) := by
  have hcoeff :
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
    rcases hΛ with ⟨E, hE⟩ | hQ
    · exact Or.inl ⟨E, ⟨eqToIso hE⟩⟩
    · exact Or.inr ⟨eqToIso hQ⟩
  simpa only [CondensedRing.localizingLowerShriek,
    CondensedRing.moduleObjectDerivedPullback] using
    restrictionLocal Λ ℓ k hcoeff f cf hf Ff _adjf

end AlgebraicGeometry.ProEtale
