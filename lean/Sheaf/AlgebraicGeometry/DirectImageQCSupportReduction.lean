/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Quasi-compact reduction for a proper-support complex

Source: literature/stacks-project/perfect.tex, Tag 08EV, label
`perfect-lemma-perfect-direct-image`, proof from “Let T be the union...” through
“Thus we may replace X by X'' (blueprint: lem-pc-direct-image-qc-support-reduction).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A quasi-compact open containing every cohomological support preserves the derived
 direct image via the adjunction unit and the canonical composition comparison.
Source: Stacks Project, Tag 08EV, `perfect-lemma-perfect-direct-image`.
(blueprint: lem-pc-direct-image-qc-support-reduction)

Proof:
1. Boundedness leaves only finitely many nonzero cohomology sheaves. Their closed supports
   have proper union T by lem-weil-pbc-closed-subset-proper-over-base-union-preimage (1).
2. The reduced induced closed subscheme on T is proper over the Noetherian base, hence
   quasi-compact, by def-weil-pbc-closed-subset-proper-over-base and
   lem-weil-pbc-qcqs-morphism-permanence (2). Apply
   lemma-nagata-immersion-shrink-to-closed-exists to obtain a quasi-compact open U containing
   T. By pqf-lem-locnoeth-lft, X and U are locally Noetherian. Thus U and S are
   quasi-separated by lem-weil-pbc-locally-noetherian-quasi-separated, and U -> S is
   quasi-compact and quasi-separated by lem-weil-pbc-qcqs-morphism-permanence (1).
3. By lem-pc-supported-open-pushforward, the adjunction unit E -> Rj_*j^*E is invertible.
   Applying Rf_* and the comparison of
   lem-pc-ringed-spaces-derived-direct-image-composition gives the asserted canonical
   isomorphism and its inverse.

The open immersion is U.ι and j^* is the shared exact derived open restriction.
The comparison c is characterized by compatibility with right-derived units. The
additivity witness only transports the equivalence between the shared category instances.
The adjunction is supplied as data: invertibility of its unit is independent of the choice
of adjunction between these fixed functors, so it includes the canonical adjunction.
-/
theorem directImage_qc_support_reduction
    {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsNoetherian S]
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E))
    (hcoherent : ∀ n : ℤ,
      RingedSpace.IsCoherent X.toRingedSpace
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E))
    (hsupport : ∀ n : ℤ,
      Scheme.Modules.HasSupportProperOver f
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E)) :
    ∃ U : X.Opens,
      IsCompact (U : Set X) ∧ QuasiCompact U.ι ∧
      QuasiCompact (U.ι ≫ f) ∧ QuasiSeparated (U.ι ≫ f) ∧
      (∀ (n : ℤ) (x : X),
        ¬ Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E).val.presheaf x) →
        x ∈ U) ∧
      ∃ (_ : (Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U)).Additive),
      ∃ adj :
        (SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι,
      ∃ c : schemeDerivedDirectImage U.ι ⋙ schemeDerivedDirectImage f ≅
          schemeDerivedDirectImage (U.ι ≫ f),
        (∀ K : HomotopyCategory
            (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) (ComplexShape.up ℤ),
          (RingedSpace.moduleDirectImage (U.ι ≫ f).toLRSHom.toShHom).rightDerivedFunctorUnit.app
              K ≫ c.inv.app (DerivedCategory.Qh.obj K) =
            (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app
                (((RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom).mapHomotopyCategory
                  (ComplexShape.up ℤ)).obj K) ≫
              (schemeDerivedDirectImage f).map
                ((RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom).rightDerivedFunctorUnit.app
                  K)) ∧
        IsIso ((schemeDerivedDirectImage f).map (adj.unit.app E) ≫
          c.hom.app
            ((SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U ⋙
              Equivalence.functor
                (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
                (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj E)) ∧
        Nonempty ((schemeDerivedDirectImage (U.ι ≫ f)).obj
            ((SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U ⋙
              Equivalence.functor
                (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
                (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj E) ≅
          (schemeDerivedDirectImage f).obj E) := by
  sorry

end AlgebraicGeometry
