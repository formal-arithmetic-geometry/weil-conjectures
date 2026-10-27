# AlgebraicGeometry.Etale.smallModel_isIso_strictHenselizationCohomologyComparison

## Reason

Complete the DIFFERENT retirement listed in coord/retire-items.tsv. The current
item has zero holes. Its unprefixed public theorem collides with the adopted
WeilConjectures theorem, which uses strictLocalization and strictLocalizationToBase.
The retained small-model theorem instead concerns strictHenselizationScheme and
strictHenselizationStructuralMap. Substitution of the upstream theorem would change
its four-factor canonical map. This distinction was checked against the H3 restoration
record and the A3 retirement of StrictLocalBaseChangeGlobalHomology.

Retain the complete original statement in the new module
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.CohomologyComparisonIso, with an explicit
smallModel_ theorem prefix. Withdraw the ambiguous module. This follows the already
landed A3 predecessor repair. Every binder, category, scheme, structural morphism,
comparison factor and public import is preserved in the retained module. The public theorem receives its distinct
name. In response to return 95339d037, the duplicate private theorem
map_mate_eq_mappedMate is removed entirely: its sole use becomes
`change IsIso (mappedMate _ _ _ _ _ _)`, a definitional conversion. The upstream
helper is private, and no copy of its statement is needed. The four-factor argument
and the small-model base-change dependency are preserved.
No adopted-source module or target statement changes. No definition is weakened.

## Old

The current module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.ExactGlobalSectionsLeray
public import Sheaf.AlgebraicGeometry.StrictHenselizationSchemeSectionsExact
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.BaseChangeGlobalHomology

/-! # Invertibility of the strict-local cohomology comparison

Source: Stacks Project, Tag 03Q9.

The original small-colimit strict henselization is retained. The canonical comparison
is displayed explicitly using the general exact-global-sections Leray construction;
its former specialized definition was withdrawn.
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

-- Keep projection reduction behind an equality proved with abstract categorical data.
private noncomputable def mappedMate
    {C D E A B T : Type*} [Category C] [Category D] [Category E]
    [Category A] [Category B] [Category T]
    {G : C ⥤ E} {H : D ⥤ A} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ A} {R₂ : A ⥤ E}
    (P : E ⥤ B) (Q : B ⥤ T) (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (sq : TwoSquare G L₁ L₂ H) (K : D) :
    Q.obj (P.obj ((R₁ ⋙ G).obj K)) ⟶ Q.obj (P.obj ((H ⋙ R₂).obj K)) :=
  Q.map (P.map ((mateEquiv a b sq).natTrans.app K))

private theorem map_mate_eq_mappedMate
    {C D E A B T : Type*} [Category C] [Category D] [Category E]
    [Category A] [Category B] [Category T]
    {G : C ⥤ E} {H : D ⥤ A} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ A} {R₂ : A ⥤ E}
    (P : E ⥤ B) (Q : B ⥤ T) (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (sq : TwoSquare G L₁ L₂ H) (K : D) :
    Q.map (P.map ((mateEquiv a b sq).natTrans.app K)) =
      mappedMate P Q a b sq K := rfl

-- Transport at the level of the square, before projecting the derived mate.
private theorem isIso_globalHomology_of_data
    {X S : Scheme.{w}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}))
    (n : ℤ)
    (E : Sheaf (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{w + 1} ⥤ AddCommGrpCat.{w + 1})
    (H : DerivedCategory.Plus
      (Sheaf (Scheme.strictHenselizationScheme s).smallEtaleTopology AddCommGrpCat.{w + 1}) ⥤
        Sheaf (Scheme.strictHenselizationScheme s).smallEtaleTopology AddCommGrpCat.{w + 1})
    (a : (upperStar AddCommGrpCat.{w + 1} f).mapDerivedCategoryPlus ⊣
      (lowerStar AddCommGrpCat.{w + 1} f).rightDerivedFunctorPlus)
    (b : (upperStar AddCommGrpCat.{w + 1}
        (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).mapDerivedCategoryPlus ⊣
      (lowerStar AddCommGrpCat.{w + 1}
        (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).rightDerivedFunctorPlus)
    (t : TwoSquare
        (upperStar AddCommGrpCat.{w + 1}
          (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus
        (upperStar AddCommGrpCat.{w + 1} f).mapDerivedCategoryPlus
        (upperStar AddCommGrpCat.{w + 1}
          (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).mapDerivedCategoryPlus
        (upperStar AddCommGrpCat.{w + 1}
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).mapDerivedCategoryPlus)
    (hE : E = Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{w + 1})
    (hH : H = DerivedCategory.Plus.homologyFunctor _ n)
    (ha : a = (upperStarLowerStarAdjunction AddCommGrpCat.{w + 1} f).derivedPlus)
    (hb : b = (upperStarLowerStarAdjunction AddCommGrpCat.{w + 1}
        (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus)
    (ht : t = TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{w + 1}
        (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom) :
    IsIso (mappedMate H E a b t K) := by
  subst E H a b t
  delta mappedMate
  exact smallModel_isIso_strictHenselization_baseChange_globalHomology f s K n

/-- The cohomology comparison in the unrestricted stalk formula is invertible.
Source: Stacks Project, Tag 03Q9; this intermediate packages the compatibility of the
strict-local base-change mate, Leray comparison, and exact inverse-image identifications.
(blueprint: lem-weil-pbc-unrestricted-strict-henselization-stalk-comparison).

Proof: apply strict-local base-change on global homology to the single complex F[0].
The displayed comparison is the composite of four maps: global sections of the exact
inverse-image/homology isomorphism; global sections of the homology of the derived
base-change mate; the strict-local Leray homology isomorphism; and cohomology of the
inverse-image/single-complex isomorphism. The second factor is invertible by the
strict-local base-change theorem; the other three are images of isomorphisms under
functors. Thus their composite is invertible. This holds for q = 0 and higher q,
including zero sheaves and empty X, and requires no torsion hypothesis.
-/
theorem isIso_strictHenselizationCohomologyComparison
    {X S : Scheme.{w}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω]
    (xbar : Spec (.of Ω) ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}) (q : ℕ) :
    IsIso
      ((Sheaf.Γ (Scheme.strictHenselizationScheme xbar).smallEtaleTopology
          AddCommGrpCat.{w + 1}).map
          ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
            (upperStar AddCommGrpCat.{w + 1} (Scheme.strictHenselizationStructuralMap xbar))
            (q : ℤ)).hom.app _) ≫
        (Sheaf.Γ (Scheme.strictHenselizationScheme xbar).smallEtaleTopology
          AddCommGrpCat.{w + 1}).map
          ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
            ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{w + 1} f).derivedPlus
              (upperStarLowerStarAdjunction AddCommGrpCat.{w + 1}
                (pullback.snd f (Scheme.strictHenselizationStructuralMap xbar))).derivedPlus
              (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{w + 1}
                (IsPullback.of_hasPullback f
                  (Scheme.strictHenselizationStructuralMap xbar)).toCommSq).hom))
                |>.natTrans.app
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≫
        (exactGlobalSectionsLerayHomologyIso
          (strictHenselizationScheme_globalSections_preservesFiniteColimits xbar)
          (pullback.snd f (Scheme.strictHenselizationStructuralMap xbar)) (q : ℤ) _).hom ≫
        (cohomology AddCommGrpCat.{w + 1}
          (pullback f (Scheme.strictHenselizationStructuralMap xbar)) (q : ℤ)).map
          (DerivedCategory.Plus.ι.map
            ((Functor.mapDerivedCategoryPlusSingleFunctor
              (upperStar AddCommGrpCat.{w + 1}
                (pullback.fst f (Scheme.strictHenselizationStructuralMap xbar))) 0).hom.app
                  F))) := by
  refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ ?_))
  · infer_instance
  · rw [map_mate_eq_mappedMate]
    apply isIso_globalHomology_of_data
    · rfl
    · rfl
    · rfl
    · rfl
    · apply congrArg (fun e : _ ≅ _ ↦ TwoSquare.mk _ _ _ _ e.hom)
      apply congrArg (pullbackSquareComparison AddCommGrpCat.{w + 1})
      exact Subsingleton.elim _ _
  · infer_instance
  · infer_instance

end AlgebraicGeometry.Etale
```

## New

The retained module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.ExactGlobalSectionsLeray
public import Sheaf.AlgebraicGeometry.StrictHenselizationSchemeSectionsExact
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.BaseChangeGlobalHomology

/-! # Invertibility of the strict-local cohomology comparison

Source: Stacks Project, Tag 03Q9.

The original small-colimit strict henselization is retained. The canonical comparison
is displayed explicitly using the general exact-global-sections Leray construction;
its former specialized definition was withdrawn. The explicit `smallModel_` name avoids
a collision with the adopted theorem on `strictLocalization`.
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

-- Package the projected mate using abstract categorical data.
private noncomputable def mappedMate
    {C D E A B T : Type*} [Category C] [Category D] [Category E]
    [Category A] [Category B] [Category T]
    {G : C ⥤ E} {H : D ⥤ A} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ A} {R₂ : A ⥤ E}
    (P : E ⥤ B) (Q : B ⥤ T) (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (sq : TwoSquare G L₁ L₂ H) (K : D) :
    Q.obj (P.obj ((R₁ ⋙ G).obj K)) ⟶ Q.obj (P.obj ((H ⋙ R₂).obj K)) :=
  Q.map (P.map ((mateEquiv a b sq).natTrans.app K))

-- Transport at the level of the square, before projecting the derived mate.
private theorem isIso_globalHomology_of_data
    {X S : Scheme.{w}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}))
    (n : ℤ)
    (E : Sheaf (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{w + 1} ⥤ AddCommGrpCat.{w + 1})
    (H : DerivedCategory.Plus
      (Sheaf (Scheme.strictHenselizationScheme s).smallEtaleTopology AddCommGrpCat.{w + 1}) ⥤
        Sheaf (Scheme.strictHenselizationScheme s).smallEtaleTopology AddCommGrpCat.{w + 1})
    (a : (upperStar AddCommGrpCat.{w + 1} f).mapDerivedCategoryPlus ⊣
      (lowerStar AddCommGrpCat.{w + 1} f).rightDerivedFunctorPlus)
    (b : (upperStar AddCommGrpCat.{w + 1}
        (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).mapDerivedCategoryPlus ⊣
      (lowerStar AddCommGrpCat.{w + 1}
        (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).rightDerivedFunctorPlus)
    (t : TwoSquare
        (upperStar AddCommGrpCat.{w + 1}
          (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus
        (upperStar AddCommGrpCat.{w + 1} f).mapDerivedCategoryPlus
        (upperStar AddCommGrpCat.{w + 1}
          (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).mapDerivedCategoryPlus
        (upperStar AddCommGrpCat.{w + 1}
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).mapDerivedCategoryPlus)
    (hE : E = Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{w + 1})
    (hH : H = DerivedCategory.Plus.homologyFunctor _ n)
    (ha : a = (upperStarLowerStarAdjunction AddCommGrpCat.{w + 1} f).derivedPlus)
    (hb : b = (upperStarLowerStarAdjunction AddCommGrpCat.{w + 1}
        (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus)
    (ht : t = TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{w + 1}
        (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom) :
    IsIso (mappedMate H E a b t K) := by
  subst E H a b t
  delta mappedMate
  exact smallModel_isIso_strictHenselization_baseChange_globalHomology f s K n

/-- The cohomology comparison in the unrestricted stalk formula is invertible.
Source: Stacks Project, Tag 03Q9; this intermediate packages the compatibility of the
strict-local base-change mate, Leray comparison, and exact inverse-image identifications.
(blueprint: lem-weil-pbc-unrestricted-strict-henselization-stalk-comparison).

Proof: apply strict-local base-change on global homology to the single complex F[0].
The displayed comparison is the composite of four maps: global sections of the exact
inverse-image/homology isomorphism; global sections of the homology of the derived
base-change mate; the strict-local Leray homology isomorphism; and cohomology of the
inverse-image/single-complex isomorphism. The second factor is invertible by the
strict-local base-change theorem; the other three are images of isomorphisms under
functors. Thus their composite is invertible. This holds for q = 0 and higher q,
including zero sheaves and empty X, and requires no torsion hypothesis.
-/
theorem smallModel_isIso_strictHenselizationCohomologyComparison
    {X S : Scheme.{w}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω]
    (xbar : Spec (.of Ω) ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}) (q : ℕ) :
    IsIso
      ((Sheaf.Γ (Scheme.strictHenselizationScheme xbar).smallEtaleTopology
          AddCommGrpCat.{w + 1}).map
          ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
            (upperStar AddCommGrpCat.{w + 1} (Scheme.strictHenselizationStructuralMap xbar))
            (q : ℤ)).hom.app _) ≫
        (Sheaf.Γ (Scheme.strictHenselizationScheme xbar).smallEtaleTopology
          AddCommGrpCat.{w + 1}).map
          ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
            ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{w + 1} f).derivedPlus
              (upperStarLowerStarAdjunction AddCommGrpCat.{w + 1}
                (pullback.snd f (Scheme.strictHenselizationStructuralMap xbar))).derivedPlus
              (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{w + 1}
                (IsPullback.of_hasPullback f
                  (Scheme.strictHenselizationStructuralMap xbar)).toCommSq).hom))
                |>.natTrans.app
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≫
        (exactGlobalSectionsLerayHomologyIso
          (strictHenselizationScheme_globalSections_preservesFiniteColimits xbar)
          (pullback.snd f (Scheme.strictHenselizationStructuralMap xbar)) (q : ℤ) _).hom ≫
        (cohomology AddCommGrpCat.{w + 1}
          (pullback f (Scheme.strictHenselizationStructuralMap xbar)) (q : ℤ)).map
          (DerivedCategory.Plus.ι.map
            ((Functor.mapDerivedCategoryPlusSingleFunctor
              (upperStar AddCommGrpCat.{w + 1}
                (pullback.fst f (Scheme.strictHenselizationStructuralMap xbar))) 0).hom.app
                  F))) := by
  refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ ?_))
  · infer_instance
  · change IsIso (mappedMate _ _ _ _ _ _)
    apply isIso_globalHomology_of_data
    · rfl
    · rfl
    · rfl
    · rfl
    · apply congrArg (fun e : _ ≅ _ ↦ TwoSquare.mk _ _ _ _ e.hom)
      apply congrArg (pullbackSquareComparison AddCommGrpCat.{w + 1})
      exact Subsingleton.elim _ _
  · infer_instance
  · infer_instance

end AlgebraicGeometry.Etale
```

The old module is withdrawn through deleted.txt. The comparison DAG node keeps
its mathematical statement, proof_deps, source and unit. Its lean attachment and
declaration name follow the retained realization, and the proof text records the
definitional conversion replacing the removed duplicate equality theorem. No new node is
needed, since the result and complete proof are precisely the existing result.

## Users

The current source and quarantine census finds no direct Lean importer of the item
and no external use of its declaration. tools/downstream.py reports zero downstream
modules. The only DAG parent is lem-weil-pbc-unrestricted-strict-henselization-stalk:
its proof_deps and step 3 retain the comparison node, which now points to the retained
small-model theorem. This is not pruning on the basis of zero imports; the full
replacement argument is preserved in this delivery. No parent edge is removed.

The listed historical Sheaf parent is already an empty withdrawn module, not a
quarantined source. Its stale Lean attachment is not used to authorize discarding
the small-model mathematics. The actual adopted parent imports the upstream twin
and applies the unprefixed theorem on strictLocalization. It stays verbatim.
The compiler compatibility probe imports both the retained theorem and this adopted
parent, checks all three theorem names, and applies the adopted comparison theorem.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | B5 | Withdraw the ambiguous module; preserve its complete theorem in the row below. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.CohomologyComparisonIso | new in B5 delivery | Same original-model signature and four-factor proof, with explicit smallModel_ name; duplicate reflexivity helper removed. |
| Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk | already withdrawn; no live claim | No imports or declarations to adapt; its DAG comparison dependency remains realized. |
| WeilConjectures.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk | adopted source; unchanged | Continues using the adopted unprefixed comparison theorem. Compatibility checked together with the retained small-model theorem. |

The unit sk-thm-br has empty realized statement and step entries. No unit route
or target meaning is changed. None of the small-model proof dependencies is claimed
unnecessary, since they remain imported by the retained module.

## Status

landed 20261023T230432-L-3425705 2026-10-23 (merge of deliver/B5/Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso)
