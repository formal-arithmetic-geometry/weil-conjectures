# Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary

## Reason

The stage-3 preflight requests a change record for additional local proof-context
commands. They keep the concrete derived-localization and sheaf-operation terms
abstract during elaboration of the completed triangle comparison. The final module
compiles cleanly in 49.4 seconds. This record documents scope, rather than a change
to any mathematical statement or definition.

All fourteen existing public declaration signatures, existing definition bodies,
and public imports are unchanged. The six theorem proof bodies are completed.
Every new helper is private and fully proved or is a private real-data construction.
There is no new public declaration, global instance, simp attribute or notation.
Only the assigned Sheaf module is changed; no source-library file is modified.

## Old

The original proof context begins, verbatim:

```lean
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A] [hA : Finite A]
```

The six original theorem signatures are, verbatim:

```lean
theorem supportGlobalOpenSectionIso_naturality {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j]
    {M N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)} (f : M ⟶ N) :
    (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 U))).map
        ((upperStar (ModuleCat.{u + 1} A) j).map f) ≫
        (supportGlobalOpenSectionIso A j N).hom =
      (supportGlobalOpenSectionIso A j M).hom ≫
        (supportGlobalEvaluation A (Scheme.ProEt.mk j)).map f

theorem supportGlobalRestriction_zero {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    Sheaf.supportedSectionsInclusion (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
        (supportGlobalRestriction j) ≫
      (sheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
        (supportGlobalRestriction j).op = 0

theorem supportGlobalModels_kInjective
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] :
    I.obj.IsKInjective ∧
      (supportedSectionsComplex A i j hPair I.obj).IsKInjective ∧
      CochainComplex.IsKInjective (supportCComplex A j I.obj)

theorem supportGlobalTriangleComparison
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] :
    ∃ (hR : (supportGlobalRow A j I).ShortExact)
      (hq : IsIso (DerivedCategory.Q.map (supportConeQuotient A i j hPair I.obj)))
      (hqR : IsIso (DerivedCategory.Q.map
        (CochainComplex.mappingCone.descShortComplex (supportGlobalRow A j I))))
      (a : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).obj (supportedSectionsComplex A i j hPair I.obj)) ≅
          (supportGlobalRow A j I).X₁)
      (b : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).obj (supportCComplex A j I.obj)) ≅ (supportGlobalRow A j I).X₃),
      a.hom ≫ (supportGlobalRow A j I).f =
        ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
          (.up ℤ)).map (supportModelSequence A i j hPair I.obj).f ∧
      ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
          (.up ℤ)).map (supportModelSequence A i j hPair I.obj).g ≫ b.hom =
        (supportGlobalRow A j I).g ∧
      ∃ e : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).rightDerivedFunctor
          ).mapTriangle.obj (supportModelTriangle A i j hPair I.obj hq)) ≅
            supportSequenceTriangle (supportGlobalRow A j I) hqR,
        e.hom.hom₁ =
          (supportGlobalUnitIso A (supportedSectionsComplex A i j hPair I.obj)
            (supportGlobalModels_kInjective A i j hPair I).2.1).hom ≫
              DerivedCategory.Q.map a.hom ∧
        e.hom.hom₂ = (supportGlobalUnitIso A I.obj
          (supportGlobalModels_kInjective A i j hPair I).1).hom ∧
        e.hom.hom₃ = (supportGlobalUnitIso A (supportCComplex A j I.obj)
          (supportGlobalModels_kInjective A i j hPair I).2.2).hom ≫
            DerivedCategory.Q.map b.hom ∧
        ∀ q : ℤ,
          DerivedCategory.HomologySequence.δ
              (supportSequenceTriangle (supportGlobalRow A j I) hqR) q (q + 1) rfl =
            (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A) q).hom.app
                (supportGlobalRow A j I).X₃ ≫
              hR.δ q (q + 1) rfl ≫
              (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A)
                (q + 1)).inv.app (supportGlobalRow A j I).X₁

theorem supportGlobalComparisonNatural
    (I J : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)] (f : I ⟶ J)
    (aI : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
      (.up ℤ)).obj (supportedSectionsComplex A i j hPair I.obj)) ≅
        (supportGlobalRow A j I).X₁)
    (aJ : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
      (.up ℤ)).obj (supportedSectionsComplex A i j hPair J.obj)) ≅
        (supportGlobalRow A j J).X₁)
    (bI : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
      (.up ℤ)).obj (supportCComplex A j I.obj)) ≅ (supportGlobalRow A j I).X₃)
    (bJ : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
      (.up ℤ)).obj (supportCComplex A j J.obj)) ≅ (supportGlobalRow A j J).X₃)
    (_haI : aI.hom ≫ (supportGlobalRow A j I).f =
      ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportModelSequence A i j hPair I.obj).f)
    (_haJ : aJ.hom ≫ (supportGlobalRow A j J).f =
      ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportModelSequence A i j hPair J.obj).f)
    (_hbI : ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportModelSequence A i j hPair I.obj).g ≫ bI.hom =
          (supportGlobalRow A j I).g)
    (_hbJ : ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportModelSequence A i j hPair J.obj).g ≫ bJ.hom =
          (supportGlobalRow A j J).g) :
    ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportAMap A i j hPair f.hom) ≫ aJ.hom =
      aI.hom ≫ ((Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A) (supportGlobalRestriction j)).mapHomologicalComplex
          (.up ℤ)).map f.hom ∧
    ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportCMap A j f.hom) ≫ bJ.hom =
      bI.hom ≫ ((supportGlobalEvaluation A (Scheme.ProEt.mk j)).mapHomologicalComplex
        (.up ℤ)).map f.hom

theorem supportGlobalBoundaryNormalization :
    ∃ δ : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A) (supportGlobalRestriction j) ⊤,
      Sheaf.SupportSequenceExact (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} A) (supportGlobalRestriction j) ⊤ δ ∧
      ∀ (I : CochainComplex.Plus
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
        [∀ n : ℤ, Injective (I.obj.X n)],
        ∃ hR : (supportGlobalRow A j I).ShortExact,
          (∀ (K : DerivedCategory.Plus
              (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
            (e : DerivedCategory.Plus.Q.obj I ≅ K) (q : ℤ),
            (Sheaf.supportSequenceModelIso _ _
              (supportGlobalEvaluation A (Scheme.ProEt.mk j)) I K e q).hom ≫
                (δ q).app ⟨K, trivial⟩ ≫
                (Sheaf.supportSequenceModelIso _ _
                  (Sheaf.supportedSectionsFunctor _ _ (supportGlobalRestriction j))
                  I K e (q + 1)).inv = hR.δ q (q + 1) rfl) ∧
          (∀ (q : ℤ) (c : (supportGlobalRow A j I).X₃.X q)
            (hc : (supportGlobalRow A j I).X₃.d q (q + 1) c = 0)
            (b : (supportGlobalRow A j I).X₂.X q)
            (_hb : (supportGlobalRow A j I).g.f q b = c),
            ∃ (a : (supportGlobalRow A j I).X₁.X (q + 1))
              (ha : (supportGlobalRow A j I).X₁.d (q + 1) (q + 1 + 1) a = 0),
              (supportGlobalRow A j I).f.f (q + 1) a =
                (supportGlobalRow A j I).X₂.d q (q + 1) b ∧
              hR.δ q (q + 1) rfl
                ((supportGlobalRow A j I).X₃.homologyπ q
                  ((supportGlobalRow A j I).X₃.cyclesMk c (q + 1) (by simp) hc)) =
                (supportGlobalRow A j I).X₁.homologyπ (q + 1)
                  ((supportGlobalRow A j I).X₁.cyclesMk a (q + 1 + 1) (by simp) ha))
```

Each original theorem body is `by sorry`.

## New

The same six theorem signatures remain verbatim:

```lean
theorem supportGlobalOpenSectionIso_naturality {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j]
    {M N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)} (f : M ⟶ N) :
    (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 U))).map
        ((upperStar (ModuleCat.{u + 1} A) j).map f) ≫
        (supportGlobalOpenSectionIso A j N).hom =
      (supportGlobalOpenSectionIso A j M).hom ≫
        (supportGlobalEvaluation A (Scheme.ProEt.mk j)).map f

theorem supportGlobalRestriction_zero {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    Sheaf.supportedSectionsInclusion (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
        (supportGlobalRestriction j) ≫
      (sheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
        (supportGlobalRestriction j).op = 0

theorem supportGlobalModels_kInjective
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] :
    I.obj.IsKInjective ∧
      (supportedSectionsComplex A i j hPair I.obj).IsKInjective ∧
      CochainComplex.IsKInjective (supportCComplex A j I.obj)

theorem supportGlobalTriangleComparison
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] :
    ∃ (hR : (supportGlobalRow A j I).ShortExact)
      (hq : IsIso (DerivedCategory.Q.map (supportConeQuotient A i j hPair I.obj)))
      (hqR : IsIso (DerivedCategory.Q.map
        (CochainComplex.mappingCone.descShortComplex (supportGlobalRow A j I))))
      (a : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).obj (supportedSectionsComplex A i j hPair I.obj)) ≅
          (supportGlobalRow A j I).X₁)
      (b : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).obj (supportCComplex A j I.obj)) ≅ (supportGlobalRow A j I).X₃),
      a.hom ≫ (supportGlobalRow A j I).f =
        ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
          (.up ℤ)).map (supportModelSequence A i j hPair I.obj).f ∧
      ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
          (.up ℤ)).map (supportModelSequence A i j hPair I.obj).g ≫ b.hom =
        (supportGlobalRow A j I).g ∧
      ∃ e : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).rightDerivedFunctor
          ).mapTriangle.obj (supportModelTriangle A i j hPair I.obj hq)) ≅
            supportSequenceTriangle (supportGlobalRow A j I) hqR,
        e.hom.hom₁ =
          (supportGlobalUnitIso A (supportedSectionsComplex A i j hPair I.obj)
            (supportGlobalModels_kInjective A i j hPair I).2.1).hom ≫
              DerivedCategory.Q.map a.hom ∧
        e.hom.hom₂ = (supportGlobalUnitIso A I.obj
          (supportGlobalModels_kInjective A i j hPair I).1).hom ∧
        e.hom.hom₃ = (supportGlobalUnitIso A (supportCComplex A j I.obj)
          (supportGlobalModels_kInjective A i j hPair I).2.2).hom ≫
            DerivedCategory.Q.map b.hom ∧
        ∀ q : ℤ,
          DerivedCategory.HomologySequence.δ
              (supportSequenceTriangle (supportGlobalRow A j I) hqR) q (q + 1) rfl =
            (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A) q).hom.app
                (supportGlobalRow A j I).X₃ ≫
              hR.δ q (q + 1) rfl ≫
              (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A)
                (q + 1)).inv.app (supportGlobalRow A j I).X₁

theorem supportGlobalComparisonNatural
    (I J : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)] (f : I ⟶ J)
    (aI : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
      (.up ℤ)).obj (supportedSectionsComplex A i j hPair I.obj)) ≅
        (supportGlobalRow A j I).X₁)
    (aJ : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
      (.up ℤ)).obj (supportedSectionsComplex A i j hPair J.obj)) ≅
        (supportGlobalRow A j J).X₁)
    (bI : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
      (.up ℤ)).obj (supportCComplex A j I.obj)) ≅ (supportGlobalRow A j I).X₃)
    (bJ : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
      (.up ℤ)).obj (supportCComplex A j J.obj)) ≅ (supportGlobalRow A j J).X₃)
    (_haI : aI.hom ≫ (supportGlobalRow A j I).f =
      ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportModelSequence A i j hPair I.obj).f)
    (_haJ : aJ.hom ≫ (supportGlobalRow A j J).f =
      ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportModelSequence A i j hPair J.obj).f)
    (_hbI : ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportModelSequence A i j hPair I.obj).g ≫ bI.hom =
          (supportGlobalRow A j I).g)
    (_hbJ : ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportModelSequence A i j hPair J.obj).g ≫ bJ.hom =
          (supportGlobalRow A j J).g) :
    ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportAMap A i j hPair f.hom) ≫ aJ.hom =
      aI.hom ≫ ((Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A) (supportGlobalRestriction j)).mapHomologicalComplex
          (.up ℤ)).map f.hom ∧
    ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportCMap A j f.hom) ≫ bJ.hom =
      bI.hom ≫ ((supportGlobalEvaluation A (Scheme.ProEt.mk j)).mapHomologicalComplex
        (.up ℤ)).map f.hom

theorem supportGlobalBoundaryNormalization :
    ∃ δ : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A) (supportGlobalRestriction j) ⊤,
      Sheaf.SupportSequenceExact (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} A) (supportGlobalRestriction j) ⊤ δ ∧
      ∀ (I : CochainComplex.Plus
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
        [∀ n : ℤ, Injective (I.obj.X n)],
        ∃ hR : (supportGlobalRow A j I).ShortExact,
          (∀ (K : DerivedCategory.Plus
              (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
            (e : DerivedCategory.Plus.Q.obj I ≅ K) (q : ℤ),
            (Sheaf.supportSequenceModelIso _ _
              (supportGlobalEvaluation A (Scheme.ProEt.mk j)) I K e q).hom ≫
                (δ q).app ⟨K, trivial⟩ ≫
                (Sheaf.supportSequenceModelIso _ _
                  (Sheaf.supportedSectionsFunctor _ _ (supportGlobalRestriction j))
                  I K e (q + 1)).inv = hR.δ q (q + 1) rfl) ∧
          (∀ (q : ℤ) (c : (supportGlobalRow A j I).X₃.X q)
            (hc : (supportGlobalRow A j I).X₃.d q (q + 1) c = 0)
            (b : (supportGlobalRow A j I).X₂.X q)
            (_hb : (supportGlobalRow A j I).g.f q b = c),
            ∃ (a : (supportGlobalRow A j I).X₁.X (q + 1))
              (ha : (supportGlobalRow A j I).X₁.d (q + 1) (q + 1 + 1) a = 0),
              (supportGlobalRow A j I).f.f (q + 1) a =
                (supportGlobalRow A j I).X₂.d q (q + 1) b ∧
              hR.δ q (q + 1) rfl
                ((supportGlobalRow A j I).X₃.homologyπ q
                  ((supportGlobalRow A j I).X₃.cyclesMk c (q + 1) (by simp) hc)) =
                (supportGlobalRow A j I).X₁.homologyπ (q + 1)
                  ((supportGlobalRow A j I).X₁.cyclesMk a (q + 1 + 1) (by simp) ha))
```

The additional principal proof-context commands are:

```lean
set_option linter.unusedSectionVars false
open CategoryTheory.Abelian
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorPlus
  DerivedCategory.Q DerivedCategory.Qh DerivedCategory.quotientCompQhIso

attribute [local irreducible] globalDerivedTriangleIso
attribute [local irreducible] globalTransportTriangleIso
attribute [local irreducible] convertSequenceTriangleIso
attribute [local irreducible] shortComplexIsoFromQuotient

section TriangleComparison
attribute [local irreducible] upperStar lowerStar upperStarLowerStarAdjunction
  globalDerivedTriangleIso globalTransportTriangleIso globalSequenceTriangleIso
  shortComplexIsoFromQuotient
  Functor.rightDerivedFunctorObjQIso supportedSectionsComplex supportCComplex
  supportModelInclusion
set_option maxRecDepth 2048 in
-- The unchanged statement and completed proof of supportGlobalTriangleComparison follow.
end TriangleComparison
```

The generic private-helper sections introduce their own category, module and universe
variables, which end with their respective sections. `GlobalIntegerBoundary` also
opens `CategoryTheory.Category` locally. Two additional universe names support the
private free-presheaf restriction-surjectivity argument. None enters an original
public signature.

Where needed, individual declarations use the declaration-scoped elaboration options
`backward.isDefEq.respectTransparency false` and `backward.defeqAttrib.useBackward true`.
The recursion-depth option is scoped to the triangle-comparison theorem; the heartbeat
and compiler time limits are unchanged. The unused-section-variable linter is disabled
in this file because the original ambient finite-coefficient hypotheses remain in scope.
Every added reducibility attribute explicitly says `local`; none is exported to importers.
All original real-data definitions are retained. No target meaning changes and no
statement review is reopened.

## Users

`python3 -B tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary
--uses supportGlobalOpenSectionIso_naturality supportGlobalRestriction_zero
supportGlobalModels_kInjective supportGlobalTriangleComparison
supportGlobalComparisonNatural supportGlobalBoundaryNormalization` reports zero
current Lean importers. Its declaration-use search finds only the assigned module
for each name. Thus no current consumer needs adaptation or acquires a different
statement. This is a source/interface check; no downstream build was run.

The DAG references in `lem-pur-retracted-support-localization-comparison` and
`def-pur-support-triangle` remain; zero current Lean importers is not treated as
withdrawal permission. The assigned module, its declarations, and the unit route
are retained. No other group's module is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary | K9 | Six proofs completed; all existing signatures and definition bodies unchanged. |

## Status

landed 20261021T214826-L-1862675 2026-10-21 (merge of deliver/K9/Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary)
