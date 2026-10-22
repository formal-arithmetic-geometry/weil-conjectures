# AlgebraicGeometry.trfConstantClosureGenerators

## Reason

Restore the module assigned in coord/rework.tsv from
quarantine/Sheaf/Paper/TrfDevissageGeneration.lean. The preserved source fails its
single-file server compile at line 124 with:

```
error(lean.unknownIdentifier): Unknown identifier `LocallyClosedStratification`
```

The landed record coord/changes/F9-retire-locally-closed-stratification.md gives
the retired definition verbatim:

```lean
abbrev LocallyClosedStratification (X : Scheme.{w}) := Stratification X
```

Expand that abbreviation in the constant-generator definition, as already done
in the current sfProEtaleClosureGenerators and sfEtaleClosureGenerators. This
preserves the old elaborated definition, including constructibility of the
strata, their scheme realizations, the actual scheme-theoretic closure, the
factorization equation and the constant regular module. In particular, this is
not a replacement by the distinct FiniteLocallyClosedStratification notion.
Empty schemes, empty strata, zero rings and non-Noetherian schemes retain the
same quantifiers and meaning. Neither theorem signature nor theorem body changes.

## Old

```lean
def trfConstantClosureGenerators (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    ObjectProperty (proEtaleDerivedCategory X A) :=
  fun K ↦ ∃ (str : LocallyClosedStratification X) (i : Fin str.n)
    (j : str.domain i ⟶ (str.immersion i).image) (_ : IsOpenImmersion j),
    j ≫ (str.immersion i).imageι = str.immersion i ∧
    Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((sfIntrinsicModuleEquivalence X A).functor.obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (str.immersion i).imageι).obj
          ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
            ((constantSheaf (ProEt.topology (str.domain i))
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
                (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))))))
```

## New

```lean
def trfConstantClosureGenerators (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    ObjectProperty (proEtaleDerivedCategory X A) :=
  fun K ↦ ∃ (str : Stratification X) (i : Fin str.n)
    (j : str.domain i ⟶ (str.immersion i).image) (_ : IsOpenImmersion j),
    j ≫ (str.immersion i).imageι = str.immersion i ∧
    Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((sfIntrinsicModuleEquivalence X A).functor.obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (str.immersion i).imageι).obj
          ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
            ((constantSheaf (ProEt.topology (str.domain i))
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
                (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))))))
```

## Users

`python3 tools/downstream.py Sheaf.Paper.TrfDevissageGeneration --allow-missing
--uses trfConstantClosureGenerators trf_devissage_generation
exists_trf_constant_coefficients_not_generating` reports zero downstream modules
and zero users of each declaration. A separate search of every Lean file under
lean/ and quarantine/ finds these module and declaration names only in the item's
archive. Thus there are no external Lean consumers to adapt.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.TrfDevissageGeneration | F3 | Restore the complete archived module; expand the retired alias in trfConstantClosureGenerators. Both theorem signatures and bodies are preserved. |

The DAG still has these mathematical parents; all retain their dependencies and
arguments without modification:

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.FiniteDualitySiteComparison | not adapted | Node lem-weil-finite-duality-site-comparison cites generation in proof step 5; the generation theorem is identical. |
| No Lean attachment: prop-trf-exceptional-kunneth | not adapted | Proof steps 11 and 14 retain their generation dependency and argument. |
| No Lean attachment: prop-trf-external-hom | not adapted | Proof steps 1 and 2 retain their generation dependency and argument. |

The node attachment and every dependency and proof step are preserved. Its lean.note
records the alias expansion. The unit sk-lem-sf-ctf-generation retains both the
generation assertion and the constant-coefficient obstruction. No target statement
or definition meaning changes, so this port creates no new semantic target-review
obligation. No source-library file or quarantine archive is changed or withdrawn.

The original source fails as above; the repaired complete module compiles through
lcompile.py in 7 seconds, with no errors or warnings. The existing generation proof
continues to compile unchanged. The one archived counterexample sorry is retained;
this repair closes zero holes and adds zero holes.

## Status

landed 20261022T002401-L-1923478 2026-10-22 (merge of deliver/F3/Sheaf.Paper.TrfDevissageGeneration)
