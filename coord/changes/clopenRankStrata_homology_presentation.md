# AlgebraicGeometry.clopenRankStrata_homology_presentation

## Reason

STATEMENT-DISPUTED: the former whole-object presentation is false. For a field k,
take Z=Y=Spec(k), i=id, rank function constantly 0, E_0=O_Z, and the other
rank terms zero. Put K=O_Z in degree 0 and n=-1. Its homology away from n has
exactly the prescribed values. Nevertheless H^-1(K)=0 and K is nonzero, so
the claimed isomorphism from H^-1(K) placed in degree -1 to K cannot exist.
The error is the assertion that the complement of the rank-n summand is acyclic.
It can carry all the other nonzero homology degrees.

Replace that conclusion by the actual intermediate step: a concentrated retract
whose homology projector fixes maps from the rank-n source. Every original
hypothesis is retained. The lifting theorem and all target signatures are unchanged.
This is a repair of a false intermediate statement, not a proof of its old statement.

## Old

```lean
theorem clopenRankStrata_homology_presentation
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i)))]
    (r : LocallyConstant Z ℕ)
    (E : ∀ n : ℕ, (Scheme.Modules.exteriorRankOpen r n).toScheme.Modules)
    (T : ℤ → Z.Modules)
    (hT : ∀ n : ℤ, T n = if 0 ≤ n then
      (Scheme.Modules.pushforward (Scheme.Modules.exteriorRankOpen r n.toNat).ι).obj
        (E n.toNat) else 0)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))
    (n : ℤ)
    (hother : ∀ m : ℤ, m ≠ n → Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) m).obj K ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj (T m))) :
    ∃ e : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj K) ≅ K,
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).inv.app
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj K) ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).map e.hom = 𝟙 _
```

## New

```lean
theorem clopenRankStrata_homology_presentation
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i)))]
    (r : LocallyConstant Z ℕ)
    (E : ∀ n : ℕ, (Scheme.Modules.exteriorRankOpen r n).toScheme.Modules)
    (T : ℤ → Z.Modules)
    (hT : ∀ n : ℤ, T n = if 0 ≤ n then
      (Scheme.Modules.pushforward (Scheme.Modules.exteriorRankOpen r n.toNat).ι).obj
        (E n.toNat) else 0)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))
    (n : ℤ)
    (hother : ∀ m : ℤ, m ≠ n → Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) m).obj K ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj (T m))) :
    ∃ (L : DerivedCategory
        (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))
      (ι : L ⟶ K) (π : K ⟶ L),
      ι ≫ π = 𝟙 L ∧
      (∀ m : ℤ, m ≠ n → IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) m).obj L)) ∧
      (∀ a : (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj (T n) ⟶
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj K,
        a ≫ (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).map π ≫
          (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).map ι = a)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ClopenRankStrataHomologyLift | S4 | The sole caller is the lifting theorem in this same item; its proof now uses the concentrated retract, and its existing signature and visibility stay identical. |
| Sheaf.AlgebraicGeometry.ClopenRankStrataFormality | unclaimed | Direct importer; does not mention the changed presentation declaration. Its use of clopenRankStrata_homology_lift is unchanged. |

The read-only downstream scan found 295 transitive importing modules and exactly
one module mentioning clopenRankStrata_homology_presentation: this item itself.
No downstream definition uses the changed lemma, and no target statement depends
on a changed definition. No module outside this item is adapted.
The presentation node has one DAG citer, the lifting node, delivered with the
revised proof and unchanged statement. The unit realized record contains no
statement or step node here, so this repair bypasses no unit step.

## Status

landed 20261013T033007-L-3678377 2026-10-13 (merge of deliver/S4/Sheaf.AlgebraicGeometry.ClopenRankStrataHomologyLift)
