# Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors

## Reason

Complete the retirement assigned in coord/queue.tsv and coord/retire-items.tsv under
the human's hand-off in coord/changes/retire-sheaf-twins-20261020.md. P2 already moved
the source factors to the canonical upstream construction; the item now has zero
declarations and zero holes. Recompiling this shim alone would not retire it.

During preparation G2's retirement landed as 20261025T060830-L-2376591. It withdrew
the duplicate evaluation, composite, and source/target formulas and reattached their
nodes to the complete canonical proofs. In particular, the canonical composite uses
the separate module pullback formula directly. Reconcile with that current source:
retain G2's withdrawals and node edits without copying or restoring any of them.

Two remaining source-factor consumers can also be retired. The combined pullback
formula has no Lean importer and no mathematical parent after G2's composite-node
update. Withdraw it and set its Lean attachment explicitly to null. Its former
abelian-factorization dependency remains mathematically needed by the target formula,
but the duplicate Sheaf abelian theorem is used only by the withdrawn combined file.
Attach that node to its complete canonical upstream proof and withdraw the copy.

The only remaining importer is the source-prefix compatibility shim. Its upstream
prefix already supplies the canonical source factors. Replace the withdrawn factor
shim import by the historical derived-pullback API import to preserve that API.
No adopted source file, target, construction or mathematical hypothesis is changed.
No unit statement or proof step is bypassed.

## Old

Assigned item, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceFactors
public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso

/-! The canonical upstream construction and the historical scalar-forgetting API.
The definitions are unchanged after unfolding the compatibility abbreviation.
(blueprint: def-sbc-raw-scalar-source-factors). -/

@[expose] public section
```

The source-prefix consumer contains:

```lean
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourcePrefix
public import Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors
```

The two retired duplicate signatures are:

`Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas`:

```lean
theorem rawModuleScalar_pullback_formulas
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    (rawModuleClassMorphism Λ k G (q : ℤ) U A
      ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z) =
      moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
        (Over.w_assoc f k) ((freeSheaf Λ S).obj U) ≫
      (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map
        (rawModuleClassMorphism Λ k G (q : ℤ) U B z) ≫
        moduleCoefficientFactorNative Λ G (q : ℤ) A B f) ∧
    (∀ (x : (abelianHigherDirectImageRawPresheaf (B.hom ≫ k) q
      (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) B)).obj
        (op U)),
      rawAbelianClassMorphism (A.hom ≫ k)
        (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) A) q U
        (abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
        (Over.w_assoc f k) q _ _
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app ((RawModuleScalarComparison.forget Λ W).obj G)) U x) =
      abelianSourceFactor f.left (B.hom ≫ k) (A.hom ≫ k)
        (Over.w_assoc f k) (RawModuleScalarComparison.freeAbelian S U) ≫
      (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map
        (rawAbelianClassMorphism (B.hom ≫ k)
          (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) B) q U x) ≫
      abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G)
        (q : ℤ) A B f)
```

`Sheaf.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula`:

```lean
theorem rawModuleScalar_pullback_abelian_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B) :
    ∀ (x : (abelianHigherDirectImageRawPresheaf (B.hom ≫ k) q
      (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) B)).obj
        (op U)),
      rawAbelianClassMorphism (A.hom ≫ k)
        (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) A) q U
        (abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) q _ _
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app ((RawModuleScalarComparison.forget Λ W).obj G)) U x) =
      abelianSourceFactor f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) (RawModuleScalarComparison.freeAbelian S U) ≫
      (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map
        (rawAbelianClassMorphism (B.hom ≫ k)
          (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) B) q U x) ≫
      abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G)
        (q : ℤ) A B f
```

## New

List these three paths in deleted.txt; the delivery installs standard empty modules:

- lean/Sheaf/AlgebraicGeometry/RawModuleScalarSourceFactors.lean
- lean/Sheaf/AlgebraicGeometry/RawModuleScalarPullbackFormulas.lean
- lean/Sheaf/AlgebraicGeometry/RawModuleScalarPullbackAbelianFormula.lean

The source-prefix imports become:

```lean
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourcePrefix
public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso
```

The factor node already names the three upstream source-factor declarations;
add only a retirement note. The unused combined formula node has lean set to null.
The abelian formula node attaches to the existing declaration below, with its
original associativity argument and without the native-class identity proof dependency.

```lean
theorem rawModuleScalar_pullback_abelian_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B) :
    ∀ (x : (abelianHigherDirectImageRawPresheaf (B.hom ≫ k) q
      (restrictedOverCoefficient ((moduleAbelianForget Λ W).obj G) B)).obj
        (op U)),
      abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) q _ _
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app ((moduleAbelianForget Λ W).obj G)) U x =
      abelianSourceFactor f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) (RawModuleScalarComparison.freeAbelian S U) ≫
      (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map x ≫
      abelianCoefficientFactor ((moduleAbelianForget Λ W).obj G)
        (q : ℤ) A B f
```

The old and canonical abelian equations use the same morphisms: rawAbelianClassMorphism
returns its supplied class, and RawModuleScalarComparison.forget abbreviates
moduleAbelianForget. Unfolding those identity bodies gives the canonical equation.
Every ring, scheme, sheaf, degree, test object and Over-arrow binder remains unchanged.
The same formula covers q = 0, zero classes and identity arrows. No target meaning
changes. Preserve the abelian node's mathematical statement and all incoming edges.

## Users

All adapted or additionally retired modules were unclaimed at preparation. K4 holds
the assigned source-factor item. The initial downstream scan listed eight modules;
G2 has since withdrawn four. The table records all eight and the canonical replacement.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors | K4 | Withdraw declaration-free shim. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas | unclaimed | Withdraw unused conjunction; no current parent or importer. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula | unclaimed | Withdraw duplicate; attach node to canonical proof. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourcePrefix | unclaimed | Replace shim import by compatibility API import. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula | unclaimed | Unchanged transitive reexport, checked by compilation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation | already withdrawn by G2 | No packet file; preserve current withdrawal and canonical node. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula | already withdrawn by G2 | No packet file; preserve current module-only factorization route. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | already withdrawn by G2 | No packet file; preserve canonical source formula. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomTargetFormula | already withdrawn by G2 | No packet file; canonical formula uses canonical abelian factorization. |
| WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceFactors | unchanged | Existing canonical source factors retained verbatim. |
| WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula | unchanged | Existing abelian formula and complete proof retained verbatim. |

The three remaining original direct importers of the factor shim are precisely the
combined formula, abelian formula and prefix. The combined module is the only Lean
importer of the abelian copy. A current repository and quarantine scan finds no other
importer. G2's canonical composite already removed the combined node's sole parent.
The source-factor node's remaining mathematical parents continue to use its canonical
definitions; the abelian node's target-formula parent uses the same canonical theorem.
The unit sk-lem-failure-field realizes neither retired duplicate statement nor any
step through them. Its statement and proof steps remain unchanged. No upstream
signature, attribute, import, non-theorem body or proof is edited.

## Status

landed 20261025T095554-L-3447682 2026-10-25 (merge of deliver/K4/Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors)
