# CochainComplex.ringedSite_kFlat_stalk_criterion

## Reason

The proof is completed using normalized point lemmas and a universal finite matrix retract.
Remove obsolete imports, including the redundant public import of
`Sheaf.Algebra.Homology.KFlat`. The retained independent-coefficient module supplies the
statement's K-flat predicate. New imports used only by proofs are private.

The theorem statement is unchanged, as checked by whitespace-normalized comparison with
the source. No definition changes meaning. Add `open scoped ZeroObject` for the zero
complex notation in a private proved helper, and backward-definitional-equality options
for the dependent tensor interfaces. A scoped unused-variable linter setting retains the
original unused `hJ` binder. These commands do not change the theorem or its definitions.

## Old

Public imports and section commands, verbatim:

```lean
public import Sheaf.CategoryTheory.Sites.RingedSitePoint
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.Algebra.Homology.Additive
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
set_option autoImplicit false
universe u v w t
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
```

The existing theorem signature, retained verbatim in the delivery:

```lean
theorem ringedSite_kFlat_stalk_criterion
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{w})
    (K : CochainComplex (ringedSiteModules.{w}
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) :
    (∀ (p : GeometricMorphism (Type w) (Sheaf J.toGrothendieck (Type w)))
      (s : RingedSitePoint R p),
      IsKFlatIndependentCoefficients (R := R) K →
        (HomologicalComplex.quasiIso (ModuleCat.{w} s.ring) (.up ℤ)).kFlat
          ((s.modules.mapHomologicalComplex (.up ℤ)).obj K)) ∧
    (∀ (I : Type t)
      (p : I → GeometricMorphism (Type w) (Sheaf J.toGrothendieck (Type w)))
      (s : ∀ i : I, RingedSitePoint R (p i)),
      JointlyReflectIsomorphisms (fun i : I ↦ (p i).inverse) →
      (∀ i : I,
        (HomologicalComplex.quasiIso (ModuleCat.{w} (s i).ring) (.up ℤ)).kFlat
          (((s i).modules.mapHomologicalComplex (.up ℤ)).obj K)) →
      IsKFlatIndependentCoefficients (R := R) K)
```

## New

Public imports and section commands, verbatim:

```lean
public import Sheaf.CategoryTheory.Sites.RingedSitePoint
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.Algebra.Homology.Additive
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace CochainComplex
```

The theorem signature is the identical signature in `Old`; its proof is now complete.
Seven new modules supply proved public lemmas, each with its own node. No existing
public declaration is removed, renamed, or changed in statement.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion --uses
CochainComplex.ringedSite_kFlat_stalk_criterion` reports zero downstream modules and
only the item's own occurrence of the declaration. DAG parents with unfinished proofs
remain supported; neither the item nor any dependency is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion | F2 | Completed proof; unused import removed; statement unchanged |

No forced adaptations. No target statement or target-used definition is changed, so
this proof does not reopen semantic target review.

## Status

landed 20261020T174753-L-794151 2026-10-20 (merge of deliver/F2/Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion)
