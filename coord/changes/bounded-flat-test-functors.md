# Bounded-flat tensor-test functors

## Reason

Kernel profiling found repeated expansion of the concrete sheaf monoidal and zero-morphism
instances while comparing the tensor-test functors. The original assembled proof could
compile in 37.6 seconds, but repeated checks exceeded the 60-second limit. Share the generic
product/tensor functor through an irreducible, explicitly constructed definition. Its generic
comparison is proved once and specialized without expanding the concrete construction.
The resulting complete module compiled in 32.5 seconds through lcompile.py.

The two old functors are definitionally equal to their new versions after unfolding
`tensorTestFunctor` and the existing `derivedTensor`. The objects, maps, signed total tensor,
and existing derived monoidal structure are identical. No hypothesis or conclusion changes.
This is an implementation change under the existing node, with no new mathematical notion.
The public helper is necessary because a private declaration cannot occur in a public
non-theorem definition body.

## Old

```lean
def strictTests {V X : Scheme.{u}} (f : V ⟶ X) (A : Type (u + 1)) [CommRing A]
    (c d : ℤ) :
    (flatInterval X A c d).FullSubcategory ×
        Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A) ⥤
      CochainComplex (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A)) ℤ :=
  (((flatInterval X A c d).ι ⋙ termwisePullback f A).prod
      (CochainComplex.singleFunctor _ 0)) ⋙
    Functor.uncurry.obj (curriedTensor _)

def derivedTests {V X : Scheme.{u}} (f : V ⟶ X) (A : Type (u + 1)) [CommRing A]
    (c d : ℤ) :
    (flatInterval X A c d).FullSubcategory ×
        Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A) ⥤
      ModuleDerivedCategory V A :=
  (((flatInterval X A c d).ι ⋙ DerivedCategory.Q ⋙
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory).prod
        (CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q)) ⋙
    Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) V)
```

## New

```lean
def tensorTestFunctor {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] (B : D ⥤ C) (S : E ⥤ C) : D × E ⥤ C :=
  B.prod S ⋙ Functor.uncurry.obj (curriedTensor C)

def strictTests {V X : Scheme.{u}} (f : V ⟶ X) (A : Type (u + 1)) [CommRing A]
    (c d : ℤ) :
    (flatInterval X A c d).FullSubcategory ×
        Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A) ⥤
      CochainComplex (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A)) ℤ :=
  tensorTestFunctor ((flatInterval X A c d).ι ⋙ termwisePullback f A)
    (CochainComplex.singleFunctor _ 0)

def derivedTests {V X : Scheme.{u}} (f : V ⟶ X) (A : Type (u + 1)) [CommRing A]
    (c d : ℤ) :
    (flatInterval X A c d).FullSubcategory ×
        Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A) ⥤
      ModuleDerivedCategory V A :=
  tensorTestFunctor ((flatInterval X A c d).ι ⋙ DerivedCategory.Q ⋙
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory)
    (CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q)
```

## Users

`tools/downstream.py Sheaf.Paper.BoundedFlatPullbackTest --uses strictTests derivedTests`
reports zero downstream modules, and only this module mentions either declaration.
A whole-library source search agrees. The DAG parent is retained unchanged: its unfinished
proof still needs this item and its mathematical statement is unchanged. No source-library
module is changed, and no target signature changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.BoundedFlatPullbackTest | H5 | Prove the natural comparison through the shared generic tensor-test functor; unfold it explicitly for strict term vanishing. |

## Status

landed 20261024T204612-L-3802673 2026-10-24 (merge of deliver/H5/Sheaf.Paper.BoundedFlatPullbackTest)
