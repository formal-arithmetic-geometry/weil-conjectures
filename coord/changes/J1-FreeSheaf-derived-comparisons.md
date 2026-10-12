# AlgebraicGeometry.Etale derived shifted-Hom comparisons

## Reason

The unchanged source file exceeds the local compiler's 60-second timeout. Diagnostics
identify expensive concrete kernel checks of the shift comparison and additive adjunction,
and the application lemma's kernel check and private-module linter. Factor the identical
compositions through proved generic helpers and a named presentation of pullback. Prove
naturality generically. Prune the two concrete equivalence/application wrappers that this
naturality proof no longer uses, after checking that no other module references them.
No retained declaration signature, target statement or mathematical object changes. No compiler or linter check is disabled and no file is split to evade the timeout.

## Old

```lean
noncomputable def Etale.upperStarSingleShiftIso (q : ℤ) :
    DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
        ((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ≅
      (v)^*[ModuleCat.{u + 1} Λ] ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q :=
  Functor.isoWhiskerLeft _ (((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.commShiftIso q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0)
      (shiftFunctor _ q) ≪≫ Functor.associator _ _ _

noncomputable def Etale.etaleLowerShriekShiftedHomEquiv
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((Etale.shiftedHomFunctor Λ ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj M) q).obj
      N) ≃+ ((Etale.shiftedHomFunctor Λ M q).obj ((v)^*[ModuleCat.{u + 1} Λ].obj N)) :=
  let i₁ := ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).mapDerivedCategoryPlusSingleFunctor
    0).app M
  let i₂ := (Etale.upperStarSingleShiftIso Λ v hv q).app N
  let adj := Etale.derivedEtaleLowerShriekUpperStarAdjunctionPlus Λ v hv
  AddEquiv.mk'
    { toFun f := adj.homEquiv _ _ (i₁.hom ≫ f) ≫ i₂.hom
      invFun g := i₁.inv ≫ (adj.homEquiv _ _).symm (g ≫ i₂.inv)
      left_inv f := by simp
      right_inv g := by simp }
    (fun a b ↦ by
      simp only [Equiv.coe_fn_mk, Adjunction.homEquiv_unit]
      erw [Preadditive.comp_add, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp])

lemma Etale.etaleLowerShriekShiftedHomEquiv_apply
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (f : (Etale.shiftedHomFunctor Λ ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj M)
      q).obj N) :
    Etale.etaleLowerShriekShiftedHomEquiv Λ v hv M q N f =
      (Etale.derivedEtaleLowerShriekUpperStarAdjunctionPlus Λ v hv).homEquiv _ _
        ((((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).mapDerivedCategoryPlusSingleFunctor
          0).app M).hom ≫ f) ≫ ((Etale.upperStarSingleShiftIso Λ v hv q).app N).hom :=
  rfl

noncomputable def Etale.etaleLowerShriekShiftedHomIso
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    Etale.shiftedHomFunctor Λ ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj M) q ≅
      (v)^*[ModuleCat.{u + 1} Λ] ⋙ Etale.shiftedHomFunctor Λ M q :=
  NatIso.ofComponents
    (fun N ↦ (Etale.etaleLowerShriekShiftedHomEquiv Λ v hv M q N).toAddCommGrpIso)
    (fun {N N'} g ↦ by
      ext f
      change Etale.etaleLowerShriekShiftedHomEquiv Λ v hv M q N'
          (f ≫ (shiftFunctor _ q).map ((DerivedCategory.Plus.singleFunctor _ 0).map g)) =
        Etale.etaleLowerShriekShiftedHomEquiv Λ v hv M q N f ≫ (shiftFunctor _ q).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map ((v)^*[ModuleCat.{u + 1} Λ].map g))
      rw [Etale.etaleLowerShriekShiftedHomEquiv_apply, Etale.etaleLowerShriekShiftedHomEquiv_apply,
        ← Category.assoc, Adjunction.homEquiv_naturality_right, Category.assoc, Category.assoc]
      congr 1
      exact (Etale.upperStarSingleShiftIso Λ v hv q).hom.naturality g)
```

## New

```lean
noncomputable def Etale.upperStarSingleShiftIso (q : ℤ) :
    DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
        ((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ≅
      (v)^*[ModuleCat.{u + 1} Λ] ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q := by
  letI := Etale.preservesFiniteLimits_upperStarForShift Λ v
  exact Etale.exactSingleShiftIso (Etale.upperStarForShift Λ v) q

noncomputable def Etale.etaleLowerShriekShiftedHomIso
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    Etale.shiftedHomFunctor Λ ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj M) q ≅
      (v)^*[ModuleCat.{u + 1} Λ] ⋙ Etale.shiftedHomFunctor Λ M q :=
  let adj := Etale.derivedEtaleLowerShriekUpperStarAdjunctionPlus Λ v hv
  let i₁ := ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).mapDerivedCategoryPlusSingleFunctor
    0).app M
  let S := DerivedCategory.Plus.singleFunctor
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙ shiftFunctor _ q
  let T := (v)^*[ModuleCat.{u + 1} Λ] ⋙ DerivedCategory.Plus.singleFunctor
    (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙ shiftFunctor _ q
  let e := Functor.associator _ _ _ ≪≫ Etale.upperStarSingleShiftIso Λ v hv q
  (Functor.associator _ _ _).symm ≪≫ Etale.adjunctionHomNatIso adj i₁ S T e ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((v)^*[ModuleCat.{u + 1} Λ]) (Functor.associator _ _ _)
```

Removed the unused concrete declarations etaleLowerShriekShiftedHomEquiv and
etaleLowerShriekShiftedHomEquiv_apply. Their only former uses were the construction and
naturality of etaleLowerShriekShiftedHomIso in the same file. This is now constructed
from the generic additive-adjunction equivalence and its generic naturality proof.
The generic helpers adjunctionHomAddEquivOfIso, adjunctionHomAddEquivOfIso_apply, and
adjunctionHomNatIso are proved without sorry. They use precisely the original component
formula adj.homEquiv (i₁.hom ≫ f) ≫ i₂.hom, and the original inverse formula
 i₁.inv ≫ adj.homEquiv.symm (g ≫ i₂.inv). The generic functor isomorphism is specialized
with the same single-object and shift comparison isomorphisms; the added associators
only regroup functor composition. No unit statement or step uses the removed wrappers.

The named upperStarForShift is literally the original pullback. exactSingleShiftIso
composes its single-object and shift comparisons exactly as before. The additive and
finite-(co)limit preservation helpers supply the usual instances. The two retained
concrete isomorphisms have unchanged declaration signatures and the same components.
No target statement or definition changes mathematical meaning.

## Users

The read-only downstream.py --uses checks for upperStarSingleShiftIso and
etaleLowerShriekShiftedHomEquiv each find 101 downstream modules, but uses of these names
only in the declaring module (4 and 5 occurrences respectively). A source search for
etaleLowerShriekShiftedHomIso and its concrete application lemma also finds only this
module. Its naturality proof and final shiftedHomFunctorUpperStarFreeSheafIso construction
are adapted/compiled in the same delivery. Other modules retain the same shifted-Hom
functor comparison, with the identical component formula. No target changes meaning;
the usual review of changed public definitions can verify this component formula.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf | J1 | Refactor the same comparisons and prune the unused equivalence/application wrappers. |

## Status

landed 20261012T060741-L-2909403 2026-10-12 (merge of deliver/J1/WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf)
