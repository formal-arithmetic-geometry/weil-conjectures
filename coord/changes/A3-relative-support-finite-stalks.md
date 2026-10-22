# relative_support_bottom_descent, relative_support_vanishing, frameClass_independent

## Reason

Implement reviewer C-c9702 E2 from the returned head c9702ffff3f. The codimension
convention uses WithBot ENat, whose top absorbs addition of c. The reviewer disputes
using that convention for the relative support result with no finiteness condition.
Require `ringKrullDim (V.presheaf.stalk (i z)) ≠ ⊤` at every z in Z in both relative
support theorems and in the frame-independence theorem that uses this descent.
This is precisely the finite-dimensional stalk option requested in the return.
The additional condition is at the ambient support stalks; no global dimension
bound, global Noetherian assumption, or bound on B is introduced.

The explicit Kummer product `frameClass`, its canonical support transport
`frameClassOnPullback`, and every coefficient and edge definition retain their
signatures and bodies. The finite hypothesis belongs to the theorems using
bottom-degree descent, not to the construction of a frame product.
No declaration or public import under WeilConjectures is edited.

## Old

RelativeSupportBottomDescent:

```lean
theorem relative_support_bottom_descent
    (P : WeilConjectures.PurityFiniteSetting.{u}) (c d : ℕ)
    {B V Z U : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    [SmoothOfRelativeDimension d v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)]
    (hcodim : ∀ z : Z,
      ringKrullDim (V.presheaf.stalk (i.base z)) =
        ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞))
    (e : U ⟶ V) [Etale e]
    (f : Fin c → Γ(U, ⊤))
    (toZ : U.zeroLocusSubscheme (Set.range f) ⟶ Z)
    (hframe : IsPullback toZ (U.zeroLocusSubschemeι (Set.range f)) i e)
    (r : ℤ) :
    (∀ b' : ℤ, b' < 2 * (c : ℤ) →
      IsZero (relativeSupportCohomologySheaf P (pullback.snd i e) r b')) ∧
    (∀ W : U.Etale, IsIso (relativeSupportEdge P (pullback.snd i e) r (2 * c) W)) ∧
    (∀ (W W' : U.Etale) (a : W' ⟶ W),
      relativeSupportClassRestriction P (pullback.snd i e) r (2 * c) a ≫
          relativeSupportEdge P (pullback.snd i e) r (2 * c) W' =
        relativeSupportEdge P (pullback.snd i e) r (2 * c) W ≫
          (relativeSupportCohomologySheaf P (pullback.snd i e) r ((2 * c : ℕ) : ℤ)).obj.map a.op) ∧
    (∀ W : U.Etale,
      IsIso (relativeSupportProComparison P.Coefficient
        (pullback.snd (pullback.snd i e) W.hom) (2 * c)
        (relativeSupportModuleRestriction P W r)) ∧
      IsIso (relativeSupportProEdge P (pullback.snd i e) r (2 * c) W)) ∧
    (∀ (W W' : U.Etale) (a : W' ⟶ W),
      relativeSupportProRestriction P (pullback.snd i e) r (2 * c) a ≫
          relativeSupportProEdge P (pullback.snd i e) r (2 * c) W' =
        relativeSupportProEdge P (pullback.snd i e) r (2 * c) W ≫
          (relativeSupportCohomologySheaf P (pullback.snd i e) r ((2 * c : ℕ) : ℤ)).obj.map a.op) ∧
    (∀ (ι : Type w) (W : ι → U.Etale)
      (a : ∀ t : ι, W t ⟶ Scheme.Etale.mk (𝟙 U)),
      Sieve.ofArrows W a ∈ U.smallEtaleTopology (Scheme.Etale.mk (𝟙 U)) →
      ∀ x y : supportCohomology (pullback.snd i e) (2 * c)
        (relativeSupportCoefficient P U r),
      (∀ t : ι,
        relativeSupportGlobalRestriction P (pullback.snd i e) r (2 * c) (a t) x =
          relativeSupportGlobalRestriction P (pullback.snd i e) r (2 * c) (a t) y) →
      x = y)
```

PurityFrameIndependence:

```lean
theorem frameClass_independent (P : PurityFiniteSetting.{u}) {B V Z : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    [SmoothOfRelativeDimension P.level v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)] (c : ℕ)
    (hcodim : ∀ z : Z, ringKrullDim (V.presheaf.stalk (i z)) =
      ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞))
    (U : Scheme.{u}) (e : U ⟶ V) [Etale e] (f g : Fin c → Γ(U, ⊤))
    (tf : U.zeroLocusSubscheme (Set.range f) ⟶ Z)
    (tg : U.zeroLocusSubscheme (Set.range g) ⟶ Z)
    (hf : IsPullback tf (U.zeroLocusSubschemeι (Set.range f)) i e)
    (hg : IsPullback tg (U.zeroLocusSubschemeι (Set.range g)) i e) :
    P.frameClassOnPullback b v i c hcodim
      { U := U, e := e, etale := inferInstance, f := f, toZ := tf, isPullback := hf } =
    P.frameClassOnPullback b v i c hcodim
      { U := U, e := e, etale := inferInstance, f := g, toZ := tg, isPullback := hg }
```

RelativeSupportVanishing (returned packet):

```lean
theorem relative_support_vanishing
    (P : WeilConjectures.PurityFiniteSetting.{u}) (c d : ℕ)
    {B V Z U : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    [SmoothOfRelativeDimension d v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)]
    (hcodim : ∀ z : Z,
      ringKrullDim (V.presheaf.stalk (i.base z)) =
        ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞))
    (e : U ⟶ V) [Etale e] (r : ℤ) :
    ∀ q : ℤ, q < 2 * (c : ℤ) →
      IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((sectionsWithSupport AddCommGrpCat.{u + 1}
            (pullback.snd i e).openComplement.ι).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((P.forgetEtale U).obj
                (Scheme.finiteEtaleTateSheaf P.Coefficient (ringChar P.Coefficient) U
                  (CharP.cast_eq_zero P.Coefficient (ringChar P.Coefficient)) r)))))
```

## New

RelativeSupportBottomDescent:

```lean
theorem relative_support_bottom_descent
    (P : WeilConjectures.PurityFiniteSetting.{u}) (c d : ℕ)
    {B V Z U : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    [SmoothOfRelativeDimension d v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)]
    (hcodim : ∀ z : Z,
      ringKrullDim (V.presheaf.stalk (i.base z)) =
        ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞))
    (hfinite : ∀ z : Z,
      ringKrullDim (V.presheaf.stalk (i.base z)) ≠ ⊤)
    (e : U ⟶ V) [Etale e]
    (f : Fin c → Γ(U, ⊤))
    (toZ : U.zeroLocusSubscheme (Set.range f) ⟶ Z)
    (hframe : IsPullback toZ (U.zeroLocusSubschemeι (Set.range f)) i e)
    (r : ℤ) :
    (∀ b' : ℤ, b' < 2 * (c : ℤ) →
      IsZero (relativeSupportCohomologySheaf P (pullback.snd i e) r b')) ∧
    (∀ W : U.Etale, IsIso (relativeSupportEdge P (pullback.snd i e) r (2 * c) W)) ∧
    (∀ (W W' : U.Etale) (a : W' ⟶ W),
      relativeSupportClassRestriction P (pullback.snd i e) r (2 * c) a ≫
          relativeSupportEdge P (pullback.snd i e) r (2 * c) W' =
        relativeSupportEdge P (pullback.snd i e) r (2 * c) W ≫
          (relativeSupportCohomologySheaf P (pullback.snd i e) r ((2 * c : ℕ) : ℤ)).obj.map a.op) ∧
    (∀ W : U.Etale,
      IsIso (relativeSupportProComparison P.Coefficient
        (pullback.snd (pullback.snd i e) W.hom) (2 * c)
        (relativeSupportModuleRestriction P W r)) ∧
      IsIso (relativeSupportProEdge P (pullback.snd i e) r (2 * c) W)) ∧
    (∀ (W W' : U.Etale) (a : W' ⟶ W),
      relativeSupportProRestriction P (pullback.snd i e) r (2 * c) a ≫
          relativeSupportProEdge P (pullback.snd i e) r (2 * c) W' =
        relativeSupportProEdge P (pullback.snd i e) r (2 * c) W ≫
          (relativeSupportCohomologySheaf P (pullback.snd i e) r ((2 * c : ℕ) : ℤ)).obj.map a.op) ∧
    (∀ (ι : Type w) (W : ι → U.Etale)
      (a : ∀ t : ι, W t ⟶ Scheme.Etale.mk (𝟙 U)),
      Sieve.ofArrows W a ∈ U.smallEtaleTopology (Scheme.Etale.mk (𝟙 U)) →
      ∀ x y : supportCohomology (pullback.snd i e) (2 * c)
        (relativeSupportCoefficient P U r),
      (∀ t : ι,
        relativeSupportGlobalRestriction P (pullback.snd i e) r (2 * c) (a t) x =
          relativeSupportGlobalRestriction P (pullback.snd i e) r (2 * c) (a t) y) →
      x = y)
```

PurityFrameIndependence:

```lean
theorem frameClass_independent (P : PurityFiniteSetting.{u}) {B V Z : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    [SmoothOfRelativeDimension P.level v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)] (c : ℕ)
    (hcodim : ∀ z : Z, ringKrullDim (V.presheaf.stalk (i z)) =
      ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞))
    (hfinite : ∀ z : Z, ringKrullDim (V.presheaf.stalk (i z)) ≠ ⊤)
    (U : Scheme.{u}) (e : U ⟶ V) [Etale e] (f g : Fin c → Γ(U, ⊤))
    (tf : U.zeroLocusSubscheme (Set.range f) ⟶ Z)
    (tg : U.zeroLocusSubscheme (Set.range g) ⟶ Z)
    (hf : IsPullback tf (U.zeroLocusSubschemeι (Set.range f)) i e)
    (hg : IsPullback tg (U.zeroLocusSubschemeι (Set.range g)) i e) :
    P.frameClassOnPullback b v i c hcodim
      { U := U, e := e, etale := inferInstance, f := f, toZ := tf, isPullback := hf } =
    P.frameClassOnPullback b v i c hcodim
      { U := U, e := e, etale := inferInstance, f := g, toZ := tg, isPullback := hg }
```

RelativeSupportVanishing (returned packet):

```lean
theorem relative_support_vanishing
    (P : WeilConjectures.PurityFiniteSetting.{u}) (c d : ℕ)
    {B V Z U : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    [SmoothOfRelativeDimension d v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)]
    (hcodim : ∀ z : Z,
      ringKrullDim (V.presheaf.stalk (i.base z)) =
        ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞))
    (hfinite : ∀ z : Z,
      ringKrullDim (V.presheaf.stalk (i.base z)) ≠ ⊤)
    (e : U ⟶ V) [Etale e] (r : ℤ) :
    ∀ q : ℤ, q < 2 * (c : ℤ) →
      IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((sectionsWithSupport AddCommGrpCat.{u + 1}
            (pullback.snd i e).openComplement.ι).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((P.forgetEtale U).obj
                (Scheme.finiteEtaleTateSheaf P.Coefficient (ringChar P.Coefficient) U
                  (CharP.cast_eq_zero P.Coefficient (ringChar P.Coefficient)) r)))))
```

The parent proof passes `hfinite` directly to the vanishing theorem. The parent
and vanishing node statements, their recorded Lean signatures and the frame-
independence node are updated together. Comments mark the original convention
STATEMENT-DISPUTED and identify this correction. No conclusion is changed.

The LocalizedTopChern theorem and definitions are unchanged. Its proof docstring
and node now explain the new hypothesis: the total space of the vector bundle,
its opens, overlaps, flag bundles, and products used for gluing are locally of
finite type over k. Their stalks are Noetherian local rings, so Krull's height
theorem gives finite Krull dimension. This applies to singular bases too.
The separate finite-stalk scratch check uses the actual Mathlib instance
`instFiniteRingKrullDimOfIsNoetherianRingOfIsLocalRing` and `ringKrullDim_ne_top`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RelativeSupportBottomDescent | A3 | Require finite ambient support stalks; pass this hypothesis to lower vanishing. |
| Sheaf.Paper.RelativeSupportVanishing | A3, new in returned packet | Restate lower vanishing with the identical finite hypothesis. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Add hfinite to frameClass_independent, which uses the corrected descent. The construction frameClassOnPullback is unchanged. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Preserve all signatures; explain finite stalk dimensions in its universal-pair proof. |

The exact-name downstream scans find no uses of either repaired existing theorem
outside its own module. Thus no current caller expression needs adaptation.
There are 18 import descendants of RelativeSupportBottomDescent and 17 of
PurityFrameIndependence; none mentions the changed theorem by name.
No downstream definition changes meaning, and no Challenge.lean target changes.
The frame-independence adaptation is explicitly requested by E2, not an adaptation
forced by a current compiler error: its existing unfinished proof has not called
bottom descent yet.

The node citer audit is recorded in statement_change.citers. The regular-immersion
citers have smooth ambient k-schemes, hence locally Noetherian ambient schemes
and finite-dimensional local rings; divisor_class already has finite-type data.
The LocalizedTopChern citer has the universal total-space argument above. The
vanishing theorem's only citer is the parent, repaired in the same packet.

## Status

landed 20261022T013344-L-3550290 2026-10-22 (merge of deliver/A3/Sheaf.Paper.RelativeSupportBottomDescent)
