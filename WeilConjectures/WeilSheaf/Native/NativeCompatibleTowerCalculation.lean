/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.Native.NativeBasicComparisons
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenProperInterchange
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedQcqsComposition.CondensedQcqsCompositionDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed

/-! # Native Weil calculation on a compatible proper/open tower

Source: Stacks Project, Tag 0F7J, `lemma-shriek-composition`, the first four
identifications in its proof; adapted to the native coefficient realization of
`def-sf-native-weil-derived-framework`.
(blueprint: lem-sf-native-weil-compatible-tower-calculation)

The compactification functors are expanded as termwise native open extension followed
by native total derived direct image. The three natural isomorphisms below give the
first intermediate identification, the proper/open identification, and their composite.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

/-- Strict pairs on condensed Dbc, with the recorded exact automorphism action.
For the field coefficient this is the Dbc presentation of the strict complexes in
`def-weil-weil-sheaf-complex`; no derived category of equivariant sheaves occurs.
Source: the pair definition (blueprint: lem-sf-native-weil-compatible-tower-calculation). -/
abbrev TowerPair {X : Scheme.{u}} (a : X ≅ X) := Endofunctor.IsoAlgebra (pull ℓ a)

/-- Compact support on strict pairs, using the specified normalized proper/open exchange.
The carrier is precisely Rp_* j_!, and its structure is exchange followed by Rp_* j_!(phi).
Source: normalized exchange (blueprint: lem-sf-native-weil-compatible-tower-calculation). -/
def towerPairSupport {X Y : Scheme.{u}} {f : X ⟶ Y} {S : System ℓ f}
    {a : X ≅ X} {b : Y ≅ Y} {sq : IsPullback a.hom f f b.hom}
    (E : Exchange ℓ S a b sq) (c : Compactification f) :
    TowerPair ℓ a ⥤ TowerPair ℓ b :=
  Endofunctor.IsoAlgebra.mapOfNatIso (E.iso c)

/-- The normalized compositor lifts to strict pairs. Its carrier is the original
compositor, rather than a newly chosen isomorphism of endpoint objects.
Source: composition--exchange equation and naturality, Stacks 0F7J
(blueprint: lem-sf-native-weil-compatible-tower-calculation). -/
def towerPairCompositor {X Z Y : Scheme.{u}} {h : X ⟶ Z} {g : Z ⟶ Y}
    (H : Comparisons ℓ h g) (a : X ≅ X) (b : Z ≅ Z) (v : Y ≅ Y)
    (shsq : IsPullback a.hom h h b.hom) (sgsq : IsPullback b.hom g g v.hom)
    (c : Compactification h) (d : Compactification g) (e : Compactification (h ≫ g)) :
    towerPairSupport ℓ (H.exchange a b v shsq sgsq).1 c ⋙
        towerPairSupport ℓ (H.exchange a b v shsq sgsq).2.1 d ≅
      towerPairSupport ℓ (H.exchange a b v shsq sgsq).2.2 e := by
  refine NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    (Endofunctor.Algebra.isoMk ((H.alpha c d e).app K.carrier) ?_)) ?_
  · change (pull ℓ v).map ((H.alpha c d e).hom.app K.carrier) ≫
        ((H.exchange a b v shsq sgsq).2.2.iso e).hom.app K.carrier ≫
          (H.sgh.support ℓ e).map K.str.hom =
      (((H.exchange a b v shsq sgsq).2.1.iso d).hom.app
          ((H.sh.support ℓ c).obj K.carrier) ≫
        (H.sg.support ℓ d).map
          (((H.exchange a b v shsq sgsq).1.iso c).hom.app K.carrier ≫
            (H.sh.support ℓ c).map K.str.hom)) ≫ (H.alpha c d e).hom.app K.carrier
    rw [← Category.assoc, H.comp_exchange a b v shsq sgsq]
    simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
      congrArg (fun t ↦
        ((H.exchange a b v shsq sgsq).2.1.iso d).hom.app
            ((H.sh.support ℓ c).obj K.carrier) ≫
          (H.sg.support ℓ d).map
            (((H.exchange a b v shsq sgsq).1.iso c).hom.app K.carrier) ≫ t)
        ((H.alpha c d e).hom.naturality K.str.hom).symm
  · intro K L f
    apply ObjectProperty.hom_ext
    apply Endofunctor.Algebra.Hom.ext
    exact (H.alpha c d e).hom.naturality f.hom.f

/-- A quasi-compact open extension preserves the recorded bounded constructible property,
even when the schemes are not separated over the field.
Source: the open compactification case of condensedShriekBoundedQcqs, Stacks 0F7J
(blueprint: lem-sf-native-weil-compatible-tower-calculation).
Proof: use the compactification (j, id) and cancel the canonical identity direct image. -/
private theorem towerOpen_preserves (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {U X : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [QuasiSeparated U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] [QuasiCompact j.left]
    (K : C ℓ U.left) :
    bc ℓ X.left ((CondensedOpenProper.J (Profinite.padicAlgClRingObj ℓ) j.left).obj K.obj) := by
  obtain ⟨_, _, _, hpres, _⟩ := condensedShriekBoundedQcqs ℓ k j
  have : (bc ℓ X.left).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined (Profinite.padicAlgClRingObj ℓ) X.left).2.1
  have hK := hpres (Compactification.ofIsOpenImmersion j.left) K
  exact (bc ℓ X.left).prop_of_iso
    ((CondensedOpenProper.rId (Profinite.padicAlgClRingObj ℓ) X.left).app
      ((CondensedOpenProper.J (Profinite.padicAlgClRingObj ℓ) j.left).obj K.obj)) hK

/-- The compatible-tower calculation, on bounded constructible native Weil complexes.
The first conjunct says that `J_s` preserves the bounded constructible object property.
The remaining conjuncts are the two intermediate natural isomorphisms and the resulting
natural isomorphism from `F_(ts,qp)` to `F_(i,q) F_(s,pW)`. Their components and inverses
are morphisms in the native equivariant derived category.

Source: Stacks Project, Tag 0F7J, `lemma-shriek-composition`, first four displayed
identifications; native adaptation, not an application of the torsion coefficient result.
(blueprint: lem-sf-native-weil-compatible-tower-calculation)

Proof:
1. Compose the quasi-compact open immersions `s,t` and the proper maps `p,q`.
The permanence statements of `lem-weil-pbc-proper-fp-permanence` and the open and
finite-type definitions show that `(s ≫ t,p ≫ q)`, `(s,pW)`, and `(i,q)` are the
specified open/proper factorizations. The Cartesian square gives `t ≫ p = pW ≫ i`,
so their underlying composites agree. Absolute separatedness is not used.
2. Apply part (b) of `lem-sf-native-weil-basic-comparisons` to `s`. Thus `J_s K`
is bounded constructible for every bounded constructible `K` on `V`.
3. Part (a) of that lemma gives `R(qp)_* ≅ Rq_* Rp_*` on the entire native derived
category. Part (b) gives `J_t J_s ≅ J_(ts)`. Whisker the inverse of the latter by
the direct images and compose with the former to obtain the first displayed isomorphism.
These comparisons impose no boundedness requirement on an intermediate direct image.
4. Apply `lem-sf-native-weil-open-proper-interchange` with `j'=t`, `p'=pW`,
`j=i`, and vertical map `p`. Its comparison `J_i RpW_* ≅ Rp_* J_t` has source
`WC^der(U)`. Restrict it along `J_s`, using step 2, invert it, and whisker by
`Rq_*`. This is exactly the second intermediate natural isomorphism below.
5. Compose the natural isomorphisms of steps 3 and 4. Expanding the notation
`F_(j,r) = Rr_* J_j` identifies its endpoints with the claimed compactification
functors. Naturality follows by pasting the naturality squares of the comparisons;
the inverse reverses their order and uses their inverses. All comparisons, their
inverses, and their functorial images remain in the native derived categories.
-/
theorem nativeWeilCompatibleTowerCalculation
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {V U Vbar W Wbar T : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [U.Over (Spec (CommRingCat.of k₀))]
    [Vbar.Over (Spec (CommRingCat.of k₀))] [W.Over (Spec (CommRingCat.of k₀))]
    [Wbar.Over (Spec (CommRingCat.of k₀))] [T.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (V ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Vbar ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Vbar ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (W ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Wbar ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Wbar ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))]
    (s : V ⟶ U) (t : U ⟶ Vbar) (i : W ⟶ Wbar)
    (p : Vbar ⟶ Wbar) (pW : U ⟶ W) (q : Wbar ⟶ T)
    [s.IsOver (Spec (CommRingCat.of k₀))] [t.IsOver (Spec (CommRingCat.of k₀))]
    [i.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))]
    [pW.IsOver (Spec (CommRingCat.of k₀))] [q.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion s] [QuasiCompact s] [IsOpenImmersion t] [QuasiCompact t]
    [IsOpenImmersion i] [QuasiCompact i] [IsProper p] [IsProper pW] [IsProper q]
    (hcart : IsPullback t pW p i) :
    (∀ (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l V)),
      objectProperty k₀ l V K → objectProperty k₀ l U
        ((ProEtaleWeilSheaf.extensionByZero k₀ l s).mapDerivedCategory.obj K)) ∧
    Nonempty
      ((objectProperty k₀ l V).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l (s ≫ t)).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l (p ≫ q)).rightDerivedFunctor ≅
        (objectProperty k₀ l V).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l s).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l t).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l q).rightDerivedFunctor) ∧
    Nonempty
      ((objectProperty k₀ l V).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l s).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l t).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l q).rightDerivedFunctor ≅
        (objectProperty k₀ l V).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l s).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l pW).rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l i).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l q).rightDerivedFunctor) ∧
    Nonempty
      ((objectProperty k₀ l V).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l (s ≫ t)).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l (p ≫ q)).rightDerivedFunctor ≅
        (objectProperty k₀ l V).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l s).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l pW).rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l i).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l q).rightDerivedFunctor) := by
  obtain ⟨hcomp, _, hopen, hopenComp, _⟩ := nativeWeilBasicComparisons k₀ l
  have hs := (hopen V U s).2.2
  obtain ⟨α⟩ := hcomp Vbar Wbar T p q
  obtain ⟨β⟩ := hopenComp V U Vbar s t
  obtain ⟨γ⟩ := nonempty_extensionByZero_rightDerivedLowerStar_iso
    k₀ l t pW p i hcart.w
  let Js := (ProEtaleWeilSheaf.extensionByZero k₀ l s).mapDerivedCategory
  let Jz := (ProEtaleWeilSheaf.extensionByZero k₀ l (s ≫ t)).mapDerivedCategory
  let Rp := (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor
  let Rq := (ProEtaleWeilSheaf.lowerStar k₀ l q).rightDerivedFunctor
  let I := (objectProperty k₀ l V).ι
  let L := (objectProperty k₀ l U).lift (I ⋙ Js) (fun K ↦ hs K.obj K.property)
  let first := Functor.isoWhiskerLeft I
    (Functor.isoWhiskerLeft Jz α ≪≫ Functor.isoWhiskerRight β.symm (Rp ⋙ Rq))
  let second := Functor.isoWhiskerRight (Functor.isoWhiskerLeft L γ.symm) Rq
  exact ⟨hs, ⟨first⟩, ⟨second⟩, ⟨first ≪≫ second⟩⟩

end AlgebraicGeometry.WeilComplex
