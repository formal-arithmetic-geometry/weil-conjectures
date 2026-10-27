# WeilConjectures.ConstantPurityFrobenius.Square

## Reason

After the proof compiled, the packet compile landed just above the 60-second
limit. The profile attributed about 15 seconds to elaboration of Square.
Replace its identity-morphism finite-type instance search by the explicit
public Mathlib open-immersion implication, as already done in systems.
Only a proposition proof changes. Proof irrelevance makes the old and new
Square definitions definitionally equal; all three identities and their maps
are identical. The theorem signature and every target retain their meanings.
The same explicit proof replaces the corresponding search inside the new theorem proof.

## Old

```lean
def Square (d : ℕ) [SmoothOfRelativeDimension d X₀.hom] : Prop :=
  let D := P.field
  let l := P.coefficients.l
  let hl := P.coefficients.different
  let Ω := P.coefficients.Qbar
  let Y₀ := point D
  let f₀ := pointMap D X₀
  letI : LocallyOfFiniteType Y₀.hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k₀))))
  letI : QuasiCompact Y₀.hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k₀))))
  letI : IsSeparated Y₀.hom :=
    inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k₀))))
  letI : IsSeparated f₀.left := inferInstanceAs (IsSeparated X₀.hom)
  letI : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType X₀.hom)
  letI : QuasiCompact f₀.left := inferInstanceAs (QuasiCompact X₀.hom)
  letI : SmoothOfRelativeDimension d f₀.left :=
    inferInstanceAs (SmoothOfRelativeDimension d X₀.hom)
  letI : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).1
  letI : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).2
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).2
  letI : IsSeparated ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    MorphismProperty.baseChange_obj (P := @IsSeparated) _ X₀ inferInstance
  letI : IsSeparated ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    MorphismProperty.baseChange_obj (P := @IsSeparated) _ Y₀ inferInstance
  letI : (FrobeniusExchange.fiberMap D f₀).IsOver (Spec (.of D.k)) :=
    zlFiberMap_isOver D f₀
  letI : IsSeparated (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).1
  letI : LocallyOfFiniteType (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).2.1
  letI : QuasiCompact (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).2.2
  letI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension d) :=
    smoothOfRelativeDimension_isStableUnderBaseChange d
  letI : SmoothOfRelativeDimension d (FrobeniusExchange.fiberMap D f₀) :=
    MorphismProperty.overPullbackMap (P := @SmoothOfRelativeDimension d)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  let Q := sourceFrobenius D l hl Ω X₀
  let H := source D l hl Ω X₀ Y₀ f₀ d
  let G := (operation D l hl Ω X₀ Y₀ f₀ c₀ S .closed).G
  let K := unit D l hl Ω (D.geometricFiber Y₀).left
  let θ₀ := (constantWeilAlgebraicallyClosedComplex l D hl Y₀ Ω).str
  let θX := (constantWeilAlgebraicallyClosedComplex l D hl X₀ Ω).str
  let u := commonUnit D l hl Ω (FrobeniusExchange.fiberMap D f₀)
  let b := sourceSquare D l hl Ω X₀ Y₀ f₀ d K
  let θH := canonicalSourceTheta D l hl Ω X₀ Y₀ f₀ d
  let γ := @RationalSmoothPurityCanonical.commonIso P
    (D.geometricFiber X₀).left (D.geometricFiber Y₀).left inferInstance inferInstance
    (FrobeniusExchange.fiber_finiteType D X₀).1
    (FrobeniusExchange.fiber_finiteType D X₀).2
    (MorphismProperty.baseChange_obj (P := @IsSeparated) _ X₀ inferInstance)
    (FrobeniusExchange.fiber_finiteType D Y₀).1
    (FrobeniusExchange.fiber_finiteType D Y₀).2
    (MorphismProperty.baseChange_obj (P := @IsSeparated) _ Y₀ inferInstance)
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
    (fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y)
    (FrobeniusExchange.fiberMap D f₀) (zlFiberMap_isOver D f₀)
    (FrobeniusExchange.fiberMap_properties D f₀).1
    (FrobeniusExchange.fiberMap_properties D f₀).2.1
    (FrobeniusExchange.fiberMap_properties D f₀).2.2
    (FrobeniusExchange.geometricCompactification D f₀ c₀) S d inferInstance K
  let e := exceptionalIso D l hl Ω X₀ Y₀ f₀ c₀ S
  (podCommonSquarePullbackComponent l Ω (FrobeniusExchange.fiberMap D f₀)
      (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
      (zlFrobenius_naturality D f₀) K).hom ≫
      (commonStageDerivedPullback l Ω (FrobeniusExchange.fiberMap D f₀)).map θ₀.hom ≫
      u.hom =
    Q.map u.hom ≫ θX.hom ∧
    θH.hom = b.hom ≫ H.map θ₀.hom ∧
    Q.map γ.hom ≫ e.hom.app K ≫ G.map θ₀.hom = θH.hom ≫ γ.hom
```

## New

```lean
def Square (d : ℕ) [SmoothOfRelativeDimension d X₀.hom] : Prop :=
  let D := P.field
  let l := P.coefficients.l
  let hl := P.coefficients.different
  let Ω := P.coefficients.Qbar
  let Y₀ := point D
  let f₀ := pointMap D X₀
  letI : LocallyOfFiniteType Y₀.hom :=
    locallyOfFiniteType_of_isOpenImmersion (𝟙 (Spec (.of D.k₀)))
  letI : QuasiCompact Y₀.hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k₀))))
  letI : IsSeparated Y₀.hom :=
    inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k₀))))
  letI : IsSeparated f₀.left := inferInstanceAs (IsSeparated X₀.hom)
  letI : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType X₀.hom)
  letI : QuasiCompact f₀.left := inferInstanceAs (QuasiCompact X₀.hom)
  letI : SmoothOfRelativeDimension d f₀.left :=
    inferInstanceAs (SmoothOfRelativeDimension d X₀.hom)
  letI : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).1
  letI : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).2
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).2
  letI : IsSeparated ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    MorphismProperty.baseChange_obj (P := @IsSeparated) _ X₀ inferInstance
  letI : IsSeparated ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    MorphismProperty.baseChange_obj (P := @IsSeparated) _ Y₀ inferInstance
  letI : (FrobeniusExchange.fiberMap D f₀).IsOver (Spec (.of D.k)) :=
    zlFiberMap_isOver D f₀
  letI : IsSeparated (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).1
  letI : LocallyOfFiniteType (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).2.1
  letI : QuasiCompact (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).2.2
  letI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension d) :=
    smoothOfRelativeDimension_isStableUnderBaseChange d
  letI : SmoothOfRelativeDimension d (FrobeniusExchange.fiberMap D f₀) :=
    MorphismProperty.overPullbackMap (P := @SmoothOfRelativeDimension d)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  let Q := sourceFrobenius D l hl Ω X₀
  let H := source D l hl Ω X₀ Y₀ f₀ d
  let G := (operation D l hl Ω X₀ Y₀ f₀ c₀ S .closed).G
  let K := unit D l hl Ω (D.geometricFiber Y₀).left
  let θ₀ := (constantWeilAlgebraicallyClosedComplex l D hl Y₀ Ω).str
  let θX := (constantWeilAlgebraicallyClosedComplex l D hl X₀ Ω).str
  let u := commonUnit D l hl Ω (FrobeniusExchange.fiberMap D f₀)
  let b := sourceSquare D l hl Ω X₀ Y₀ f₀ d K
  let θH := canonicalSourceTheta D l hl Ω X₀ Y₀ f₀ d
  let γ := @RationalSmoothPurityCanonical.commonIso P
    (D.geometricFiber X₀).left (D.geometricFiber Y₀).left inferInstance inferInstance
    (FrobeniusExchange.fiber_finiteType D X₀).1
    (FrobeniusExchange.fiber_finiteType D X₀).2
    (MorphismProperty.baseChange_obj (P := @IsSeparated) _ X₀ inferInstance)
    (FrobeniusExchange.fiber_finiteType D Y₀).1
    (FrobeniusExchange.fiber_finiteType D Y₀).2
    (MorphismProperty.baseChange_obj (P := @IsSeparated) _ Y₀ inferInstance)
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
    (fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y)
    (FrobeniusExchange.fiberMap D f₀) (zlFiberMap_isOver D f₀)
    (FrobeniusExchange.fiberMap_properties D f₀).1
    (FrobeniusExchange.fiberMap_properties D f₀).2.1
    (FrobeniusExchange.fiberMap_properties D f₀).2.2
    (FrobeniusExchange.geometricCompactification D f₀ c₀) S d inferInstance K
  let e := exceptionalIso D l hl Ω X₀ Y₀ f₀ c₀ S
  (podCommonSquarePullbackComponent l Ω (FrobeniusExchange.fiberMap D f₀)
      (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
      (zlFrobenius_naturality D f₀) K).hom ≫
      (commonStageDerivedPullback l Ω (FrobeniusExchange.fiberMap D f₀)).map θ₀.hom ≫
      u.hom =
    Q.map u.hom ≫ θX.hom ∧
    θH.hom = b.hom ≫ H.map θ₀.hom ∧
    Q.map γ.hom ≫ e.hom.app K ≫ G.map θ₀.hom = θH.hom ≫ γ.hom
```

## Users

No current Lean module directly imports the item. The main theorem is checked
against the modified definition by the packet compile. No other module is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | C4 | Explicit proof of identity finite type. |

## Status

landed 20261027T034621-L-3666357 2026-10-27 (merge of deliver/C4/Sheaf.Paper.ConstantPurityFrobeniusSquare)
