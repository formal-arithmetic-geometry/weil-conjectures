# WeilConjectures.FixProjectionCompactification data interface

## Reason

The single-refinement integral and field steps must import the comparison predicates
without importing the theorem which assembles them. Move the three existing definitions
verbatim to ProjectionCompactificationData and publicly re-export that module from the
original module. Add the strictly local refinementLaw predicate there. No definition data
is selected from a new theorem, and no original signature, body, namespace or visibility changes.
The unchanged theorem comparison is reduced to the finite coefficient clause and the two higher
single-refinement steps, combined by explicit functorial cancellation and the cocycle.

Returned-delivery repair, 2026-10-26: this record is delivered at
coord/changes/J2-projection-compactification-local-interface.md. The landing tool maps
reviewer overrides for that path from the basename
J2-projection-compactification-local-interface.change.md (tools/batch_land.py, fixes).
The previous override used the basename without .change, which the landing rejected.
The New section now includes all four definitions verbatim; no external override is
needed to supply their text. The ten-consumer census below was refreshed against the
current shared source and is unchanged.

## Old

In lean/Sheaf/Paper/FixProjectionCompactificationComparison.lean:

```lean
/-- Package a given compactification with the identity base-change square. This selects
its projection from the recorded exchange/projection family without choosing any new map.
Source: prop-sf-pf-coherence.proof.md, chosen compactification
(blueprint: lem-fix-projection-compactification-comparison). -/
def identitySquare {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left) : SixFunctorCompactifiedSquare D := by
  letI : LocallyOfFiniteType Y.obj.hom := Y.property.1
  letI : QuasiCompact Y.obj.hom := Y.property.2
  let Z : SixFunctorSpace D :=
    ⟨Over.mk (c.g ≫ Y.obj.hom),
      inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y.obj.hom)),
      inferInstanceAs (QuasiCompact (c.g ≫ Y.obj.hom))⟩
  let i : X ⟶ Z := ObjectProperty.homMk
    (Over.homMk c.i (by
      change c.i ≫ c.g ≫ Y.obj.hom = X.obj.hom
      rw [← Category.assoc, ← c.comm]
      exact f.hom.w))
  let p : Z ⟶ Y := ObjectProperty.homMk (Over.homMk c.g rfl)
  have h : f = i ≫ p := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact c.comm
  exact
    { X := X, Y := Y, X' := X, Y' := Y, Z := Z, Z' := Z
      f := f, f' := f, g := 𝟙 Y, g' := 𝟙 X
      i := i, i' := i, p := p, p' := p, h := 𝟙 Z
      open_i := c.isOpenImmersion, open_i' := c.isOpenImmersion
      proper_p := c.isProper, proper_p' := c.isProper
      factorization := h, factorization' := h
      square := IsPullback.of_horiz_isIso ⟨by simp⟩
      properSquare := IsPullback.of_horiz_isIso ⟨by simp⟩
      openSquare := IsPullback.of_horiz_isIso ⟨by simp⟩
      squareComm := by simp, properComm := by simp, openComm := by simp }

/-- The displayed compactification comparison equation at a higher coefficient stage.
The tensor, projection and rho are all taken from the supplied normalized operation datum;
P is instantiated below with exactly the recorded finite-Tor domain at that stage.
Source: prop-sf-pf-coherence.proof.md, compactification-independence sentence
(blueprint: lem-fix-projection-compactification-comparison). -/
def higherLaw {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (T : ∀ X, B X ⥤ B X ⥤ B X)
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (P : ∀ Y, ObjectProperty (B Y)) : Prop :=
  ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c₁ c₂ : Compactification f.hom.left) (K : B X) (L : B Y), P Y L →
    (A (identitySquare f c₁)).projectionComponent K L ≫
        (S.comparison f c₁ c₂).hom.app
          (((T X).obj K).obj ((S.pull f).obj L)) =
      ((T Y).map ((S.comparison f c₁ c₂).hom.app K)).app L ≫
        (A (identitySquare f c₂)).projectionComponent K L

/-- The finite-coefficient equation in fixed-scalar coordinates. The common-refinement
comparison is theta(d,c1) inverse followed by theta(d,c2), exactly as prescribed by
compactification_coherence. The retained target witness is transported by e; quantifying
over e keeps every presentation of the tensor object, rather than choosing an antecedent.
K is bounded constructible, and only L is required to have finite Tor amplitude.
Source: prop-sf-pf-coherence.proof.md, compactification-independence sentence
(blueprint: lem-fix-projection-compactification-comparison). -/
def finiteLaw (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (hl : IsUnit (C.l : D.k)) : Prop :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c₁ c₂ d : Compactification f) (r₁ : d.Refinement c₁) (r₂ : d.Refinement c₂)
    (O : RefinementFiniteLevelOrigin C.l E n hn X)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (OT : RefinementFiniteLevelOrigin C.l E n hn X),
    let K := refinementFiniteLevelFixedObject C.l E n hn X O
    let M := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
    let T := ((derivedTensor M X).obj K).obj ((upperStar M f).leftDerivedFunctor.obj L)
    ∀ (e : refinementFiniteLevelFixedObject C.l E n hn X OT ≅ T),
    intrinsicFiniteTorsionConstructible C.l E n hn X
      ((sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing C.l E n)).functor.obj
        K) →
    finiteTorConstructible C.l E n hn Y
      ((sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing C.l E n)).functor.obj
        L) →
    let rhoK := (refinementComparisonIsomorphism D.k C.l hl E n hn f r₁ O).symm ≪≫
      refinementComparisonIsomorphism D.k C.l hl E n hn f r₂ O
    let rhoT := (rightDerivedLowerShriekOfCompactification M c₁).mapIso e.symm ≪≫
      (refinementComparisonIsomorphism D.k C.l hl E n hn f r₁ OT).symm ≪≫
      refinementComparisonIsomorphism D.k C.l hl E n hn f r₂ OT ≪≫
      (rightDerivedLowerShriekOfCompactification M c₂).mapIso e
    ((projectionMapOfCompactification M c₁).app K).app L ≫ rhoT.hom =
      ((derivedTensor M Y).map rhoK.hom).app L ≫
        ((projectionMapOfCompactification M c₂).app K).app L

```

## New

In lean/Sheaf/Paper/ProjectionCompactificationData.lean, under the unchanged namespace
WeilConjectures.FixProjectionCompactification:

```lean
/-- Package a given compactification with the identity base-change square. This selects
its projection from the recorded exchange/projection family without choosing any new map.
Source: prop-sf-pf-coherence.proof.md, chosen compactification
(blueprint: lem-fix-projection-compactification-comparison). -/
def identitySquare {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left) : SixFunctorCompactifiedSquare D := by
  letI : LocallyOfFiniteType Y.obj.hom := Y.property.1
  letI : QuasiCompact Y.obj.hom := Y.property.2
  let Z : SixFunctorSpace D :=
    ⟨Over.mk (c.g ≫ Y.obj.hom),
      inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y.obj.hom)),
      inferInstanceAs (QuasiCompact (c.g ≫ Y.obj.hom))⟩
  let i : X ⟶ Z := ObjectProperty.homMk
    (Over.homMk c.i (by
      change c.i ≫ c.g ≫ Y.obj.hom = X.obj.hom
      rw [← Category.assoc, ← c.comm]
      exact f.hom.w))
  let p : Z ⟶ Y := ObjectProperty.homMk (Over.homMk c.g rfl)
  have h : f = i ≫ p := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact c.comm
  exact
    { X := X, Y := Y, X' := X, Y' := Y, Z := Z, Z' := Z
      f := f, f' := f, g := 𝟙 Y, g' := 𝟙 X
      i := i, i' := i, p := p, p' := p, h := 𝟙 Z
      open_i := c.isOpenImmersion, open_i' := c.isOpenImmersion
      proper_p := c.isProper, proper_p' := c.isProper
      factorization := h, factorization' := h
      square := IsPullback.of_horiz_isIso ⟨by simp⟩
      properSquare := IsPullback.of_horiz_isIso ⟨by simp⟩
      openSquare := IsPullback.of_horiz_isIso ⟨by simp⟩
      squareComm := by simp, properComm := by simp, openComm := by simp }

/-- The displayed compactification comparison equation at a higher coefficient stage.
The tensor, projection and rho are all taken from the supplied normalized operation datum;
P is instantiated below with exactly the recorded finite-Tor domain at that stage.
Source: prop-sf-pf-coherence.proof.md, compactification-independence sentence
(blueprint: lem-fix-projection-compactification-comparison). -/
def higherLaw {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (T : ∀ X, B X ⥤ B X ⥤ B X)
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (P : ∀ Y, ObjectProperty (B Y)) : Prop :=
  ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c₁ c₂ : Compactification f.hom.left) (K : B X) (L : B Y), P Y L →
    (A (identitySquare f c₁)).projectionComponent K L ≫
        (S.comparison f c₁ c₂).hom.app
          (((T X).obj K).obj ((S.pull f).obj L)) =
      ((T Y).map ((S.comparison f c₁ c₂).hom.app K)).app L ≫
        (A (identitySquare f c₂)).projectionComponent K L

/-- The local comparison square for one proper refinement. Common refinements are
assembled from two such squares using the recorded comparison cocycle.
Source: prop-sf-pf-coherence.proof.md, compactification-independence calculation, step 5
(blueprint: def-sf-projection-single-refinement-law). -/
def refinementLaw {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (T : ∀ X, B X ⥤ B X ⥤ B X)
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (P : ∀ Y, ObjectProperty (B Y)) : Prop :=
  ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (_r : c.Refinement d) (K : B X) (L : B Y), P Y L →
    (A (identitySquare f c)).projectionComponent K L ≫
        (S.comparison f c d).hom.app
          (((T X).obj K).obj ((S.pull f).obj L)) =
      ((T Y).map ((S.comparison f c d).hom.app K)).app L ≫
        (A (identitySquare f d)).projectionComponent K L

/-- The finite-coefficient equation in fixed-scalar coordinates. The common-refinement
comparison is theta(d,c1) inverse followed by theta(d,c2), exactly as prescribed by
compactification_coherence. The retained target witness is transported by e; quantifying
over e keeps every presentation of the tensor object, rather than choosing an antecedent.
K is bounded constructible, and only L is required to have finite Tor amplitude.
Source: prop-sf-pf-coherence.proof.md, compactification-independence sentence
(blueprint: lem-fix-projection-compactification-comparison). -/
def finiteLaw (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (hl : IsUnit (C.l : D.k)) : Prop :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c₁ c₂ d : Compactification f) (r₁ : d.Refinement c₁) (r₂ : d.Refinement c₂)
    (O : RefinementFiniteLevelOrigin C.l E n hn X)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (OT : RefinementFiniteLevelOrigin C.l E n hn X),
    let K := refinementFiniteLevelFixedObject C.l E n hn X O
    let M := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
    let T := ((derivedTensor M X).obj K).obj ((upperStar M f).leftDerivedFunctor.obj L)
    ∀ (e : refinementFiniteLevelFixedObject C.l E n hn X OT ≅ T),
    intrinsicFiniteTorsionConstructible C.l E n hn X
      ((sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing C.l E n)).functor.obj
        K) →
    finiteTorConstructible C.l E n hn Y
      ((sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing C.l E n)).functor.obj
        L) →
    let rhoK := (refinementComparisonIsomorphism D.k C.l hl E n hn f r₁ O).symm ≪≫
      refinementComparisonIsomorphism D.k C.l hl E n hn f r₂ O
    let rhoT := (rightDerivedLowerShriekOfCompactification M c₁).mapIso e.symm ≪≫
      (refinementComparisonIsomorphism D.k C.l hl E n hn f r₁ OT).symm ≪≫
      refinementComparisonIsomorphism D.k C.l hl E n hn f r₂ OT ≪≫
      (rightDerivedLowerShriekOfCompactification M c₂).mapIso e
    ((projectionMapOfCompactification M c₁).app K).app L ≫ rhoT.hom =
      ((derivedTensor M Y).map rhoK.hom).app L ≫
        ((projectionMapOfCompactification M c₂).app K).app L
```

The three original definitions above are byte-identical to the current source.
The additional refinementLaw definition quantifies only over a proper refinement c → d.
The original module publicly imports ProjectionCompactificationData, preserving every
existing declaration name and its visibility. The original node keeps comparison as
its declaration; the data node records all four definitions, and the original node
cites that data node in proof_deps (reviewer FIX: its stmt_deps stay unchanged, since a
stage-3 stmt_deps change is refused together with a proof change).

## Users

The source-only downstream.py census covers all ten transitive importers below.
The only external textual user of identitySquare is SixFunctorMixedSupportCupProduct;
higherLaw and finiteLaw have no external textual users. Every old public import of the
item remains. No target type or definition meaning changes, and no consumer adaptation
is necessary.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.DerivedPoincarePairing | unclaimed in shared snapshot | Identical declarations publicly re-exported; no source adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed in shared snapshot | Identical declarations publicly re-exported; no source adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeData | unclaimed in shared snapshot | Identical declarations publicly re-exported; no source adaptation. |
| Sheaf.Paper.FiniteProjectionIdentityNormalization | unclaimed in shared snapshot | Identical declarations publicly re-exported; no source adaptation. |
| Sheaf.Paper.FiniteProjectionOpenAssembly | unclaimed in shared snapshot | Identical declarations publicly re-exported; no source adaptation. |
| Sheaf.Paper.FiniteProjectionRefinementLeft | unclaimed in shared snapshot | Identical declarations publicly re-exported; no source adaptation. |
| Sheaf.Paper.FiniteProjectionTensorSquare | unclaimed in shared snapshot | Identical declarations publicly re-exported; no source adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed in shared snapshot | Identical declarations publicly re-exported; no source adaptation. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed in shared snapshot | Identical declarations publicly re-exported; no source adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed in shared snapshot | Identical declarations publicly re-exported; no source adaptation. |

## Status

landed 20261025T211625-L-3999844 2026-10-25 (merge of deliver/J2/Sheaf.Paper.FixProjectionCompactificationComparison)
