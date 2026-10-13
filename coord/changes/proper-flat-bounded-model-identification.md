# proper_flat_boundedPresentation_model_baseChange

## Reason

The existing statement was correctly marked STATEMENT-DISPUTED by A2. It quantified
 over arbitrary C, without identifying C with the direct image of F. Over Spec k,
 a nonzero free module in degree -1 satisfies the structural hypotheses and violates
 negative vanishing. The zero complex also satisfies them and violates the degree-zero
 comparison when f is the identity and F is the structure sheaf. The caller selected C
 solely by these structural properties, so adding a model hypothesis without adapting
 its construction would leave an unjustified application.

This repairs an intermediate interface. Every Challenge.lean target and every public
 definition used by those targets remains identical. In particular the bounded-model
 existence theorem, and its downstream finite-presentation theorem, retain their
 exact original signatures and mathematical strength.

## Old

```lean
theorem proper_flat_boundedPresentation_model_baseChange {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules) [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f] [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation] (hF : F.IsFlatOver f) (U : T.Opens) (hU : IsAffine U.toScheme) (C : CochainComplex U.toScheme.Modules ℤ) (a : ℤ) (b : ℕ) (hge : C.IsStrictlyGE a) (hle : C.IsStrictlyLE b) (hflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme)) (hqc : ∀ n : ℤ, (C.X n).IsQuasicoherent) (hfp : ∀ n : ℤ, (C.X n).IsFinitePresentation) : (∀ {S : Scheme.{u}} (g : S ⟶ U.toScheme) (i : ℤ), i < 0 → IsZero ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology i)) ∧ (∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T') [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ, Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology q ≅ (higherDirectImage f' q).obj ((Modules.pullback g').obj F)))
```

## New

```lean
theorem proper_flat_boundedPresentation_model_baseChange {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules) (U : T.Opens) (C D : CochainComplex U.toScheme.Modules ℤ) (b d : ℕ) (hCle : C.IsStrictlyLE b) (hDge : D.IsStrictlyGE 0) (hDle : D.IsStrictlyLE d) (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme)) (hDflat : ∀ n : ℤ, (D.X n).IsFlatOver (𝟙 U.toScheme)) (e : C ⟶ D) (he : QuasiIso e) (hcomp : ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T') [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ, Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj D).homology q ≅ (higherDirectImage f' q).obj ((Modules.pullback g').obj F))) : (∀ {S : Scheme.{u}} (g : S ⟶ U.toScheme) (i : ℤ), i < 0 → IsZero ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology i)) ∧ (∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T') [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ, Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology q ≅ (higherDirectImage f' q).obj ((Modules.pullback g').obj F)))
```

The repaired theorem transports a genuine cohomology model along a quasi-isomorphism
 of bounded-above flat complexes. It proves preservation under arbitrary pullback using
 the existing K-flat interface. The actual cohomology model and perfect replacement
 are supplied together in the unchanged caller, using two strictly smaller statements:
 a Cech model without finite-presentation terms, and an affine perfect replacement
 with a chain map but no direct-image or universal-cohomology conclusion.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModelBaseChange | T2 | Own intermediate signature repaired and proof completed. |
| Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModel | unclaimed | Forced proof and proof-import adaptation; every declaration signature and visibility identical. |

The full downstream scan has 783 transitive importers, and only the caller above
 mentions the changed declaration outside its own module. All other importers retain
 their statements and definitions: the direct caller's unchanged signature is the
 public boundary, and no downstream source needs adaptation.

The forced changes to ProperFlatBoundedPresentationModel are its proof imports and
 lines 64 onward. Its former arbitrary structural witness is replaced by the Cech
 witness and the finite-presentation replacement with the missing quasi-isomorphism.
 The new comparison call passes precisely those witnesses. There are no other changes
 to that module, including its docstring and original signature.

## Status

landed 20261013T010621-L-2673236 2026-10-13 (merge of deliver/T2/Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModelBaseChange)
