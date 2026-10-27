# WeilConjectures.sfQcqsCompactSupportRealization

## Reason

The general-field realization needs a constructed normalized isomorphism and its finite projection equations. It does not need uniqueness of arbitrary natural transformations over an arbitrary field. The only consumers which actually assert uniqueness use `FiniteFieldDatum.k`, an algebraically closed field. The node review of 2026-10-17 explicitly anticipated restricting the general-K0 uniqueness assertion at stage 3 if finite-reduction rigidity fails. This delivery removes that unused general assertion and its two intermediate modules instead of relocating its hole. The arbitrary-field mathematical assertions are not disproved or replaced by weaker statements under their old names; their nodes retain their historical statements and lose their Lean attachments.

The compact-support values, integral/rational functor actions, realization type, and its projection predicate stay identical. The realization is `asIso` of the explicit `sfQcqsCompactSupportRealizationMap`: the actual reduction unit, total limit of the chosen whole strict proper/open comparison, and the inverse recorded gamma. Its finite projections and invertibility are proved separately. It does not choose an arbitrary isomorphism satisfying finite projection equations. The chosen whole strict comparison theorem already has a complete Lean proof. No witness is extracted from a theorem with a `sorry` proof. No source-library declaration is changed. No target statement changes.

## Old

The arbitrary-field detection theorem `sfQcqsCompactSupport_torsion_input_ext` was an unfinished assertion. `sfQcqsCompactSupport_reduction_ext` and `sfQcqsCompactSupport_normalizedLift_existsUnique` forwarded its claim to the following generic uniqueness theorem and definition.

```lean
theorem sfQcqsCompactSupportRealization_existsUnique :
    ∃! τ : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ≅
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι,
      SfQcqsCompactSupportRealizationSpec l E K₀ hl c τ := by
  obtain ⟨τ, hτ, huniq⟩ :=
    sfQcqsCompactSupport_normalizedLift_existsUnique l E K₀ hl c
  have hcomponent (K : sfIntegralConstructibleCategory l E X) : IsIso (τ.app K) := by
    obtain ⟨hcomplete, hfinite⟩ := sfQcqsCompactSupport_finiteComparison l E K₀ hl c K
    have hred (n : ℕ) :
        IsIso ((scalarReductionDerivedExtension l E Y n).map (τ.app K)) := by
      haveI := hfinite n
      haveI : IsIso ((scalarReductionDerivedExtension l E Y n).map (τ.app K) ≫
          (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom) := by
        rw [hτ K n]
        infer_instance
      exact IsIso.of_isIso_comp_right
        ((scalarReductionDerivedExtension l E Y n).map (τ.app K))
        (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom
    have himage := constructible_of_complete_reduction_isos l E Y hcomplete
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).property
      (fun n ↦ @asIso _ _ _ _
        ((scalarReductionDerivedExtension l E Y n).map (τ.app K)) (hred n))
    exact constructible_isIso_of_reductions l E Y (τ.app K) himage
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).property hred
  letI : ∀ K, IsIso (τ.app K) := hcomponent
  haveI : IsIso τ := NatIso.isIso_of_isIso_app τ
  refine ⟨asIso τ, hτ, ?_⟩
  intro σ hσ
  apply Iso.ext
  exact huniq σ.hom hσ

/-- The canonical realization fixed by the preceding projection normalization.
Source: Bhatt--Scholze, Definition 6.7.6
(blueprint: def-weil-integral-rational-qbar-compact-support). -/
def sfQcqsCompactSupportRealization :
    (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ≅
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι :=
  (sfQcqsCompactSupportRealization_existsUnique l E K₀ hl c).exists.choose
```

The other retired public declarations, including the old projection predicate used only by the retired normalized-lift theorem, were:

```lean
theorem sfQcqsCompactSupport_torsion_input_ext
    (τ τ' : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι)
    (h : ∀ (n : ℕ) (K : sfIntegralConstructibleCategory l E X),
      (scalarReductionDerivedRestriction l E X n).essImage K.obj →
        τ.app K = τ'.app K) : τ = τ' := by sorry
```

```lean
theorem sfQcqsCompactSupport_reduction_ext
    (τ τ' : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι)
    (h : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      (scalarReductionDerivedExtension l E Y n).map (τ.app K) =
        (scalarReductionDerivedExtension l E Y n).map (τ'.app K)) : τ = τ' := by
  apply sfQcqsCompactSupport_torsion_input_ext l E K₀ hl c τ τ'
  intro n K hK
  have hQ := sfQcqsCompactSupport_torsion_coefficient_action l E K₀ hl c n K hK
  exact reduction_map_ext_on_restriction
    (derivedScalarExtensionRestrictionAdjunction l E Y n).choose hQ (h K n)
```

```lean
def SfQcqsCompactSupportMorphismSpec
    (τ : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι) : Prop :=
  ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    (scalarReductionDerivedExtension l E Y n).map (τ.app K) ≫
        (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom =
      (finiteReductionIso l E Y n).inv.app ((image (completed l E) c).obj K.obj) ≫
        (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app K.obj ≫
        (finiteImageIso l E n c).hom.app
          ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj K.obj) ≫
        (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
          ((finiteReductionIso l E X n).hom.app K.obj)

/-- The finite proper/open mates lift to one natural morphism into the recorded
integral action, uniquely with their prescribed projection normalization. Invertibility
is a separate assertion: this theorem constructs and identifies a morphism only.

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks Tags 0941 and 0F7J
(blueprint: lem-qcqs-compact-support-normalized-lift).

Proof: use the coherent compact-support reduction tower, including its actual quotient
transitions, and the total right-derived limit and projection-normalized comparison
recorded in `exists_compactSupportRepresentativeComparison`. On strict K-flat input
complexes the open scalar-adjunction mate is the extension-summand tensor map. Apply
proper direct image to that whole diagram, and its right-adjunction comparison with
total inverse limit. The source augmentation is the canonical completion unit.
The resulting natural morphism into the total limit transports through the recorded
gamma to the specified integral action. Transpose each projection through the fixed
scalar adjunction: the unit/counit identities give exactly the displayed equation,
including `finiteReductionIso` and `finiteImageIso` as its endpoint coordinates.
The construction commutes with roofs since all transformations are derived on whole
strict complexes. For uniqueness use those normalized universal comparisons on strict
resolutions and the total-limit adjunction, before evaluation; the prescribed projection
mates are the same universal counit, and its Hom transpose is unique. Transport back
through gamma gives equality of the natural morphisms. This last step is a rigidity
statement for these functors and this normalization, not a claim that unrelated finite
evaluations are faithful on a derived category. Zero input and the empty scheme cause
no change to the universal comparison or its naturality. -/
theorem sfQcqsCompactSupport_normalizedLift_existsUnique :
    ∃! τ : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι,
      SfQcqsCompactSupportMorphismSpec l E K₀ hl c τ := by
  obtain ⟨σ, hσ⟩ := sfQcqsCompactSupport_normalizedIso_exists l E K₀ hl c
  let τ := σ.hom
  have hτ : SfQcqsCompactSupportMorphismSpec l E K₀ hl c τ := hσ
  refine ⟨τ, hτ, fun τ' hτ' ↦ ?_⟩
  apply sfQcqsCompactSupport_reduction_ext l E K₀ hl c τ' τ
  intro K n
  apply (cancel_mono (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom).mp
  exact (hτ' K n).trans (hτ K n).symm
```

The other public theorem signatures retired with the entire assigned module are:

```lean
theorem sfQcqsCompactSupport_torsion_input_iff_reduction_eq (τ τ' : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶ sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙ (sfIntegralConstructible l E Y).ι) : (∀ (n : ℕ) (K : sfIntegralConstructibleCategory l E X), (scalarReductionDerivedRestriction.{u, u} l E X n).essImage K.obj → τ.app K = τ'.app K) ↔ (∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ), (scalarReductionDerivedExtension.{u, u} l E Y n).map (τ.app K) = (scalarReductionDerivedExtension.{u, u} l E Y n).map (τ'.app K))
```

```lean
theorem sfQcqsCompactSupport_torsion_input_ext_of_finite_shifted_hom (hfin : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ), Finite (((image (completed l E) c).obj K.obj)⟦(1 : ℤ)⟧ ⟶ (sfDerivedReductionRestricted l E Y n).obj ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj)) (τ τ' : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶ sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙ (sfIntegralConstructible l E Y).ι) (h : ∀ (n : ℕ) (K : sfIntegralConstructibleCategory l E X), (scalarReductionDerivedRestriction l E X n).essImage K.obj → τ.app K = τ'.app K) : τ = τ'
```

```lean
theorem sfQcqsCompactSupport_torsion_input_ext_of_isAlgClosed [IsAlgClosed K₀] (τ τ' : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶ sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙ (sfIntegralConstructible l E Y).ι) (h : ∀ (n : ℕ) (K : sfIntegralConstructibleCategory l E X), (scalarReductionDerivedRestriction l E X n).essImage K.obj → τ.app K = τ'.app K) : τ = τ'
```

## New

The entire assigned `QcqsCompactSupportTorsionInputDetection` module is withdrawn: its finite-evaluation and torsion-input criteria are unnecessary for the direct finite-Hom uniqueness proof. `QcqsCompactSupportReductionRigidity` and `QcqsCompactSupportNormalizedLift` are likewise withdrawn as empty modules. All six nodes are retained and detached. A full parent scan includes all statement/proof/step dependencies and quarantined sources; only the retired chain and the parent updated here used these assertions. The realization is constructed and specified without these nodes. Optional uniqueness is now a separately named theorem proved directly by finite shifted Hom and the Milnor injection over an algebraically closed field, exactly sufficient for every consumer of uniqueness.

```lean
def sfQcqsCompactSupportRealizationMap :
    (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι :=
  let H := qcqsCompactSupport_strictReductionComparison l E K₀ hl c
  let SY := H.choose_spec.choose
  let β := H.choose_spec.choose_spec.choose
  let γ := H.choose_spec.choose_spec.choose_spec.choose
  let A := (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c
  Functor.whiskerLeft A SY.adjunction.unit ≫
    Functor.whiskerRight (Functor.whiskerLeft (sfIntegralConstructible l E X).ι β)
      (coefficientSequenceLimit l E Y) ≫ γ.inv

/-- The explicit universal comparison has the finite proper/open projection coordinates.
Source: Bhatt--Scholze, Definition 6.7.6; Stacks 0941, 0F7J
(blueprint: def-weil-integral-rational-qbar-compact-support).

Proof: transpose the actual reduction unit and total-limit projection under the
finite scalar adjunction. The normalized strict comparison equations identify the
two resulting factors with the actual proper/open mate in the stated coordinates. -/
theorem sfQcqsCompactSupportRealizationMap_spec :
    ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      (scalarReductionDerivedExtension l E Y n).map
          ((sfQcqsCompactSupportRealizationMap l E K₀ hl c).app K) ≫
          (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom =
        (finiteReductionIso l E Y n).inv.app ((image (completed l E) c).obj K.obj) ≫
          (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app K.obj ≫
          (finiteImageIso l E n c).hom.app
            ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj K.obj) ≫
          (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1))
            c).map ((finiteReductionIso l E X n).hom.app K.obj) := by
  let H := qcqsCompactSupport_strictReductionComparison l E K₀ hl c
  let SX := H.choose
  let SY := H.choose_spec.choose
  let β := H.choose_spec.choose_spec.choose
  let γ := H.choose_spec.choose_spec.choose_spec.choose
  have hβ := H.choose_spec.choose_spec.choose_spec.choose_spec.1
  have hγ := H.choose_spec.choose_spec.choose_spec.choose_spec.2
  intro K n
  exact (projection_transpose (coefficientFiniteAdjunction l E Y n) SY.adjunction
    (coefficientSequenceDerivedEvaluation l E Y n) (coefficientSequenceProjection l E Y n)
    (SY.reductionEvaluation n) (fun P ↦ SY.unit_projection P n)
    (β.app K.obj) (γ.app K)
    _ (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom (hγ K n)).trans (hβ K.obj n)

/-- The explicit comparison is invertible on every integral constructible input.
Source: Bhatt--Scholze, Lemma 6.7.7; Stacks 0941, 0F7J
(blueprint: def-weil-integral-rational-qbar-compact-support).

Proof: its finite reductions are the invertible proper/open coefficient mates.
Completeness of the actual output and these reductions give its constructibility.
The constructible cone then has zero reductions; its completeness Roos triangle
makes it zero. Componentwise invertibility gives invertibility of the transformation. -/
theorem sfQcqsCompactSupportRealizationMap_isIso :
    IsIso (sfQcqsCompactSupportRealizationMap l E K₀ hl c) := by
  let τ := sfQcqsCompactSupportRealizationMap l E K₀ hl c
  have hcomponent (K : sfIntegralConstructibleCategory l E X) : IsIso (τ.app K) := by
    obtain ⟨hcomplete, hfinite⟩ := sfQcqsCompactSupport_finiteComparison l E K₀ hl c K
    have hred (n : ℕ) :
        IsIso ((scalarReductionDerivedExtension l E Y n).map (τ.app K)) := by
      have := hfinite n
      have : IsIso ((scalarReductionDerivedExtension l E Y n).map (τ.app K) ≫
          (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom) := by
        rw [show (scalarReductionDerivedExtension l E Y n).map (τ.app K) ≫
            (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom = _ from
          sfQcqsCompactSupportRealizationMap_spec l E K₀ hl c K n]
        infer_instance
      exact IsIso.of_isIso_comp_right
        ((scalarReductionDerivedExtension l E Y n).map (τ.app K))
        (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom
    have himage := constructible_of_complete_reduction_isos l E Y hcomplete
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).property
      (fun n ↦ @asIso _ _ _ _
        ((scalarReductionDerivedExtension l E Y n).map (τ.app K)) (hred n))
    exact constructible_isIso_of_reductions l E Y (τ.app K) himage
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).property hred
  let : ∀ K, IsIso (τ.app K) := hcomponent
  exact NatIso.isIso_of_isIso_app τ

/-- The constructed realization of the recorded integral compact-support action.
Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks 0941, 0F7J
(blueprint: def-weil-integral-rational-qbar-compact-support). -/
def sfQcqsCompactSupportRealization :
    (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ≅
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι :=
  letI := sfQcqsCompactSupportRealizationMap_isIso l E K₀ hl c
  asIso (sfQcqsCompactSupportRealizationMap l E K₀ hl c)

/-- The constructed realization has the actual finite proper/open projection coordinates.
Source: Bhatt--Scholze, Definition 6.7.6; Stacks 0941, 0F7J
(blueprint: def-weil-integral-rational-qbar-compact-support).

Proof: these are the projection equations of the explicit universal comparison. -/
theorem sfQcqsCompactSupportRealization_spec :
    SfQcqsCompactSupportRealizationSpec l E K₀ hl c
      (sfQcqsCompactSupportRealization l E K₀ hl c) :=
  sfQcqsCompactSupportRealizationMap_spec l E K₀ hl c

/-- The projection-normalized realization is unique over an algebraically closed field.
Source: SGA 4½, finiteness theorem; Bhatt--Scholze 6.7.6--6.7.7; Stacks 0941.
(blueprint: def-weil-integral-rational-qbar-compact-support).

Proof: cancel the finite reduction isomorphisms in the projection equations.
The recorded output is constructible and complete. Transport the algebraically
closed finite shifted-Hom theorem through the constructed realization to obtain
finite shifted Hom from the actual output into each restricted output reduction.
The Milnor injection then identifies the two components. Natural-transformation
and natural-isomorphism extensionality prove uniqueness. No assertion of uniqueness
over an arbitrary base field is used to construct the realization. -/
theorem sfQcqsCompactSupportRealization_existsUnique_of_isAlgClosed [IsAlgClosed K₀] :
    ∃! τ : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ≅
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι,
      SfQcqsCompactSupportRealizationSpec l E K₀ hl c τ := by
  let σ := sfQcqsCompactSupportRealization l E K₀ hl c
  have hσ := sfQcqsCompactSupportRealization_spec l E K₀ hl c
  refine ⟨σ, hσ, fun τ hτ ↦ ?_⟩
  apply Iso.ext
  ext K
  let M := (sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K
  apply derivedComplete_finiteReduction_ext l E Y M.property.1 ?_
    (τ.hom.app K) (σ.hom.app K) ?_
  · intro n
    let e := (shiftFunctor _ (1 : ℤ)).mapIso (σ.app K)
    have hfin : Finite
        (M.obj⟦(1 : ℤ)⟧ ⟶ (sfDerivedReductionRestricted l E Y n).obj M.obj) :=
      integralReduction_shiftedHom_finite_algClosed l E K₀ hl Y M M n
    exact @Finite.of_equiv _ _ hfin (e.homCongr (Iso.refl _)).symm
  · intro n
    apply (cancel_mono (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom).mp
    exact (hτ K n).trans (hσ K n).symm
```

Four proofs that previously unfolded the arbitrary-field uniqueness witness now use `sfQcqsCompactSupportRealization_spec`: `CompactificationCompletedRealization`, `IntegralOpenSupportNormalization`, `IntegralSupportCounitProjection`, and `IntegralSupportTowerNormalization`. `CompactSupportCoefficientModels` uses `sfQcqsCompactSupportRealization_existsUnique_of_isAlgClosed` for its two algebraically closed uniqueness assertions, with the local standard instance `let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀` derived from its existing datum. All their signatures stay identical. The coefficient-model proof uses the constructed comparisons directly for its object-property clauses and the separate uniqueness theorem only for the two final assertions. The construction is locally irreducible in that consumer, with transparency respected, to avoid unnecessary unfolding during elaboration.

To keep each file below the compile limit, proved helpers from the coefficient-model
consumer move verbatim to `Sheaf.Paper.CompactSupportCoefficientModelHelpers`:
`coefficientExtensionTensor_naturality`, `coefficientIntegralBasis`,
`coefficientQuotientBasis`, `coefficientSectionModule`, `coefficientTensor_hom_ext`,
`tensorCancellationUnique`, `coefficientBalancingNaturalIso_existsUnique`,
`coefficientBalancingNaturalIso`, `coefficientBalancingNaturalIso_tmul`,
`coefficientModuleBalancing`, `coefficientBalancingNaturalIso_app`, and
`coefficientLocalizationUnique`. The previously private natural-balancing uniqueness lemma is now the public
`WeilConjectures.compactSupportCoefficientModels_balancing_existsUnique`, with its
unchanged signature and proof attached to the new node
`lem-pur-compact-support-coefficient-balancing-natural-iso`. All other helpers remain
private, and no unproved statement is added. The consumer uses `import all` and retains all its original public
names and signatures. Its DAG attachment remains there, with a note recording the
proof split and its new proved natural-balancing node. The old whole consumer took 80--84 seconds; its profile showed
37.5 seconds in tactic execution, 21.3 in type checking, and 25.9 in linting.
Local irreducibility and simplifying the final proof alone did not resolve the timeout.
After the private split, the helper compiles in 32.9 seconds and the retained public
consumer in 46.1 seconds. All seven delivered Lean modules pass in import order.

All eight other existing modules edited or withdrawn were rechecked against the live
claim records after adding the helper node; all remain unclaimed. The balancing
normalization writes its scalar action explicitly via `ModuleCat.isModule`; its
mathematical statement and proof are unchanged from the previous private helper.

## Users

The table includes the full source downstream closure, as reported by `tools/downstream.py`; textual occurrences of the removed generic uniqueness theorem are exactly the adapted proofs listed above. Other users retain the same realization type and projection predicate. Current claims were read from the coordination records. Direct importers and textual users are checked with the delivery overlay.

| module | group holding it | effect |

| --- | --- | --- |

| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.CartierKummerDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.ClosedTransportedHomCounitFormula | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.DiagonalDifferenceCentredChartConstruction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.DiagonalDifferenceChartRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameChange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.DiagonalDifferenceNormalFrameConstruction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.DiagonalDifferenceReesFrame | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.ProperOpenRefinementAlphaPlusInclusion | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.ProperOpenRefinementMatePlusCompatibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.DeligneLaumon.ContinuousCoefficientGeometricCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.DeligneLaumon.FiniteStageFibreVanishing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.DeligneLaumon.NormalizedContinuousCoefficientFamily | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.DeligneLaumon.NormalizedStratifiedEmbeddedLattices | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.DeligneLaumon.OrdinarySectionScalarComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.DeligneLaumon.RawHeartAdicComparisonBridge | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.DeligneLaumon.RawHeartAdicLisseData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.DeligneLaumon.RawHeartAdicStrataBridge | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.FourierTransform.FourierDeligneTransform | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicActualSystemsNormalized | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicAmbientHomEvaluationComparison | Q1 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicClosureScalarCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicCommonStageFibreTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicCommonStageFibreZeroMap | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicCommonStageHeartExactness | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicCompletedTensorRealizationDescent | Q2 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicFibreComparisonData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicFiniteConstructibilityComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicFiniteRealizationCocone | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicFiniteRealizationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicFiniteScalarCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicNormalizedFibreCommonStage | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicNormalizedFibreCommonStageData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicNormalizedFibreData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicNormalizedFibreExactness | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicNormalizedFibrePullback | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicNormalizedFibreScalar | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicNormalizedPullbackRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicNormalizedPuritySystems | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicOperationDomainsSourceComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicProperOrdinaryPushPreservation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicPunctualWeights | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicPurityFiniteTensorComponents | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicPurityObjects | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicPuritySourceNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicPuritySourceTransitionSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicPurityTwistRestrictionComponents | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicRealizationFamilyData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicReindexingCore | C4 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicReindexingFunctoriality | D2 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicReindexingHom | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicReindexingTensor | A5 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicStratifiedPullbackInterface | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineCoefficientCounitMaps | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineCoefficientCounitNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineCounitMateUnitChange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineCurveHcZero | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineDiagonalDncCoordinateIdentity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineDiagonalDncNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineDiagonalIntegrationConstructions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineDiagonalIntegrationOrientation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineDiagonalIntegrationTranslationIntegration | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineDiagonalIntegrationTranslationTranspose | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineDiagonalPowerCoefficient | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineDiagonalPresentedBaseChange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineDiagonalRawTransposePower | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineDiagonalRestrictedTransposes | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineDiagonalSectionCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineDiagonalTateCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineDiagonalTraceRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineDiagonalTransposePower | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineIntegrationExponentTransition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineLineComparisonNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineLineCompositeTranspose | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineLineInvariance | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineLinePurityComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineLinePuritySource | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineLineStandingTranspose | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineOrderedCounitData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineOrderedCounitDescentComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineOrderedCounitSuccessor | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineOrderedCounitZero | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineOrderedEvaluationContraction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineOrderedFirstLineCounit | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineOrderedIntegrationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineOrderedIntegrationSuccessor | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineOrderedIntegrationTransposes | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineOrderedTransposeCounit | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineSpaceProductDomain | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineSpacePurityComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineSpacePurityCompositionMaps | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineSpacePurityCoordinateInvariance | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineSpacePurityOrderedBlocks | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineSpaceThomMap | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineSpaceZeroSectionConstructions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineSpaceZeroSectionPurity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineTargetDiagonalDnc | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineTowerIntegrationSiteTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineTranslationTrace | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AffineVectorTracePresentation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BarrettIndRealization | R5 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BaseChangedLineTraceEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BasicOperationCoefficientCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BasicOperationReductionAndEvaluation | Z9 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BoundaryDualizingComposition | P9 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BoundaryFiniteEvaluationRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BoundaryFiniteSiteData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BoundaryFiniteSiteRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BoundaryFiniteTorDomains | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BoundaryQFoundation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BoundaryQMaps | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BoundaryQTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.BoundedSiteExchangeTransposes | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CartesianSectionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CartierClassAgreement | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CartierRelativeKummerRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CartierSupportedComparisonSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CentredDiagonalSourcePasting | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ChartDiagonalSourceSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ChartDncNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ChartDncSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ChartDncVectorFactorData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ChartDncVectorFactors | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ChartEpsilonPasting | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ChartExceptionalCounitEquation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ChartIntegrationAdjoints | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ChartNormalIntegrationSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ChernFlagFormula | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalFiltrationDiagramFibres | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalFiltrationExactDiagram | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalFiniteWeilDiagramData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalFiniteWeilDiagramRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalFrontierExistence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalLisseWeilFrontierData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalLocalFrobeniusData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalNormalizedTwoFibreComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalNormalizedTwoFibreData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRawLisseCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRawLisseCommonDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRawLisseCommonFibres | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRawLisseCommonRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRawLisseCommonRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRawLisseCommonRestrictionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRawLisseCommonSystem | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRawLisseFiniteConstruction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRawLisseFiniteOperations | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRawLisseIntrinsicFibrePullback | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRawLisseOperations | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRawLissePointFibres | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRawLisseRealizationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRawLisseScalarCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRealizationLocalSpectrum | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRealizationPunctualPurity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalRealizedAnchorEigenvalue | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalSuccessiveRestrictions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalSystemRawLisseRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalTwoFibreCommonData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalTwoFibreScalarData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalWeilCoherentDiagramStages | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalWeilFiltrationTransportData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalWeilFiniteDiagramDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalWeilPrescribedIsomorphismLifts | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClassicalWeilRestrictionExistence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClopenCompletedTowerRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClopenCounitAdjointComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClopenPrescribedWeilFiltration | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClopenSystemRealizationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClopenSystemRestrictionEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClosedCoefficientTransposeCocycles | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClosedScalarDomains | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ClosedSupportExceptionalMate | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CochainLocalizationTensorIso | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoefSupportOpenTensorModel | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoefSupportPointSectionsComparisonExistence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoefSupportPointSectionsData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoefSupportPointSectionsModelExistence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoefficientFirstCompactSupportSiteSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoefficientMapGeometricSquares | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CommonAdicSectionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CommonConstantUnitFrobenius | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CommonFrobeniusSquareNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CommonStageOpenHeartAdjunction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CommonStagePointReturn | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CommonStageSmoothOperationCore | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CommonStageSmoothOperationShift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportCoefficientModels | unclaimed | Proof adapted to the specification or algebraically closed uniqueness theorem; signature identical. |

| Sheaf.Paper.CompactSupportCompletedProjectionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportCompletedScalarArrow | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportCompositeTransposeDomains | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportCondensedRealization | H1 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportCondensedRealizationSetup | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportLimitEquationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportLimitEquationRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportNativeEffectivity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportNativeRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportNormalizedRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportNormalizedScalarDescent | T5 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportPathReductionSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportProjectionCoherenceLaws | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportProjectionFieldStages | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportProjectionFiniteStages | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportProjectionIntegralStages | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportProjectionRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportProjectionRealizationLift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportProjectionRightUnit | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportRealizationCoordinates | K4 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportRealizationFactorNormalization | K2 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportRealizationFactorization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportRealizationIdentity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportScalarGammaIdentification | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportScalarLimitCompletedComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportScalarLimitFoundations | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportScalarLimitReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportScalarProjectionIdentification | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportScalarRoosNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportScalarRoosTensorNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportScalarShiftNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportScalarShiftStructures | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportScalarShiftWitness | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportStageActionAdjunction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportStrictScalarComposition | H2 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportStrictScalarRefinement | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportSystemTransposeNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactSupportTotalLimitRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactificationBOrdinaryProjectionSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactificationBProjectionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactificationBProjectionDomains | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactificationBProjectionReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Proof adapted to the specification or algebraically closed uniqueness theorem; signature identical. |

| Sheaf.Paper.CompactificationCompletedRealizationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactificationFiniteProjectionModels | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactificationStrictRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ComparedSmoothExchangeComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ComparisonImageClosedSectionNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ComparisonPullbackRestrictionCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompleteIntegralConstantRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompleteProjectionDescentMaps | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompleteProjectionMateDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompleteProjectionReductionSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompletedContinuousHomHypotheses | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompletedLocalFibreComparisonData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompletedPullbackFractionDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompletedScalarAssociatorLocalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompletedScalarExactLocalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompletedScalarTransportCounit | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompositionIteratedMateExpansion | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompositionSingleMatePresentation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CompositionTensorMate | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConcreteIntegralProjectionCone | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConcreteOpenScalarTensorSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConcreteProjectionCoefficientCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConcreteProjectionFactorizationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConcreteProjectionFieldDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConcreteProjectionReductionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConcreteProjectionReductionSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConcreteProperScalarTensorSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConcreteSupportScalarIsomorphism | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CondensedTateIntegralTower | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CondensedTateIntegralTowerData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantCompletedOrdinaryAssociativity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantCompletedScalarAssociativity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantDirectImageTowerRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionCyclicSheetPartition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionPullbackSheetComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionRestrictionLocalConjugacy | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionReturnData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionReturnExactFunctor | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionReturnLocalOperators | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionReturnLocalSpectra | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionReturnTransportComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionSheetCoefficientEquivalences | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionSheetCommonStageEquivalences | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionSheetGeometry | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionSheetHeartData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionSheetTensorSplitting | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionWeilHeartData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleCompactSupportTargetIso | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleExceptionalCoefficientAssemblyData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleExceptionalCoefficientStages | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleExceptionalCompositor | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleExceptionalCompositorData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleExceptionalLeftRefinements | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleExceptionalRefinementMate | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleLeftCompositorCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleMateCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleRationalHomComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleRationalLeftRefinement | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleRingLeftRefinement | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleTensorComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ConstructibleWeilModelSquares | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ContinuousAmbientGeometricCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateAdjunctionComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateCartierBoundarySign | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateLineAdjunction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateLineAdjunctionMaps | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateLineAugmentationRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateLineConjugateExponents | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateLineCounitTensor | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateProductPresentations | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateSectionArrows | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateSectionProductRecursion | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateSectionProjection | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateSectionProjectiveTrace | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateSectionSiteTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateSectionTensorTrace | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateSupportedProductRecursion | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateTowerCompactTranspose | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateTowerExceptionalCompositors | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateTowerNormalizationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateTowerNormalizationFusion | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateTowerNormalizationInduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoordinateZeroBaseChange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CurveClassicalFiltrationPullback | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CurveClassicalPullbackExists | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CurveRestrictionFiltrationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.CurveRestrictionLocalPowers | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DerivedTensorRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DerivedWeilOperations | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalAffineCounitRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalAffineIntegrationSiteSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalAffineRankZeroActual | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalAffineTraceCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalAffineTraceMapAgreement | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalAffineTraceSiteComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalAffineTraceSiteData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalCounitComparisonData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalDncAffineModel | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalDncChartNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalDncEtaleBeta | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalDncEtaleDualizing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalDncEtaleFactors | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalDncEtaleNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalDncEtaleNaturalityLocalInverse | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalDncEtaleNaturalityTwist | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalEtaleAlphaSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalEtaleFactorization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalEtaleInverseDeformation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalEtaleLocalityUnitChange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalEtaleNormalEndpoint | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalEtaleNormalTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalEtaleRestrictedDualizingData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalEtaleRhoUnitSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalEtaleSourceDualizing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalEtaleSourceEndpoint | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalEtaleSourceTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalOrdinaryChartLift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalOrdinaryOrientationGluing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalOrdinaryOrientationNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalOrdinaryOverlap | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalOrdinaryRealizeRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalOrientationChartExistence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalOrientationCharts | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalOrientationCompatibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalOrientationRefinement | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DiagonalOrientationRefinementData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DifferenceCoordinateSectionIdentifications | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DifferenceFirstInputRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DifferenceSecondInputRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DoubleDiagonalSectionIdentifications | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DualBaseChange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DualStalkFrobenius | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DualizingCocycleSourceEtale | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DualizingObjectPurity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DualizingPrimitiveOpenRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DualizingSigmaCocycleLocality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.DualizingUnitComposite | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.EtaleCartesianTowerTensorComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.EtaleCompositeEComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.EtaleMiddleTensorAssembly | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.EtaleTensorSourceTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.EvenLineBinaryProductNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.EvenLineCoefficientProjectionNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.EvenLineCoordinateIntertwining | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.EvenLineProductIntegrationMaps | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.EvenLineProductIntegrationSymmetry | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.EvenTateLineSelfSymmetry | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExactProperOpenProjectionMate | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalCommonStageFromRational | E2 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalDualizingBaseChangePasting | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalFieldDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalFieldStageCompletion | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalFiniteIntrinsicBounds | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalFiniteOperations | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalFiniteRestrictionAdjunction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalIntegralAdjunctionLocalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalIntegralAdjunctionLocalizationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalIntegralScalarMates | R9 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalIntegralSupportAdjoint | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalRationalStageLocalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalRefinementLeftConstruction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalRefinementMatesData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalRefinementRightSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalRefinementSystemData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalRefinementSystemRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalRefinementTransportData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalRingScalarMates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalRingStageAssembly | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalRingStageAssemblyData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalRingTransportFamily | M9 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalScalarMateLocalization | E3 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExchangeFunctoriality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FdPullbackWeilReturnSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FieldCohomologyPerfectDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FieldOrientedExchangeSquares | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FieldProjectionRefinementSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FieldShriekCompositionCoefficientSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FieldShriekCompositionIntegralComponent | S5 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FieldShriekCompositionIntegralNaturality | S6 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FieldShriekCompositionNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FilteredCondensedCanonicalComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FilteredCondensedCounitBijective | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FilteredCondensedCounitFiniteFormula | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FilteredCondensedRepresentingPair | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FilteredCondensedRepresentingPairData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteClopenExceptionalRestriction | R3 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteCompactSupportCoefficientSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteCompactSupportEvaluationRefinement | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteDiagonalDncReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteDiagonalVectorReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteEtaleSectionIntegration | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteEtaleSpecializationCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteExceptionalSiteNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteFirstRootChart | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteForwardCompactifiedSwap | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteForwardProductCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteFreeCoefficientExtensionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteFreeCompactSupportData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteFreeCompactSupportGeometricSquares | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteFreeCompactSupportSiteSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteGeometricOrientationExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteGeometricPurityCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteGeometricPurityFactors | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteGeometricPurityMate | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteGeometricTensorExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteIntrinsicProjectionCompatibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteIntrinsicProjectionRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FinitePointCounitUnitNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FinitePositiveChartFrameExt | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FinitePositiveChartRecursion | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FinitePositiveRootChartPower | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FinitePositiveRootCharts | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProCoefficientCounitTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProductCompactification | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProductOpenRestrictionPasting | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProductOrdinaryNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProjectionBinaryIterationTrianglePasting | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProjectionBinarySquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProjectionBinaryTriangleSquare | E4 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProjectionCompactificationSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProjectionCompactificationTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProjectionCompositionRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProjectionCompositionTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProjectionExchangeData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProjectionFromDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProjectionIdentityNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProjectionOpenAssembly | F1 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProjectionOperationPresentation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProjectionRefinementLeft | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteProjectionTensorSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FinitePublishedRootChartPower | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FinitePuritySourceUnitReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteRankZeroNormalIntegration | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteRationalHeartComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteReductionBaseChangeSource | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteReductionExceptionalFiniteModel | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteReductionLineChartScalars | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteReductionLineInputConstructible | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteReductionReassociation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteReductionShiftedPullbackCube | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteReductionSourceChartIndependence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteReductionTensorSource | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteRefinementAmbientNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteRefinementProjectionRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteRestrictionDiagramNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteRingRefinementCoordinates | B7 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteRootLinePowerTransition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteScalarCochainComparisonIso | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteScalarMonoidalRepresentative | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteScalarRepresentativeIso | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteScalarTensorData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteScalarTensorSource | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteSheafH0Augmentation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteSignedTwistProducts | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteSmoothProQuotientTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteSmoothZeroOrientationCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteSourceChartPowerTransition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteSourceChartScalarTransition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTargetChangeCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTateSourceMap | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTateSourceStructuralCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorComparisonEquations | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorLineChartReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorLineDerivedExistence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorPresentationReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorProductFrameExt | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorProductMap | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorProductMapIsIso | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorPullbackCompositionReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorPullbackTensorReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorReductionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorSemilinearReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorShiftCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorShiftFirst | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorShiftSecond | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorSignedReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTensorSymmetryCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTorStability | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTripleProductDefinitions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTripleProductNormalForms | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FlagLocalComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ForwardProductCoordinateTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FourierKernelConvolution | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FourierTraceFormula | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FrobeniusSystemExchangeInverse | K3 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.FrobeniusWitnessedCompactification | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.GeneralChartComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.GeometricCommonStageDirectImage | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.GeometricComparisonData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.GeometricOperations | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.GeometricQuotientWeilCompositionSeries | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.GermReparametrizationDerivedDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.GlobalIdentityNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.GlobalVerdierDualityData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.HigherTensorIdentityComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IdentityCompactificationLimitComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IdentityCompactificationSystemMate | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralClosedSupportNormalization | P6 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralCompositionCoefficientSquare | T9 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralDatumPullCompositionReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralDualizingExceptionalUnit | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralLissePullbackNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralNormalizedRingRefinementLaws | B8 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralOpenAdjunctionReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralOpenAdjunctionTransposeNormalization | S7 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralOpenEmptyPullbackVanishing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralOpenProjectionCoefficientData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralOpenPullTensorReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralOpenSupportNormalization | unclaimed | Proof adapted to the specification or algebraically closed uniqueness theorem; signature identical. |

| Sheaf.Paper.IntegralOrientedExchangeSquares | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralPointTransportComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralPointTransportTowerData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionCoordinateData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionDirectFactorEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionFactorEvaluationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionFiniteEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionMiddleMap | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionOpenFactorEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionOpenFactorReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionOpenTensorCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionOperationPresentation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionProperFactorReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionPullEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionReductionCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionReductionNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionRefinementSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionSupportEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionSupportFactorCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionSystemCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionSystemEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProjectionTensorEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProperOperationProjection | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProperProjectionCoefficientData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProperProjectionSystemNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProperSupportReductionIdentity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralProperTensorPullbackReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralPublishedCounitEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralQuotientCohomologicalBounds | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralScalarIsomorphismExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralSectionsPerfectReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralSemilinearGermSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralStageProjectionReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralStageProjectionStructuralIdentities | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralSupportAdjunctFiniteCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralSupportFunctorNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralSupportNormalizationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegralSupportReductionNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegrationAffineExponentTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegrationCoefficientProjectionNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegrationExponentTransposeData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegrationExponentTransposeTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntegrationProjectiveExponentSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.InternalHomPullback | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntrinsicConstructibleFibreExactness | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IntrinsicLocalLatticeComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.InverseContravariantBidual | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IsomorphismFiniteExchangeCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IteratedTateSourceComposite | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.IteratedWeilMap | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.KummerSiteCohomologyNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LineCounitComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LineKummerFieldRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LineZeroClassExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LisseExtensionInertia | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LisseFieldNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LisseLatticeChoiceExistence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LisseLatticeHeartLift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LisseLatticeHeartLiftData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LisseLatticeLisseDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LisseLatticeNormalizedRealizations | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LisseLatticeRealizationFaithful | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LisseLatticeSingleComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LissePointNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LissePointSectionsRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LissePullbackNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LisseRationalRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LisseTensorNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LisseTensorPullbackRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LisseTensorPullbackRealizationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocalFrobeniusLargeCoefficients | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocalFrobeniusLargeCompositionAssociativity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocalFrobeniusLargeCompositionCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocalFrobeniusLargeScalarTower | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocalFrobeniusLargeTransportAddition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocalFrobeniusLargeTransportNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocalFrobeniusLargeWeilAddition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocalFrobeniusStepCompatibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocalizedTopChern | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocallyFiniteAdicCompactSupportData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocallyFiniteAdicConstructibleRealization | R1 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.LocallyFiniteCompactSupportStageAction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.MiddleExchangeProjectionBaseChange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.MixedCompactSupportExchangeData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.MixedCupCoefficientChange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.MixedCupCoefficientData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.MixedCupCoefficientSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.MixedCupFieldCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.MixedCupFieldNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.MixedCupFieldOperations | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.MixedCupOperationComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.MixedCupRingedNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.MixedCupTensorClosure | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.MixedCupTensorComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.MixedCupTensorElementary | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.MixedCupTensorNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ModelAffineIntegrationOrientation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ModelChartOrientationAssembly | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ModelOrientationChartDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ModelOrientationSourceNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ModelOrientationTateDetection | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeAdicCompactSupportSums | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeAdicRealizationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeAdicReindexingData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeCoefficientInverseImage | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeCompactSupportFiniteComparison | N3 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeCompactSupportGeometry | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeDirectImageSections | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeWeilComparisonStructure | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeWeilDerivedInductionComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeWeilDualizingHomTransposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeWeilFreeCoproduct | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeWeilHeartProperties | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeWeilInductionComparisonData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeWeilInductionSummands | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeWeilProperNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | J3 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalSectionIntegrationBaseChange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalSectionIntegrationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalSectionIntegrationOrientation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedCommonCoefficientLaws | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedEtaleComparisonComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedEtaleRestrictionComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedFieldPurityTrace | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedHeartRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedIntegralScalarUnit | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedIntegralScalarUnitUnderlying | F2 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedLatticeFiniteFree | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedOrientationPerfectDuality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedPullbackCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedPullbackNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedPullbackObjects | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedRationalLeftComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedRationalLeftIdentity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedRationalLeftLaws | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedRingRefinementLaws | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedScalarAssociatorLocalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedScalarAssociatorLocalizationTransport | K7 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedSmoothOrientationUnits | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedStageCoefficientCalculus | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedSupportEtalePresentation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedTateTensorTower | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedTateTensorTowerCore | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedTateTensorTowerProperties | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.NormalizedTateTensorTowerZero | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OmegaProperCoefficientProjection | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OmegaProperCoefficientProjectionHomology | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OpenWeilCarrierRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OpenWeilCoefficientFibres | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OpenWeilFiniteStageFrobenius | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OpenWeilGeometricFibres | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OpenWeilPunctualSpectrum | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OperationCoefficientActionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OperationScalarTransportNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OrderedAffineComparisonNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OrderedAffineLineTransposeNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OrderedAffineTransposeData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OrderedAffineTransposeProjection | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OrderedAffineTransposeSuccessor | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OrderedIntegrationComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OrdinaryOpenScalarComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OrientationCoordinateBoundaryPullback | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OrientationCoordinateModelBoundary | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OrientationLocalResidue | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OrientedPerfectDuality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.OriginalScalarMateShift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.P1KummerTraceSiteTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PerfectDualPairAndTateStability | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PfReductionProperOpenIdentities | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PodReconstructionCommonStageCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PodReconstructionCommonStageData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PodReconstructionRawRationalNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PodReconstructionScalarRealizations | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PoincareDualityConventions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointFiniteMultiplicationInverse | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointFrobeniusNormalizationDefinitions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointFrobeniusTransportNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointIdentityExchangeRecipe | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointPowerRoosComparisonSpecialization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointPowerStrictInsertionSpecialization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointPullbackConeLocalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointQuotientComparisonCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointQuotientTowerCoherentSource | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointQuotientTowerData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointQuotientTowerHomotopy | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointReductionAugmentationComplete | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointRestrictionWholeRoosSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointScalarPunctualSpectrum | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointSectionsCompletionCone | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointSystemInsertionComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointSystemInsertionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointSystemNormalizedComparisonData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointSystemNormalizedComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointSystemPowerRoosData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointSystemRoosComparisonAssembly | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointSystemRoosRestrictionAssembly | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointSystemRoosTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointSystemRoosTransportData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointSystemRoosTransportRepresentative | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointSystemStrictInsertions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointSystemTransportDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointTransportResolutionCancellation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointTransportStrictQuotient | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointTransportStrictQuotientAllComplexes | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointTransportStrictQuotientFiniteEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointTransportStrictQuotientIdentities | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointTransportStrictQuotientModels | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointTransportStrictQuotientSections | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointTransportTowerRealizationAssembly | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointTransportTowerRealizationConstruction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointTransportTowerRealizationIdentities | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointTransportTowerRealizationSpec | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointWeilAlgebraicFlag | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointWeilHeartFlagData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointWeilPairingCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointWeilPairingRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointWeilTensorRepresentatives | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PointWeilTransportUnitShift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProEtaleAffineLineCounit | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProEtaleFrameIntegration | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProEtaleProjectionIntegration | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProEtaleProjectiveCoefficient | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProEtaleProjectiveLineTrace | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProEtaleVectorIntegration | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProEtaleVectorIntegrationArrows | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProductCompositionCoordinateComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProductExchangeCoordinateDefinitions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProductExchangeCounitCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProductHorizontalExchangeFactorization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProductOpenAdjunctionNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProductOpenCounitNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProductOpenSupportNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProductOpenTensorProjection | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProductOpenTensorProjectionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectionFactorCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectionFiniteBaseChangeRouteRealization | G1 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectionFiniteBaseChangeTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectionFormulaCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectionIdentityAssembly | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectionIdentityProperCounit | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectionIdentityTensorUnit | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectionPurityAgreement | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectionPurityCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectionReductionPresentation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectionScalarSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectionTensorIntegration | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectionUnitIntegration | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectionUnitPresentationNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectionWeilTensorDomainBridge | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProperCoefficientDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProperCoefficientDescentData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProperCompactCoefficientActionComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProperCompactIntegralComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProperCompactRationalFunctorComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProperIntegralScalarSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProperIntegralTowerComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProperRationalScalarSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProperSupportCoefficientAdjunction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProperSupportFiniteAdjunction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ProperWeilIterateGermFormula | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurCoordinateRepresentingFamily | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurIntegralRepresentingPair | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurIntegralRepresentingPairData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurIntegralSupportComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurIntegralSupportDerivedComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurIntegralSupportOrdinaryComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurRepresentingPairFiniteScalar | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurSupportPresentationAlpha | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityAffineLineBoundaryRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityAffineLineOrientationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityChernClasses | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityCompactSupportTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityCompositionComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityConstantFamilyBaseChange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityCoprojection | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityFiniteTateSourceComparisonCalculus | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityGysinStructure | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityKappaStages | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityKummerTriangleConcentration | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityOrientationDatum | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityRankZeroFamilyReadings | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityRelativeKummer | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PuritySectionBaseComparisonLaws | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PuritySectionConstantTrivialization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PuritySectionEtaleRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PuritySectionFibreSquares | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PuritySectionNormalizedSpecialization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PuritySectionRestrictionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PuritySectionRestrictionEtaleFunctorial | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityTateDatum | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityTwistCancellation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityWitnessedMateNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.PurityWitnessedOpenChartTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.QcqsCompactSupportNormalizedLift | unclaimed | Changed here; see Old/New and pruning record. |

| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Changed here; see Old/New and pruning record. |

| Sheaf.Paper.QcqsCompactSupportReductionRigidity | unclaimed | Changed here; see Old/New and pruning record. |

| Sheaf.Paper.QcqsCompactSupportTorsionInputDetection | A2 | Changed here; see Old/New and pruning record. |

| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.QuotientGermTower | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.QuotientStalkNaturalDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RankZeroBundleSectionCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalAmbientPullComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalAmbientPullModels | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalBalancedFreePullback | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalContinuousComparisonCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalContinuousFiltrationModels | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalContinuousPullbackTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalModuleRealizationFunctor | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalOrdinaryCohomologyTensor | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalPullSingleComputation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalPullbackCompositionCoherence | S3 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalPullbackFlatComputationCounit | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalPurityExchangeEndpointData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalPurityExchangeEndpoints | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalPurityLocalizedFamilyData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalRealizationFiniteConeModels | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalRealizationHomTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalRealizationOrdinaryLocalization | F8 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalRealizationScalarCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalRealizationTensorComparison | F9 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalReturnBlockPower | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalScalarBalancedLocalization | S4 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalScalarCompletionUnitSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalScalarMixedUnitCancellation | T2 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalScalarObjectTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalStalkExact | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalStratumPullbackData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalStratumPullbackModels | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RationalizationOrientedExchangeSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RealWeights | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ReconstructedBrownMateLaws | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ReconstructedPairRefinementCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ReconstructedPairRefinementData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ReconstructedRefinementCommon | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ReconstructedRefinementSingleDegree | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ReconstructedRefinementTraceSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ReconstructedRefinementTraceTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RefinementFiniteOriginEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RelativeKummerSiteNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RelativeKunneth | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RelativeKunnethClosedFibre | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RelativeKunnethConstructions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RestrictedAffineDiagonalDncTrace | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RestrictedAffineDiagonalDncVectorCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RestrictedAffineDiagonalSectionTrace | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RestrictedAffineDiagonalTraceBaseChange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RestrictedAffineDiagonalVectorIntegration | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RingCanonicalScalarInvertibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RingEndpointScalarRestrictions | F3 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RingOpenMapInvertibility | P7 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RingOpenRefinement | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.RingRefinementScalarWord | F4 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SbcDatumExchangeComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ScalarFibreCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ScalarFibreComponentData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ScalarFibreComponents | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ScalarFibreNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ScalarHomPresentationEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ScalarLimitConstraintShift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ScalarLimitTensorComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ScalarLimitTensorRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ScalarRefinementOriginsF | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ScalarRoosComparisonUnique | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SectionEtaleOpenCancellation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SectionsRationalModelComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SemilinearCommonOrdinaryCubes | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SemilinearCommonRefinementCubes | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SemilinearCommonSupportCubes | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SemilinearExchangeCubeCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SemilinearExchangeCubeData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SemilinearExchangeDescentData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SemilinearExchangeReindexing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SemilinearExchangeReindexingData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SemilinearGermIterationDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SemilinearRationalOrdinaryCubes | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SemilinearRationalRefinementCubes | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SemilinearRationalSupportCubes | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfAdicCommonStageDescentEquivalence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfBcCompletedMateDomain | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfBidualityClass | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfCompletedExchangeTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfFieldMateDomain | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfIntegralLocalizationConstruction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfNormalizedCommonStageWeilSquares | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfNormalizedRationalClosedComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfNormalizedRationalWeilSquares | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfPackageBaseChangeDomainRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfPackageIntegralSupportTowerNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfPackageQbarAdjunctionMapDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfPositiveFiniteLocalizationConstruction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfQbarLocalizationCommonStage | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfQbarLocalizationExactDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfQbarLocalizationFiniteCoherence | G6 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfQbarLocalizationFiniteData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfRationalLocalizationOrthogonality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SfRecollementReductionBoundary | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SmoothExceptionalTensorPasting | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SmoothExchangeScalarCompatibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SmoothOrientationCoefficientFamily | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SmoothOrientationPuritySquares | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SmoothOrientationStageExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SmoothOrientationTransportSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SmoothOrientedExchangeComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SmoothPurityMap | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SmoothPurityQbar | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SmoothPurityTensorUnit | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SmoothTrace | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SourceSectionAutomorphismModel | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SourceSectionIdentityModel | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SourceSectionRestrictionModel | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SourceSectionStalkConeComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SourceSectionStalkConeData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SpecifiedIntegralUnitOrientation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.StrictProperRestrictionComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.StrictQuotientStalkReindexing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.StrictReductionCompactSupportNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.StrictScalarMateShift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.StrictScalarTowerAssociator | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.StrictTateTensorTowerLift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SupportedCartierDerivedPullback | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SupportedProjectiveChern | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SupportedProjectiveChernComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemClopenMateIdentification | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemCompactSupportRestrictionCocycle | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemCompositorRefinementSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemFiniteCompositorCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemFiniteEvaluationCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemFiniteRefinementMateCoordinates | G2 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemIdentityOpenEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemProjectionChangeCompatibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemProjectionTriangleCompatibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemProperIdentityOpenProjection | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemRefinementFiniteCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemScalarBasisDistributivity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemScalarProjectionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemScalarRefinementRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemScalarTensorConstituents | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemTensorPresentationCoreExistence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemTensorPresentationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemTensorPresentationIdentification | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.SystemTensorSemilinearRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TateTensorNormalizedSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TateTensorQuotientBalancing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TensorHeartSpecialization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TensorHomExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TensorMateBaseChange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TraceBoundedQuotientStalkRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TraceCorrespondences | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TraceFixedScheme | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TraceStalkCompositorTowerData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TraceStalkCompositorTowerRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TraceStalkTowerDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TraceStrictStalkTowers | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwConventions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwFrobeniusAction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedCoordinateSectionCoprojection | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedCoordinateSectionNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VaryingDimensionDualizingInverse | P4 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorBundleThom | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorBundleThomClass | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorFrameIntegrationSiteDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorIntegrationChartComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorIntegrationChartCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorIntegrationChartTranspose | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorIntegrationIdentityAdjunct | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorIntegrationUnitTranspose | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorModelChartDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorNormalizedTraceCartesian | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorTensorOrdinaryNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorTensorProjectionComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorTensorSiteEquations | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VectorZeroSectionIntegrationBaseChange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VerdierCompositionMateNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VerdierExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.VerdierPairingThreeTransposes | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilBaseChangeSemilinearPasting | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilFourierInversion | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilGenericLissity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilGeometricFiberProperties | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilIndOpenRealization | P9 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilIndOpenRepresentability | Q5 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilIndProperHigherRealization | Q6 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilIndProperHigherRepresentability | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilIndProperOpenHigher | Q7 | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilIndSheafCategory | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilPullbackFibreReturn | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlCanonicalImmersionPunctualSpectrum | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlCanonicalImmersionStalkConjugacy | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlImmersionFilteredReductionTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlImmersionRestrictionAssembly | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlOpenCompactSupportRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlOpenExtensionAssembly | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlOpenExtensionTExact | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlOpenWeilUnitEmptyFibre | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlSfPbcNormalizedHeartModel | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlShriekComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlWeilPullCompositorEquivariance | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SecSmoothPurity.FiniteGeneralRingData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SecSmoothPurity.FiniteGeneralRingExponent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SecSmoothPurity.FiniteGeneralRingIntegrationExponent | G3 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SecSmoothPurity.RationalPurityCommonComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SecSmoothPurity.RationalPurityLineComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SecSmoothPurity.ReductionOrientation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.AmbientExactClopenComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.AmbientExactClopenData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.AmbientOrdinaryClopenLocalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.AmbientProperOpenCalculus | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.AmbientSystemBetaLocalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.AmbientSystemClopenLocalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.AmbientUnderivedClopenPasting | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CanonicalShiftSynchronization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CanonicalTreeGeneratorShiftLaws | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CartesianCandidateSiteSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CartesianCompactSupportCompositor | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CartesianTowerRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefDualizingSiteMates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient | Q8 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefFinitePairingEvaluationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefIntegralFiniteDualizingCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefIntegralFiniteExtensionCocycles | G8 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility | G9 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefIntegralFiniteExtensionReductionPairing | H5 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefIntegralScalarQuotientTransition | Q9 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefPairingCompactificationModels | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefPairingFiniteNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefPairingFrameNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefPairingHomRepresentativeComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefPairingSystemDinaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefQbarVerdierCore | U4 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefQbarVerdierData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefQbarVerdierDualizing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefQbarVerdierExceptional | G4 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefQbarVerdierHomComparisonComponents | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefQbarVerdierHomComparisonExtension | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefQbarVerdierInternalHom | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefQbarVerdierInternalHomComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefQbarVerdierInternalHomUniversal | H1 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefScalarReductionExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefSystemProjectionEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefTowerEvaluationPairingData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefVerdierWeilData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefWeilExceptionalCompatibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefWeilLeftExchangeCompatibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefWeilNormalizedDuality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefficientDualizingClosedDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefficientProjectionPointData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefficientSystemSymmetricCalculus | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefficientUnitFiniteTor | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CoefficientUnitNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CompactifiedProperTowerExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CompletedProjectionExchangeData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CompletedProjectionExchangeDomains | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CompletedProjectionExchangePaths | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CompletedProjectionExchangeRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CompletedProjectionExchangeSystem | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CompletedShriekCompositionLaws | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CompletedSystemPullbackPreservation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CompletedTensorSlotShiftLaws | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CompositionProjectionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ConstantOrdinaryCompactificationComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ExceptionalIntegralNormalizedAdjunction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ExceptionalIntegralRealizationAssembly | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ExceptionalIntegralReconstructionEquivalence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ExceptionalIntegralSystemExistence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteAdjunctionCoefficientUnitData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteAdjunctionDiagramData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteAdjunctionGeometricRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteAdjunctionSystemDuality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteAdjunctionSystemEnriched | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteCoefficientVerdierData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteCounitRestrictionSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteDualizingAffineRestriction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteDualizingCoefficientNormalization | H9 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteDualizingData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteDualizingScalarRealization | J5 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteExceptionalData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteExceptionalDomain | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteExceptionalQuotientCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteExceptionalQuotientIso | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteFreeEtaleProEtaleTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteIntrinsicBidualComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteMappingAdjunctionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteMappingEtaleDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteMappingEtaleDescentIsIso | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteVerdierCoefficientDiagrams | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FiniteVerdierProEtaleLeftTor | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FrobeniusAffineEqualizerPresentation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FrobeniusCohomologyCoefficientCocycle | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FrobeniusCohomologyComparisonFactors | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FrobeniusCohomologyRationalCocycle | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FrobeniusCohomologyRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FrobeniusCohomologyRealizationTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralBasicGeneratorSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralBasicRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralBasicRealizationData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralCanonicalAmbientModels | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralCanonicalRealizationSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralCompactificationComparisonData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralCompactificationOrdinaryComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralCompactificationOrdinaryScalarAction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralComparisonRecursionLaws | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralConstantCompleteTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralConstantCompleteTransportComplete | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralConstantCompleteTransportHom | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralDualizingFiniteBounds | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralDualizingMappingLimit | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralDualizingMappingLimitGlobal | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralDualizingMappingLimitHom | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralDualizingRoosModel | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralExceptionalLimitConstructible | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralExpressionCanonicalEquations | X5 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralExpressionCanonicalSupport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralExpressionCoefficientSquares | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralExpressionRecursion | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralExpressionRecursionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralExpressionTransposeIsIso | Y6 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | H4 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralOpenRealizationNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralOrdinaryCanonicalIsoSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralOrdinaryCompactificationSquares | H2 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralOrdinaryExchangeProjectionSquares | X7 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralOrdinaryExpressionNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralOrdinaryExpressionReduction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare | H3 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralRealizationAssemblyData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | J1 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralSupportCounitProjection | unclaimed | Proof adapted to the specification or algebraically closed uniqueness theorem; signature identical. |

| Sheaf.SixFunctors.IntegralSupportRealizationComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralSupportTowerNormalization | unclaimed | Proof adapted to the specification or algebraically closed uniqueness theorem; signature identical. |

| Sheaf.SixFunctors.IntegralSystemDualityCompatibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralVerdierModels | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralVerdierReductionPairing | G7 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.KappaCoefficientCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.KappaGeometricComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.KappaMixedCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.KunnethFirstOpenSubstitution | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.KunnethSecondOpenSubstitution | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.NormalizedRingCompactScalarCocycle | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OpenBaseChangeReductionSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OpenClosedWeilMateCoefficient | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OpenClosedWeilMateCompletion | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OpenClosedWeilMateData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OpenClosedWeilMateDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OpenClosedWeilMateFinite | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OpenClosedWeilMateIntegral | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OpenClosedWeilMateStructures | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OpenInterchangeReductionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OpenInterchangeReductionSquares | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OpenScalarAdjunctionCounit | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OpenSupportStepBounds | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OpenTensorReductionSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OrdinaryAmbientAlphaPasting | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OrdinaryAmbientAlphaUnits | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OrdinaryAmbientProperOpenLaws | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.OrdinaryProperOpenInvertibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ProductCompactificationIdentity | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ProjectionRefinementComparisons | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ProjectionRefinementData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ProjectionRefinementDescent | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ProjectionRefinementInputs | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ProjectionRefinementNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ProjectionRefinementSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ProjectionSystemCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ProperOpenInterchangeReductionSquare | Y8 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ProperOpenLambdaReductionSquare | Y9 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.PublishedSystemAmbientCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.PublishedSystemTensorComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RamifiedScalarPreparation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RamifiedScalarSupportCompatibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RationalDualizingIdentification | V2 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RationalExceptionalIdentifications | V3 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RationalHomIdentifications | V4 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RationalOperations | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RationalOperationsData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RationalVerdier | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RationalVerdierComparisonBiduality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RationalVerdierComparisonEvaluation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RationalVerdierComparisonNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RationalVerdierComposition | W3 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RationalVerdierDatum | W4 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RationalVerdierExtension | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RationalVerdierModels | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RationalVerdierUnit | X2 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RealizationTreeShiftData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RealizationTreeSingleShift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RealizationTreeSystemSquare | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RefinementProjectionCounit | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RefinementProjectionLocalTensor | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RefinementProjectionProperComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.RefinementProjectionWords | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.SchemeGaloisComparisonNormalForm | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.SemilinearOrdinaryCompactificationComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.StructuralReductionWordSubstitution | Z5 | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.SystemProperOpenSupport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.SystemTensorShiftCoherence | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.SystemTotalEnrichedTranspose | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.TensorExchangeCoherentConclusions | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.TensorExchangeNormalizedModels | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.TensorExchangePresentation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.TensorHomTranspositionData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.ThreeCellCompositor | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.TriangleProjectionCompositorContraction | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.TriangleProjectionNormalForm | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.TriangleProjectionSystemNormalForm | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.VerdierExchangeData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SmoothPurity.OrdinaryBinaryProductTranspose | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SmoothPurity.OrdinaryProductTransposeData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SmoothPurity.OrdinaryTripleLeftComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SmoothPurity.OrdinaryTripleProductTranspose | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.SmoothPurity.OrdinaryTripleRightComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.TraceFormula.CompactDirectPowerTransportNormalization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.TraceFormula.FrobeniusCompactPowerExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.TraceFormula.FrobeniusProperPowerExchange | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.TraceFormula.LocalNormalizationStrictRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.TraceFormula.PointConeLiftsChainNaturality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.WeilSheaf.CompactSupportBrownConstructibility | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.WeilSheaf.NativeExceptionalCounitHomSquares | J7 | Same realization type and projection specification; no source adaptation. |

| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.WeilSheaf.NativeExceptionalLeftModels | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.WeilSheaf.NativeExceptionalPointUnit | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.WeilSheaf.OrdinaryClosedPresentation | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.WeilSheaf.StructuralBidualInvertible | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.WeilSheaf.StructuralDualizingIdentification | unclaimed | Same realization type and projection specification; no source adaptation. |

| Sheaf.WeilSheaf.StructuralOmegaHomPairs | unclaimed | Same realization type and projection specification; no source adaptation. |

| WeilConjectures | unclaimed | Same realization type and projection specification; no source adaptation. |

| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same realization type and projection specification; no source adaptation. |

| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same realization type and projection specification; no source adaptation. |

| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same realization type and projection specification; no source adaptation. |

| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same realization type and projection specification; no source adaptation. |

| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Same realization type and projection specification; no source adaptation. |

| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Same realization type and projection specification; no source adaptation. |

| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same realization type and projection specification; no source adaptation. |

| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Same realization type and projection specification; no source adaptation. |

| WeilConjectures.WeilSheaf.Karoubian | unclaimed | Same realization type and projection specification; no source adaptation. |

| WeilConjectures.WeilSheaf.KaroubianPointer | unclaimed | Same realization type and projection specification; no source adaptation. |

| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Same realization type and projection specification; no source adaptation. |

| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Same realization type and projection specification; no source adaptation. |

| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Same realization type and projection specification; no source adaptation. |

| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Same realization type and projection specification; no source adaptation. |

| WeilConjectures.WeilSheaf.VerdierDual | J1 | Same realization type and projection specification; no source adaptation. |

| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Same realization type and projection specification; no source adaptation. |

| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Same realization type and projection specification; no source adaptation. |


## Status

landed 20261027T205738-L-1609185 2026-10-27 (merge of deliver/A2/Sheaf.Paper.QcqsCompactSupportTorsionInputDetection)
