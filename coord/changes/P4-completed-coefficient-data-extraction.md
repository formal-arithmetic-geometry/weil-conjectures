# AlgebraicGeometry.ProEtale.SfbCompletedCoefficientComparison

## Reason

The normalized integral cone is a strictly smaller part of the comparison theorem.
It must be stated in its own module, importing the concrete quotient tower and constant-section
map without importing the theorem that will use it. Move the existing definitions to a data
module and reexport it publicly from the original module. Every declaration keeps its namespace,
name, type and visibility. Ten bodies move verbatim. In the comparison predicate, the rational
pullback equation is reexpressed with the underlying `coefficientPullbackIso` maps. The old raw
`condensedPullbackHom` formulation repeatedly caused kernel deterministic timeouts (about
70 seconds in an isolated naturality helper). The existing source theorem already supplies the
bundled comparison equations. Source-library modules and all target signatures are untouched.

The mathematical condition is preserved: `coefficientPullbackIso` is `mapMonCompIso.symm`
followed by `mapMonNatIso upperStarFromPointComp`. Its underlying component is the identity
followed by `(upperStarFromPointComp f).hom.app Λ`, hence equals `condensedPullbackHom Λ f`
by the identity law. The proved private `sfb_ring_comparison_underlying` in the item module
checks exactly this normalization in arbitrary monoidal categories. The definition review
should check this equivalent representation explicitly; no pullback leg condition is dropped.
Targets using this definition through the completed-comparison theorem require the statement
meaning review of stages/2-statements.md §4 again; this record explicitly reopens that check.

## Old

The following declarations were in
`lean/Sheaf/AlgebraicGeometry/ProEtaleCompletedCoefficients.lean`:

```lean
/-- Constant rings, as ring objects in abelian sheaves, with the standard integer tensor.
Source: the constant finite quotients in the first display of the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbConstantRing (X : Scheme.{u}) :
    RingCat.{u + 1} ⥤ Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  RingCat.toMonAb ⋙ (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapMon

/-- The same constant-ring construction on the pro-étale point.
Source: the finite quotients in the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbPointConstantRing :
    RingCat.{u + 1} ⥤ Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  RingCat.toMonAb ⋙ (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMon

/-- The quotient tower, including the harmless terminal zero quotient at exponent zero.
Its maps are the quotient reductions, not arbitrary ring homomorphisms.
Source: first display of the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbCoefficientQuotientTower (R : Type) [CommRing R] (I : Ideal R) :
    ℕᵒᵖ ⥤ RingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ RingCat.of (ULift.{u + 1} (R ⧸ I ^ n)))
    (fun n : ℕ ↦ RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))).comp
        ULift.ringEquiv.toRingHom)))

/-- Constant sections of a topological ring, mapped into its condensed abelian sheaf.
This is the adjoint of the map sending a scalar to its constant continuous function.
Source: normalization of the reduction maps in the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbConstantToContinuous (R : Type) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} R)) ⟶ Profinite.continuousMapRingObj R :=
  ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv _ _).symm
    { app S := AddCommGrpCat.ofHom
        { toFun := fun x ↦ ULift.up (ContinuousMap.const S.unop x.down)
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := fun _ _ _ ↦ rfl }

/-- The pulled-back inclusion of integers into their coefficient field. The underlying
map is precisely `p_X^*` applied to postcomposition with the given continuous inclusion.
Source: second display of the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbCoefficientInclusion (R K : Type) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (φ : R →+* K) (hφ : Continuous φ) (X : Scheme.{u}) :
    coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶
      coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K)) :=
  (upperStarFromPoint X).mapMon.map (Mon.ofHom
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap φ hφ)))

/-- The coefficient field as a module over the pulled-back integers, using their actual
inclusion. Source: the sequential module colimit in the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbRationalCoefficientModule (R K : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K]
    (i : ∀ X : Scheme.{u}, coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶
      coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K))) (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj R) X) :=
  (Mod.comap (i X).hom).obj
    (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj K) X))

/-- The sequential diagram of integer modules with transition multiplication by `ℓ`.
Multiplication by `ℓ` is used only as a module map.
Source: second display of the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbRationalizationSequence (ℓ : ℕ) (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] (X : Scheme.{u}) :
    ℕ ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj R) X) :=
  Functor.ofSequence (fun _ : ℕ ↦ ℓ •
    𝟙 (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj R) X)))

/-- Expanded first and second comparisons, including their canonical maps and pullback
compatibility. The reductions are normalized by the actual quotient maps on constants.
`IsLimit` and `IsColimit` give the displayed comparison isomorphisms by uniqueness of
limits and colimits. The last clause is the universal property of localization as rings;
thus the ring structure on the sequential module colimit is the localization structure.

Source: first two displays and inverse-image paragraph of the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
def SfbCompletedCoefficientComparison (ℓ : ℕ) (R K : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (I : Ideal R)
    (i : ∀ X : Scheme.{u}, coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶
      coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K))) : Prop :=
  ∃ ρ : (Functor.const ℕᵒᵖ).obj (Mon.mk (Profinite.continuousMapRingObj.{u} R)) ⟶
      sfbCoefficientQuotientTower R I ⋙ sfbPointConstantRing,
    (∀ n : ℕ, sfbConstantToContinuous R ≫ (ρ.app (op n)).hom =
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
        (AddCommGrpCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((Ideal.Quotient.mk (I ^ n)).comp ULift.ringEquiv.toRingHom)).toAddMonoidHom)) ∧
    (∀ X : Scheme.{u},
      Nonempty (IsLimit ((upperStarFromPoint X).mapMon.mapCone
        (Cone.mk (Mon.mk (Profinite.continuousMapRingObj R)) ρ))) ∧
      Nonempty ((sfbCoefficientQuotientTower R I ⋙ sfbPointConstantRing ⋙
        (upperStarFromPoint X).mapMon) ≅
          (sfbCoefficientQuotientTower R I ⋙ sfbConstantRing X))) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      Nonempty (IsLimit ((upperStar Ab.{u + 1} f).mapMon.mapCone
        ((upperStarFromPoint Y).mapMon.mapCone
          (Cone.mk (Mon.mk (Profinite.continuousMapRingObj R)) ρ))))) ∧
    ∃ ι : ∀ X : Scheme.{u}, sfbRationalizationSequence ℓ R X ⟶
        (Functor.const ℕ).obj (sfbRationalCoefficientModule R K i X),
      (∀ X : Scheme.{u},
        ((ι X).app 0).hom = (i X).hom ∧
        Nonempty (IsColimit (Cocone.mk (sfbRationalCoefficientModule R K i X) (ι X))) ∧
        IsIso (ℓ • 𝟙 (condensedRingObj (Profinite.continuousMapRingObj K) X))) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (m : ℕ),
        (upperStar Ab.{u + 1} f).map (((ι Y).app m).hom) ≫
            condensedPullbackHom (Profinite.continuousMapRingObj K) f =
          condensedPullbackHom (Profinite.continuousMapRingObj R) f ≫
            ((ι X).app m).hom) ∧
      (∀ (X : Scheme.{u}) (B : Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})),
        IsIso (ℓ • 𝟙 B.X) →
        ∀ a : coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶ B,
          ∃! b : coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K)) ⟶ B,
            i X ≫ b = a)

/-- The finite-subextension diagram, in ring objects rather than only abelian sheaves.
Source: third display of the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbFiniteSubfieldRingDiagram (ℓ : ℕ) [Fact ℓ.Prime] :
    PadicAlgCl.FiniteIntermediateField ℓ ⥤
      Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) where
  obj E := Mon.mk (Profinite.continuousMapRingObj E)
  map f := Mon.ofHom (Profinite.padicSubfieldRingObjMap ℓ (leOfHom f))
  map_id E := by
    apply Mon.Hom.ext
    exact Profinite.padicSubfieldRingObjMap_id ℓ E
  map_comp f g := by
    apply Mon.Hom.ext
    exact Profinite.padicSubfieldRingObjMap_comp ℓ (leOfHom f) (leOfHom g)

/-- The canonical finite-field cocone as a cocone of rings; its legs are the inclusions
into the finite-subextension-valued algebraic-closure coefficients.
Source: third display of the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbFiniteSubfieldRingCocone (ℓ : ℕ) [Fact ℓ.Prime] :
    Cocone (sfbFiniteSubfieldRingDiagram.{u} ℓ) where
  pt := Mon.mk (Profinite.padicAlgClRingObj ℓ)
  ι :=
    { app E := Mon.ofHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
      naturality := fun E F f ↦ by
        apply Mon.Hom.ext
        exact (Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl ℓ (leOfHom f)).trans
          (Category.comp_id _).symm }

/-- The standard finite constant coefficient rings `ZMod (ℓ^n)`, with reduction maps.
Source: final paragraph of the comparison proposition
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def sfbZModCoefficientTower (ℓ : ℕ) : ℕᵒᵖ ⥤ RingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ RingCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))
    (fun n : ℕ ↦ RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).comp
        ULift.ringEquiv.toRingHom)))
```

## New

The declarations are in
`lean/Sheaf/AlgebraicGeometry/ProEtaleCompletedCoefficientData.lean`.
All construction bodies are verbatim; only the comparison predicate's rational pullback
condition uses the equivalent bundled comparison:
```lean
(∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (m : ℕ),
  (upperStar Ab.{u + 1} f).map (((ι Y).app m).hom) ≫
      ((coefficientPullbackIso f
        (Mon.mk (Profinite.continuousMapRingObj K))).hom).hom =
    ((coefficientPullbackIso f
      (Mon.mk (Profinite.continuousMapRingObj R))).hom).hom ≫ ((ι X).app m).hom)
```

The original module replaces its local definitions by

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficientData
```

The original module keeps all its existing public imports. Private proof helpers and proof
imports implement the comparison assembly. The proved rationalization helper is separately
compiled in the new `ProEtaleCompletedRationalization` module and imported for its proof;
its public declaration is new and changes no existing signature. The comparison predicate unfolds to the bundled
naturality equation above. All other unfolding equations and all existing declaration signatures
are preserved. The two new theorem interfaces are the normalized compact quotient cone and
the scalar telescope's ring universal property.

## Users

The direct importers and all modules mentioning a relocated declaration are listed below. The full transitive downstream
closure was inspected with `tools/downstream.py`; downstream modules retain the same exported names,
mathematical types, constructions and public imports. A repository-wide occurrence search shows
that existing consumers extract only the integral cone and quotient tower, never the rational
naturality field. There are no forced adaptations. Direct-importer compiles are recorded in
report.md after verification.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients | P4 | Assembly uses the equivalent bundled naturality condition. |
| Sheaf.Paper.CompletedCoefficientRingComparison | unclaimed | Same constant rings, maps and ZMod tower. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Same constant ring construction. |
| Sheaf.Paper.CompletedRootProjectionLinear | unclaimed (K4 delivery landed) | Same constant ring and ZMod tower bodies; no rational naturality field used. |
| Sheaf.Paper.IntegralTensorPullbackData | unclaimed | Definitions publicly reexported; integral fields unchanged; no source adaptation. |
| Sheaf.Paper.CondensedZlReductionCone | unclaimed | Definitions publicly reexported; integral fields unchanged; no source adaptation. |
| Sheaf.Paper.CondensedZlReduction | unclaimed | Definitions publicly reexported; integral fields unchanged; no source adaptation. |

## Status

landed 20261027T034720-L-3678500 2026-10-27 (merge of deliver/P4/Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients)
