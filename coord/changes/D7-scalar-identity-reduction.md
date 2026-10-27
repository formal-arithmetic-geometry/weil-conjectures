# AlgebraicGeometry.ProEtale.OpenScalarTensor.scalarId

## Reason

Kernel checking the concrete support identity repeatedly unfolded the equality transport through the chosen derived localization and exceeded 60 seconds. Fix the same canonical isomorphism by a unique equality specification and expose its original expression as scalarId_eq. The equality specification is proved, determines the object exactly, and adds no mathematical assumption or data choice. The scalarId signature and its mathematical value are unchanged. This is a definition-performance repair required to compile the actual identity proof, not a split of the proof to evade the limit.

## Old

```lean
/-- Scalar multiplication gives the identity-coefficient unitor.
Source: Stacks 07A6 (blueprint: def-sp-open-scalar-tensor-data). -/
def scalarId (A : Type u) [CommRing A] (T : Scheme.{u}) :
    scalar m (RingHom.id A) T ≅ 𝟭 (proEtaleDerivedCategory T A) :=
  eqToIso (congrArg (fun a ↦ ((m T).scalar a).derived)
    ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map_id
      (CommRingCat.of (ULift.{u + 1, u} A)))) ≪≫
    scalarHomExtensionId (m T) (proEtaleConstantRing T A)

```

## New

```lean
/-- The canonical scalar identity is uniquely fixed to its original restriction-adjunction
construction. This equality specification shields the derived localization from reduction.
Source: Stacks 07A6 (blueprint: def-sp-open-scalar-tensor-data).
Proof: the displayed isomorphism is a witness, and equality to it implies uniqueness. -/
theorem scalarId_existsUnique (A : Type u) [CommRing A] (T : Scheme.{u}) :
    ∃! e : scalar m (RingHom.id A) T ≅ 𝟭 (proEtaleDerivedCategory T A),
      e = eqToIso (congrArg (fun a ↦ ((m T).scalar a).derived)
    ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map_id
      (CommRingCat.of (ULift.{u + 1, u} A)))) ≪≫
    scalarHomExtensionId (m T) (proEtaleConstantRing T A) := by
  exact ⟨_, rfl, fun _ h ↦ h⟩

/-- The unit-normalized identity scalar isomorphism, with its original canonical value.
Source: Stacks 07A6 (blueprint: def-sp-open-scalar-tensor-data). -/
def scalarId (A : Type u) [CommRing A] (T : Scheme.{u}) :
    scalar m (RingHom.id A) T ≅ 𝟭 (proEtaleDerivedCategory T A) :=
  (scalarId_existsUnique m A T).exists.choose

/-- Explicit equation for the canonical scalar identity.
Source: Stacks 07A6 (blueprint: def-sp-open-scalar-tensor-data).
Proof: this is the defining equality of the uniquely specified identity isomorphism. -/
theorem scalarId_eq (A : Type u) [CommRing A] (T : Scheme.{u}) :
    scalarId m A T = eqToIso (congrArg (fun a ↦ ((m T).scalar a).derived)
    ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map_id
      (CommRingCat.of (ULift.{u + 1, u} A)))) ≪≫
    scalarHomExtensionId (m T) (proEtaleConstantRing T A) :=
  (scalarId_existsUnique m A T).exists.choose_spec

```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompactSupportScalarCoordinates | unclaimed | Canonical value and existing signatures preserved; no consumer edit. |
| Sheaf.Paper.ConcreteProjectionReductionSquare | D7 | Canonical value and existing signatures preserved; no consumer edit. |
| Sheaf.Paper.OpenScalarCounitSquare | unclaimed | Canonical value and existing signatures preserved; no consumer edit. |
| Sheaf.Paper.PfReductionProperOpenIdentities | unclaimed | Canonical value and existing signatures preserved; no consumer edit. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Canonical value and existing signatures preserved; no consumer edit. |
| Sheaf.SixFunctors.OpenScalarAdjunctionCounit | unclaimed | Canonical value and existing signatures preserved; no consumer edit. |
| Sheaf.SixFunctors.OpenScalarCoefficientCoherence | unclaimed | Canonical value and existing signatures preserved; no consumer edit. |
| Sheaf.SixFunctors.OpenScalarProjectionCompatibility | unclaimed | Canonical value and existing signatures preserved; no consumer edit. |
| Sheaf.SixFunctors.OpenScalarTensorModels | unclaimed | Canonical value and existing signatures preserved; no consumer edit. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed | Canonical value and existing signatures preserved; no consumer edit. |
| Sheaf.SixFunctors.OpenScalarTensorData | unclaimed | Canonical value and existing signatures preserved; no consumer edit. |
| Sheaf.Paper.ConcreteProjectionCoefficientCoherence | D7 | Canonical value and existing signatures preserved; no consumer edit. |

Existing users of scalarId use it in statements or through the normalized interface; no source changes are needed. All copied unchanged direct consumers compiled against the repaired module, including PfReductionProperOpenIdentities (57.9 seconds on recheck). The new ConcreteProjectionCoefficientCoherence uses scalarId_eq to prove its unchanged tensor identity and the support identity. The meanings of the project's target statements are preserved by the proved equality.

## Status

landed 20261025T201645-L-2595850 2026-10-25 (merge of deliver/D7/Sheaf.Paper.ConcreteProjectionReductionSquare)
