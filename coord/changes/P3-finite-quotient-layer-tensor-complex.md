# finiteQuotientLayerTensorComplex

## Reason

The assigned local-model theorem lacked any concrete algebraic witness. Construct its
ideal layer and tensor complex, prove the two support bounds and finite successor-ring
terms, and separate the remaining sheaf-derived comparison. This changes no existing
statement, definition, instance, attribute, or public import. In particular, no target
statement changes meaning, and no existing consumer needs adaptation.

## Old

These declarations and their two modules did not exist. The assigned theorem had a
single `sorry` proof and the same signature it retains in this delivery.

## New

New explicit construction and its proved API, verbatim:

```lean
def finiteQuotientLayerModule {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ) :
    ModuleCat.{t} (A ⧸ I ^ (0 + 1)) :=
  ModuleCat.of _ ((I ^ (n + 1) : Ideal A) ⧸
    (I ^ (0 + 1) • ⊤ : Submodule A (I ^ (n + 1) : Ideal A)))

/-- The constructed residue module is the actual kernel of the quotient ring map.
Source: Stacks Project, Tag 094I, its ideal-layer identification.
(blueprint: def-weil-pbc-finite-quotient-layer-tensor-complex). -/
def finiteQuotientLayerKernelEquiv {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ) :
    finiteQuotientLayerModule I n ≃
      RingHom.ker (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
          I ^ (n + 1 + 1) ≤ I ^ (n + 1))) := by
  let e : finiteQuotientLayerModule I n ≃
      Ideal.map (Ideal.Quotient.mk (I ^ (n + 1 + 1))) (I ^ (n + 1)) := by
    simpa only [finiteQuotientLayerModule, Nat.reduceAdd, pow_one] using
      Ideal.powQuotPowSuccEquivMapMkPowSuccPow I (n + 1)
  exact e.trans (Equiv.setCongr (congrArg SetLike.coe
    (Ideal.Quotient.factor_ker
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
        I ^ (n + 1 + 1) ≤ I ^ (n + 1))).symm))

/-- Tensor with the ideal layer and retain the successor-ring action by restriction.
Source: Stacks Project, Tags 0942 and 094I.
(blueprint: def-weil-pbc-finite-quotient-layer-tensor-complex). -/
def finiteQuotientLayerTensor {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ) :
    ModuleCat.{t} (A ⧸ I ^ (0 + 1)) ⥤ ModuleCat.{t} (A ⧸ I ^ (n + 1 + 1)) :=
  MonoidalCategory.tensorLeft (finiteQuotientLayerModule I n) ⋙
    ModuleCat.restrictScalars
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : 0 + 1 ≤ n + 1 + 1)))

instance finiteQuotientLayerTensor_additive {A : Type t} [CommRing A]
    (I : Ideal A) (n : ℕ) : (finiteQuotientLayerTensor I n).Additive := by
  unfold finiteQuotientLayerTensor
  infer_instance

/-- Apply the layer tensor functor term by term, including to the differential.
Source: Stacks Project, Tags 0942, 094H and 094I.
(blueprint: def-weil-pbc-finite-quotient-layer-tensor-complex). -/
def finiteQuotientLayerTensorComplex {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ I ^ (0 + 1))) ℤ) :
    CochainComplex (ModuleCat.{t} (A ⧸ I ^ (n + 1 + 1))) ℤ :=
  ((finiteQuotientLayerTensor I n).mapHomologicalComplex (.up ℤ)).obj P

/-- The ideal layer embeds in the finite successor quotient, hence is a finite type.
Source: Stacks Project, Tag 0942; Mathlib's ideal-power quotient equivalence.
(blueprint: def-weil-pbc-finite-quotient-layer-tensor-complex). -/
theorem finiteQuotientLayerModule_finite {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) : Finite (finiteQuotientLayerModule d.ideal n) := by
  have := d.quotientFinite (n + 1)
  exact Finite.of_equiv _ (finiteQuotientLayerKernelEquiv d.ideal n).symm

/-- Tensoring with the finite ideal layer has finite successor-coefficient terms.
Source: Stacks Project, Tags 0942 and 094I.
(blueprint: def-weil-pbc-finite-quotient-layer-tensor-complex). -/
theorem finiteQuotientLayerTensorComplex_finite {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (0 + 1))) ℤ)
    (hP : ∀ i : ℤ, Module.Finite (A ⧸ d.ideal ^ (0 + 1)) (P.X i)) (i : ℤ) :
    Module.Finite (A ⧸ d.ideal ^ (n + 1 + 1))
      ((finiteQuotientLayerTensorComplex d.ideal n P).X i) := by
  have := d.quotientFinite 0
  have := finiteQuotientLayerModule_finite d n
  have : Module.Finite (A ⧸ d.ideal ^ (0 + 1))
      (finiteQuotientLayerModule d.ideal n) := Module.Finite.of_finite
  have := hP i
  have : Finite ((finiteQuotientLayerModule d.ideal n) ⊗[A ⧸ d.ideal ^ (0 + 1)] P.X i) :=
    Module.finite_of_finite (A ⧸ d.ideal ^ (0 + 1))
  have : Finite ((finiteQuotientLayerTensorComplex d.ideal n P).X i) := by
    change Finite ((finiteQuotientLayerModule d.ideal n) ⊗[A ⧸ d.ideal ^ (0 + 1)] P.X i)
    infer_instance
  exact Module.Finite.of_finite

/-- A layer tensor complex retains the lower support bound, including for a zero layer.
Source: Stacks Project, Tag 094I.
(blueprint: def-weil-pbc-finite-quotient-layer-tensor-complex). -/
theorem finiteQuotientLayerTensorComplex_ge {A : Type t} [CommRing A]
    (I : Ideal A) (n : ℕ)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ I ^ (0 + 1))) ℤ)
    (a : ℤ) (h : P.IsStrictlyGE a) :
    (finiteQuotientLayerTensorComplex I n P).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (finiteQuotientLayerTensor I n).map_isZero (P.isZero_of_isStrictlyGE a i hi)

/-- A layer tensor complex retains the upper support bound, even for an empty interval.
Source: Stacks Project, Tag 094I.
(blueprint: def-weil-pbc-finite-quotient-layer-tensor-complex). -/
theorem finiteQuotientLayerTensorComplex_le {A : Type t} [CommRing A]
    (I : Ideal A) (n : ℕ)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ I ^ (0 + 1))) ℤ)
    (b : ℤ) (h : P.IsStrictlyLE b) :
    (finiteQuotientLayerTensorComplex I n P).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (finiteQuotientLayerTensor I n).map_isZero (P.isZero_of_isStrictlyLE b i hi)

```

The separate new module `Sheaf.Paper.FiniteQuotientLayerTensorHomologyComparison`
states `AlgebraicGeometry.Scheme.finiteQuotient_layer_tensor_homology_comparison`.
It has one named theorem with `:= by sorry`, a source and complete proof in words,
and a matching node. It concerns homology of the specified tensor complex, has no
existential witness, omits the lower support and term-finiteness hypotheses, and
makes no support or finiteness conclusion. The assigned theorem uses it through a
private proof import. All existing signatures and public imports stay identical.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FiniteQuotientLayerLocalComplexCore | P3 | Uses the explicit witness, proved bounds and finiteness, and the remaining homology comparison. |
| Sheaf.Paper.FiniteQuotientLayerTensorHomologyComparison | P3 (new) | States the comparison for the constructed tensor complex. |

These are the only users: both dependencies are new modules. Existing importers of
the assigned module see exactly its existing declarations and statements.

## Status

landed 20261027T210155-L-1667419 2026-10-27 (merge of deliver/P3/Sheaf.Paper.FiniteQuotientLayerLocalComplexCore)
