# AlgebraicGeometry.Scheme.FinitePerfectModelsOn (definition relocation)

## Reason

The two coefficient-filtration obligations need the existing model predicates,
while the assigned successor proof imports those obligations. Move the existing
interface into a lower module to avoid an import cycle. No definition, instance
body, signature, attribute, target or hypothesis changes mathematically. This is
not a definition repair and is not counted as closing a proof hole.

## Old

The following block was defined in Sheaf.Paper.FinitePerfectQuotientModels:

```lean
/-- The locally bijective characterization at the actual coefficient universe.
Source: Stacks Tag 03DA
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).
Proof: the small pro-etale site is essentially small in universe t+1. -/
theorem finitePerfectModelsAbLocallyBijective (X : Scheme.{t}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} := by
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{t, t + 1, t + 1,
    t + 2, t + 1, t + 1, t + 1} _
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Standard algebraic derived localization.
Source: Stacks Tag 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsAlgebraHasDerived (A : Type t) [CommRing A] :
    HasDerivedCategory (ModuleCat.{t} A) := HasDerivedCategory.standard _
/-- Standard derived localization for the actual coefficient sheaves.
Source: Stacks Tag 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsRingHasDerived (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) :
    HasDerivedCategory (SheafOfModules.{t + 1} R) := HasDerivedCategory.standard _
/-- Sheafification on the concrete localized site.
Source: Stacks Tag 03DA
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsSliceAbSheafify (X : Scheme.{t}) (U : X.ProEt) :
    HasSheafify ((ProEt.topology X).over U) AddCommGrpCat.{t + 1} :=
  letI : EssentiallySmall.{t + 1} (Over U) := essentiallySmallSelf.{0, t, t + 1} _
  hasSheafifyEssentiallySmallSite.{t, t + 1, t + 1, t + 2, t + 1} _ _
/-- Local bijectivity on the concrete localized site.
Source: Stacks Tag 03DA
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsSliceAbLocallyBijective (X : Scheme.{t}) (U : X.ProEt) :
    ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  letI : EssentiallySmall.{t + 1} (Over U) := essentiallySmallSelf.{0, t, t + 1} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{t, t + 1, t + 1,
    t + 2, t + 1, t + 1, t + 1} _
/-- Standard derived localization on each slice.
Source: Stacks Tag 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsSliceHasDerived (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (U : X.ProEt) :
    HasDerivedCategory (SheafOfModules.{t + 1} (R.over U)) :=
  HasDerivedCategory.standard _

/-- Apply the actual constant module functor termwise, with its universe lift.
Source: Stacks Tags 03CY and 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
def finiteModelConstantComplex (X : Scheme.{t}) (B : Type t) [CommRing B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ) :=
  ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
    koszulConstantFunctor X B).mapHomologicalComplex (.up ℤ)).obj P

/-- A finite quotient admits perfect constant models in a specified interval on a chart.
Source: Stacks Tags 094I and 09C2
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
def FinitePerfectModelsOn (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (M : DerivedCategory (CompletedAdicModules X d)) (n : ℕ) (V : X.Etale)
    (a b : ℤ) : Prop :=
  ∃ T : Sieve V, T ∈ X.smallEtaleTopology V ∧
    ∀ (W : X.Etale) (g : W ⟶ V), T g →
      ∃ P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))) ℤ,
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Projective (A ⧸ d.ideal ^ (n + 1)) (P.X i) ∧
          Module.Finite (A ⧸ d.ideal ^ (n + 1)) (P.X i)) ∧
        Nonempty
          (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
              ((toProEt X).obj W) ((completedAdicQuotientReduction X d n).obj M) ≅
            ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
              ((toProEt X).obj W) ((completedAdicDerivedChange X (φ n)).obj
                (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P))))

/-- Etale local finite-projective quotient models with one interval on each chart.
The covering and the model at a finite level may depend on that level. This property
asserts no compatible choice of trivializations and no completed realization.
Source: Stacks Tags 09C2 and 094I
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
def HasUniformFinitePerfectModels (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (M : DerivedCategory (CompletedAdicModules X d)) : Prop :=
  ∃ S : Sieve (⊤_ X.Etale), S ∈ X.smallEtaleTopology (⊤_ X.Etale) ∧
    ∀ (V : X.Etale) (f : V ⟶ ⊤_ X.Etale), S f →
      ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
        FinitePerfectModelsOn X d φ M n V a b

/-- Normalization of the finite coefficient identifications on constant sections.
This fixes their compatibility with the quotient homomorphisms, rather than permitting
independent identifications at different levels.
Source: Stacks Tags 093M and 09C2
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
def FinitePerfectModelsNormalized (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n) : Prop :=
  ∀ (n : ℕ) (U : X.ProEtᵒᵖ) (a : completedAdicQuotient d n),
    (φ n).hom.app U ((koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1))).app U a) =
      (AlgebraicGeometry.ProEtale.finiteCoefficientScalarMap X
        (completedAdicQuotient d n)).app U a

/-- The finite comparisons preserve both quotient transitions and the scalar map.
Source: Stacks Tags 093M and 09C6
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
def FinitePerfectModelsCompatible (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n) : Prop :=
  (∀ n : ℕ,
    adicConstantMap X (adicQuotientMap d.ideal (n + 2) (n + 1) (Nat.le_succ _)) ≫
        φ n = φ (n + 1) ≫
      completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)) ∧
  (∀ n : ℕ,
    completedAdicScalar X d ≫ completedAdicCommProjection X d n =
      adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) ≫ φ n)
```

The item's public imports were:

```lean
public import Sheaf.Paper.CompletedAdicIntrinsicCompletion
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
```

## New

The same block, verbatim, is defined in
Sheaf.Paper.FinitePerfectQuotientModelData:

```lean
/-- The locally bijective characterization at the actual coefficient universe.
Source: Stacks Tag 03DA
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).
Proof: the small pro-etale site is essentially small in universe t+1. -/
theorem finitePerfectModelsAbLocallyBijective (X : Scheme.{t}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} := by
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{t, t + 1, t + 1,
    t + 2, t + 1, t + 1, t + 1} _
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Standard algebraic derived localization.
Source: Stacks Tag 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsAlgebraHasDerived (A : Type t) [CommRing A] :
    HasDerivedCategory (ModuleCat.{t} A) := HasDerivedCategory.standard _
/-- Standard derived localization for the actual coefficient sheaves.
Source: Stacks Tag 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsRingHasDerived (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) :
    HasDerivedCategory (SheafOfModules.{t + 1} R) := HasDerivedCategory.standard _
/-- Sheafification on the concrete localized site.
Source: Stacks Tag 03DA
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsSliceAbSheafify (X : Scheme.{t}) (U : X.ProEt) :
    HasSheafify ((ProEt.topology X).over U) AddCommGrpCat.{t + 1} :=
  letI : EssentiallySmall.{t + 1} (Over U) := essentiallySmallSelf.{0, t, t + 1} _
  hasSheafifyEssentiallySmallSite.{t, t + 1, t + 1, t + 2, t + 1} _ _
/-- Local bijectivity on the concrete localized site.
Source: Stacks Tag 03DA
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsSliceAbLocallyBijective (X : Scheme.{t}) (U : X.ProEt) :
    ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  letI : EssentiallySmall.{t + 1} (Over U) := essentiallySmallSelf.{0, t, t + 1} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{t, t + 1, t + 1,
    t + 2, t + 1, t + 1, t + 1} _
/-- Standard derived localization on each slice.
Source: Stacks Tag 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsSliceHasDerived (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (U : X.ProEt) :
    HasDerivedCategory (SheafOfModules.{t + 1} (R.over U)) :=
  HasDerivedCategory.standard _

/-- Apply the actual constant module functor termwise, with its universe lift.
Source: Stacks Tags 03CY and 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
def finiteModelConstantComplex (X : Scheme.{t}) (B : Type t) [CommRing B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ) :=
  ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
    koszulConstantFunctor X B).mapHomologicalComplex (.up ℤ)).obj P

/-- A finite quotient admits perfect constant models in a specified interval on a chart.
Source: Stacks Tags 094I and 09C2
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
def FinitePerfectModelsOn (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (M : DerivedCategory (CompletedAdicModules X d)) (n : ℕ) (V : X.Etale)
    (a b : ℤ) : Prop :=
  ∃ T : Sieve V, T ∈ X.smallEtaleTopology V ∧
    ∀ (W : X.Etale) (g : W ⟶ V), T g →
      ∃ P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))) ℤ,
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Projective (A ⧸ d.ideal ^ (n + 1)) (P.X i) ∧
          Module.Finite (A ⧸ d.ideal ^ (n + 1)) (P.X i)) ∧
        Nonempty
          (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
              ((toProEt X).obj W) ((completedAdicQuotientReduction X d n).obj M) ≅
            ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
              ((toProEt X).obj W) ((completedAdicDerivedChange X (φ n)).obj
                (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P))))

/-- Etale local finite-projective quotient models with one interval on each chart.
The covering and the model at a finite level may depend on that level. This property
asserts no compatible choice of trivializations and no completed realization.
Source: Stacks Tags 09C2 and 094I
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
def HasUniformFinitePerfectModels (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (M : DerivedCategory (CompletedAdicModules X d)) : Prop :=
  ∃ S : Sieve (⊤_ X.Etale), S ∈ X.smallEtaleTopology (⊤_ X.Etale) ∧
    ∀ (V : X.Etale) (f : V ⟶ ⊤_ X.Etale), S f →
      ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
        FinitePerfectModelsOn X d φ M n V a b

/-- Normalization of the finite coefficient identifications on constant sections.
This fixes their compatibility with the quotient homomorphisms, rather than permitting
independent identifications at different levels.
Source: Stacks Tags 093M and 09C2
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
def FinitePerfectModelsNormalized (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n) : Prop :=
  ∀ (n : ℕ) (U : X.ProEtᵒᵖ) (a : completedAdicQuotient d n),
    (φ n).hom.app U ((koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1))).app U a) =
      (AlgebraicGeometry.ProEtale.finiteCoefficientScalarMap X
        (completedAdicQuotient d n)).app U a

/-- The finite comparisons preserve both quotient transitions and the scalar map.
Source: Stacks Tags 093M and 09C6
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
def FinitePerfectModelsCompatible (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n) : Prop :=
  (∀ n : ℕ,
    adicConstantMap X (adicQuotientMap d.ideal (n + 2) (n + 1) (Nat.le_succ _)) ≫
        φ n = φ (n + 1) ≫
      completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)) ∧
  (∀ n : ℕ,
    completedAdicScalar X d ≫ completedAdicCommProjection X d n =
      adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) ≫ φ n)
```

The lower module retains all five former public imports above. The item now uses:

```lean
public import Sheaf.Paper.FinitePerfectQuotientModelData
```

Thus importing the original item still exposes every original public declaration
and import. The item retains its local instance registration for
finitePerfectModelsAbLocallyBijective, all existing proved helpers and both
residuePerfect theorems with unchanged signatures. Private proof imports add
only the finite-module step, Tor detection, algebraic perfectness and exact
constant-realization APIs. No existing module besides the item is changed.
All targets and all consumers use exactly the same definitions as before.

## Users

The following are all textual users of the moved declarations in both roots;
the direct importers are also checked by the project downstream/import search.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FinitePerfectAdicCanonicalComparison | unclaimed | Names, types, instances and definition bodies unchanged through the public reexport; no adaptation. |
| Sheaf.Paper.FinitePerfectAdicComplexRoos | unclaimed | Names, types, instances and definition bodies unchanged through the public reexport; no adaptation. |
| Sheaf.Paper.FinitePerfectAdicFlatTensorComparison | unclaimed | Names, types, instances and definition bodies unchanged through the public reexport; no adaptation. |
| Sheaf.Paper.FinitePerfectAdicFreeTensorCone | unclaimed | Names, types, instances and definition bodies unchanged through the public reexport; no adaptation. |
| Sheaf.Paper.FinitePerfectAdicMarkedRoos | unclaimed | Names, types, instances and definition bodies unchanged through the public reexport; no adaptation. |
| Sheaf.Paper.FinitePerfectAdicRealization | unclaimed | Names, types, instances and definition bodies unchanged through the public reexport; no adaptation. |
| Sheaf.Paper.FinitePerfectAdicTowerExtraction | K6 | Names, types, instances and definition bodies unchanged through the public reexport; no adaptation. |
| Sheaf.Paper.FinitePerfectAdicTowerLimit | unclaimed | Names, types, instances and definition bodies unchanged through the public reexport; no adaptation. |
| Sheaf.Paper.FinitePerfectQuotientModels | D2 | Own item: complete the successor combination; preserve every public type. |
| Sheaf.Paper.IntegralResidueStratumInput | unclaimed | Names, types, instances and definition bodies unchanged through the public reexport; no adaptation. |
| Sheaf.Paper.IntegralResidueStratumLift | unclaimed | Names, types, instances and definition bodies unchanged through the public reexport; no adaptation. |
| Sheaf.Paper.ResidueLissePerfectLift | unclaimed | Names, types, instances and definition bodies unchanged through the public reexport; no adaptation. |

The five direct importers are FinitePerfectAdicTowerExtraction,
FinitePerfectAdicRealization, IntegralResidueStratumInput,
IntegralResidueStratumLift and ResidueLissePerfectLift, all under Sheaf.Paper.
Their unchanged originals compiled against this delivery in 9.3 to 42.1 seconds
per file, without errors or warnings. Verification copies were removed afterward.
Transitive users retain the identical public types and bodies; none is adapted
or delivered.

## Status

landed 20261027T052607-L-456495 2026-10-27 (merge of deliver/D2/Sheaf.Paper.FinitePerfectQuotientModels)
