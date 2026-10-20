# WeilConjectures.IntegralHom presentation interface extraction

## Reason

Extract the presentation interface so the three proof obligations may import it
without a cycle through their parent theorem. The item publicly re-exports the
interface. All existing signatures and visibility are retained. Twenty-four
declaration bodies are unchanged. The remaining definition, `homModelMap`, uses
the existing named `coefficientHomResolutionIso` instead of inlining its
localization factorization. An independent scratch equality proof by `rfl`
compiled against this packet. This refactoring prevents expensive repeated
elaboration while preserving the actual morphism. The existing sheafification
attribute is retained in the interface module.

## Old

The following declarations were directly in `Sheaf.Paper.IntegralHomReduction`:

```lean
namespace WeilConjectures.IntegralHom

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

/-- Existing large-coefficient sheafification on the unchanged small site.
Source: Stacks 03DA (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable instance abSheafify :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbSheafify.{t, u} Y

/-- Existing locally bijective sheafification criterion at the coefficient universe.
Source: Stacks 03DA (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable instance abLocallyBijective :
    (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbLocallyBijective.{t, u} Y

/-- The existing module category, retaining both site universes.
Source: Stacks 03DA (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable abbrev Modules := SheafOfModules.{max u (t + 1)}
  ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)

/-- Standard localization instance for the existing module category.
Source: Stacks 05RU (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable instance derivedCategory : HasDerivedCategory (Modules.{t, u} Y R) :=
  HasDerivedCategory.standard _

/-- The standard unbounded derived localization.
Source: Stacks 05RU (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable abbrev Derived := @DerivedCategory (Modules.{t, u} Y R) _ _
  (HasDerivedCategory.standard _)

/-- The existing ambient derived internal Hom, without a change of coefficients.
Source: Stacks 08J7 (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable abbrev hom : (Derived.{t, u} Y R)ᵒᵖ × Derived.{t, u} Y R ⥤ Derived.{t, u} Y R :=
  @derivedInternalHomOfUniverses.{t + 1, t, u}
    _ _ (AlgebraicGeometry.Scheme.ProEt.topology Y) _ _ R
      (HasDerivedCategory.standard _)

/-- The recorded monoidal localization structure for the independent coefficient universe.
Source: Stacks 03EK (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable instance tensorLocalization :
    ((AlgebraicGeometry.Scheme.ProEt.topology Y).W.inverseImage
      (PresheafOfModules.toPresheaf.{max u (t + 1)}
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (forget₂ CommRingCat RingCat)).obj R).obj)).IsMonoidal :=
  SheafOfModules.isMonoidal_W_independentCoefficients R

/-- The existing sectionwise sheaf tensor bifunctor.
Source: Stacks 03EK (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable abbrev ordinaryTensor :=
  @MonoidalCategory.curriedTensor (Modules.{t, u} Y R) _ (SheafOfModules.monoidalCategory R)

/-- Zero preservation in the first tensor argument, from the existing tensor interface.
Source: Stacks 03EK (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable instance ordinaryTensorZero : (ordinaryTensor.{t, u} Y R).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R

/-- Zero preservation in the second tensor argument.
Source: Stacks 03EK (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable instance ordinaryTensorObjZero (M : Modules.{t, u} Y R) :
    ((ordinaryTensor.{t, u} Y R).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R M

/-- Countable totalizations use the existing cocompleteness of module sheaves.
Source: Stacks 03DA (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable instance countableColimits :
    HasColimitsOfSize.{0, 0} (Modules.{t, u} Y R) :=
  letI := integralCoefficientAbSheafify.{t, u} Y
  letI := integralCoefficientAbLocallyBijective.{t, u} Y
  letI : IsGrothendieckAbelian.{max u (t + 1)} (Modules.{t, u} Y R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1,t,u}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R).1
  hasColimitsOfSizeShrink.{0, 0, max u (t + 1), max u (t + 1),
    max u (t + 1), max u (t + 1) + 1} (Modules.{t, u} Y R)

/-- Signed total tensor of complexes, using Mathlib's existing totalization.
Source: Stacks 06YL (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable def totalTensor :
    CochainComplex (Modules.{t, u} Y R) ℤ ⥤ CochainComplex (Modules.{t, u} Y R) ℤ ⥤
      CochainComplex (Modules.{t, u} Y R) ℤ :=
  letI := countableColimits.{t, u} Y R
  letI := ordinaryTensorZero.{t, u} Y R
  letI : ∀ M : Modules.{t, u} Y R,
      ((ordinaryTensor.{t, u} Y R).obj M).PreservesZeroMorphisms :=
    fun M ↦ ordinaryTensorObjZero.{t, u} Y R M
  (ordinaryTensor.{t, u} Y R).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)

/-- The recorded K-flat predicate, with independent coefficient universe.
Source: Stacks 06YN (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable abbrev flat : ObjectProperty (CochainComplex (Modules.{t, u} Y R) ℤ) :=
  CochainComplex.IsKFlatIndependentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology Y) (R := R)

/-- Pure tensors mapped through the ordinary module-sheafification unit.
Source: Stacks 03EK (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable def pair (M N : Modules.{t, u} Y R)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (((ordinaryTensor.{t, u} Y R).obj M).obj N).val.obj U :=
  (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
      (𝟙 ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
          (M.val ⊗ N.val)).app U (x ⊗ₜ[R.obj.obj U] y))

/-- A local homogeneous tensor inserted into the appropriate total summand.
Source: Stacks 06YL (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable def totalPair (P Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    (((totalTensor.{t, u} Y R).obj P).obj Q).X (i + j) |>.val.obj U :=
  letI := countableColimits.{t, u} Y R
  letI := ordinaryTensorZero.{t, u} Y R
  letI : ∀ M : Modules.{t, u} Y R,
      ((ordinaryTensor.{t, u} Y R).obj M).PreservesZeroMorphisms :=
    fun M ↦ ordinaryTensorObjZero.{t, u} Y R M
  (CochainComplex.ιMapBifunctor P Q (ordinaryTensor.{t, u} Y R) i j (i + j) rfl).val.app U
    (pair.{t, u} Y R (P.X i) (Q.X j) U x y)

/-- The existing Hom-complex product projection, with its source type kept explicit.
Source: Stacks 0A8X (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable def projection (P I : CochainComplex (Modules.{t, u} Y R) ℤ)
    (j i : ℤ) :=
  (Classical.choose (homComplex_projections_exists.{t + 1, t, max u (t + 1), max u (t + 1)}
    (R := R))) P I j i (i + j) rfl

/-- The product projection in the existing Hom complex, evaluated at the identity slice.
Source: Stacks 0A8X (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable def evaluate (P I : CochainComplex (Modules.{t, u} Y R) ℤ)
    (j i : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (f : (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I).X j |>.val.obj U)
    (x : (P.X i).val.obj U) : (I.X (i + j)).val.obj U :=
  (((projection.{t, u} Y R P I j i).val.app U f).app (op (Over.mk (𝟙 U.unop)))).hom x

/-- Canonical localization comparison from a Hom complex to derived internal Hom.
It is the Hom map to the fixed K-injective replacement, followed by Localization.fac.
Source: Stacks 08J7 (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable def homModelMap (P I : CochainComplex (Modules.{t, u} Y R) ℤ) :
    DerivedCategory.Q.obj (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I) ⟶
      (hom.{t, u} Y R).obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I) :=
  letI : HasDerivedCategory (Modules.{t, u} Y R) := HasDerivedCategory.standard _
  letI : IsGrothendieckAbelian.{max u (t + 1)} (Modules.{t, u} Y R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1,t,u}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R).1
  DerivedCategory.Q.map
    (((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R)).obj (op P)).map
      ((CochainComplex.toKInjectiveResolution.{max u (t + 1)} _).app I)) ≫
    (Localization.fac _
      (derivedInternalHomOfUniverses_inverts.{t + 1, t, u}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R _
        (CochainComplex.toKInjectiveResolution.{max u (t + 1)} _)
        (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app
          _ M).2, CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj _ M⟩))
      (DerivedCategory.Q.op.prod DerivedCategory.Q)).inv.app (op P, I)

/-- A presentation of the existing derived tensor and its evaluation adjunction.
The last field fixes evaluation on every K-flat test representative by the actual
Hom-complex evaluation, including the sign for the order P tensor Hom(P,I).
Source: Stacks 08J9, 06YU (blueprint: lem-coef-integral-hom-reduction). -/
structure TensorPresentation where
  tensor : Derived.{t, u} Y R × Derived.{t, u} Y R ⥤ Derived.{t, u} Y R
  representative :
    ((flat.{t, u} Y R).ι.prod (flat.{t, u} Y R).ι) ⋙ Functor.uncurry.obj (totalTensor.{t, u} Y R) ⋙
      DerivedCategory.Q ≅
    (((flat.{t, u} Y R).ι ⋙ DerivedCategory.Q).prod
      ((flat.{t, u} Y R).ι ⋙ DerivedCategory.Q)) ⋙ tensor
  adjunction : ∀ K : Derived.{t, u} Y R,
    (Functor.curry.obj tensor).obj K ⊣ (Functor.curry.obj (hom.{t, u} Y R)).obj (op K)
  evaluation : ∀ (P I S : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hP : flat.{t, u} Y R P) (hS : flat.{t, u} Y R S), I.IsKInjective →
    ∀ q : S ⟶ homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I,
      ∃ beta : ((totalTensor.{t, u} Y R).obj P).obj S ⟶ I,
        (∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
          (x : (P.X i).val.obj U) (s : (S.X j).val.obj U),
          (beta.f (i + j)).val.app U (totalPair.{t, u} Y R P S i j U x s) =
            (i * j).negOnePow • evaluate.{t, u} Y R P I j i U ((q.f j).val.app U s) x) ∧
        representative.inv.app (⟨P, hP⟩, ⟨S, hS⟩) ≫ DerivedCategory.Q.map beta =
          tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
            (DerivedCategory.Q.map q ≫ homModelMap.{t, u} Y R P I)) ≫
          (adjunction (DerivedCategory.Q.obj P)).counit.app (DerivedCategory.Q.obj I)

end WeilConjectures.IntegralHom

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

namespace IntegralHom

/-- Additivity of the same ordinary scalar extension, from its recorded adjunction packet.
Source: Stacks 03CZ (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable instance reductionAdditive (n : ℕ) :
    (integralReductionChangeOfRings l E Y D hl n).Additive :=
  scalarReductionExtensionAdditive l E Y n

/-- Zero preservation supplied by additivity of coefficient extension.
Source: Stacks 03CZ (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable instance reductionZero (n : ℕ) :
    (integralReductionChangeOfRings l E Y D hl n).PreservesZeroMorphisms :=
  inferInstance

/-- The canonical derived-reduction counit on complexes, including quotient factors.
Source: Stacks 06YY (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable def reductionCounit (n : ℕ)
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :
    (integralDerivedReduction l E Y D hl n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P) :=
  (integralDerivedReduction l E Y D hl n).map
      ((DerivedCategory.quotientCompQhIso _).app P).inv ≫
    (integralDerivedReductionCounit l E Y D hl n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((integralReductionChangeOfRings l E Y D hl n).mapHomotopyCategoryFactors
        (.up ℤ)).app P).hom ≫
    ((DerivedCategory.quotientCompQhIso _).app
      (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P)).hom

/-- The ordinary extension unit, with its recorded normalization x maps to 1 tensor x.
Its choice is determined by the adjunction and the sectionwise normalization.
Source: Stacks 03CZ (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable def reductionUnit (n : ℕ)
    (M : completedIntegralModuleSheaves l E Y D hl) :
    M ⟶ (completedIntegralRestrictScalars l E Y D hl n).obj
      ((integralReductionChangeOfRings l E Y D hl n).obj M) :=
  (Classical.choose (scalarReductionExtension_adjunction l E Y n)).unit.app M

/-- Canonical tensor comparison for reduction. Its normalization uses every K-flat
pair and the actual ordinary extension units on local sections. The chain comparison
is required to be invertible; its displayed unit formula uniquely determines it.
Thus neither the derived comparison nor the ordinary comparison is an arbitrary map.
Source: Stacks 07A4 and 06YY (blueprint: lem-coef-integral-hom-reduction). -/
structure ReductionPresentation
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)) (n : ℕ) where
  target : TensorPresentation.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)
  mu : a.tensor ⋙ integralDerivedReduction l E Y D hl n ≅
    ((integralDerivedReduction l E Y D hl n).prod
      (integralDerivedReduction l E Y D hl n)) ⋙ target.tensor
  normalization :
    ∀ (P Q : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
      (hp : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) P)
      (hq : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) Q),
    ∃ (hp' : flat.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)
        (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P))
      (hq' : flat.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)
        (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj Q))
      (beta : ((totalTensor.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)).obj
        (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P)).obj
        (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj Q) ⟶
      ((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj
        (((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj Q)),
      IsIso beta ∧
      (∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
        (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
        (beta.f (i + j)).val.app U
          (totalPair.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)
            (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P)
            (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj Q)
            i j U ((reductionUnit l E Y D hl n (P.X i)).val.app U x)
              ((reductionUnit l E Y D hl n (Q.X j)).val.app U y)) =
        (reductionUnit l E Y D hl n
          ((((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj Q).X
            (i + j))).val.app U
          (totalPair.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) P Q i j U x y)) ∧
      (integralDerivedReduction l E Y D hl n).map
          (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
        mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        target.tensor.map (Prod.mkHom (reductionCounit l E Y D hl n P)
          (reductionCounit l E Y D hl n Q)) ≫
        target.representative.inv.app (⟨_, hp'⟩, ⟨_, hq'⟩) ≫ DerivedCategory.Q.map beta =
        reductionCounit l E Y D hl n
          (((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj Q)

/-- The comparison is exactly the transpose of reduced evaluation, using the inverse
canonical tensor comparison. In particular it is a morphism over the finite quotient.
Source: blueprint order 2134, displayed comparison and pairing;
Stacks 07A6 and 08J9 (blueprint: lem-coef-integral-hom-reduction). -/
noncomputable def comparison
    {a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)}
    {n : ℕ} (m : ReductionPresentation l E Y D hl a n)
    (K L : completedIntegralDerivedCategory l E Y D hl) :
    (integralDerivedReduction l E Y D hl n).obj
        ((hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj (op K, L)) ⟶
      (hom.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)).obj
        (op ((integralDerivedReduction l E Y D hl n).obj K),
          (integralDerivedReduction l E Y D hl n).obj L) :=
  (m.target.adjunction ((integralDerivedReduction l E Y D hl n).obj K)).homEquiv _ _
    (m.mu.inv.app (K, (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj (op K, L)) ≫
      (integralDerivedReduction l E Y D hl n).map ((a.adjunction K).counit.app L))

end IntegralHom

```

## New

On the current source tree, the interface uses
`public import WeilConjectures.Algebra.Homology.HomComplexProjections` in place
of the removed `Sheaf.Algebra.Homology.HomComplexProjections` path. The canonical
module exports the same `CategoryTheory.homComplex_projections_exists` theorem;
the projection definition and all presentation signatures remain unchanged.

The declarations above are publicly exposed in
`Sheaf.Paper.IntegralHomReductionModels`, and the parent re-exports them through:

```lean
public import Sheaf.Paper.IntegralHomReductionModels
```

All names, universes, signatures and visibility are retained; twenty-four bodies
are identical. The sole refactored body is:

```lean
noncomputable def homModelMap (P I : CochainComplex (Modules.{t, u} Y R) ℤ) :
    DerivedCategory.Q.obj (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I) ⟶
      (hom.{t, u} Y R).obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I) :=
  letI : IsGrothendieckAbelian.{max u (t + 1)} (Modules.{t, u} Y R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1,t,u}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R).1
  DerivedCategory.Q.map
    (((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R)).obj (op P)).map
      ((CochainComplex.toKInjectiveResolution.{max u (t + 1)} _).app I)) ≫
    (coefficientHomResolutionIso.{u, t + 1, t, max u (t + 1) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R P I).inv
```

Its named factorization is defined by the original `Localization.fac` expression.
The scratch module `IntegralHomDefinitionCheck` copies the old definition verbatim
and proves equality to the new one by `rfl`; it compiled in 6.2 seconds. The added
public import `Sheaf.Paper.CoefficientHomRepresentativeEvaluation` supplies that
factorization. Local irreducibility attributes on the large representative maps
and the two reduction unit/counit maps prevent their repeated unfolding while
checking later presentation fields. These attributes and backward elaboration
options are local to the file. A later delivery compile hit the file limit, so
local irreducibility was also applied to homComplexFunctor,
derivedInternalHomOfUniverses, integralDerivedReduction, and
integralReductionChangeOfRings while checking the presentation fields. The
revised interface compiled in 29.9 seconds, with all signatures unchanged. The
original structure API is retained.

The main theorem retains its exact signature. Its proof uses private imports.
There is no change to mathematical meaning; a target review can check the
compiled definitional equality when auditing the implementation refactoring.

## Users

The table includes the 1,105 transitive importers from the original `downstream.py`
snapshot, the item itself, and additional textual users found by current preflight
and source checks, including quarantined consumers. Holders are read from current project claim metadata. The tool's
textual `homModelMap` users are the item, PointCompletedEvaluation and
PointDerivedHomEvaluation. Public re-export preserves the interface, and the
refactored map is definitionally the original map. No consumer source is adapted.
Current direct consumers and the two external textual users are checked through
lcompile.py; results and any published-build failures are recorded in report.md.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | Z5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | Z6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleHomOfPreserves | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorHomAdjunctionOfPreserves | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange | G9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization | P9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | J2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | R1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | D3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | D2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteConstantLocalModel | C9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.FormalPuncturedSections | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiberComponentsSection | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | P9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | H9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport | Y5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.LogSmoothTraitPunctualPurity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.MonomialBoundaryPurityCriterion | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.MonomialTraitPunctualPurity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.PrimeFieldPunctualPurity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructibleLowerStar | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | E6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit | D9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleTorsionStalk | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | X7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.PunctualPurityTraitTest | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | S1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | K1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | P5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothPunctualPurityAscent | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | F9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | D9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicClosedConstructible | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | B8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | T4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | C7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | G5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | C8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | Y5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ArbitraryFieldAdjunctionScalars | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | Q8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | Q9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | R5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.BoundedConstructibleBaseChange | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | G3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CartesianCoefficientTwists | Z6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CartesianCoefficients | E8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | E2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CartierClassAgreement | U5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ChernFlagFormula | G4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | A7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | R3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentHom | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | F3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentSections | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CoefficientHeart | X8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CoefficientHeartFiltration | P4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CoefficientHeartTriangulated | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | K6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | Y2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | R7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompactFiberStalk | E7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | U3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | K4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | R6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | Q4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompactSupportReductionTower | P2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | R9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | H3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | Y9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | D2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedCompactSupportProjection | F2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedERealization | C4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedPointCoefficients | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedPointDiscreteConstantComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CondensedZlReduction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | W3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | J4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ConstantToContinuousScalarFlat | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | R2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | H1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | R2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | E6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | K2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DenseOpenPiOneSurjective | E3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | T2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DerivedNakayama | M9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DerivedNakayamaFirstReduction | T3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DerivedNakayamaResolution | U1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | S9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DiagonalTowerSystem | W6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DirectImageChangeRingTranspose | J2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | G8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | R2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.EtaleLocalMonodromyRealization | U9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | U4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.EtaleSectionDeformationComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.EtaleWeilSheafEquivalence | H6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.EvenTensorPositivity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | Z5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | Z6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | D6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | Q3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | P8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | F1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | G1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | C2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteClosedShriek | K6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | M1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | G9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteConstantModelResolution | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | M4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | V8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | U1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | U3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | U5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | K8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteModelStratumFiltration | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | N3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteProperBaseChange | U4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | W7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | G9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | A4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | W2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | N4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | Y6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FormalClosedSupportDerived | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FormalClosedSupportSheaves | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | X3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | V8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | A5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | D9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralCoefficientExtComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | W4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | X2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | W7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | W5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | G2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | P1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | P1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | S4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralCriterionReductions | X3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralDerivedCoefficientData | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | M3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralExtensionByZero | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | C5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | C3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralHomReduction | M4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralModels | D4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralModelsOperations | N1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralOpenExtensionReduction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | Y8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | B4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | F5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | V4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | C2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | Y9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralTensorProduct | N3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralTensorPullback | J2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralTensorShriek | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralTwistBaseChange | J4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralTwistScalarCoherence | N4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.InternalHomDualTorAmplitude | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | D4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.LisseCompletedSystemComparison | Q2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | H8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | Q5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | A6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.LocalizedTopChern | E5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | H9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.LocallyConstantPerfectComplex | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.MateOpenRestriction | U2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | E5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | A5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | W5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.NormalProEtaleMonodromy | K7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | T8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.OpenFiltrationSuccessor | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PadicIntegersInvertEll | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | E4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PointDerivedHomEvaluation | J9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PointSectionsReconstruction | G8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | B4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | D2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProjectionSectionNormalization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | E9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | T6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | P9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | Y5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | V4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperHeartBoundTorsion | J4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | T7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperUnboundedWindowBounded | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | J9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PuncturedDerivedCompletionSections | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | Y2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | P3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | J6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | E2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityConventions | X8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | R3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | R2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityDivisorClass | J7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityDncComparisons | G3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityFrameIndependence | A4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityGysinStructure | F1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PuritySourceTransports | V6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.QbarAffineSupportBound | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | H9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.QbarDerivedDirectImage | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.QbarOrdinaryAdjunction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | D3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | U7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | Z9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | K8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalStalkExact | A7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RealSheafSections | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | A3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ResidueLisseProjectiveModels | G2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SectionDerivedRealization | J8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SectionModuleOperationsData | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | F9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SfBidualityClass | C6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | K9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | T3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | X7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothLisseIntegralLattice | T8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityCoefficientTowers | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityCoefficientTowersAbelian | C9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionBaseChange | F8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityMap | R2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedTowers | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | C1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | J3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerEvaluationAdjoint | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerInjectiveComponents | T4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerLevels | J4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | M4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerRightExtension | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerRightExtensionFiniteColimits | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.StratifiedLattice | M6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.StratifiedLatticeRank | T9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SystemClopenTensorCompatibility | Y5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | F5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | K1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TAdmissibleCoefficientModels | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TateTwistLocallyFree | S7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | N2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TraceBaseChangeFirst | E1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | U5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | C2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | J8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwConventions | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwistPreservesFiniteness | G5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | Z9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | X8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | B2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.WContractibleCondensedScalarEvaluation | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | A8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.WeilFourierTransform | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | E7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | S2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | U8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | Q8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | P7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | J7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | U2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.RingTheory.CompleteLocalConnectednessBound | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.RingTheory.NormalPuncturedHypersurfaceConnected | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | W9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | U8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | U9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Z8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | G8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | M9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | G1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | N2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | M1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | V1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.BrownHypothesesAmbient | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | Z9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.ClosedImmersionTensorProjection | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | R5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | J1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | F2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | J5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.CompactCoefficientComposition | U6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | V5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | Q6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | J6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | P6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.FieldTensor | G2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | E3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | W2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | M6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | J7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | M7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | N3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | B5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | M2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntTensorProjection | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | Z8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | W8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | P5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | A8 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralLisseReductionEquivalence | T1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | T3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | R1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | T9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | R5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.ModuleMapmodPullbackKFlat | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | J1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | M2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.OpenImmersionTensorProjection | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | R9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | F4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | K2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | X5 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | A4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.RationalVerdier | V4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.ScalarSixPullback | U6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | E4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | S6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | D6 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | H1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Topology.ProfiniteCondensedRing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Topology.ProfinitePointSite | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | Y7 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | H1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | T2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| TargetsCheck | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ArtinSchreierDual | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Constituent | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DirectImageUnit | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.GeometricSMul | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LaurentPoints | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LinearCharacters | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Punctual | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualSupport | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RamifiedAtInfinity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryGenericRep | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodConstruction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodExistence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseWeilSheafTensor | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentationTensor | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSections | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationFunctor | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationTensor | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.FieldStagePointers | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverEquivalence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExists | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyLift | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyPullback | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.TwistedSection | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | H5 | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.Statement | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierFunctions | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierInertia | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierIsotypic | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierMul | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierMulGeometric | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierNeg | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPlane | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPullback | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrivialization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalkFrobenius | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalkGaloisInvariants | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalkSpecialization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStrictHenselization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.CohomologySequence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ConstantTwistWeight | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.DerivedHom | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FiniteEtale | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FiniteLeray | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FiniteLowerStar | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FinitePointCohomology | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.GlobalSectionsUpperStar | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.IhomCurry | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.IhomLisse.CompWeil | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.IhomLisse.UpperStar | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.IhomLisse.UpperStarDual | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.Isotypic | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.IsotypicPullback | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.LSeries | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.LisseExtension | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.LowerStarTriangulated | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ProperBaseChange | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.ShiftedSheaf | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.SplitTorsor | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.StalkRationalPoint | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.StalkStrictlyHenselian | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.StalkTensorTrace | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.TorsorPairing | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.TraceFunction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.UpperStarLowerStar | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunctionWeil | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged signatures and meaning; no source adaptation. |

| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Mentions the retained IntegralHom names; no source adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | G2 | Mentions the retained IntegralHom names; no source adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | C6 | Mentions the retained IntegralHom names; no source adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | Mentions the retained IntegralHom names; no source adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Mentions the retained IntegralHom names; no source adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Mentions the retained IntegralHom names; no source adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Mentions the retained IntegralHom names; no source adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Mentions the retained IntegralHom names; no source adaptation. |
| Sheaf.Paper.ExchangeFunctoriality | D6 | Mentions the retained IntegralHom names; no source adaptation. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Mentions the retained IntegralHom names; no source adaptation. |

| Sheaf.Paper.CompactificationProjectionPasting | E3 | Mentions retained IntegralHom names; no source adaptation. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed | Mentions retained IntegralHom names; no source adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Mentions retained IntegralHom names; no source adaptation. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Mentions retained IntegralHom names; no source adaptation. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Mentions retained IntegralHom names; no source adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Mentions retained IntegralHom names; no source adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | H6 | Mentions retained IntegralHom names; no source adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | R6 | Mentions retained IntegralHom names; no source adaptation. |

| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Uses the retained derivedCategory instance; no source adaptation. |

| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | A4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ConstructibleProjectionMates | C1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.DualBaseChange | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | Q1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | V9 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.IdentificationCoefficientTransport | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | E3 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | G4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | N4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | R2 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | H1 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | P4 | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Unchanged signatures and meaning; no source adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Unchanged signatures and meaning; no source adaptation. |

| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Quarantined consumer; retained signatures and meaning unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing | unclaimed | Quarantined consumer; retained signatures and meaning unchanged; no source adaptation. |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed | Quarantined consumer; retained signatures and meaning unchanged; no source adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Quarantined consumer; retained signatures and meaning unchanged; no source adaptation. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | Quarantined consumer; retained signatures and meaning unchanged; no source adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Quarantined consumer; retained signatures and meaning unchanged; no source adaptation. |

## Status

landed 20261020T230810-L-613944 2026-10-20 (merge of deliver/M4/Sheaf.Paper.IntegralHomReduction)
