module

public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Paper.QuotientSystemFlatModels
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.MixedReductionUnit
public import Sheaf.Paper.CompletedLineTensorCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Sheaf.Paper.CoefficientExtensionReductionData

/-! # Composition of normalized mixed completed reduction units

Source: current blueprint lem-fix-operation-reduction.proof.md, tensor reassociation
and transport of the specified maps; coefficient-composition detail preceding compact support.
(blueprint: lem-weil-mixed-reduction-unit-composition)

The equalities are in the derived category of the entire ringed quotient sequence site.
They retain all horizontal transitions and the fixed universal-counit and Roos normalizations.

## Main definitions and statements

- `IntegralCoherentReduction.derived`: reduction on the whole quotient sequence site.
- `MixedCoherentReduction.completed`: its counit-normalized completed mixed unit.
- `mixedReductionUnit_composition`: the composition and identity laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.IntegralCoherentReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The constant completed ring on the vertical sequence site.
Source: Bhatt--Scholze, Definition 3.5.2 (blueprint: lem-weil-mixed-reduction-unit-composition). -/
def constantRing := SemilinearSections.quotientConstantRing.{t + 1, t, u}
  (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)

/-- All quotient projections form one map of sequence ring sheaves.
Source: Bhatt--Scholze, Definition 3.5.2 (blueprint: lem-weil-mixed-reduction-unit-composition).
Proof: at (n,U) use the nth projection of the completed ring. The limit projection
identities give horizontal naturality; vertical naturality is that of the projections.
These components determine a unique sheaf morphism. -/
theorem projection_existsUnique :
    ∃! f : constantRing l E W ⟶ coefficientSequenceCommRingSheaf l E W,
      ∀ (n : ℕ) (U : W.ProEtᵒᵖ), f.hom.app (op (n, U.unop)) =
        (completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U := by
  let α := completedIntegralCommRingProjectionUnrestricted l E W
  have hα (n : ℕ) : α (n + 1) ≫ coefficientSequenceCommRingTransition l E W n = α n := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply (forget₂ CommRingCat RingCat).map_injective
    change (limit.π (integralCoefficientSheafSystem l E W) (op (n + 1))).hom.app U ≫
        (integralCoefficientSheafTransition l E W n).hom.app U =
      (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app U
    have h := congrArg (fun k ↦ k.hom.app U)
      (limit.w (integralCoefficientSheafSystem l E W) (homOfLE (Nat.le_succ n)).op)
    simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using h
  let f : constantRing l E W ⟶ coefficientSequenceCommRingSheaf l E W :=
    SemilinearSections.quotientRingMap.{t + 1, t, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)
      (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) α hα
  refine ⟨f, fun _ _ ↦ rfl, ?_⟩
  intro g hg
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact hg U.unop.1 (op U.unop.2)

/-- The actual quotient map on the entire sequence site.
Source: Bhatt--Scholze, Definition 3.5.2 (blueprint: lem-weil-mixed-reduction-unit-composition). -/
def projection := (projection_existsUnique l E W).exists.choose

/-- Exact constant sequences, before tensoring by the quotient system.
Source: Bhatt--Scholze, Definition 3.5.2 (blueprint: lem-weil-mixed-reduction-unit-composition). -/
abbrev constant := SemilinearSections.quotientConstant.{t + 1, t, u}
  (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)

/-- The existing universal tensor model on the ringed sequence site.
Its ordinary functor is fixed on objects and maps; its derived pair is fixed up to
its unique counit-preserving isomorphism, rather than by a bare existence choice.
Source: Stacks 06YY (blueprint: lem-weil-mixed-reduction-unit-composition). -/
def model := (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel
  (projection l E W)).some

/-- Ordinary tensor reduction with every horizontal quotient map retained.
Source: Bhatt--Scholze, Definition 3.5.2 (blueprint: lem-weil-mixed-reduction-unit-composition). -/
abbrev ordinary := constant l E W ⋙ (model l E W).E

/-- The sheafified pure-tensor section of the simultaneous reduction model.
Source: Bhatt--Scholze, Definition 3.5.2 (blueprint: lem-weil-mixed-reduction-unit-composition). -/
def tensor (M : integralTowerModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E W n).obj.obj U) (x : M.val.obj U) :
    ((ordinary l E W).obj M).val.obj (op (n, U.unop)) :=
  (eqToHom ((model l E W).obj_eq ((constant l E W).obj M)).symm).val.app
    (op (n, U.unop))
      ((toSheafify (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (SheafOfModules.changeOfRingsPresheaf (projection l E W)
          ((constant l E W).obj M)).presheaf).app (op (n, U.unop))
            (s ⊗ₜ[(constantRing l E W).obj.obj (op (n, U.unop)),
              ((projection l E W).hom.app (op (n, U.unop))).hom] x))

/-- Coherent derived reduction, in the derived category of the entire sequence site.
Source: Bhatt--Scholze, Definition 3.5.2 (blueprint: lem-weil-mixed-reduction-unit-composition). -/
def derived := (constant l E W).mapDerivedCategory ⋙ (model l E W).T

/-- The universal reduction counit on every complex, before finite evaluation.
This is the cochain presentation of the homotopy-category counit square.
Source: Stacks 06YY (blueprint: lem-weil-mixed-reduction-unit-composition). -/
def counit (P : CochainComplex (integralTowerModules l E W) ℤ) :
    (derived l E W).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((ordinary l E W).mapHomologicalComplex (.up ℤ)).obj P) :=
  (model l E W).T.map ((constant l E W).mapDerivedCategoryFactors.hom.app P) ≫
    (model l E W).ε.app (((constant l E W).mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (constant l E W ⋙ (model l E W).E)) (.up ℤ)).hom.app P)

end WeilConjectures.IntegralCoherentReduction

namespace WeilConjectures.MixedCoherentReduction
variable (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

/-- The quotient inclusions as one ring-sheaf morphism, including all transitions.
Source: blueprint reduction paragraph (blueprint: lem-weil-mixed-reduction-unit-composition).
Proof: coefficient inclusions commute with quotient projections. The component maps
therefore commute with all horizontal maps and with vertical restriction; uniqueness
is equality of natural transformations component by component. -/
theorem ringMap_existsUnique :
    ∃! f : coefficientSequenceCommRingSheaf l E W ⟶ coefficientSequenceCommRingSheaf l L W,
      ∀ (n : ℕ) (U : W.ProEtᵒᵖ), f.hom.app (op (n, U.unop)) =
        (integralScalarQuotientSheafMap l E L ι W n).hom.app U := by
  let τ : coefficientSequenceCommRingSystem l E W ⟶
      coefficientSequenceCommRingSystem l L W :=
    NatTrans.ofOpSequence (integralScalarQuotientSheafMap l E L ι W) (fun n ↦ by
      simp only [coefficientSequenceCommRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact (coefficientExtensionQuotient_naturality l E L ι W n).symm)
  let f : coefficientSequenceCommRingSheaf l E W ⟶
      coefficientSequenceCommRingSheaf l L W :=
    ⟨Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := W.ProEt)).functor
      (Functor.uncurry.map (Functor.whiskerRight τ
        (sheafToPresheaf (Scheme.ProEt.topology W) CommRingCat)))⟩
  refine ⟨f, fun _ _ ↦ rfl, ?_⟩
  intro g hg
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact hg U.unop.1 (op U.unop.2)

/-- The actual sequence-ring coefficient inclusion.
Source: blueprint reduction paragraph (blueprint: lem-weil-mixed-reduction-unit-composition). -/
def ringMap := (ringMap_existsUnique l E L ι W).exists.choose

/-- Exact restriction on entire semilinear quotient systems.
Source: blueprint reduction paragraph (blueprint: lem-weil-mixed-reduction-unit-composition). -/
abbrev restrict := SemilinearSections.res (ringMap l E L ι W)

/-- Its exact derived realization, before finite evaluation.
Source: blueprint reduction paragraph (blueprint: lem-weil-mixed-reduction-unit-composition). -/
abbrev restrictD := (restrict l E L ι W).mapDerivedCategory

/-- The sheafified tensor formula of the mixed unit, with every transition retained.
Source: blueprint tensor reassociation paragraph (blueprint:
lem-weil-mixed-reduction-unit-composition).
Proof: at (n,U) send s tensor x to iota_n(s) tensor (1 tensor x).
The balanced relation follows from the completed coefficient projection identity.
This commutes with quotient maps and vertical restrictions. Sheafification gives
existence, and local generation by pure tensors gives uniqueness. -/
theorem ordinary_existsUnique :
    ∃! η : IntegralCoherentReduction.ordinary l E W ⟶
      completedOrdinaryScalarExtension l E L ι W ⋙
        IntegralCoherentReduction.ordinary l L W ⋙ restrict l E L ι W,
      ∀ (M : integralTowerModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf l E W n).obj.obj U) (x : M.val.obj U),
        (η.app M).val.app (op (n, U.unop))
          (IntegralCoherentReduction.tensor l E W M n U s x) =
          IntegralCoherentReduction.tensor l L W
            ((completedOrdinaryScalarExtension l E L ι W).obj M) n U
            ((integralScalarQuotientSheafMap l E L ι W n).hom.app U s)
            (completedScalarTensorSection l E L ι W M U 1 x) := by
  sorry

/-- The uniquely prescribed sheaf transformation on the whole sequence site.
Source: blueprint tensor reassociation paragraph (blueprint:
lem-weil-mixed-reduction-unit-composition). -/
def ordinary := (ordinary_existsUnique l E L ι W).exists.choose

/-- The termwise mixed unit, with the two composite functor identifications included.
Source: blueprint tensor reassociation paragraph (blueprint:
lem-weil-mixed-reduction-unit-composition). -/
def complex :
    (IntegralCoherentReduction.ordinary l E W).mapHomologicalComplex (.up ℤ) ⟶
      (completedOrdinaryScalarExtension l E L ι W).mapHomologicalComplex (.up ℤ) ⋙
        (IntegralCoherentReduction.ordinary l L W).mapHomologicalComplex (.up ℤ) ⋙
          (restrict l E L ι W).mapHomologicalComplex (.up ℤ) :=
  NatTrans.mapHomologicalComplex (ordinary l E L ι W) (.up ℤ) ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (completedOrdinaryScalarExtension l E L ι W ⋙
        IntegralCoherentReduction.ordinary l L W ⋙ restrict l E L ι W)) (.up ℤ)).inv ≫
    Functor.whiskerLeft _ (Functor.mapHomologicalComplexCompIso
      (Iso.refl (IntegralCoherentReduction.ordinary l L W ⋙ restrict l E L ι W)) (.up ℤ)).inv

/-- Descent is characterized by the universal counit square on the entire homotopy
category, here presented on all cochain representatives, not after finite evaluation.
Source: blueprint tensor reassociation paragraph (blueprint:
lem-weil-mixed-reduction-unit-composition).
Proof: use the universal left-derived reduction counits and the ordinary scalar
counit. On flat-term K-flat representatives they are invertible. The sheaf formula
therefore descends uniquely through localization, naturally for every cochain map.
Homotopic maps agree, so this cochain equation is the full homotopy-category equation.
No quotient map is required to be flat. -/
theorem derived_existsUnique :
    ∃! η : IntegralCoherentReduction.derived l E W ⟶
      completedDerivedScalarExtension l E L ι W ⋙
        IntegralCoherentReduction.derived l L W ⋙ restrictD l E L ι W,
      ∀ P : CochainComplex (integralTowerModules l E W) ℤ,
        η.app (DerivedCategory.Q.obj P) ≫
          (restrictD l E L ι W).map
            ((IntegralCoherentReduction.derived l L W).map (completedScalarCounit l E L ι W P) ≫
              IntegralCoherentReduction.counit l L W
                ((completedOrdinaryScalarComplex l E L ι W).obj P)) ≫
          (restrict l E L ι W).mapDerivedCategoryFactors.hom.app
            (((IntegralCoherentReduction.ordinary l L W).mapHomologicalComplex (.up ℤ)).obj
              ((completedOrdinaryScalarComplex l E L ι W).obj P)) =
        IntegralCoherentReduction.counit l E W P ≫
          DerivedCategory.Q.map ((complex l E L ι W).app P) := by
  sorry

/-- The universal ordinary derived mixed unit, with its full counit normalization.
Source: blueprint tensor reassociation paragraph (blueprint:
lem-weil-mixed-reduction-unit-composition). -/
def derived := (derived_existsUnique l E L ι W).exists.choose

/-- The completed mixed unit is reduction of the prescribed diagonal Roos comparison
after the uniquely descended ordinary mixed unit. The zero shifted-product coordinate
and quotient augmentation are those of completedScalarComparison, without a chain inverse.
Source: blueprint transport paragraph (blueprint: lem-weil-mixed-reduction-unit-composition). -/
def completed (K : DerivedCategory (integralTowerModules l E W)) :
    (IntegralCoherentReduction.derived l E W).obj K ⟶
      (restrictD l E L ι W).obj
        ((IntegralCoherentReduction.derived l L W).obj
          ((integralScalarExtensionOfUniverses l E L ι W).obj K)) :=
  (derived l E L ι W).app K ≫
    (restrictD l E L ι W).map
      ((IntegralCoherentReduction.derived l L W).map
        ((completedScalarComparison l E L ι W).app K))

attribute [local irreducible] IntegralCoherentReduction.model
  completedIntegralCommRingSheafUnrestricted

private theorem ringMap_id : ringMap l E E (AlgHom.id ℚ_[l] E) W = 𝟙 _ := by
  apply (ringMap_existsUnique l E E (AlgHom.id ℚ_[l] E) W).unique
  · exact (ringMap_existsUnique l E E (AlgHom.id ℚ_[l] E) W).exists.choose_spec
  · intro n U
    have hring : integralScalarQuotientMap l E E (AlgHom.id ℚ_[l] E) n =
        RingHom.id _ := by
      ext x
      rfl
    have hq : integralScalarQuotientSheafMap l E E (AlgHom.id ℚ_[l] E) W n = 𝟙 _ := by
      unfold integralScalarQuotientSheafMap
      rw [hring]
      convert (constantSheaf (Scheme.ProEt.topology W)
        CommRingCat.{max u (t + 1)}).map_id
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
        using 1 <;> rfl
    rw [hq]
    rfl

/-- Identity scalar restriction is the identity on sections.
Source: blueprint repeated-field convention (blueprint: lem-weil-mixed-reduction-unit-composition).
Proof: the identity coefficient embedding induces the identity ring map on every
quotient. The identity maps on section groups are therefore linear and natural,
and give inverse isomorphisms. Their components determine the isomorphism uniquely. -/
theorem restrictUnit_existsUnique :
    ∃! e : restrict l E E (AlgHom.id ℚ_[l] E) W ≅ 𝟭 _,
      ∀ (M : coefficientSequenceModules l E W) (U : (ℕ × W.ProEt)ᵒᵖ)
        (x : M.val.obj U), (e.hom.app M).val.app U x = x := by
  let heq : restrict l E E (AlgHom.id ℚ_[l] E) W ≅ 𝟭 _ :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        ModuleCat.restrictScalarsId'App _
          (congrArg (fun f ↦ (f.hom.app U).hom) (ringMap_id l E W)) (M.val.obj U))
        (by intro U V f; ext x; rfl))) (by intro M M' f; ext U x; rfl)
  refine ⟨heq, fun _ _ _ ↦ rfl, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext M
  ext U x
  exact he M U x

/-- The identity-on-sections identification after deriving exact restriction.
Source: blueprint repeated-field convention (blueprint:
lem-weil-mixed-reduction-unit-composition). -/
def restrictUnit : restrictD l E E (AlgHom.id ℚ_[l] E) W ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (restrictUnit_existsUnique l E W).exists.choose ≪≫
    Functor.mapDerivedCategoryIdIso _

variable (N : Type u) [Field N] [Algebra ℚ_[l] N] [FiniteDimensional ℚ_[l] N]
  (j : L →ₐ[ℚ_[l]] N)

private theorem ringMap_comp :
    ringMap l E L ι W ≫ ringMap l L N j W = ringMap l E N (j.comp ι) W := by
  apply (ringMap_existsUnique l E N (j.comp ι) W).unique
  · intro n U
    have hq (n : ℕ) : (integralScalarQuotientMap l L N j n).comp
        (integralScalarQuotientMap l E L ι n) =
          integralScalarQuotientMap l E N (j.comp ι) n := by
      apply RingHom.ext
      intro x
      induction x using Quotient.inductionOn' with
      | h x => rfl
    have hs : integralScalarQuotientSheafMap l E L ι W n ≫
        integralScalarQuotientSheafMap l L N j W n =
          integralScalarQuotientSheafMap l E N (j.comp ι) W n := by
      unfold integralScalarQuotientSheafMap
      rw [← Functor.map_comp]
      congr 1
      ext x
      exact congrArg (fun f ↦ f x.down) (hq n)
    change (ringMap l E L ι W).hom.app (op (n, U.unop)) ≫
        (ringMap l L N j W).hom.app (op (n, U.unop)) = _
    exact (congrArg₂ (fun f g ↦ f ≫ g)
      ((ringMap_existsUnique l E L ι W).exists.choose_spec n U)
      ((ringMap_existsUnique l L N j W).exists.choose_spec n U)).trans
        (congrArg (fun f ↦ f.hom.app U) hs)
  · exact (ringMap_existsUnique l E N (j.comp ι) W).exists.choose_spec

/-- Successive restrictions identify by the identity on every section group.
Source: blueprint coefficient composition (blueprint: lem-weil-mixed-reduction-unit-composition).
Proof: the composite quotient homomorphism is the quotient of j composed with iota.
Both restricted actions are therefore identical. Identity section maps give the
natural isomorphism and its inverse; sectionwise equality proves uniqueness. -/
theorem restrictComp_existsUnique :
    ∃! e : restrict l L N j W ⋙ restrict l E L ι W ≅ restrict l E N (j.comp ι) W,
      ∀ (M : coefficientSequenceModules l N W) (U : (ℕ × W.ProEt)ᵒᵖ)
        (x : M.val.obj U), (e.hom.app M).val.app U x = x := by
  let e : restrict l L N j W ⋙ restrict l E L ι W ≅ restrict l E N (j.comp ι) W :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        (ModuleCat.restrictScalarsComp'App _ _ _
          (congrArg (fun f ↦ (f.hom.app U).hom) (ringMap_comp l E L ι W N j).symm)
          (M.val.obj U)).symm) (by intro U V f; ext x; rfl)))
      (by intro M M' f; ext U x; rfl)
  refine ⟨e, fun _ _ _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  ext U x
  exact he' M U x

/-- The same identity identification of successive derived scalar restrictions.
Source: blueprint coefficient composition (blueprint: lem-weil-mixed-reduction-unit-composition). -/
def restrictComp : restrictD l L N j W ⋙ restrictD l E L ι W ≅
    restrictD l E N (j.comp ι) W :=
  Functor.mapDerivedCategoryCompNatIso
    (restrictComp_existsUnique l E L ι W N j).exists.choose

end WeilConjectures.MixedCoherentReduction

namespace WeilConjectures

/-- The normalized composition and identity equations on whole coherent reduction diagrams.
Source: blueprint lem-fix-operation-reduction, first and last paragraphs, coefficient
composition before compact support (blueprint: lem-weil-mixed-reduction-unit-composition).
Proof:
1. Before completion, the two successive sheaf maps both send s tensor x to
   iota_20(s) tensor (1 tensor x); the identity map followed by multiplication is identity.
   The formulas commute with every quotient transition, hence hold on entire systems.
2. Apply lem-coef-semilinear-derived-sections and
   lem-trf-ringed-kflat-word-comparison-descent on the sequence site. The universal
   counits descend the balanced comparisons and their pasting identities. The normalized
   adjunction of lem-pur-sheaf-ring-derived-coefficient-adjunction and mate pasting identify
   these with the ordinary derived mixed units. The reassociation is that of
   lem-sfb-successive-derived-quotient-normalization. No quotient flatness is used.
3. By lem-pur-quotient-scalar-comparison-descent, chi is the natural quotient/zero-shifted
   map. By lem-weil-finite-free-completed-scalar-comparison it is invertible on complete
   inputs; ordinary extension is complete, and completed extension is complete by transport.
4. The associator and unit of lem-pur-completed-line-tensor-coherence satisfy a*t=chi*d
   and e*chi=lambda, where t=C21(chi10)*chi21. These are scalar equations without lines.
5. Naturality of the ordinary mixed unit and then of chi rewrites eta21*eta10 as
   r2(t)*v21*v10. Restrict every term to the original quotient system.
6. Postcompose with r2(a); cancel t by step 4 and use step 2 to get eta20.
   Likewise e*chi=lambda and the ordinary identity law give r0(e)*eta00=identity.
   Equal adjacent fields and both identity insertions are included.
7. These equations precede finite evaluation. The fixed strict Roos realization acts
   diagonally on both product coordinates and carries (0,gamma) to (0,f*gamma).
   lem-pur-strict-roos-homotopy-functor, exact countable products from
   lem-weil-proetale-countable-products-exact, and lem-weil-strict-roos-comparison
   carry the equations to their strict-tower and derived-limit realizations with
   the prescribed augmentation. No chain inverse to chi or detection by projections
   of a derived limit is asserted. -/
theorem mixedReductionUnit_composition
    (l : ℕ) [Fact l.Prime] (A M N : Type u) [Field A] [Field M] [Field N]
    [Algebra ℚ_[l] A] [Algebra ℚ_[l] M] [Algebra ℚ_[l] N]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] M] [FiniteDimensional ℚ_[l] N]
    (ι : A →ₐ[ℚ_[l]] M) (j : M →ₐ[ℚ_[l]] N) (W : Scheme.{t})
    (K : DerivedCategory (integralTowerModules l A W))
    (hK : IntegralOnSlice.IsComplete l A W none K) :
    (MixedCoherentReduction.completed l A M ι W K ≫
        (MixedCoherentReduction.restrictD l A M ι W).map
          (MixedCoherentReduction.completed l M N j W
            ((integralScalarExtensionOfUniverses l A M ι W).obj K)) ≫
        (MixedCoherentReduction.restrictComp l A M ι W N j).hom.app
          ((IntegralCoherentReduction.derived l N W).obj
            ((integralScalarExtensionOfUniverses l M N j W).obj
              ((integralScalarExtensionOfUniverses l A M ι W).obj K))) ≫
        (MixedCoherentReduction.restrictD l A N (j.comp ι) W).map
          ((IntegralCoherentReduction.derived l N W).map
            (CompletedLineTensor.associator l A W M ι N j K hK).hom) =
      MixedCoherentReduction.completed l A N (j.comp ι) W K) ∧
    (MixedCoherentReduction.completed l A A (AlgHom.id ℚ_[l] A) W K ≫
        (MixedCoherentReduction.restrictUnit l A W).hom.app
          ((IntegralCoherentReduction.derived l A W).obj
            ((integralScalarExtensionOfUniverses l A A (AlgHom.id ℚ_[l] A) W).obj K)) ≫
        (IntegralCoherentReduction.derived l A W).map
          (CompletedLineTensor.unit l A W K hK).hom = 𝟙 _) := by
  sorry

end WeilConjectures
