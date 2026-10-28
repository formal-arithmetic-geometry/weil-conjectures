/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q10 and D4
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.CoefTowerCoaugmentation
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Sheaf.Paper.PointAutomorphismRestrictionNatural
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.Paper.PointSystemEvaluationComparisons
import all Sheaf.Paper.PointRestrictionSystemChainMap
import all Sheaf.Paper.PointAutomorphismRestrictionNatural
import Sheaf.AlgebraicGeometry.ProEtale.FiniteComparisonIsomorphism
import Sheaf.Paper.PointSystemTensorTransition
/-! # Exact section functors and normalized chain transport on strict systems

This is the chain-level construction of point-system transport, before localization.
The declarations retain their original names and definitions. They are compiled
separately from the derived evaluation argument.
(blueprint: lem-trf-point-system-transport-chain).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard

universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointSystemTransport

variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual rth power of geometric Frobenius at the point.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-chain). -/
def pointPower : ℕ → (Spec (.of D.k) ≅ Spec (.of D.k))
  | 0 => Iso.refl _
  | r + 1 => pointPower r ≪≫ frobeniusPointIso D

/-- Postcompose every site object by h^r, retaining its coefficient index.
Source: blueprint proof (3), inverse-image recipe
(blueprint: lem-trf-point-system-transport-chain). -/
def reindex (r : ℕ) : (ℕ × (Spec (.of D.k)).ProEt) ⥤
    (ℕ × (Spec (.of D.k)).ProEt) :=
  (𝟭 ℕ).prod (proEtaleIsoPostcompose (pointPower D r).hom)

/-- Reindexing preserves the vertical sheaf condition.
Source: Stacks 0941 and 09A5 (blueprint: lem-trf-point-system-transport-chain).
Proof: the sequence topology tests covers in the vertical slice. Postcomposition
by h^r is a covering-preserving site equivalence, by
lem-weil-proetale-isomorphism-inverse-image. Its product with the identity of the
index category therefore preserves the same sheaf condition. -/
@[instance] theorem reindexContinuous (r : ℕ) :
    (reindex D r).IsContinuous
      (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))
      (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k)))) := by
  exact PointRestrictionSystem.reindexContinuous D (pointPower D r).hom

/-- The existing sequence coefficient sheaf, with commutativity forgotten.
Source: Stacks 0941 (blueprint: lem-trf-point-system-transport-chain). -/
abbrev sequenceRing :=
  (sheafCompose (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E (Spec (.of D.k)))

/-- Assemble precisely the inverses of the canonical finite coefficient comparisons.
Source: blueprint proof (3), coefficient square
(blueprint: lem-trf-point-system-transport-chain).
Proof: the finite coefficient isomorphisms commute with quotient maps, since both
composites fix each constant section after quotient reduction. Thus their inverses
are natural in horizontal and vertical arrows. They form a map of sequence sheaves.
Every component is prescribed, so natural-transformation extensionality proves uniqueness. -/
theorem coefficient_existsUnique (r : ℕ) :
    ∃! c : sequenceRing D l E ⟶
      ((reindex D r).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))
        (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))).obj
          (sequenceRing D l E),
      ∀ (n : ℕ) (U : (Spec (.of D.k)).ProEt),
        HEq (c.hom.app (op (n, U)))
          ((inv (inverseImageFiniteCoefficientMap l E (pointPower D r).hom n)).hom.app
            (op U)) := by
  exact PointRestrictionSystem.coefficient_existsUnique D l E (pointPower D r).hom

/-- The coefficient map is chosen from its unique sectionwise specification.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-chain). -/
def coefficient (r : ℕ) := (coefficient_existsUnique D l E r).exists.choose

/-- The levelwise inverse image on actual strict systems: precompose with h^r and
transport the scalar action by c_n inverse. Horizontal restrictions are unchanged.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-chain). -/
def pull (r : ℕ) : coefficientSequenceModules l E (Spec (.of D.k)) ⥤
    coefficientSequenceModules l E (Spec (.of D.k)) :=
  SheafOfModules.pushforward (F := reindex D r) (coefficient D l E r)

/-- Exactness of the actual levelwise inverse image on strict systems.
Source: Stacks 0941 and 015F (blueprint: lem-trf-point-system-transport-chain).
Proof: kernels and cokernels of strict systems are componentwise by
lem-coef-semilinear-derived-sections. Each component is the exact inverse-image
equivalence of lem-weil-proetale-isomorphism-inverse-image. Its transported coefficient
action leaves the underlying kernel and cokernel sheaves unchanged. -/
theorem pull_exact (r : ℕ) : (pull D l E r).Additive ∧
    PreservesFiniteLimits (pull D l E r) ∧ PreservesFiniteColimits (pull D l E r) := by
  let g := (pointPower D r).hom
  let Q := proEtaleIsoPostcompose g
  let Q' := proEtaleIsoPostcompose (inv g)
  let e := proEtaleIsoPostcompose_equivalence g
  let e₀ : (Spec (.of D.k)).ProEt ≌ (Spec (.of D.k)).ProEt :=
    CategoryTheory.Equivalence.mk Q Q' e.2.1.some.symm e.2.2.1.some
  let e₁ := (CategoryTheory.Equivalence.refl (C := ℕ)).prod e₀
  let P := (𝟭 ℕ).prod Q'
  let J := coefficientSequenceTopology (ProEt.topology (Spec (.of D.k)))
  have : P.IsEquivalence := e₁.isEquivalence_inverse
  have : P.IsContinuous J J := by
    apply Functor.isContinuous_iff_coverPreserving.mpr
    exact (by
      constructor
      intro X S hS
      change (S.functorPushforward P).functorPullback
        (Prod.sectR X.1 (Spec (.of D.k)).ProEt) ∈ ProEt.topology _ _
      change S.functorPullback (Prod.sectR X.1 (Spec (.of D.k)).ProEt) ∈
        ProEt.topology _ _ at hS
      apply (ProEt.topology _).superset_covering _
        ((CoverPreserving.of_isContinuous Q' (ProEt.topology _)
          (ProEt.topology _)).cover_preserve hS)
      rintro Y f ⟨Z, a, b, ha, rfl⟩
      exact ⟨(X.1, Z), Prod.mkHom (𝟙 X.1) a, Prod.mkHom (𝟙 X.1) b, ha, rfl⟩)
  have : (reindex D r ⋙ P).IsContinuous J J :=
    Functor.isContinuous_comp _ _ J J J
  have : (P ⋙ reindex D r).IsContinuous J J :=
    Functor.isContinuous_comp _ _ J J J
  have : e₁.functor.IsContinuous J J := reindexContinuous D r
  have : e₁.inverse.IsContinuous J J := by
    dsimp only [e₁, CategoryTheory.Equivalence.prod, e₀, CategoryTheory.Equivalence.mk]
    exact (show P.IsContinuous J J from inferInstance)
  have : (e₁.functor ⋙ e₁.inverse).IsContinuous J J :=
    Functor.isContinuous_comp _ _ J J J
  have : (e₁.inverse ⋙ e₁.functor).IsContinuous J J :=
    Functor.isContinuous_comp _ _ J J J
  let A := AddCommGrpCat.{max u (t + 1)}
  let H := (reindex D r).sheafPushforwardContinuous A J J
  let H' := P.sheafPushforwardContinuous A J J
  let es : Sheaf J A ≌ Sheaf J A := CategoryTheory.Equivalence.mk H H'
    ((Functor.sheafPushforwardContinuousComp P (reindex D r) A J J J ≪≫
      Functor.sheafPushforwardContinuousId' e₁.counitIso A J).symm)
    (Functor.sheafPushforwardContinuousComp (reindex D r) P A J J J ≪≫
      Functor.sheafPushforwardContinuousId' e₁.unitIso.symm A J)
  have : H.IsEquivalence := es.isEquivalence_functor
  let V := SheafOfModules.toSheaf.{max u (t + 1)} (sequenceRing D l E)
  let T := pull D l E r
  have : T.Additive := ⟨fun {_ _} f g ↦ by ext U x; rfl⟩
  let ei : T ⋙ V ≅ V ⋙ H := Iso.refl _
  have : PreservesFiniteLimits (T ⋙ V) := preservesFiniteLimits_of_natIso ei.symm
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_reflects_of_preserves T V
  have : PreservesFiniteColimits (T ⋙ V) := preservesFiniteColimits_of_natIso ei.symm
  have : ReflectsFiniteColimits V := reflectsFiniteColimitsOfReflectsIsomorphisms V
  change T.Additive ∧ PreservesFiniteLimits T ∧ PreservesFiniteColimits T
  exact ⟨‹T.Additive›, ‹PreservesFiniteLimits T›,
    preservesFiniteColimits_of_reflects_of_preserves T V⟩

/-- Additivity from the stated exactness of system inverse image.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-chain). -/
instance pullAdditive (r : ℕ) : (pull D l E r).Additive := (pull_exact D l E r).1

/-- Finite-limit preservation from the stated exactness.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-chain). -/
instance pullLimits (r : ℕ) : PreservesFiniteLimits (pull D l E r) :=
  (pull_exact D l E r).2.1

/-- Finite-colimit preservation from the stated exactness.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-chain). -/
instance pullColimits (r : ℕ) : PreservesFiniteColimits (pull D l E r) :=
  (pull_exact D l E r).2.2

/-- Restrict through the completed coefficient projections and take sections at
all levels, keeping every original transition. Scalars are the canonical common
universe lift of R, as in the recorded coefficient tower operations.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-chain). -/
def sections : coefficientSequenceModules l E (Spec (.of D.k)) ⥤
    (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none)) :=
  coefficientSequenceRestriction l E (Spec (.of D.k)) ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pointRestrictionSections l E D.k none)

/-- Exact sections on whole strict systems.
Source: Stacks 0941, 0946 and 015F (blueprint: lem-trf-point-system-transport-chain).
Proof: coefficientSequenceRestriction changes only scalar actions. Exactness of
point sections is lem-weil-point-proetale-sections-exact. Tower kernels and cokernels
are levelwise, so their composite preserves finite limits, colimits and addition. -/
theorem sections_exact : (sections D l E).Additive ∧
    PreservesFiniteLimits (sections D l E) ∧ PreservesFiniteColimits (sections D l E) := by
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have := (restriction_sections_exact l E D.k none).1
  have := (restriction_sections_exact l E D.k none).2
  let T := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pointRestrictionSections l E D.k none)
  have : PreservesFiniteLimits T := by
    constructor
    intro J _ _
    apply preservesLimitsOfShape_of_evaluation
    intro n
    change PreservesLimitsOfShape J
      ((evaluation ℕᵒᵖ _).obj n ⋙ pointRestrictionSections l E D.k none)
    infer_instance
  have : PreservesFiniteColimits T := by
    constructor
    intro J _ _
    apply preservesColimitsOfShape_of_evaluation
    intro n
    change PreservesColimitsOfShape J
      ((evaluation ℕᵒᵖ _).obj n ⋙ pointRestrictionSections l E D.k none)
    infer_instance
  constructor
  · exact (PointRestrictionSystem.operations_additive D l E (𝟙 _)).1
  · constructor
    · exact comp_preservesFiniteLimits (coefficientSequenceRestriction l E _) T
    · exact comp_preservesFiniteColimits (coefficientSequenceRestriction l E _) T

/-- Additivity of whole-system sections.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-chain). -/
instance sectionsAdditive : (sections D l E).Additive := (sections_exact D l E).1

/-- Finite-limit preservation of whole-system sections.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-chain). -/
instance sectionsLimits : PreservesFiniteLimits (sections D l E) := (sections_exact D l E).2.1

/-- Finite-colimit preservation of whole-system sections.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-chain). -/
instance sectionsColimits : PreservesFiniteColimits (sections D l E) :=
  (sections_exact D l E).2.2

/-- The termwise sections complex functor with the whole tower as its coefficients.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-chain). -/
abbrev complexSections := (sections D l E).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The termwise sections of the levelwise inverse-image systems.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-chain). -/
abbrev transportedComplexSections (r : ℕ) :=
  (pull D l E r ⋙ sections D l E).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The prescribed component of a chain transformation, in the canonical site-reindexing
model. HEq only identifies the unchanged section carriers after scalar restriction;
the right side is the actual presheaf restriction, not an arbitrary fiber map.
Source: blueprint proof (3), steps 1--4
(blueprint: lem-trf-point-system-transport-chain). -/
def HasRestrictionComponents (r : ℕ)
    (u : complexSections D l E ⟶ transportedComplexSections D l E r) : Prop :=
  ∀ (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ)
    (i : ℤ) (n : ℕ),
    HEq (fun x : (((complexSections D l E).obj M).X i).obj (op n) ↦
      (((u.app M).f i).app (op n)) x)
      (fun x : (M.X i).val.obj (op (n, ProEt.mk (𝟙 (Spec (.of D.k))))) ↦
        (M.X i).val.map
          (Prod.mkHom (𝟙 n) (pointRestrictionArrow (pointPower D r).hom)).op x)

/-- The unique natural R-linear chain map of strict towers with the specified
restriction/insertion components.
Source: blueprint proof (3), steps 1--4
(blueprint: lem-trf-point-system-transport-chain).
Proof: lem-weil-point-automorphism-restriction-natural gives the A_n-linear restriction
map at each level. Naturality of module restrictions makes it commute with every
quotient-linear transition. The coefficient square identifies the transported actions,
including restriction through the completed projections. The same naturality for each
differential makes a chain map, and for a chain map f makes a natural transformation.
Strict tower maps are families of components, so these specified values prove uniqueness. -/
theorem chainTransport_existsUnique (_hl : l ≠ D.p) (r : ℕ) (_hr : 1 ≤ r) :
    ∃! u : complexSections D l E ⟶ transportedComplexSections D l E r,
      HasRestrictionComponents D l E r u := by
  exact (PointRestrictionSystem.restriction_system_chain_map D l E _hl
    (pointPower D r).hom).2

/-- The specified chain transformation, determined uniquely on all sections.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-chain). -/
def chainTransport (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) :
    complexSections D l E ⟶ transportedComplexSections D l E r :=
  (chainTransport_existsUnique D l E hl r hr).exists.choose

/-- The ordinary localization of whole R-module towers, at the common scalar universe.
Source: Stacks 05RU and 0941 (blueprint: lem-trf-point-system-transport-chain). -/
instance towerDerived : HasDerivedCategory
    (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none)) :=
  HasDerivedCategory.standard _

/-- Whole-system sections descended to the ordinary unbounded derived categories.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-chain). -/
abbrev derivedSections := (sections D l E).mapDerivedCategory

/-- The second exact functor descended on whole systems, before taking any limit.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-chain). -/
abbrev transportedDerivedSections (r : ℕ) := (pull D l E r ⋙ sections D l E).mapDerivedCategory

end WeilConjectures.PointSystemTransport
