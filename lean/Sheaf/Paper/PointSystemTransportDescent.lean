/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
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
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Strict point transport and descent on whole coefficient systems

Source: blueprint main-20261015, `prop-trf-rational-frobenius-integral-model`,
proof (3), point-factor prerequisite; Stacks Tags 0941, 015F and 04VG
(blueprint: lem-trf-point-system-transport-descent).

The source is the recorded ringed sequence site, without normalization or boundedness.
The target is the ordinary derived category of whole integral-module towers. The index
`n : ℕ` means exponent `n+1`. Site and coefficient universes remain independent.

## Main definitions

* `pull`, `sections`: actual inverse image and exact sections of strict systems.
* `chainTransport`, `derivedTransport`: the uniquely normalized natural maps.
* `finiteTransportComplex`, `finiteTransportDerived`: the finite representative recipe.

## Main statements

* `point_system_transport_descent`: unique descent on entire system derived categories.
* `coefficient_squares`, `tensorTransition_existsUnique`: original coefficient transitions.
* `finite_evaluation`: evaluation agrees with the finite point-transport recipe.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointSystemTransport

variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual rth power of geometric Frobenius at the point.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-descent). -/
def pointPower : ℕ → (Spec (.of D.k) ≅ Spec (.of D.k))
  | 0 => Iso.refl _
  | r + 1 => pointPower r ≪≫ frobeniusPointIso D

/-- Postcompose every site object by h^r, retaining its coefficient index.
Source: blueprint proof (3), inverse-image recipe
(blueprint: lem-trf-point-system-transport-descent). -/
def reindex (r : ℕ) : (ℕ × (Spec (.of D.k)).ProEt) ⥤
    (ℕ × (Spec (.of D.k)).ProEt) :=
  (𝟭 ℕ).prod (proEtaleIsoPostcompose (pointPower D r).hom)

/-- Reindexing preserves the vertical sheaf condition.
Source: Stacks 0941 and 09A5 (blueprint: lem-trf-point-system-transport-descent).
Proof: the sequence topology tests covers in the vertical slice. Postcomposition
by h^r is a covering-preserving site equivalence, by
lem-weil-proetale-isomorphism-inverse-image. Its product with the identity of the
index category therefore preserves the same sheaf condition. -/
@[instance] theorem reindexContinuous (r : ℕ) :
    (reindex D r).IsContinuous
      (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))
      (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k)))) := by
  sorry

/-- The existing sequence coefficient sheaf, with commutativity forgotten.
Source: Stacks 0941 (blueprint: lem-trf-point-system-transport-descent). -/
abbrev sequenceRing :=
  (sheafCompose (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E (Spec (.of D.k)))

/-- Assemble precisely the inverses of the canonical finite coefficient comparisons.
Source: blueprint proof (3), coefficient square
(blueprint: lem-trf-point-system-transport-descent).
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
  sorry

/-- The coefficient map is chosen from its unique sectionwise specification.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-descent). -/
def coefficient (r : ℕ) := (coefficient_existsUnique D l E r).exists.choose

/-- The levelwise inverse image on actual strict systems: precompose with h^r and
transport the scalar action by c_n inverse. Horizontal restrictions are unchanged.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-descent). -/
def pull (r : ℕ) : coefficientSequenceModules l E (Spec (.of D.k)) ⥤
    coefficientSequenceModules l E (Spec (.of D.k)) :=
  SheafOfModules.pushforward (F := reindex D r) (coefficient D l E r)

/-- Exactness of the actual levelwise inverse image on strict systems.
Source: Stacks 0941 and 015F (blueprint: lem-trf-point-system-transport-descent).
Proof: kernels and cokernels of strict systems are componentwise by
lem-coef-semilinear-derived-sections. Each component is the exact inverse-image
equivalence of lem-weil-proetale-isomorphism-inverse-image. Its transported coefficient
action leaves the underlying kernel and cokernel sheaves unchanged. -/
theorem pull_exact (r : ℕ) : (pull D l E r).Additive ∧
    PreservesFiniteLimits (pull D l E r) ∧ PreservesFiniteColimits (pull D l E r) := by
  sorry

/-- Additivity from the stated exactness of system inverse image.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-descent). -/
instance pullAdditive (r : ℕ) : (pull D l E r).Additive := (pull_exact D l E r).1

/-- Finite-limit preservation from the stated exactness.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-descent). -/
instance pullLimits (r : ℕ) : PreservesFiniteLimits (pull D l E r) :=
  (pull_exact D l E r).2.1

/-- Finite-colimit preservation from the stated exactness.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-descent). -/
instance pullColimits (r : ℕ) : PreservesFiniteColimits (pull D l E r) :=
  (pull_exact D l E r).2.2

/-- Restrict through the completed coefficient projections and take sections at
all levels, keeping every original transition. Scalars are the canonical common
universe lift of R, as in the recorded coefficient tower operations.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-descent). -/
def sections : coefficientSequenceModules l E (Spec (.of D.k)) ⥤
    (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none)) :=
  coefficientSequenceRestriction l E (Spec (.of D.k)) ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pointRestrictionSections l E D.k none)

/-- Exact sections on whole strict systems.
Source: Stacks 0941, 0946 and 015F (blueprint: lem-trf-point-system-transport-descent).
Proof: coefficientSequenceRestriction changes only scalar actions. Exactness of
point sections is lem-weil-point-proetale-sections-exact. Tower kernels and cokernels
are levelwise, so their composite preserves finite limits, colimits and addition. -/
theorem sections_exact : (sections D l E).Additive ∧
    PreservesFiniteLimits (sections D l E) ∧ PreservesFiniteColimits (sections D l E) := by
  sorry

/-- Additivity of whole-system sections.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-descent). -/
instance sectionsAdditive : (sections D l E).Additive := (sections_exact D l E).1

/-- Finite-limit preservation of whole-system sections.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-descent). -/
instance sectionsLimits : PreservesFiniteLimits (sections D l E) := (sections_exact D l E).2.1

/-- Finite-colimit preservation of whole-system sections.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-descent). -/
instance sectionsColimits : PreservesFiniteColimits (sections D l E) :=
  (sections_exact D l E).2.2

/-- The termwise sections complex functor with the whole tower as its coefficients.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-descent). -/
abbrev complexSections := (sections D l E).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The termwise sections of the levelwise inverse-image systems.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-descent). -/
abbrev transportedComplexSections (r : ℕ) :=
  (pull D l E r ⋙ sections D l E).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The prescribed component of a chain transformation, in the canonical site-reindexing
model. HEq only identifies the unchanged section carriers after scalar restriction;
the right side is the actual presheaf restriction, not an arbitrary fiber map.
Source: blueprint proof (3), steps 1--4
(blueprint: lem-trf-point-system-transport-descent). -/
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
(blueprint: lem-trf-point-system-transport-descent).
Proof: lem-weil-point-automorphism-restriction-natural gives the A_n-linear restriction
map at each level. Naturality of module restrictions makes it commute with every
quotient-linear transition. The coefficient square identifies the transported actions,
including restriction through the completed projections. The same naturality for each
differential makes a chain map, and for a chain map f makes a natural transformation.
Strict tower maps are families of components, so these specified values prove uniqueness. -/
theorem chainTransport_existsUnique (_hl : l ≠ D.p) (r : ℕ) (_hr : 1 ≤ r) :
    ∃! u : complexSections D l E ⟶ transportedComplexSections D l E r,
      HasRestrictionComponents D l E r u := by
  sorry

/-- The specified chain transformation, determined uniquely on all sections.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-descent). -/
def chainTransport (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) :
    complexSections D l E ⟶ transportedComplexSections D l E r :=
  (chainTransport_existsUnique D l E hl r hr).exists.choose

/-- The ordinary localization of whole R-module towers, at the common scalar universe.
Source: Stacks 05RU and 0941 (blueprint: lem-trf-point-system-transport-descent). -/
instance towerDerived : HasDerivedCategory
    (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none)) :=
  HasDerivedCategory.standard _

/-- Whole-system sections descended to the ordinary unbounded derived categories.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-descent). -/
abbrev derivedSections := (sections D l E).mapDerivedCategory

/-- The second exact functor descended on whole systems, before taking any limit.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-descent). -/
abbrev transportedDerivedSections (r : ℕ) := (pull D l E r ⋙ sections D l E).mapDerivedCategory

/-- Existence and uniqueness of the descent of the specified transformation, together
with quasi-isomorphism preservation and naturality for every derived system morphism.
The codomain is D(Tow(Mod R)), not a tower of separate derived categories.
Source: blueprint proof (3), steps 5--6; Stacks 015F and 04VG
(blueprint: lem-trf-point-system-transport-descent).
Proof: the two exact functors preserve homology and hence quasi-isomorphisms by
lem-weil-pbc-exact-functor-derived-factorization. Apply
lem-weil-pbc-localization-universal-property to the source category of entire system
complexes, with quasi-isomorphisms inverted, and target D(Tow(Mod R)). Its full
faithfulness on natural transformations gives the unique descent with the displayed
representative equation. Naturality holds for chain maps and for inverses of
quasi-isomorphisms, thus for every morphism in the localized system category.
No step assumes that derived evaluation is faithful. -/
theorem point_system_transport_descent (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) :
    (∀ (M N : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ)
      (f : M ⟶ N), QuasiIso f →
        QuasiIso ((complexSections D l E).map f) ∧
        QuasiIso ((transportedComplexSections D l E r).map f)) ∧
    ∃! I : derivedSections D l E ⟶ transportedDerivedSections D l E r,
      (∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
        I.app (DerivedCategory.Q.obj M) ≫
            (pull D l E r ⋙ sections D l E).mapDerivedCategoryFactors.hom.app M =
          (sections D l E).mapDerivedCategoryFactors.hom.app M ≫
            DerivedCategory.Q.map ((chainTransport D l E hl r hr).app M)) ∧
      (∀ {C C' : coefficientSequenceDerived l E (Spec (.of D.k))} (f : C ⟶ C'),
        (derivedSections D l E).map f ≫ I.app C' =
          I.app C ≫ (transportedDerivedSections D l E r).map f) := by
  sorry

/-- The descended map, specified by the localization representative equation.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-descent). -/
def derivedTransport (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) :
    derivedSections D l E ⟶ transportedDerivedSections D l E r :=
  (point_system_transport_descent D l E hl r hr).2.exists.choose

/-- The exact coefficient squares for quotient and completed coefficients.
Source: blueprint proof (3), step 3
(blueprint: lem-trf-point-system-transport-descent).
Proof: both quotient composites extend the same map on constant presheaves, and
sheafification preserves the equality. The completed map is the limit lift with
these finite components, so its projection equation is the defining limit equation. -/
theorem coefficient_squares (r n : ℕ) :
    inverseImageFiniteCoefficientMap l E (pointPower D r).hom (n + 1) ≫
        integralCoefficientSheafTransition l E (Spec (.of D.k)) n =
      (isoSectionwiseInverseImage (pointPower D r).hom RingCat.{max u (t + 1)}).map
          (integralCoefficientSheafTransition l E (Spec (.of D.k)) n) ≫
        inverseImageFiniteCoefficientMap l E (pointPower D r).hom n ∧
    inverseImageCompletedCoefficientMap l E (pointPower D r).hom ≫
        limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n) =
      (isoSectionwiseInverseImage (pointPower D r).hom RingCat.{max u (t + 1)}).map
          (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n)) ≫
        inverseImageFiniteCoefficientMap l E (pointPower D r).hom n := by
  sorry

/-- The finite tensor-unit comparison is invertible on every unbounded complex.
Source: blueprint proof (3), step 2
(blueprint: lem-trf-point-system-transport-descent).
Proof: on local tensor generators define the inverse by x tensor a mapping to
c_n inverse(a) times x. Balancedness is the identity
b c_n inverse(a)x = c_n inverse(c_n(b)a)x. It commutes with restrictions and
sheafifies. The two composites are identity on x and on x tensor a, respectively.
Apply naturality to each differential; no flatness assumption is used. -/
@[instance] theorem finiteComparison_isIso (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    IsIso (inverseImageFiniteComparisonComplex l E (pointPower D r).hom n K) := by
  sorry

/-- The inverse comparison sends the local tensor generator x tensor a to c_n inverse(a)x.
Here a times j(x) is exactly the sheafified generator x tensor a.
Source: blueprint proof (3), step 2
(blueprint: lem-trf-point-system-transport-descent).
Proof: expand the inverse on generators from finiteComparison_isIso. The tensor
balancing relation carries c_n inverse(a)x tensor 1 to x tensor a, so this is the
inverse of j on every generator and thus on the sheafification. -/
theorem finiteComparison_inverse (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
    (i : ℤ) (U : (Spec (.of D.k)).ProEt)
    (a : (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.obj (op U))
    (x : (K.X i).val.obj (op ((proEtaleIsoPostcompose (pointPower D r).hom).obj U))) :
    ((inv (inverseImageFiniteComparisonComplex l E (pointPower D r).hom n K)).f i).val.app
        (op U)
        (a • ((inverseImageFiniteComparisonComplex l E (pointPower D r).hom n K).f i).val.app
          (op U) x) =
      @SMul.smul _ ((K.X i).val.obj
        (op ((proEtaleIsoPostcompose (pointPower D r).hom).obj U))) inferInstance
        ((inv (inverseImageFiniteCoefficientMap l E (pointPower D r).hom n)).hom.app
          (op U) a) x := by
  sorry

/-- The actual quotient of constant integral scalars in the common universe.
Source: blueprint coefficient conventions (blueprint: lem-trf-point-system-transport-descent). -/
def quotient (n : ℕ) : pointRestrictionScalars.{t, u} l E none →+*
    pointRestrictionScalars.{t, u} l E (some n) :=
  RingHom.ulift (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))

/-- Additivity of the recorded finite inverse image, exposed at its finite-module interface.
Source: Stacks 03D6 (blueprint: lem-trf-point-system-transport-descent). -/
instance finitePullAdditive {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    (inverseImageFiniteModules.{t, u} l E g n).Additive :=
  (isoSectionwiseModuleInverseImage_exact g (inverseImageFiniteCoefficientMap l E g n)).1

/-- Left exactness of the recorded finite inverse image.
Source: Stacks 03D6 (blueprint: lem-trf-point-system-transport-descent). -/
instance finitePullLimits {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    PreservesFiniteLimits (inverseImageFiniteModules.{t, u} l E g n) :=
  (isoSectionwiseModuleInverseImage_exact g (inverseImageFiniteCoefficientMap l E g n)).2.1

/-- Right exactness of the recorded finite inverse image.
Source: Stacks 03D6 (blueprint: lem-trf-point-system-transport-descent). -/
instance finitePullColimits {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    PreservesFiniteColimits (inverseImageFiniteModules.{t, u} l E g n) :=
  (isoSectionwiseModuleInverseImage_exact g (inverseImageFiniteCoefficientMap l E g n)).2.2

/-- The recorded tensor pullback, with both finite-module endpoints explicit.
Source: def-weil-inverse-image-pullback-comparison (a)
(blueprint: lem-trf-point-system-transport-descent). -/
def tensorPull (r n : ℕ) : integralOperationsFiniteModules l E (Spec (.of D.k)) n ⥤
    integralOperationsFiniteModules l E (Spec (.of D.k)) n :=
  integralOperationsLevelPullback.{t, u} l E (pointPower D r).hom n

/-- Additivity of that recorded tensor pullback.
Source: Stacks 03D2 (blueprint: lem-trf-point-system-transport-descent). -/
instance tensorPullAdditive (r n : ℕ) : (tensorPull D l E r n).Additive :=
  integralOperationsLevelPullback_additive l E (pointPower D r).hom n

/-- Left exactness of that recorded tensor pullback.
Source: Stacks 03D6 (blueprint: lem-trf-point-system-transport-descent). -/
instance tensorPullLimits (r n : ℕ) : PreservesFiniteLimits (tensorPull D l E r n) :=
  (inverseImageFinitePullback_exact l E (pointPower D r).hom n).1

/-- Right exactness of that recorded tensor pullback.
Source: Stacks 03D6 (blueprint: lem-trf-point-system-transport-descent). -/
instance tensorPullColimits (r n : ℕ) : PreservesFiniteColimits (tensorPull D l E r n) :=
  (inverseImageFinitePullback_exact l E (pointPower D r).hom n).2

/-- The unchanged finite coefficient sections, followed by the actual R→A_n restriction.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-descent). -/
def finiteRSections (n : ℕ) :
    integralOperationsFiniteModules l E (Spec (.of D.k)) n ⥤
      ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none) :=
  pointRestrictionSections l E D.k (some n) ⋙
    ModuleCat.restrictScalars (quotient.{t, u} l E n)


/-- Finite R-sections are additive and exact with independent site/coefficient sizes.
Source: Stacks 0946, 015F (blueprint: lem-trf-point-system-transport-descent).
Proof: finite point sections are exact by lem-weil-point-proetale-sections-exact;
restriction of scalars keeps the kernel and cokernel of the underlying abelian groups.
The scalar map is the quotient homomorphism, so it does not impose flatness. -/
theorem finiteRSections_exact (n : ℕ) : (finiteRSections D l E n).Additive ∧
    PreservesFiniteLimits (finiteRSections D l E n) ∧
    PreservesFiniteColimits (finiteRSections D l E n) := by
  sorry

/-- Additivity from finite-section exactness.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-descent). -/
instance finiteRSectionsAdditive (n : ℕ) : (finiteRSections D l E n).Additive :=
  (finiteRSections_exact D l E n).1

/-- Left exactness from finite-section exactness.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-descent). -/
instance finiteRSectionsLimits (n : ℕ) : PreservesFiniteLimits (finiteRSections D l E n) :=
  (finiteRSections_exact D l E n).2.1

/-- Right exactness from finite-section exactness.
Source: Stacks 015F (blueprint: lem-trf-point-system-transport-descent). -/
instance finiteRSectionsColimits (n : ℕ) : PreservesFiniteColimits (finiteRSections D l E n) :=
  (finiteRSections_exact D l E n).2.2

/-- Additivity at the finite coefficient point-section interface.
Source: Stacks 03CW (blueprint: lem-trf-point-system-transport-descent). -/
instance finiteSectionsAdditive (n : ℕ) :
    (pointRestrictionSections l E D.k (some n)).Additive :=
  pointRestrictionSectionsAdditive l E D.k (some n)

/-- The A_n-linear finite sigma, with precisely the restriction/insertion values.
Source: blueprint proof (3), step 1
(blueprint: lem-trf-point-system-transport-descent).
Proof: use the restriction construction of lem-weil-point-automorphism-restriction-natural
for h^r at some n; its coefficient normalization does not use l ≠ D.p.
The constant-section normalization makes restriction A_n-linear for the transported target
action. Apply module naturality to the differentials. Component values determine
the chain map uniquely. -/
theorem finiteSigma_existsUnique (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ∃! σ : ((pointRestrictionSections l E D.k (some n)).mapHomologicalComplex
        (.up ℤ)).obj K ⟶
      ((pointRestrictionInverseImage.{t, u} l E (pointPower D r).hom (some n) ⋙
        pointRestrictionSections l E D.k (some n)).mapHomologicalComplex (.up ℤ)).obj K,
      ∀ (i : ℤ) (x : (K.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        σ.f i x = pointRestrictionRaw l E (pointPower D r).hom (some n) (K.X i) x := by
  sorry

/-- The finite sigma as an A_n-linear chain map, before restricting to R.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-descent). -/
def finiteSigma (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :=
  (finiteSigma_existsUnique D l E r n K).exists.choose


/-- The identical finite map with its scalars restricted by R→A_n.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-descent). -/
def finiteSigmaR (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ((finiteRSections D l E n).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n ⋙
        finiteRSections D l E n).mapHomologicalComplex (.up ℤ)).obj K :=
  ((ModuleCat.restrictScalars.{max u (t + 1)} (quotient.{t, u} l E n)).mapHomologicalComplex
      (.up ℤ)).map (finiteSigma D l E r n K)

/-- The dependency's comparison with its complex endpoints stated explicitly.
Source: def-weil-inverse-image-pullback-comparison (a)
(blueprint: lem-trf-point-system-transport-descent). -/
def comparisonComplex (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ((inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n).mapHomologicalComplex
      (.up ℤ)).obj K ⟶ ((tensorPull D l E r n).mapHomologicalComplex (.up ℤ)).obj K :=
  inverseImageFiniteComparisonComplex.{t, u} l E (pointPower D r).hom n K

/-- Map a comparison of finite complexes through sections, using the standard
composition isomorphisms rather than unfolding the tensor model.
Source: blueprint proof (3), steps 2 and 7
(blueprint: lem-trf-point-system-transport-descent). -/
def mapFiniteComplexComparison (n : ℕ)
    (F G : integralOperationsFiniteModules l E (Spec (.of D.k)) n ⥤
      integralOperationsFiniteModules l E (Spec (.of D.k)) n)
    [F.Additive] [G.Additive]
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
    (j : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶
      (G.mapHomologicalComplex (.up ℤ)).obj K) :
    ((F ⋙ finiteRSections D l E n).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((G ⋙ finiteRSections D l E n).mapHomologicalComplex (.up ℤ)).obj K :=
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl (F ⋙ finiteRSections D l E n)) (.up ℤ)).inv.app K ≫
    ((finiteRSections D l E n).mapHomologicalComplex (.up ℤ)).map j ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (G ⋙ finiteRSections D l E n)) (.up ℤ)).hom.app K

/-- The finite point-transport recipe on any representative: restriction, inverse-image
insertion and sheafification, followed by the sheafified tensor insertion j.
Source: def-weil-frobenius-point-transport with h^r replacing h, blueprint proof (3), step 7
(blueprint: lem-trf-point-system-transport-descent). -/
def finiteTransportComplex (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ((finiteRSections D l E n).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((tensorPull D l E r n ⋙
        finiteRSections D l E n).mapHomologicalComplex (.up ℤ)).obj K :=
  finiteSigmaR D l E r n K ≫
    mapFiniteComplexComparison D l E n
      (inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n)
      (tensorPull D l E r n) K (comparisonComplex D l E r n K)


/-- The tensor-model nth term, still a sheaf of completed-coefficient modules.
Source: blueprint proof (3), step 3
(blueprint: lem-trf-point-system-transport-descent). -/
def tensorLevel (r n : ℕ) : coefficientSequenceModules l E (Spec (.of D.k)) ⥤
    scalarReductionSource l E (Spec (.of D.k)) :=
  coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙
    tensorPull D l E r n ⋙
      scalarReductionRestriction l E (Spec (.of D.k)) n


/-- The actual sheafified tensor insertion x↦x tensor 1 at any site object.
Source: def-weil-inverse-image-pullback-comparison (a), blueprint proof (3)
(blueprint: lem-trf-point-system-transport-descent). -/
def insertion (r n : ℕ) (M : coefficientSequenceModules l E (Spec (.of D.k)))
    (U : (Spec (.of D.k)).ProEt)
    (x : ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M).val.obj
      (op ((proEtaleIsoPostcompose (pointPower D r).hom).obj U))) :=
  (((tensorPull D l E r n).obj
      ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)).val.map
    (proEtaleIsoCommaArrow (pointPower D r).hom U).op)
      (integralOperationsPullbackGenerator l E (pointPower D r).hom n
        ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)
        ((proEtaleIsoPostcompose (pointPower D r).hom).obj U) x)


/-- The tensor transition is fixed on all local generators, including their scalar a.
For a=1 the formula is exactly v_n(x) tensor rho_n(1)=v_n(x) tensor 1.
Source: blueprint proof (3), step 3
(blueprint: lem-trf-point-system-transport-descent).
Proof: inverse-image the actual horizontal restriction of M, extend scalars by
rho_n, then sheafify. coefficient_squares makes the formula balanced and linear
after completed scalar restriction. On x tensor a it has precisely the displayed
value. It commutes with restrictions and module morphisms, and hence gives a natural
transformation. The local tensor generators generate the sheafified tensor product;
completed projections are locally surjective, so completed linearity and the formula
on all a prove uniqueness. This uses the original transitions of M, not derived
reduction isomorphisms or cartesianness. -/
theorem tensorTransition_existsUnique (r n : ℕ) :
    ∃! τ : tensorLevel D l E r (n + 1) ⟶ tensorLevel D l E r n,
      ∀ (M : coefficientSequenceModules l E (Spec (.of D.k)))
        (U : (Spec (.of D.k)).ProEt)
        (a : (integralCoefficientSheaf l E (Spec (.of D.k)) (n + 1)).obj.obj (op U))
        (x : ((coefficientSequenceEvaluation l E (Spec (.of D.k)) (n + 1)).obj M).val.obj
          (op ((proEtaleIsoPostcompose (pointPower D r).hom).obj U))),
        (τ.app M).val.app (op U)
            (@SMul.smul _
              (((tensorPull D l E r (n + 1)).obj
                ((coefficientSequenceEvaluation l E (Spec (.of D.k)) (n + 1)).obj M)).val.obj
                  (op U)) inferInstance a (insertion D l E r (n + 1) M U x)) =
          @SMul.smul _
            (((tensorPull D l E r n).obj
              ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)).val.obj (op U))
            inferInstance
            ((integralCoefficientSheafTransition l E (Spec (.of D.k)) n).hom.app (op U) a)
            (insertion D l E r n M U
              ((M.val.presheaf.map
                (Prod.mkHom (homOfLE (Nat.le_succ n))
                  (𝟙 ((proEtaleIsoPostcompose (pointPower D r).hom).obj U))).op) x)) := by
  sorry


/-- The ordinary nth evaluation on whole integral-module towers.
Source: Stacks 0941 (blueprint: lem-trf-point-system-transport-descent). -/
abbrev towerEvaluation (n : ℕ) :=
  (evaluation ℕᵒᵖ (ModuleCat.{max u (t + 1)}
    (pointRestrictionScalars.{t, u} l E none))).obj (op n)

/-- Canonical evaluation comparisons are identity on all underlying sections.
Source: blueprint proof (3), steps 3--4 and 7
(blueprint: lem-trf-point-system-transport-descent).
Proof: restricting through the completion and then through R has the quotient
R→A_n action, by the completed projection equation. The sequence reindexing is
(n,U)↦(n,h^r U), with action c_n inverse, exactly the finite inverse image. Thus
identity on the section carriers is linear, natural and inverse to itself on both
sides. Equality on every section proves uniqueness of the pair of comparisons. -/
theorem evaluation_existsUnique (r n : ℕ) :
    ∃! e :
      (sections D l E ⋙ towerEvaluation.{t, u} l E n ≅
        coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙ finiteRSections D l E n) ×
      ((pull D l E r ⋙ sections D l E) ⋙ towerEvaluation.{t, u} l E n ≅
        coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙
          (inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n ⋙ finiteRSections D l E n)),
      ∀ M : coefficientSequenceModules l E (Spec (.of D.k)),
        HEq (fun x : ((sections D l E).obj M).obj (op n) ↦ e.1.hom.app M x)
          (fun x : M.val.obj (op (n, ProEt.mk (𝟙 (Spec (.of D.k))))) ↦ x) ∧
        HEq (fun x : ((sections D l E).obj ((pull D l E r).obj M)).obj (op n) ↦
            e.2.hom.app M x)
          (fun x : M.val.obj (op (n,
            (proEtaleIsoPostcompose (pointPower D r).hom).obj
              (ProEt.mk (𝟙 (Spec (.of D.k)))))) ↦ x) := by
  sorry


/-- Evaluation comparisons chosen by their unique identity-on-sections normalization.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-descent). -/
def evaluationComparisons (r n : ℕ) := (evaluation_existsUnique D l E r n).exists.choose

/-- Evaluate the source derived whole-tower functor, using the exact ordinary comparison.
Source: Stacks 015F, blueprint proof (3)
(blueprint: lem-trf-point-system-transport-descent). -/
def sourceEvaluation (r n : ℕ) :
    derivedSections D l E ⋙ (towerEvaluation.{t, u} l E n).mapDerivedCategory ≅
      coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n ⋙
        (finiteRSections D l E n).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (sections D l E) (towerEvaluation.{t, u} l E n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (evaluationComparisons D l E r n).1 ≪≫
      Functor.mapDerivedCategoryCompIso
        (coefficientSequenceEvaluation l E (Spec (.of D.k)) n) (finiteRSections D l E n)


/-- Evaluate the target derived whole-tower functor, using its normalized comparison.
Source: Stacks 015F, blueprint proof (3)
(blueprint: lem-trf-point-system-transport-descent). -/
def targetEvaluation (r n : ℕ) :
    transportedDerivedSections D l E r ⋙
        (towerEvaluation.{t, u} l E n).mapDerivedCategory ≅
      coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n ⋙
        (inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n ⋙
          finiteRSections D l E n).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (pull D l E r ⋙ sections D l E)
    (towerEvaluation.{t, u} l E n)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (evaluationComparisons D l E r n).2 ≪≫
        Functor.mapDerivedCategoryCompIso
          (coefficientSequenceEvaluation l E (Spec (.of D.k)) n)
          (inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n ⋙ finiteRSections D l E n)


/-- The finite j comparison on an arbitrary derived coefficient object, transported
through the localization's chosen representative. It is the same sheafified tensor-unit
comparison, evaluated after R-scalar restriction.
Source: blueprint proof (3), steps 2 and 7
(blueprint: lem-trf-point-system-transport-descent). -/
def finiteDerivedComparison (r n : ℕ)
    (C : normalizedDVRDerived l E (Spec (.of D.k)) n) :
    (inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n ⋙
      finiteRSections D l E n).mapDerivedCategory.obj C ⟶
        (tensorPull D l E r n ⋙
          finiteRSections D l E n).mapDerivedCategory.obj C :=
  (inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n ⋙
    finiteRSections D l E n).mapDerivedCategory.map (DerivedCategory.Q.objObjPreimageIso C).inv ≫
    (inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n ⋙
      finiteRSections D l E n).mapDerivedCategoryFactors.hom.app
        (DerivedCategory.Q.objPreimage C) ≫
    DerivedCategory.Q.map
      (mapFiniteComplexComparison D l E n
        (inverseImageFiniteModules.{t, u} l E (pointPower D r).hom n)
        (tensorPull D l E r n) (DerivedCategory.Q.objPreimage C)
        (comparisonComplex D l E r n (DerivedCategory.Q.objPreimage C))) ≫
    (tensorPull D l E r n ⋙
      finiteRSections D l E n).mapDerivedCategoryFactors.inv.app
        (DerivedCategory.Q.objPreimage C) ≫
    (tensorPull D l E r n ⋙
      finiteRSections D l E n).mapDerivedCategory.map (DerivedCategory.Q.objObjPreimageIso C).hom


/-- The finite point-transport recipe with h replaced by h^r, using exactly sigma
followed by Gamma(j), and the canonical localization representative comparisons.
At r=1 this is the coefficient-sized presentation of def-weil-frobenius-point-transport;
no separate choice of a fiber identification is made.
Source: blueprint proof (3), step 7
(blueprint: lem-trf-point-system-transport-descent). -/
def finiteTransportDerived (r n : ℕ)
    (C : normalizedDVRDerived l E (Spec (.of D.k)) n) :
    (finiteRSections D l E n).mapDerivedCategory.obj C ⟶
      (tensorPull D l E r n ⋙
        finiteRSections D l E n).mapDerivedCategory.obj C :=
  (finiteRSections D l E n).mapDerivedCategory.map (DerivedCategory.Q.objObjPreimageIso C).inv ≫
    (finiteRSections D l E n).mapDerivedCategoryFactors.hom.app
      (DerivedCategory.Q.objPreimage C) ≫
    DerivedCategory.Q.map (finiteTransportComplex D l E r n (DerivedCategory.Q.objPreimage C)) ≫
    (tensorPull D l E r n ⋙
      finiteRSections D l E n).mapDerivedCategoryFactors.inv.app
        (DerivedCategory.Q.objPreimage C) ≫
    (tensorPull D l E r n ⋙
      finiteRSections D l E n).mapDerivedCategory.map (DerivedCategory.Q.objObjPreimageIso C).hom


/-- Evaluation of the actual descended system morphism, through j, is exactly the
finite point-transport recipe. In particular this is iota^(r) whenever the nth
coefficient object is bounded constructible. The equation is available on arbitrary
ambient objects because the representative recipe itself has no boundedness condition.
Source: blueprint proof (3), step 7
(blueprint: lem-trf-point-system-transport-descent).
Proof: evaluate the representative equation of point_system_transport_descent.
The two evaluation comparisons are identity on the underlying sections. Thus the
chain map becomes precisely finiteSigmaR, by its unique restriction normalization.
Postcomposing with j gives finiteTransportComplex. The exact evaluation functors
and their mapDerivedCategory comparisons descend this equation. Transport to the
chosen representative of the evaluated object gives the displayed equality, which
is the recipe defining def-weil-frobenius-point-transport with h^r in place of h.
This proves equality of actual evaluated derived morphisms; no faithfulness of
derived evaluations, cartesianness or finite Tor-amplitude is used. -/
theorem finite_evaluation (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) (n : ℕ)
    (C : coefficientSequenceDerived l E (Spec (.of D.k))) :
    (sourceEvaluation D l E r n).inv.app C ≫
        (towerEvaluation.{t, u} l E n).mapDerivedCategory.map
          ((derivedTransport D l E hl r hr).app C) ≫
        (targetEvaluation D l E r n).hom.app C ≫
        finiteDerivedComparison D l E r n
          ((coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj C) =
      finiteTransportDerived D l E r n
        ((coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj C) := by
  sorry


end WeilConjectures.PointSystemTransport
