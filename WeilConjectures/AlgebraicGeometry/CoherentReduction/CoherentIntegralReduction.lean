/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
public import WeilConjectures.AlgebraicGeometry.Semilinear.ConstantCoefficientSystem
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.AlgebraicGeometry.FiniteProperQuotient.FiniteProperExceptionalQuotient
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Instances.Discrete

/-! # The actual coherent integral reduction system

Source: Zheng, Construction 4.1, and the first step of
`lem-sfb-finite-proper-exceptional-coherent-tower`.
(blueprint: def-sfb-coherent-integral-reduction)

Coefficients are continuous condensed rings pulled back from the point. The
reduction is one derived scalar extension on the sequence site. The field of
coefficients may have universe u+1 while the schemes have universe u.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall


universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CoherentReduction

/-- The small pro-etale site in the coefficient universe, with its original morphisms.
Source: Bhatt--Scholze, section 4.1, small pro-etale site size convention
(blueprint: def-sfb-coherent-integral-reduction). -/
local instance proEtSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  @essentiallySmall_of_small_of_locallySmall.{u + 1, u, u + 1} X.ProEt _ inferInstance
    (@locallySmall_of_univLE.{u + 1, u, u + 1} X.ProEt _
      (@univLE_of_max.{u, u + 1} UnivLE.self))

/-- The sequence site has the same coefficient-size bound.
Source: Zheng, Construction 4.1, coefficient system site
(blueprint: def-sfb-coherent-integral-reduction). -/
local instance sequenceSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × X.ProEt) :=
  @essentiallySmall_of_small_of_locallySmall.{u + 1, u, u + 1} (ℕ × X.ProEt) _ inferInstance
    (@locallySmall_of_univLE.{u + 1, u, u + 1} (ℕ × X.ProEt) _
      (@univLE_of_max.{u, u + 1} UnivLE.self))

/-- Continuous functions on profinite tests, with pointwise commutative ring operations.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: def-sfb-coherent-integral-reduction). -/
def continuousPresheaf (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] : Profinite.{u}ᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj S := CommRingCat.of C(S.unop, T)
  map f := CommRingCat.ofHom
    (ContinuousMap.compRightAlgHom ℤ T f.unop.hom.hom).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The continuous condensed coefficient ring, with its actual section construction.
Sheafification is included so the construction does not require a sheaf proof as data.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: def-sfb-coherent-integral-reduction). -/
def continuousPoint (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] : Sheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} :=
  (presheafToSheaf _ CommRingCat.{u + 1}).obj (continuousPresheaf T)

/-- Continuous postcomposition defines the coefficient homomorphisms.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: def-sfb-coherent-integral-reduction). -/
def continuousPointMap {T S : Type (u + 1)} [CommRing T] [CommRing S]
    [TopologicalSpace T] [TopologicalSpace S] [IsTopologicalRing T] [IsTopologicalRing S]
    (f : T →+* S) (hf : Continuous f) : continuousPoint T ⟶ continuousPoint S :=
  (presheafToSheaf _ CommRingCat.{u + 1}).map
    { app := fun U ↦ CommRingCat.ofHom (f.compLeftContinuous U.unop hf)
      naturality := fun _ _ _ ↦ rfl }

/-- The sheafified map sending a scalar to its constant continuous function.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: def-sfb-coherent-integral-reduction). -/
def pointConstants (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] :
    (constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).obj
      (CommRingCat.of T) ⟶ continuousPoint T :=
  (presheafToSheaf _ CommRingCat.{u + 1}).map
    { app := fun U ↦ CommRingCat.ofHom (ContinuousMap.C (α := U.unop))
      naturality := fun _ _ _ ↦ rfl }

/-- Forget commutativity and then multiplication, retaining the canonical internal ring.
Source: the ring-object construction, Stacks 00YV
(blueprint: def-sfb-coherent-integral-reduction). -/
abbrev abelianPoint (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (continuousPoint T))

/-- The continuous coefficients are commutative internal ring objects.
Source: pointwise multiplication, Stacks 00YV
(blueprint: def-sfb-coherent-integral-reduction). -/
instance abelianPoint_comm (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] : IsCommMonObj (abelianPoint T) :=
  Sheaf.isCommMonObj_sheafCompose_obj
    (coherentTopology Profinite.{u})
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (continuousPoint T)) (fun U a b ↦ @mul_comm ((continuousPoint T).obj.obj U) inferInstance a b)

/-- The actual internal coefficient ring p_T^* underline(A).
Source: the blueprint's pulled-back-coefficient convention
(blueprint: def-sfb-coherent-integral-reduction). -/
abbrev internalRing (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :=
  condensedRingObj (abelianPoint T) X

/-- The actual multiplication on the pulled-back continuous ring.
Source: pointwise multiplication, Stacks 00YV
(blueprint: def-sfb-coherent-integral-reduction). -/
instance internalRingMonObj (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] : MonObj (internalRing X T) :=
  inferInstanceAs (MonObj (condensedRingObj (abelianPoint T) X))

/-- Commutativity is transported by the original pullback, rather than chosen afresh.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
instance internalRingComm (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] : IsCommMonObj (internalRing X T) :=
  inferInstanceAs (IsCommMonObj (condensedRingObj (abelianPoint T) X))

/-- The section-ring presentation of the same internal coefficients.
Source: Stacks 00YV, the recorded section-action equivalence
(blueprint: def-sfb-coherent-integral-reduction). -/
abbrev sectionRing (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (internalRing X T)

/-- A morphism of internal rings, reconstructed on their original sections.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
def internalSectionMap (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R ⟶
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) S :=
  ⟨Functor.whiskerRight
    ((Monoidal.commMonFunctorCategoryEquivalence X.ProEtᵒᵖ Ab.{u + 1}).functor.map
      ((sheafToPresheaf _ Ab.{u + 1}).mapCommMon.map (CommMon.homMk (Mon.ofHom f))))
    InternalAbelianSheafModule.commMonToRing.{u + 1}⟩

/-- Pull back a continuous scalar homomorphism, then reconstruct the section homomorphism.
Source: the blueprint's coefficient morphisms
(blueprint: def-sfb-coherent-integral-reduction). -/
def sectionMap (X : Scheme.{u}) {T S : Type (u + 1)} [CommRing T] [CommRing S]
    [TopologicalSpace T] [TopologicalSpace S] [IsTopologicalRing T] [IsTopologicalRing S]
    (f : T →+* S) (hf : Continuous f) : sectionRing X T ⟶ sectionRing X S :=
  internalSectionMap X ((upperStarFromPoint X).map
    ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (continuousPointMap f hf))))

/-- The underlying constant-section map on the scheme, using the canonical
constant-sheaf comparison for inverse image from the coefficient point.
Source: the blueprint's pulled-back coefficients
(blueprint: def-sfb-coherent-integral-reduction). -/
def schemeConstants (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj (AddCommGrpCat.of T) ⟶
      internalRing X T := by
  letI : HasSheafify (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  letI : (coherentTopology Profinite.{u}).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  exact (constantSchemeIso X).hom.app (AddCommGrpCat.of T) ≫
    (upperStarFromPoint X).map
      (((constantCommuteCompose (coherentTopology Profinite.{u})
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).app (CommRingCat.of T)).inv ≫
        (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (pointConstants T)))

/-- Forgetting a ring sheaf preserves local isomorphisms on the pro-etale site.
Source: Stacks 00WH (blueprint: def-sfb-coherent-integral-reduction). -/
instance coefficientForgetPreserves (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
  GrothendieckTopology.instPreservesSheafification _ _

/-- Constant sections determine the map to the reconstructed continuous coefficient ring.
Source: the constant-ring/section-action comparison, Stacks 00YV
(blueprint: def-sfb-coherent-integral-reduction).

Proof: constant functions preserve addition, multiplication and one before
sheafification. Monoidal pullback from the point preserves those identities.
The section-action equivalence reconstructs this map as a homomorphism of
commutative ring sheaves. Its underlying additive map is exactly the composite
displayed here, because constantSchemeIso is the constant-pullback comparison.
The forgetful functor from commutative rings to abelian groups is faithful;
the prescribed additive map therefore proves uniqueness. Reconstructing the
section rings retains their original carriers and additive restrictions, which
accounts for the heterogeneous equality of the two ring presentations.
-/
theorem constantSections_existsUnique (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    ∃! f : realizationRing.{u + 1, u} (Scheme.ProEt.topology X) T ⟶ sectionRing X T,
      HEq ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map f)
        (((constantCommuteCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
            forget₂ RingCat.{u + 1} Ab.{u + 1})).app (CommRingCat.of T)).hom ≫
          schemeConstants X T) := by
  sorry

/-- The uniquely specified constant-section homomorphism.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
def constantSections (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :=
  (constantSections_existsUnique X T).exists.choose

/-- For finite discrete coefficients the constant-section homomorphism is an isomorphism.
Source: Bhatt--Scholze, finite coefficient comparison
(blueprint: def-sfb-coherent-integral-reduction).

Proof: continuous functions into a finite discrete ring are locally constant.
On a profinite test each such function is constant on a finite clopen partition.
These partitions are covers for the coherent topology, so pointConstants is
locally surjective. Equality of constant functions is locally detected, giving
local injectivity. Sheafification makes it an isomorphism. Pullback to X and
section-ring reconstruction preserve it. The preceding additive normalization
identifies the resulting map with constantSections by uniqueness. This includes
the zero ring and the empty scheme.
-/
theorem constantSections_isIso (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [Finite T] [TopologicalSpace T] [DiscreteTopology T] :
    IsIso (constantSections X T) := by
  sorry

/-- The finite constant-coefficient identification, with its original constant-section map.
Source: finite coefficient comparison
(blueprint: def-sfb-coherent-integral-reduction). -/
def finiteConstantIso (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [Finite T] [TopologicalSpace T] [DiscreteTopology T] :
    realizationRing.{u + 1, u} (Scheme.ProEt.topology X) T ≅ sectionRing X T :=
  letI := constantSections_isIso X T
  asIso (constantSections X T)

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The spectral topology on the ring of integers, with no discrete replacement.
Source: the blueprint's integral coefficient ring
(blueprint: def-sfb-coherent-integral-reduction). -/
instance integersTopology : TopologicalSpace (Padic.coefficientExtensionIntegers l E) :=
  letI := spectralNorm.normedField ℚ_[l] E
  inferInstance

/-- The spectral topology makes O a topological ring.
Source: the blueprint's integral coefficient ring
(blueprint: def-sfb-coherent-integral-reduction). -/
instance integersTopologicalRing : IsTopologicalRing (Padic.coefficientExtensionIntegers l E) :=
  letI := spectralNorm.normedField ℚ_[l] E
  inferInstance

/-- Every finite quotient carries its discrete topology.
Source: the finite torsion levels of the blueprint
(blueprint: def-sfb-coherent-integral-reduction). -/
instance quotientTopology (n : ℕ) : TopologicalSpace (Etale.FiniteProperQuotient.Ring l E n) :=
  ⊥

/-- These specified finite quotient topologies are discrete.
Source: the finite torsion levels of the blueprint
(blueprint: def-sfb-coherent-integral-reduction). -/
instance quotientDiscrete (n : ℕ) : DiscreteTopology (Etale.FiniteProperQuotient.Ring l E n) :=
  ⟨rfl⟩

/-- The quotient homomorphism from O to the positive ell-power quotient.
Source: the finite torsion levels of the blueprint
(blueprint: def-sfb-coherent-integral-reduction). -/
def quotient (n : ℕ) : Padic.coefficientExtensionIntegers l E →+*
    Etale.FiniteProperQuotient.Ring l E n :=
  Ideal.Quotient.mk _

/-- Positive ell-power quotients of the ring of integers are finite rings.
Source: the blueprint's finite torsion coefficients
(blueprint: def-sfb-coherent-integral-reduction).

Proof: the integer ring of the finite extension is a DVR with finite residue
field. The nonzero element ell has positive valuation, so ell^(n+1) generates
the same ideal as a positive power of a uniformizer. Filter its quotient by
successive powers of that uniformizer. Each successive quotient is the finite
residue field. Induction on the positive exponent makes the entire quotient
finite. Ramified extensions are included: the exponent is multiplied by their
ramification index, not replaced by n+1.
-/
theorem quotient_finite (n : ℕ) : Finite (Etale.FiniteProperQuotient.Ring l E n) := by
  sorry

/-- Finiteness for the actual positive ell-power quotients.
Source: finite torsion coefficients
(blueprint: def-sfb-coherent-integral-reduction). -/
instance quotientFinite (n : ℕ) : Finite (Etale.FiniteProperQuotient.Ring l E n) :=
  quotient_finite l E n

/-- Positive ell-power quotients of the spectral ring of integers are continuous
with their discrete topology.
Source: the finite torsion levels in the blueprint; Zheng, Construction 4.1
(blueprint: def-sfb-coherent-integral-reduction).

Proof: the spectral absolute value restricts to the given l-adic absolute value.
The ideal generated by ell^(n+1) in O is therefore open: a sufficiently small
spectral ball is contained in it, using the discrete valuation of the finite
extension. Every fibre of the quotient map is a translate of this open ideal.
Preimages of arbitrary sets of the discrete quotient are unions of these open
fibres. The quotient homomorphism is continuous. Positivity of n+1 excludes the
zero-exponent convention; ramification changes the valuation of ell but not
openness of its positive powers.
-/
theorem quotient_continuous (n : ℕ) : Continuous (quotient l E n) := by
  sorry

/-- Finite coefficient sheaves on the pro-etale site, obtained from the point.
Source: the blueprint's quotient coefficient system
(blueprint: def-sfb-coherent-integral-reduction). -/
abbrev coefficients (X : Scheme.{u}) (n : ℕ) :=
  sectionRing X (Etale.FiniteProperQuotient.Ring l E n)

/-- Adjacent quotient maps on the actual pulled-back section rings.
Source: the blueprint's quotient coefficient system
(blueprint: def-sfb-coherent-integral-reduction). -/
def transitions (X : Scheme.{u}) (n : ℕ) :
    coefficients l E X (n + 1) ⟶ coefficients l E X n :=
  sectionMap X (Etale.FiniteProperQuotient.quotient l E (Nat.le_succ n))
    (continuous_of_discreteTopology)

/-- The actual coefficient morphism from continuous integral to finite coefficients.
Source: the blueprint's derived reduction
(blueprint: def-sfb-coherent-integral-reduction). -/
def coefficientMap (X : Scheme.{u}) (n : ℕ) :
    sectionRing X (Padic.coefficientExtensionIntegers l E) ⟶ coefficients l E X n :=
  sectionMap X (quotient l E n) (quotient_continuous l E n)

/-- The integral quotient maps form a morphism of the actual ring systems.
Source: Zheng, Construction 4.1, and the original quotient maps in blueprint step 1
(blueprint: def-sfb-coherent-integral-reduction).

Proof: both ring homomorphisms O to A_n send x to its class modulo ell^(n+1).
Postcomposition on continuous functions preserves composition. So do sheafification,
forgetting to abelian groups, pullback from the point, and section-ring reconstruction.
Their images are the displayed equality of sheaf morphisms. This also proves the
equal-index and composite quotient identities; no coefficient quotient is treated as flat.
-/
theorem coefficientMap_compatible (X : Scheme.{u}) (n : ℕ) :
    coefficientMap l E X (n + 1) ≫ transitions l E X n =
      (𝟙 (sectionRing X (Padic.coefficientExtensionIntegers l E))) ≫
        coefficientMap l E X n := by
  sorry

/-- The normalized simultaneous derived extension of the constant integral system.
Source: Zheng, Construction 4.1; the existing normalized semilinear calculus
(blueprint: def-sfb-coherent-integral-reduction). -/
def reductionScalar (X : Scheme.{u}) :
    ScalarSystems.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (constantCoefficients.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (sectionRing X (Padic.coefficientExtensionIntegers l E)))
      (constantCoefficientTransitions.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (sectionRing X (Padic.coefficientExtensionIntegers l E)))
      (coefficients l E X) (transitions l E X) (coefficientMap l E X)
      (coefficientMap_compatible l E X) :=
  SemilinearDerivedSectionsData.coefficientExtension.{u + 1, u, u + 1}
    (Classical.choice (semilinearDerivedSections.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X)
    (constantCoefficients.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (sectionRing X (Padic.coefficientExtensionIntegers l E)))
    (constantCoefficientTransitions.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (sectionRing X (Padic.coefficientExtensionIntegers l E)))))
    (coefficients l E X) (transitions l E X) (coefficientMap l E X)
    (coefficientMap_compatible l E X)

/-- The exact section-action equivalence, on the actual continuous integral coefficients.
Source: the recorded internal/sectionwise module equivalence, Stacks 00YV
(blueprint: def-sfb-coherent-integral-reduction). -/
def integralSections (X : Scheme.{u}) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
    (internalRing X (Padic.coefficientExtensionIntegers l E))).functor

/-- Section-action transport leaves addition of morphisms unchanged.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
instance integralSections_additive (X : Scheme.{u}) : (integralSections l E X).Additive where
  map_add := by intros; rfl

/-- An equivalence preserves kernels.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
instance integralSections_limits (X : Scheme.{u}) :
    PreservesFiniteLimits (integralSections l E X) :=
  inferInstanceAs (PreservesFiniteLimits
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
      (internalRing X (Padic.coefficientExtensionIntegers l E))).functor)

/-- An equivalence preserves cokernels.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
instance integralSections_colimits (X : Scheme.{u}) :
    PreservesFiniteColimits (integralSections l E X) :=
  inferInstanceAs (PreservesFiniteColimits
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
      (internalRing X (Padic.coefficientExtensionIntegers l E))).functor)

/-- Bounded constructible integral complexes, with precisely the existing cohomology predicate.
Source: the blueprint's Dbc notation
(blueprint: def-sfb-coherent-integral-reduction). -/
abbrev Bc (X : Scheme.{u}) :=
  BoundedConstructible (internalRing X (Padic.coefficientExtensionIntegers l E))

/-- Actual integral reductions as one object of the ordinary derived category of systems.
This is section-action transport, the exact diagonal, and one simultaneous derived
scalar extension. Its K-flat normalization is part of reductionScalar's model.
Source: Zheng, Construction 4.1; blueprint coherent-tower proof, step 1
(blueprint: def-sfb-coherent-integral-reduction). -/
def reduction (X : Scheme.{u}) :
    DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (internalRing X (Padic.coefficientExtensionIntegers l E))) ⥤
      DS.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (coefficients l E X) (transitions l E X) :=
  (integralSections l E X).mapDerivedCategory ⋙
    derivedConstantSystem.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (sectionRing X (Padic.coefficientExtensionIntegers l E)) ⋙
    ScalarData.T.{u + 1, u, u + 1} _ (reductionScalar l E X).scalar

/-- Restrict the canonical reduction functor to the full bounded constructible category.
Source: blueprint coherent-tower statement
(blueprint: def-sfb-coherent-integral-reduction). -/
def reductionBc (X : Scheme.{u}) : Bc l E X ⥤
    DS.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X) :=
  (boundedConstructible (internalRing X (Padic.coefficientExtensionIntegers l E))).ι ⋙
    reduction l E X

end AlgebraicGeometry.ProEtale.CoherentReduction
