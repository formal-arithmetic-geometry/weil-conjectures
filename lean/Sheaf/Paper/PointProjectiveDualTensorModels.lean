/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.PointDerivedHomModels
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Algebra.Homology.BoundedFiniteProjectiveDualTensor
import Sheaf.Paper.PointFiniteProjectiveAdjunctionUnits
import Sheaf.Paper.PointFiniteProjectiveExtensionModels
import Sheaf.Paper.PointExtensionTensorComparison
import Sheaf.Paper.PointPerfectExtensionConstructible
import Sheaf.Paper.PointFiniteProjectiveDualComparison
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact
import Sheaf.Algebra.Homology.IndependentBoundedExactTermHom
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Flat.Basic

/-! # Finite-projective dual and tensor models at the integral point

Source: main-20261015 blueprint, sec-six-functors/sk-thm-sf-package,
lem-pod-point-dualizing-complex.proof.md, second sentence; comparison identification,
third paragraph; Stacks Tags 07VI, 06YS, 08JI and 08JJ.
(blueprint: lem-pod-point-projective-dual-tensor-models).

All aliases below refer to the existing point-model constructions. In particular B
is the inverse limit of finite constant coefficient sheaves, not the constant R-sheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.PointDerivedHom.derivedSheaves
  WeilConjectures.PointDerivedHom.derivedModules
  WeilConjectures.PointDerivedHom.abSheafify
  WeilConjectures.PointDerivedHom.abLocallyBijective
  WeilConjectures.PointDerivedHom.ringLocallyBijective
  WeilConjectures.IntegralHom.abSheafify
  WeilConjectures.IntegralHom.abLocallyBijective
  WeilConjectures.IntegralHom.derivedCategory
  WeilConjectures.IntegralHom.tensorLocalization
  WeilConjectures.IntegralHom.countableColimits
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Opposite SheafOfModules CategoryTheory.SplitPerfectHom

namespace WeilConjectures.PointProjectiveDualTensorModels

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The existing lifted ring of integers, changing only universe size.
Source: blueprint coefficient convention
(blueprint: lem-pod-point-projective-dual-tensor-models). -/
abbrev R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)

/-- The actual completed commutative coefficient sheaf on the small pro-etale point.
Source: blueprint point proof (blueprint: lem-pod-point-projective-dual-tensor-models). -/
abbrev B := completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))

/-- The canonical map from constant scalars to that inverse limit.
Source: blueprint point proof (blueprint: lem-pod-point-projective-dual-tensor-models). -/
abbrev alpha := PointDerivedHom.coefficientMap.{u, u} D.k l E 1 true

/-- The generic scalar construction is the actual integral point-section map.
Source: the completed coefficient limit lift
(blueprint: lem-pod-point-projective-dual-tensor-models). -/
theorem scalar_eq :
    PointDerivedHom.scalar.{u, u} D.k (B D l E) (alpha D l E)
      (op (PointDerivedHom.finalObject D.k)) = pointIntegralSectionMap l E D.k := by
  rfl

/-- The existing sheaf module category; site objects remain in u+1 and arrows in u.
Source: Stacks 03D1 (blueprint: lem-pod-point-projective-dual-tensor-models). -/
abbrev Modules := integralTowerModules l E (Spec (.of D.k))

/-- R concentrated in degree zero, using the standard single-complex construction.
Source: Stacks 0A8X (blueprint: lem-pod-point-projective-dual-tensor-models). -/
abbrev ringComplex := (CochainComplex.singleFunctor (ModuleCat.{u + 1} (R l E)) 0).obj
  (ModuleCat.of (R l E) (R l E))

/-- B concentrated in degree zero in the recorded module category.
Source: Stacks 0A8X (blueprint: lem-pod-point-projective-dual-tensor-models). -/
abbrev coefficient := (CochainComplex.singleFunctor (Modules D l E) 0).obj
  (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))))

/-- The recorded ordinary Hom complex into R[0], including its signed differential.
Source: Stacks 0A8X (blueprint: lem-pod-point-projective-dual-tensor-models). -/
abbrev dual (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :=
  CochainComplex.moduleHomComplex P (ringComplex l E)

/-- The recorded signed algebraic total tensor of P and its dual.
Source: Stacks 012Z (blueprint: lem-pod-point-projective-dual-tensor-models). -/
abbrev tensor (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :=
  PointDerivedHom.moduleTotal P (dual l E P)

/-- Reading the coefficient R[0] in a degree equal to zero uses the canonical single iso.
Source: Stacks 0A8X (blueprint: lem-pod-point-projective-dual-tensor-models). -/
abbrev moduleValue (n : ℤ) (h : n = 0) :=
  (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0
    (ModuleCat.of (R l E) (R l E)) n h).hom

/-- The same canonical single-complex coordinate for B[0].
Source: Stacks 0A8X (blueprint: lem-pod-point-projective-dual-tensor-models). -/
abbrev sheafValue (n : ℤ) (h : n = 0) :=
  (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0
    (SheafOfModules.unit
      (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))) n h).hom

variable (L : ModuleCat.{u + 1} (R l E) ⥤ Modules D l E)
  (hobj : ∀ M : ModuleCat.{u + 1} (R l E),
    L.obj M = PointDerivedHom.extensionObject.{u, u} D.k (B D l E) (alpha D l E) M)
  (adj : L ⊣ PointDerivedHom.sections.{u, u} D.k (B D l E) (alpha D l E))

/-- Termwise application of the specified L; its adjunction supplies additivity.
Source: Stacks 0A8X (blueprint: lem-pod-point-projective-dual-tensor-models). -/
abbrev model (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :
    CochainComplex (Modules D l E) ℤ :=
  letI := PointDerivedHom.sections_additive.{u, u} D.k (B D l E) (alpha D l E)
  letI := adj.left_adjoint_additive
  (L.mapHomologicalComplex (.up ℤ)).obj P

/-- The termwise adjunction unit, with no unspecified chain comparison.
Source: blueprint point proof (blueprint: lem-pod-point-projective-dual-tensor-models). -/
def unit (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :
    P ⟶ ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
      (model D l E L adj P) :=
  letI := PointDerivedHom.sections_additive.{u, u} D.k (B D l E) (alpha D l E)
  letI := adj.left_adjoint_additive
  (adj.mapHomologicalComplex (.up ℤ)).unit.app P

/-- The termwise unit has the original generator formula.
Source: the explicit point adjunction
(blueprint: lem-pod-point-projective-dual-tensor-models). -/
theorem unit_apply
    (hex : PointDerivedHom.ExplicitAdjunction.{u, u} D.k (B D l E)
      (alpha D l E) L hobj adj)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) (i : ℤ) (x : P.X i) :
    ((unit D l E L adj P).f i).hom x =
      PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj
        (P.X i) (op (PointDerivedHom.finalObject D.k)) 1 x := by
  change (adj.unit.app (P.X i)).hom x = _
  have h := hex.1 (P.X i) (L.obj (P.X i)) (𝟙 _) x
  rw [adj.homEquiv_id] at h
  exact h

/-- A termwise invertible adjunction unit is an isomorphism of the actual point models.
Source: termwise adjunction and the componentwise isomorphism criterion
(blueprint: lem-pod-point-projective-dual-tensor-models). -/
theorem unit_isIso
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (h : ∀ i : ℤ, IsIso (adj.unit.app (P.X i))) : IsIso (unit D l E L adj P) := by
  have hcomp (i : ℤ) : IsIso ((unit D l E L adj P).f i) := h i
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The canonical unit isomorphism; its inverse is uniquely determined by the unit.
Source: the finite-projective adjunction unit and its termwise lifting
(blueprint: lem-pod-point-projective-dual-tensor-models). -/
@[irreducible] def unitIso
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    [IsIso (unit D l E L adj P)] :
    P ≅ ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
      (model D l E L adj P) :=
  asIso (unit D l E L adj P)

/-- The canonical unit isomorphism sends x to the original generator 1 tensor x.
Source: the explicit point adjunction
(blueprint: lem-pod-point-projective-dual-tensor-models). -/
theorem unitIso_apply
    (hex : PointDerivedHom.ExplicitAdjunction.{u, u} D.k (B D l E)
      (alpha D l E) L hobj adj)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    [IsIso (unit D l E L adj P)] (i : ℤ) (x : P.X i) :
    (((unitIso D l E L adj P).hom).f i).hom x =
      PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj
        (P.X i) (op (PointDerivedHom.finalObject D.k)) 1 x := by
  unfold unitIso
  exact unit_apply D l E L hobj adj hex P i x

/-- The ordinary signed total tensor of the two actual sheaf models.
Source: Stacks 012Z (blueprint: lem-pod-point-projective-dual-tensor-models). -/
abbrev tensorModel (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :=
  PointDerivedHom.total.{u, u} D.k (B D l E)
    (model D l E L adj P) (model D l E L adj (dual l E P))

/-- The existing standard localization, with its coefficient universe fixed explicitly.
Source: Stacks 05RU (blueprint: lem-pod-point-projective-dual-tensor-models). -/
abbrev sheafQ := @DerivedCategory.Q (Modules D l E) _ _ (HasDerivedCategory.standard _)

/-- All conclusions for the fixed finite-projective model, including normalization of
both isomorphisms and the actual adjunction units. This is an expansion of this node's
conclusion, not an additional hypothesis or replacement definition of its objects.
Source: blueprint point proof (blueprint: lem-pod-point-projective-dual-tensor-models). -/
def Result (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) : Prop :=
  letI : HasSheafify (Scheme.ProEt.topology (Spec (.of D.k))) AddCommGrpCat.{u + 1} :=
    PointDerivedHom.abSheafify.{u, u} D.k
  letI : (Scheme.ProEt.topology (Spec (.of D.k))).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := PointDerivedHom.abLocallyBijective.{u, u} D.k
  letI := IntegralHom.countableColimits.{u, u} (Spec (.of D.k)) (B D l E)
  letI := SheafOfModules.cochainModulesMonoidal.{u + 1, u, u + 1} (B D l E)
  letI : HasDerivedCategory.{u + 2} (Modules D l E) := HasDerivedCategory.standard _
  (∀ Q ∈ [dual l E P, tensor l E P],
    (∃ a b : ℤ, Q.IsStrictlyGE a ∧ Q.IsStrictlyLE b) ∧
      ∀ i : ℤ, Module.Projective (R l E) (Q.X i) ∧ Module.Finite (R l E) (Q.X i)) ∧
  (∀ Q ∈ [P, dual l E P, tensor l E P],
    (∀ i : ℤ, Module.Finite (R l E) (Q.homology i)) ∧
    ∀ F : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ,
      F.Acyclic → (PointDerivedHom.moduleTotal F Q).Acyclic) ∧
  (∀ Q ∈ [model D l E L adj P, model D l E L adj (dual l E P),
      tensorModel D l E L adj P],
    (∃ a b : ℤ, Q.IsStrictlyGE a ∧ Q.IsStrictlyLE b) ∧
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} (R := B D l E) Q ∧
    ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := B D l E) (Q.X i) ∧
      ∃ (r : ℕ)
        (s : Q.X i ⟶ SheafOfModules.free
          (R := PointDerivedHom.ring.{u, u} D.k (B D l E)) (ULift.{u + 1} (Fin r)))
        (t : SheafOfModules.free
          (R := PointDerivedHom.ring.{u, u} D.k (B D l E)) (ULift.{u + 1} (Fin r)) ⟶ Q.X i),
        s ≫ t = 𝟙 (Q.X i)) ∧
  (∃ beta : tensorModel D l E L adj P ≅ model D l E L adj (tensor l E P),
    ∀ (p j : ℤ) (U : (Scheme.ProEt (Spec (.of D.k)))ᵒᵖ)
      (b b' : (B D l E).obj.obj U) (x : P.X p) (f : (dual l E P).X j),
      (beta.hom.f (p + j)).val.app U
        (PointDerivedHom.totalElement.{u, u} D.k (B D l E)
          (model D l E L adj P) (model D l E L adj (dual l E P)) p j U
          (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj
            (P.X p) U b x)
          (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj
            ((dual l E P).X j) U b' f)) =
        PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj
          ((tensor l E P).X (p + j)) U (b * b')
          (PointDerivedHom.moduleTotalElement P (dual l E P) p j x f)) ∧
  Nonempty ((sheafQ D l E).obj (tensorModel D l E L adj P) ≅
    (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology (Spec (.of D.k))) (B D l E)).obj
      ((sheafQ D l E).obj (model D l E L adj P),
        (sheafQ D l E).obj (model D l E L adj (dual l E P)))) ∧
  (∀ Q ∈ [coefficient D l E, model D l E L adj P,
      model D l E L adj (dual l E P), tensorModel D l E L adj P],
    finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((sheafQ D l E).obj Q)) ∧
  (∀ Q ∈ [ringComplex l E, P, dual l E P, tensor l E P],
    QuasiIso (unit D l E L adj Q) ∧
    ∀ (i : ℤ) (x : Q.X i), ((unit D l E L adj Q).f i).hom x =
      PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj
        (Q.X i) (op (PointDerivedHom.finalObject D.k)) 1 x) ∧
  (∃ kappa : L.obj (ModuleCat.of (R l E) (R l E)) ≅
      SheafOfModules.unit (PointDerivedHom.ring.{u, u} D.k (B D l E)),
    (∀ (U : (Scheme.ProEt (Spec (.of D.k)))ᵒᵖ) (b : (B D l E).obj.obj U) (r : R l E),
      kappa.hom.val.app U
        (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj
          (ModuleCat.of (R l E) (R l E)) U b r) =
        b * PointDerivedHom.scalar.{u, u} D.k (B D l E) (alpha D l E) U r) ∧
    ∀ r : R l E, kappa.hom.val.app (op (PointDerivedHom.finalObject D.k))
      ((adj.unit.app (ModuleCat.of (R l E) (R l E))).hom r) =
      PointDerivedHom.scalar.{u, u} D.k (B D l E) (alpha D l E)
        (op (PointDerivedHom.finalObject D.k)) r) ∧
  ∃ h : model D l E L adj (dual l E P) ≅
      PointDerivedHom.sheafHom.{u, u} D.k (B D l E)
        (model D l E L adj P) (coefficient D l E),
    (∀ (p j : ℤ) (hpj : p + j = 0) (U : (Scheme.ProEt (Spec (.of D.k)))ᵒᵖ)
      (b b' : (B D l E).obj.obj U) (f : (dual l E P).X j) (x : P.X p),
      (sheafValue D l E (p + j) hpj).val.app U
        (PointDerivedHom.homValue.{u, u} D.k (B D l E)
          (model D l E L adj P) (coefficient D l E) j p U
          ((h.hom.f j).val.app U
            (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj
              ((dual l E P).X j) U b f))
          (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj
            (P.X p) U b' x)) =
        b * b' * PointDerivedHom.scalar.{u, u} D.k (B D l E) (alpha D l E) U
          ((moduleValue l E (p + j) hpj).hom ((f.v p (p + j) rfl).hom x))) ∧
    IsIso ((sheafQ D l E).map h.hom ≫
      IntegralHom.homModelMap.{u, u} (Spec (.of D.k)) (B D l E)
        (model D l E L adj P) (coefficient D l E))

/-- Finite-projective point dual and tensor models, with the actual canonical maps.
Source: blueprint point-dualizing proof, second sentence; comparison proof, third paragraph
(blueprint: lem-pod-point-projective-dual-tensor-models).

Proof plan (the node's seven steps):
1. Split each finite projective into a finite free module. Dualize the splitting
(lem-sf-finite-projective-dual) and tensor splittings. The dual support is [-b,-a]
and the tensor support [a-b,b-a]. Noetherian submodules and their quotients give finite
cohomology (lem-weil-pbc-noetherian-submodule-finite); projectives are flat
(lem-weil-pbc-projective-module-flat), hence bounded-flat K-flatness applies
(lem-pc-module-bounded-flat-kflat).
2. Constant finite-power/matrix formulas (lem-sfb-constant-finite-free-presentation-extension)
send these splittings to retracts of finite sums of B. Tensor their splittings for D.
Tensoring with a retract of a finite sum preserves exactness, giving flatness.
Apply lem-pc-bounded-above-flat-kflat-site and lem-pur-kflat-total-tensor-model.
3. The balancing inverse sends b tensor (x tensor f) to
(b tensor x) tensor (1 tensor f). Balancing relations prove both composites.
In bidegree (i,j), both differentials are dx tensor f + (-1)^i x tensor df;
therefore these maps sum to a chain isomorphism.
4. Apply lem-sfb-adic-perfect-model-complete-reduction to R[0], P, its dual and
its tensor, using the DVR maximal ideal (lem-weil-l-adic-extension-integers-dvr).
The unit-compatible quotient/Koszul comparison of
lem-weil-pbc-constant-completion-equivalence gives actual derived completeness.
5. Compute reductions by lem-pur-derived-change-of-rings. The quotient is the actual
finite constant coefficient sheaf by lem-weil-pbc-constant-completion-equivalence.
Finite-power/retract formulas identify the reduction with the constant reduced complex.
Its terms, cycles and cohomology are finite (lem-weil-valued-dvr-finite-quotients),
so it is constructible on the single point stratum. Each reduction has the original
support interval; its flat terms give the same Tor interval independently of level.
6. The explicit adjunction gives x mapped to 1 tensor x. On R this is the assumed
constant-value isomorphism, on finite powers coordinatewise. If vu=1 is a finite
free splitting, v eta_free^{-1} Gamma(L(u)) is the inverse to eta. Naturality gives
both identities and commutation with differential, for each of the four complexes.
7. With dual basis m_j, lambda_j, inverse evaluation sends a local homomorphism h
to sum_j h(1 tensor m_j) tensor lambda_j. The dual-basis identities prove both
composites. The source and target Hom differentials are both -(-1)^n f d_P,
so this is a chain isomorphism. Finally lem-weil-pbc-ringed-site-bounded-free-rhom-model
makes the canonical ordinary-Hom-to-derived-Hom map invertible; its composite with
this specified evaluation is the asserted canonical derived isomorphism. -/
theorem point_projective_dual_tensor_models
    (_hl : l ≠ D.p) [IsNoetherianRing (R l E)]
    (_hmap : ∀ {M N : ModuleCat.{u + 1} (R l E)} (f : M ⟶ N),
      L.map f = eqToHom (hobj M) ≫
        PointDerivedHom.extensionMorphism.{u, u} D.k (B D l E) (alpha D l E) f ≫
          eqToHom (hobj N).symm)
    (_hexplicit : PointDerivedHom.ExplicitAdjunction.{u, u} D.k (B D l E)
      (alpha D l E) L hobj adj)
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits (PointDerivedHom.sections.{u, u} D.k (B D l E) (alpha D l E))]
    [PreservesFiniteColimits (PointDerivedHom.sections.{u, u} D.k (B D l E) (alpha D l E))]
    (_hsections : Function.Bijective (PointDerivedHom.scalar.{u, u} D.k (B D l E)
      (alpha D l E) (op (PointDerivedHom.finalObject D.k))))
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) (a b : ℤ)
    (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hP : ∀ i : ℤ, Module.Projective (R l E) (P.X i) ∧ Module.Finite (R l E) (P.X i)) :
    Result D l E L hobj adj P := by
  let : HasSheafify (Scheme.ProEt.topology (Spec (.of D.k))) AddCommGrpCat.{u + 1} :=
    PointDerivedHom.abSheafify.{u, u} D.k
  let : (Scheme.ProEt.topology (Spec (.of D.k))).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := PointDerivedHom.abLocallyBijective.{u, u} D.k
  let := IntegralHom.countableColimits.{u, u} (Spec (.of D.k)) (B D l E)
  let := SheafOfModules.cochainModulesMonoidal.{u + 1, u, u + 1} (B D l E)
  let : HasDerivedCategory.{u + 2} (Modules D l E) := HasDerivedCategory.standard _
  let := PointDerivedHom.sections_additive.{u, u} D.k (B D l E) (alpha D l E)
  let := adj.left_adjoint_additive
  have halg := CochainComplex.bounded_finiteProjective_dual_tensor P a b _ha _hb _hP
  have hmodels := PointDerivedHom.point_finiteProjective_extension_models.{u}
    D.k (B D l E) (alpha D l E) L hobj adj _hexplicit _hsections
  obtain ⟨hu, hunit, κ, hκ, hκη⟩ :=
    PointDerivedHom.point_finiteProjective_adjunction_units.{u, u}
      D.k (B D l E) (alpha D l E) L hobj adj _hexplicit _hsections
  obtain ⟨β, hβ⟩ := PointDerivedHom.point_extension_tensor_comparison.{u}
    D.k (B D l E) (alpha D l E) L hobj adj _hmap P (dual l E P)
  have hfp (Q : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
      (hQ : Q ∈ [P, dual l E P, tensor l E P]) :
      (∃ c d : ℤ, Q.IsStrictlyGE c ∧ Q.IsStrictlyLE d) ∧
      ∀ i, Module.Projective (R l E) (Q.X i) ∧ Module.Finite (R l E) (Q.X i) := by
    simp only [List.mem_cons] at hQ
    rcases hQ with rfl | hQ
    · exact ⟨⟨a, b, _ha, _hb⟩, _hP⟩
    · exact halg Q (by simpa only [List.mem_cons] using hQ)
  have hfiniteKflat (Q : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
      (hQ : Q ∈ [P, dual l E P, tensor l E P]) :
      (∀ i, Module.Finite (R l E) (Q.homology i)) ∧
      ∀ F, F.Acyclic → (PointDerivedHom.moduleTotal F Q).Acyclic := by
    obtain ⟨⟨c, d, hc, hd⟩, hterms⟩ := hfp Q hQ
    constructor
    · intro i
      have := (hterms i).2
      have : Module.Finite (R l E) (Q.cycles i) :=
        Module.Finite.of_injective (Q.iCycles i).hom
          ((ModuleCat.mono_iff_injective _).1 inferInstance)
      exact Module.Finite.of_surjective (Q.homologyπ i).hom
        ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    · apply CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat Q
        ⟨d, fun i hi ↦ Q.isZero_of_isStrictlyLE d i hi⟩
      intro i
      have := (hterms i).1
      infer_instance
  have hm (Q : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
      (hQ : Q ∈ [P, dual l E P, tensor l E P]) :
      (∃ c d : ℤ, (model D l E L adj Q).IsStrictlyGE c ∧
        (model D l E L adj Q).IsStrictlyLE d) ∧
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (R := B D l E) (model D l E L adj Q) ∧
      ∀ i, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (R := B D l E) ((model D l E L adj Q).X i) ∧
        ∃ (r : ℕ)
          (s : (model D l E L adj Q).X i ⟶ SheafOfModules.free
            (R := PointDerivedHom.ring.{u, u} D.k (B D l E)) (ULift.{u + 1} (Fin r)))
          (t : SheafOfModules.free (R := PointDerivedHom.ring.{u, u} D.k (B D l E))
            (ULift.{u + 1} (Fin r)) ⟶ (model D l E L adj Q).X i), s ≫ t = 𝟙 _ := by
    obtain ⟨⟨c, d, hc, hd⟩, ht⟩ := hfp Q hQ
    obtain ⟨hmc, hmd, hk, hf⟩ := hmodels Q c d hc hd ht
    exact ⟨⟨c, d, hmc, hmd⟩, hk, hf⟩
  have hmP := hm P (by simp)
  have hmD := hm (dual l E P) (by simp)
  have hmT := hm (tensor l E P) (by simp)
  have htot := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (B D l E) (model D l E L adj P) (model D l E L adj (dual l E P))
    hmP.2.1 hmD.2.1 (fun i ↦ (hmP.2.2 i).1) (fun i ↦ (hmD.2.2 i).1)
  have hconstruct (Q : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
      (hQ : Q ∈ [P, dual l E P, tensor l E P]) :
      finiteTorConstructibleIntegral l E (Spec (.of D.k))
        ((sheafQ D l E).obj (coefficient D l E)) ∧
      finiteTorConstructibleIntegral l E (Spec (.of D.k))
        ((sheafQ D l E).obj (model D l E L adj Q)) := by
    obtain ⟨⟨c, d, hc, hd⟩, ht⟩ := hfp Q hQ
    exact PointPerfectExtensionConstructible.point_perfect_extension_constructible
      D l E L hobj adj _hl _hmap Q c d hc hd ht
  have hhom : IsIso (IntegralHom.homModelMap.{u, u} (Spec (.of D.k)) (B D l E)
      (model D l E L adj P) (coefficient D l E)) := by
    let := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
       (Scheme.ProEt.topology (Spec (.of D.k))) (B D l E)).1
    have hexact (i : ℤ) (S : ShortComplex (Modules D l E)) (hS : S.ShortExact) :
        ∃ hz : SheafOfModules.homObjMap (R := B D l E) (𝟙 ((model D l E L adj P).X i)) S.f ≫
            SheafOfModules.homObjMap (R := B D l E) (𝟙 ((model D l E L adj P).X i)) S.g = 0,
          (ShortComplex.mk
            (SheafOfModules.homObjMap (R := B D l E) (𝟙 ((model D l E L adj P).X i)) S.f)
            (SheafOfModules.homObjMap (R := B D l E) (𝟙 ((model D l E L adj P).X i)) S.g)
            hz).ShortExact := by
      obtain ⟨n, s, t, hst⟩ := (hmP.2.2 i).2
      exact (SheafOfModules.ringedSite_finite_retract_dual_exact.{u + 1, u, u}
        n ((model D l E L adj P).X i) s t hst).2.2.2.2.2.1 S hS
    have hbounded : ∃ c d : ℤ, ∀ i : ℤ, i < c ∨ d < i →
        IsZero ((model D l E L adj P).X i) := by
      obtain ⟨c, d, hc, hd⟩ := hmP.1
      refine ⟨c, d, fun i hi ↦ ?_⟩
      rcases hi with hi | hi
      · exact (model D l E L adj P).isZero_of_isStrictlyGE c i hi
      · exact (model D l E L adj P).isZero_of_isStrictlyLE d i hi
    let _ : QuasiIso ((CochainComplex.toKInjectiveResolution.{u + 1}
        (Modules D l E)).app (coefficient D l E)) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1}
        (Modules D l E) (coefficient D l E)).2
    have hq := quasiIso_homComplex_map_of_bounded_exact_terms.{u + 1, u, u}
       (Scheme.ProEt.topology (Spec (.of D.k))) (B D l E)
      (model D l E L adj P) hbounded hexact
      ((CochainComplex.toKInjectiveResolution.{u + 1} (Modules D l E)).app
        (coefficient D l E))
    let := hq
    dsimp only [IntegralHom.homModelMap]
    infer_instance
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨halg, hfiniteKflat, ?_, ⟨β, hβ⟩, ?_, ?_, ?_, ⟨κ, hκ, hκη⟩, ?_⟩
  · intro Q hQ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | rfl | rfl
    · exact hmP
    · exact hmD
    · obtain ⟨⟨c, d, hc, hd⟩, _, ht⟩ := hmT
      let _ : (model D l E L adj (tensor l E P)).IsStrictlyGE c := hc
      let _ : (model D l E L adj (tensor l E P)).IsStrictlyLE d := hd
      have hb : (tensorModel D l E L adj P).IsStrictlyGE c ∧
          (tensorModel D l E L adj P).IsStrictlyLE d :=
        ⟨@CochainComplex.isStrictlyGE_of_iso _ _ _ _ _ β.symm c hc,
          @CochainComplex.isStrictlyLE_of_iso _ _ _ _ _ β.symm d hd⟩
      refine ⟨⟨c, d, hb⟩, htot.1, fun i ↦ ⟨htot.2.1 i, ?_⟩⟩
      obtain ⟨r, s, t, hst⟩ := (ht i).2
      exact ⟨r, β.hom.f i ≫ s, t ≫ β.inv.f i, by
        rw [Category.assoc, ← Category.assoc s, hst, Category.id_comp]
        exact congrFun (congrArg HomologicalComplex.Hom.f β.hom_inv_id) i⟩
  · exact htot.2.2.2
  · intro Q hQ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | rfl | rfl | rfl
    · exact (hconstruct P (by simp)).1
    · exact (hconstruct P (by simp)).2
    · exact (hconstruct (dual l E P) (by simp)).2
    · have h := (hconstruct (tensor l E P) (by simp)).2
      obtain ⟨hc, a', b', hab, htor⟩ := h
      constructor
      · exact (sfIntegralConstructible l E (Spec (.of D.k))).prop_of_iso
          ((sheafQ D l E).mapIso β.symm) hc
      · refine ⟨a', b', hab, fun n ↦ ?_⟩
        have e := (scalarReductionDerivedExtension.{u, u} l E (Spec (.of D.k)) n).mapIso
          ((sheafQ D l E).mapIso β.symm)
        refine ⟨(htor n).1, ?_⟩
        intro A F hA f hf hF M i hi
        obtain ⟨eA⟩ := hA
        exact (htor n).2 A F ⟨eA ≪≫ e.symm⟩ f hf hF M i hi
  · intro Q hQ
    have hterms : ∀ i, Module.Projective (R l E) (Q.X i) ∧
        Module.Finite (R l E) (Q.X i) := by
      simp only [List.mem_cons] at hQ
      rcases hQ with rfl | hQ
      · intro i
        by_cases hi : i = 0
        · subst i
          let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (ModuleCat.of (R l E) (R l E))
          exact ⟨Module.Projective.of_equiv e.toLinearEquiv.symm,
            Module.Finite.equiv e.toLinearEquiv.symm⟩
        · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
            (ModuleCat.of (R l E) (R l E)) i hi
          let _ : Subsingleton ((ringComplex l E).X i) :=
            ModuleCat.isZero_iff_subsingleton.mp hz
          exact ⟨inferInstance, inferInstance⟩
      · exact (hfp Q (by simpa only [List.mem_cons] using hQ)).2
    have hcomp (i : ℤ) : IsIso ((unit D l E L adj Q).f i) := by
      let _ : Module.Projective (R l E) (Q.X i) := (hterms i).1
      let _ : Module.Finite (R l E) (Q.X i) := (hterms i).2
      exact @hu (Q.X i) (hterms i).2 (hterms i).1
    have : IsIso (unit D l E L adj Q) := HomologicalComplex.Hom.isIso_of_components _
    exact ⟨inferInstance, fun i x ↦ hunit (Q.X i) x⟩
  · obtain ⟨h, hh⟩ := PointDerivedHom.point_finiteProjective_dual_comparison.{u}
      D.k (B D l E) (alpha D l E) L hobj adj _hmap _hexplicit P a b _ha _hb _hP
    exact ⟨h, hh, inferInstance⟩

attribute [instance] WeilConjectures.PointDerivedHom.derivedSheaves
  WeilConjectures.PointDerivedHom.derivedModules
  WeilConjectures.PointDerivedHom.abSheafify
  WeilConjectures.PointDerivedHom.abLocallyBijective
  WeilConjectures.PointDerivedHom.ringLocallyBijective
  WeilConjectures.IntegralHom.abSheafify
  WeilConjectures.IntegralHom.abLocallyBijective
  WeilConjectures.IntegralHom.derivedCategory
  WeilConjectures.IntegralHom.tensorLocalization
  WeilConjectures.IntegralHom.countableColimits
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.scalarReductionSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall

end WeilConjectures.PointProjectiveDualTensorModels
