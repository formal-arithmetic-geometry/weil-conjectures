/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Retract
import Sheaf.Paper.FiniteScalarPerfectRefinement
import Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization
public import Sheaf.Paper.CartesianCoefficients
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # Uniform scalar-perfect bounds on a locally closed stratum

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (2), local models and the stratum geometry checks
(blueprint: lem-sfb-stratum-perfect-uniform-bounds).

Scalar modules are the existing internal modules in abelian groups over the actual
section ring Gamma(*). A retract of a finite free scalar module is precisely a finite
projective ordinary module. Scalar realization is the canonical constant-sheaf extension
of det-def-sfb-constructible-local-model. All derived categories are uncompleted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.StratumPerfectBounds

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing module-object encoding of ordinary modules over Gamma(*).
Source: blueprint local models, (2)
(blueprint: lem-sfb-stratum-perfect-uniform-bounds). -/
abbrev Scalars := Mod Ab.{u + 1} (scalarRingObj Λ)

/-- The existing internal-module encoding of Gamma_T-module sheaves.
Source: blueprint local models, (2)
(blueprint: lem-sfb-stratum-perfect-uniform-bounds). -/
abbrev Modules (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)

/-- Termwise ordinary scalar realization, using the canonical constant scalar map.
Source: blueprint local models, (2)
(blueprint: lem-sfb-stratum-perfect-uniform-bounds). -/
abbrev realized (T : Scheme.{u}) (F : CochainComplex (Scalars Λ) ℤ) :=
  letI : PreservesColimitsOfSize.{0, 0} pointUpperStar.{u} :=
    pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
  letI : PreservesFiniteColimits (scalarConstant T) :=
    inferInstanceAs (PreservesFiniteColimits
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙ upperStarFromPoint T))
  letI : PreservesFiniteColimits (finiteConstantScalarExtension Λ T) :=
    inferInstanceAs (PreservesFiniteColimits
      ((scalarConstant T).mapMod (scalarRingObj Λ) ⋙
        Mod.extendScalars (scalarCoefficientHom Λ T)))
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (finiteConstantScalarExtension Λ T)
  letI := Functor.additive_of_preservesBinaryBiproducts (finiteConstantScalarExtension Λ T)
  ((finiteConstantScalarExtension Λ T).mapHomologicalComplex (.up ℤ)).obj F

/-- All the local and global assertions, with the original cover and complexes retained.
This only packages the conclusion of the node; it imposes no exactness hypothesis on
scalar realization or any tensor test module.
Source: blueprint local models, (2)
(blueprint: lem-sfb-stratum-perfect-uniform-bounds). -/
def Assertion (S : Scheme.{u}) : Prop :=
  ∀ (Q : DerivedCategory (Modules Λ S))
    (𝒰 : Scheme.Cover.{i} Scheme.proetalePrecoverage S)
    (F : 𝒰.I₀ → CochainComplex (Scalars Λ) ℤ),
    (∀ i, ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero ((F i).X q)) →
    (∀ i q, ∃ m : ℕ, Nonempty (Retract ((F i).X q)
      (Mod.finiteFree (scalarRingObj Λ) m))) →
    (∀ i, Nonempty
      ((CondensedRing.upperStar Λ (𝒰.f i)).mapDerivedCategory.obj Q ≅
        DerivedCategory.Q.obj (realized Λ (𝒰.X i) (F i)))) →
    ∃ (n : ℕ) (α : Fin n → 𝒰.I₀) (V : ∀ j, (𝒰.X (α j)).Opens) (r s : ℤ),
      r ≤ s ∧
      (∀ j, IsAffineOpen (V j)) ∧
      Presieve.ofArrows (fun j ↦ (V j).toScheme)
        (fun j ↦ (V j).ι ≫ 𝒰.f (α j)) ∈ Scheme.proetalePrecoverage.coverings S ∧
      (∀ j q, q < r ∨ s < q → IsZero ((F (α j)).X q)) ∧
      (∀ j, Nonempty
        ((CondensedRing.upperStar Λ ((V j).ι ≫ 𝒰.f (α j))).mapDerivedCategory.obj Q ≅
          DerivedCategory.Q.obj (realized Λ (V j).toScheme (F (α j))))) ∧
      (∀ j q, Mod.IsFinitelyPresented (scalarRingObj Λ)
          ((HomologicalComplex.homologyFunctor (Scalars Λ) (.up ℤ) q).obj (F (α j))) ∧
        Nonempty
          ((CondensedRing.upperStar Λ ((V j).ι ≫ 𝒰.f (α j))).obj
              ((DerivedCategory.homologyFunctor _ q).obj Q) ≅
            (finiteConstantScalarExtension Λ (V j).toScheme).obj
              ((HomologicalComplex.homologyFunctor (Scalars Λ) (.up ℤ) q).obj
                (F (α j))))) ∧
      (∀ q : ℤ, q < r ∨ s < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj Q)) ∧
      (∀ (N : Modules Λ S) (j : Fin n), Nonempty
        ((CondensedRing.upperStar Λ ((V j).ι ≫ 𝒰.f (α j))).mapDerivedCategory.obj
            (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N) ≅
          DerivedCategory.Q.obj
            (realized Λ (V j).toScheme (F (α j)) ⊗
              (CochainComplex.singleFunctor _ 0).obj
                ((CondensedRing.upperStar Λ ((V j).ι ≫ 𝒰.f (α j))).obj N)))) ∧
      (∀ (N : Modules Λ S) (q : ℤ), q < r ∨ s < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N))) ∧
      (∀ q : ℤ, HasFiniteConstantLocalModel Λ S
        ((DerivedCategory.homologyFunctor _ q).obj Q)) ∧
      constantModelBoundedConstructible Λ S Q ∧
      DerivedCategory.torAmplitudeIn (Modules Λ S) r s Q ∧
      (IsEmpty S → n = 0 ∧ r = 0 ∧ s = 0)

/-- Uniform models, scalar cohomology, and Tor bounds for a locally closed stratum.
Finite discrete coefficients have no additional ell-primary condition. The algebraic
closure is the specified finite-subextension-valued condensed ring.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (2)
(blueprint: lem-sfb-stratum-perfect-uniform-bounds).

Proof plan:
1. A field is Noetherian. Finite type over it makes X Noetherian. Factor the immersion
   as closed then open; lem-sfb-noetherian-open-closed-finite-presentation gives finite
   type. Composition, separated cancellation and permanence give the asserted geometry
   of S and a. The qcqs and finite-affine-cover lemmas give the finite open cover of S.
2. If S is nonempty, lem-sfb-finite-scalar-perfect-refinement gives a finite affine
   refinement, retaining the specified complexes. Take the minimum and maximum of their
   finitely many bounds, before choosing any test module N.
3. Coefficient sections localization and cartesian coefficients identify the restricted
   coefficients. Lem-sfb-admissible-scalar-model-cohomology gives finitely presented
   scalar cohomology and its realized cohomology formula. Exact restriction commutes
   with homology by lem-sp-exact-functor-preserves-homology.
4. A realized finite-projective term is a retract of a finite free coefficient sheaf.
   Tensoring a short exact sequence with it is a retract of a finite sum of that
   sequence, hence exact. Lem-pc-bounded-above-flat-kflat-site gives K-flatness.
5. Use lem-pc-kflat-resolution and lem-trf-site-one-sided-tensor-normalization with
   arbitrary N[0]. Restriction preserves K-flatness and flat terms; localized tensor
   restriction identifies the ordinary tensors. The retained bounded flat chart model
   therefore computes the displayed tensor; its terms vanish outside the same interval.
6. Restriction is exact. For either cohomology sheaf, vanishing on a cover implies
   global vanishing: pull the cover back to each test object and use sheaf uniqueness.
7. The same finite scalar cohomology models give constructibility on the single stratum
   S. Global boundedness and the arbitrary-N bound give Dbc and the stated Tor interval,
   hence Dctf by det-def-sfb-constructible-tor-amplitude.
8. If S is empty its site objects have the empty cover, so every module sheaf is zero.
   Use the empty refinement and r=s=0; all model assertions on members are vacuous. -/
theorem stratum_perfect_uniform_bounds
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hpl : p ≠ ℓ)
    (_hΛ :
      (∃ (A : Type u) (_ : CommRing A), Finite A ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (cartesianFinitePointRing A))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (X S : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] (a : S ⟶ X) [IsImmersion a] :
    IsNoetherian S ∧ CompactSpace S ∧ QuasiSeparatedSpace S ∧
    (∃ (m : ℕ) (U : Fin m → S.Opens),
      (∀ j, IsAffineOpen (U j)) ∧ ∀ x : S, ∃ j, x ∈ U j) ∧
    LocallyOfFiniteType (a ≫ (X ↘ Spec (.of k))) ∧
    QuasiCompact (a ≫ (X ↘ Spec (.of k))) ∧
    IsSeparated (a ≫ (X ↘ Spec (.of k))) ∧
    LocallyOfFiniteType a ∧ QuasiCompact a ∧ IsSeparated a ∧ Assertion.{u, i} Λ S := by
  sorry

end AlgebraicGeometry.ProEtale.StratumPerfectBounds
