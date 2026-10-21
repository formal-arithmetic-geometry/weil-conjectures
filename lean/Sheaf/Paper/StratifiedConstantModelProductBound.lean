/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.Paper.IntegralModelSurjectiveClosedReflection
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.WeaklyEtaleStability
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Algebra.Module.FinitePresentation
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.Paper.CartesianCoefficients
import Sheaf.CategoryTheory.LocallyPrescribedModulesSmall
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Sheaf.CategoryTheory.JointAdjunctionModelEmbedding

/-!
# Small stratum-product and image-subsheaf models

Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-int-integral-heart/sk-lem-int-integral-heart-triangulated.proof.md, paragraph (2),
final sentence (blueprint: lem-sfb-stratified-constant-model-product-bound).

The index types below lie in `u + 1`, the universe of the bounded sites and sections.
The coefficient rings and schemes lie in `u`. Image indices are actual families of
submodules whose underlying presheaf is a sheaf, rather than arbitrary chosen objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.StratifiedConstantModels

/-- Schemes occurring as strata of finite locally closed stratifications of X.
Source: paragraph (2), finite stratifications
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
abbrev Stratum (X : Scheme.{u}) : Type (u + 1) :=
  {T : Scheme.{u} // ∃ (S : Scheme.FiniteLocallyClosedStratification X)
    (s : Fin S.n), S.domain s = T}

/-- The stratum scheme at one position, with its occurrence witness.
Source: paragraph (2), finite stratifications
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
def stratumAt {X : Scheme.{u}} (S : Scheme.FiniteLocallyClosedStratification X)
    (s : Fin S.n) : Stratum X :=
  ⟨S.domain s, S, s, rfl⟩

/-- All pairs of a bounded finite stratification and a tuple of local-model labels.
This is a type in `u + 1`, including the unique empty tuple when `S.n = 0`.
Source: paragraph (2), the small set of gluing data
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
abbrev Index (X : Scheme.{u}) (I : Stratum X → Type (u + 1)) : Type (u + 1) :=
  Σ S : Scheme.FiniteLocallyClosedStratification X, ∀ s : Fin S.n, I (stratumAt S s)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Internal coefficient modules, using the existing pulled-back ring object.
Source: paragraph (2), modules on the small pro-etale site
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
abbrev Modules (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)

/-- The product of the direct images of the chosen stratum models.
Source: paragraph (2), gluing data, and Stacks Tag 03DB for products
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
def product {X : Scheme.{u}} (I : Stratum X → Type (u + 1))
    (F : ∀ T : Stratum X, I T → Modules Λ T.val) (j : Index X I) : Modules Λ X :=
  ∏ᶜ fun s : Fin j.1.n ↦
    (CondensedRing.lowerStar Λ (j.1.immersion s)).obj (F (stratumAt j.1 s) (j.2 s))

/-- The existing internal-to-sectionwise equivalence, preserving underlying sections.
Source: Stacks Tag 00YV, as used in paragraph (2)
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
abbrev sectionModule {X : Scheme.{u}} (P : Modules Λ X) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)).functor.obj P

/-- Actual families of submodules of the sections of P, stable under restriction,
whose associated presheaf satisfies the sheaf condition. This index is in `u + 1`.
Source: paragraph (2), small-site gluing data; Stacks Tag 03DA
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
abbrev ImageIndex {X : Scheme.{u}} (P : Modules Λ X) : Type (u + 1) :=
  {N : (sectionModule Λ P).val.Submodule //
    Presheaf.IsSheaf (Scheme.ProEt.topology X) N.toPresheafOfModules.presheaf}

/-- All image-subsheaf labels for all stratum products, in the same small universe.
Source: paragraph (2), the set of all gluing data
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
abbrev TotalImageIndex {X : Scheme.{u}} (I : Stratum X → Type (u + 1))
    (F : ∀ T : Stratum X, I T → Modules Λ T.val) : Type (u + 1) :=
  Σ j : Index X I, ImageIndex Λ (product Λ I F j)

/-- The image subsheaf specified by its family of subsets, with inherited operations.
Source: paragraph (2), small-site gluing data; Stacks Tag 03DA
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
def imageSheaf {X : Scheme.{u}} (P : Modules Λ X) (N : ImageIndex Λ P) :
    SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) (condensedRingObj Λ X))) :=
  ⟨N.val.toPresheafOfModules, N.property⟩

/-- Inclusion of the actual image subsheaf into P, on every section.
Source: paragraph (2), small-site gluing data; Stacks Tag 03DA
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
def imageInclusion {X : Scheme.{u}} (P : Modules Λ X) (N : ImageIndex Λ P) :
    imageSheaf Λ P N ⟶ sectionModule Λ P :=
  ⟨N.val.ι⟩

/-- The small family of products and their actual image subsheaves bounds all
constructible integral coefficient modules. Labels are supplied for each stratum
scheme, and all choices of stratification and labels occur in `Index`.

Source: blueprint main-20261015, sk-lem-int-integral-heart-triangulated.proof.md,
paragraph (2), final sentence
(blueprint: lem-sfb-stratified-constant-model-product-bound).

Proof:
1. Each bounded pro-etale site has terminal object and finite limits, using weakly
   etale stability and scheme fibre products; pass to its small skeleton.
2. Finite matrices over O_E form a small set; their actual cokernels represent every
   finitely presented scalar module (def-sc-finitely-presented-module).
3. Pro-etale localization and proEtaleObjectInverseImageRestriction identify these
   scalar models with slice-local models, using cartesian coefficients. Apply
   essentiallySmall_locally_prescribed and choose representatives simultaneously
   over the set of stratum schemes.
4. Finite stratifications form a set in `u + 1`. Dependent sums of their finite
   tuples of representative labels give exactly `Index X I` in `u + 1`.
5. Form the products using the module adjunctions and sectionwise limits. The
   internal-to-sectionwise equivalence preserves the sections of these products.
6. A constructible module has a finite constant-model stratification: quasi-compact
   locally Noetherian X is qcqs. Choose representative labels and isomorphisms.
7. Cartesian pullback is exact. Noetherian stratum detection says these pullbacks
   jointly detect zero objects. Apply mono_pi_lift_adjunction_models to obtain
   the monomorphism with the specified adjunction-unit components.
8. For a mono m, the ranges of its injective section maps form a submodule family.
   The sectionwise bijections from its source to these ranges transport the sheaf
   axiom and give an isomorphism over the product. Equal families identify the
   subobjects over that product; general non-monic images are not used.
9. Such families belong to the product of the powersets of the section sets, in
   `u + 1`. `ImageIndex` takes precisely the sheaf subfamilies, so the dependent
   sum over `Index X I` is still a type in `u + 1`.
10. Zero models are allowed. For empty X the empty stratification is allowed;
    its product is the zero module, and all module sheaves on the empty site are
    zero by the empty covering sheaf axiom. Empty strata cause no exception. -/
theorem exists_stratified_constant_model_product_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [CompactSpace X] [IsLocallyNoetherian X] :
    ∃ (I : Stratum X → Type (u + 1))
      (F : ∀ T : Stratum X, I T →
        Modules (integralModelCondensedCoefficients l E).X T.val),
      (∀ (T : Stratum X) (t : I T),
        HasFiniteConstantLocalModel (integralModelCondensedCoefficients l E).X T.val (F T t)) ∧
      (∀ (T : Stratum X) (M : Modules (integralModelCondensedCoefficients l E).X T.val),
        HasFiniteConstantLocalModel (integralModelCondensedCoefficients l E).X T.val M →
          ∃ t : I T, Nonempty (M ≅ F T t)) ∧
      (∀ (C : Modules (integralModelCondensedCoefficients l E).X X),
        IsConstantModelConstructible (integralModelCondensedCoefficients l E).X X C →
          ∃ (j : Index X I)
            (φ : ∀ s : Fin j.1.n,
              (CondensedRing.upperStar (integralModelCondensedCoefficients l E).X
                (j.1.immersion s)).obj C ≅ F (stratumAt j.1 s) (j.2 s))
            (v : C ⟶ product (integralModelCondensedCoefficients l E).X I F j),
            Mono v ∧ ∀ s : Fin j.1.n,
              v ≫ Pi.π (fun s : Fin j.1.n ↦
                (CondensedRing.lowerStar (integralModelCondensedCoefficients l E).X
                  (j.1.immersion s)).obj (F (stratumAt j.1 s) (j.2 s))) s =
                (CondensedRing.upperStarLowerStarAdjunction
                  (integralModelCondensedCoefficients l E).X (j.1.immersion s)).unit.app C ≫
                  (CondensedRing.lowerStar (integralModelCondensedCoefficients l E).X
                    (j.1.immersion s)).map (φ s).hom) ∧
      (∀ (j : Index X I),
        (∀ N : ImageIndex (integralModelCondensedCoefficients l E).X
          (product (integralModelCondensedCoefficients l E).X I F j),
          Mono (imageInclusion (integralModelCondensedCoefficients l E).X _ N)) ∧
        (∀ (M : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
                (Scheme.ProEt.topology X)
                (condensedRingObj (integralModelCondensedCoefficients l E).X X))))
          (m : M ⟶ sectionModule (integralModelCondensedCoefficients l E).X
            (product (integralModelCondensedCoefficients l E).X I F j)),
          Mono m → ∃ (N : ImageIndex (integralModelCondensedCoefficients l E).X
              (product (integralModelCondensedCoefficients l E).X I F j))
            (e : M ≅ imageSheaf (integralModelCondensedCoefficients l E).X _ N),
            e.hom ≫ imageInclusion (integralModelCondensedCoefficients l E).X _ N = m)) ∧
      (IsEmpty X → ∃ j : Index X I, j.1.n = 0) ∧
      (∀ j : Index X I, j.1.n = 0 →
        IsZero (product (integralModelCondensedCoefficients l E).X I F j)) := by
  sorry

end AlgebraicGeometry.ProEtale.StratifiedConstantModels
