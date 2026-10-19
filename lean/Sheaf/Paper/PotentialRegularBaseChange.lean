/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.SixFunctors.EtaleGenericHomTriangle
public import Sheaf.Paper.CoefficientChangeDualizing
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.RingTheory.FiniteFreeResolution
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.Refinement
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.RingTheory.RegularBaseChange
import Sheaf.AlgebraicGeometry.RegularEtaleDirectImageBaseChange
import WeilConjectures.CategoryTheory.TruncationTriangle
import Sheaf.RingTheory.StrictHenselizationTriples
import Mathlib.RingTheory.Localization.Submodule
import Sheaf.RingTheory.StrictHenselizationNoetherian
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.ExcellentOfWeaklyEtale
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Sheaf.RingTheory.WeaklyEtaleField
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import Sheaf.RingTheory.StrictHenselizationPresentationIn
import Sheaf.AlgebraicGeometry.EtaleInternalHomLocalization

/-! # Regular pullback of internal Hom and strict-local testing

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII,
Propositions 4.2.2 and 6.2.3.2, and the beginning of 6.5
(blueprint: lem-per-potential-regular-base-change).

The comparison is the existing evaluation transpose. The left-derived inverse image
is canonically the termwise exact inverse image by `leftDerivedUpperStarIsoMapDerivedCategory`.
The coefficient lift only implements the ordinary small-etale universe convention.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Etale.CoefficientChangeDualizing

namespace AlgebraicGeometry.Etale.PotentialRegularBaseChange

/-- The specified prime-power coefficient ring, lifted to the small-etale coefficient universe.
Source: ILO XVII, 4.2.2 (blueprint: lem-per-potential-regular-base-change). -/
abbrev Coefficients (ℓ r : ℕ) := ULift.{u + 1} (ZMod (ℓ ^ r))

/-- The existing derived inverse image, canonically identified with exact inverse image.
Source: ILO XVII, 4.2.2 (blueprint: lem-per-potential-regular-base-change). -/
abbrev pull (ℓ r : ℕ) {X Y : Scheme.{u}} (p : Y ⟶ X) :
    DerivedCategoryModule (Coefficients.{u} ℓ r) X ⥤
      DerivedCategoryModule (Coefficients.{u} ℓ r) Y :=
  (upperStar (ModuleCat.{u + 1} (Coefficients.{u} ℓ r)) p).leftDerivedFunctor

/-- Regular pullback makes the evaluation-induced internal-Hom comparison invertible.
Evaluation compatibility is part of the definition of the specified comparison:
its transpose is pullback of evaluation after the inverse canonical tensor comparison.
Source: ILO XVII, Proposition 4.2.2, pp. 281--282
(blueprint: lem-per-potential-regular-base-change).

Proof:
1. Exact inverse image preserves cohomology, triangles and constructibility, by
   lem-trf-geometric-inverse-image-exact, lem-sf-exact-functor-derived-triangulated
   and prop-constructible-pullback.
2. The tensor comparison and tensor-Hom adjunction define beta as the transpose of
   pulled-back evaluation. Naturality and the signed shift compatibility of
   lem-weil-pbc-ringed-internal-hom-exact-restriction give a morphism of Hom triangles,
   including the connecting square. Thus invertibility is local and stable under triangles.
3. For a finite constant module, use lem-weil-pbc-finite-free-resolution-noetherian.
   A bounded-below target representative exists by lem-weil-pbc-dplus-injective-representative.
   In each total Hom degree only finitely many finite-free terms contribute, so
   lem-weil-pbc-ringed-site-bounded-free-rhom-model gives the comparison isomorphism.
   The evaluation formula identifies this isomorphism with beta. No finite projective
   dimension of the constant module is assumed.
4. Trivialize a lisse sheaf etale locally and apply Step 3. Conservative derived
   geometric stalks (lem-weil-pbc-derived-stalk-conservative) give the lisse case.
5. Induct on closed subsets, uniformly over their scheme structures and regular maps,
   by lem-weil-pbc-noetherian-scheme-closed-subsets-minimal. A finite stratification and
   finitely many irreducible components give a dense open lisse locus. Use
   lemma-constructible-immersion-independence to pass from strata to these opens.
6. Apply lem-per-etale-internal-hom-localization to this open and its closed complement.
   Base-changed maps remain regular (lem-weil-pbc-regular-base-change on affine charts).
   The right comparison is invertible by lem-per-regular-etale-direct-image-base-change
   and the lisse case. The left is invertible by induction and
   lem-per-regular-supported-base-change, including its closed-counit compatibility.
7. Transposing the squares identifies these outer comparisons and beta as a morphism
   of the actual localization triangles. The evaluation equation gives the open-unit
   square and the supported counit identity gives the closed square. Two-out-of-three
   (lem-sf-triangle-morphism-iso) gives beta. Finally the finite truncation triangles
   of lem-weil-pbc-truncation-triangle extend from sheaves to bounded constructible L.
-/
theorem regular_internalHom
    (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) (hr : 1 ≤ r)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hY : ∀ U : Y.affineOpens, IsExcellent Γ(Y, U))
    (hℓX : IsUnit (ℓ : Γ(X, ⊤))) (hℓY : IsUnit (ℓ : Γ(Y, ⊤)))
    (p : Y ⟶ X) [Flat p]
    (hreg : ∀ (x : X) (k' : Type u) [Field k']
      [Algebra (X.residueField x) k'] [Module.Finite (X.residueField x) k'],
      IsRegularScheme (pullback (p.fiberToSpecResidueField x)
        (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k')))))
    (L : DerivedCategoryModule (Coefficients.{u} ℓ r) X)
    (hL : DerivedCategory.isBoundedConstructible (Coefficients.{u} ℓ r) X L)
    (Q : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Coefficients.{u} ℓ r)))) :
    IsIso (etaleInternalHomPullbackComparison (Coefficients.{u} ℓ r) p L Q.obj) := by
  sorry

/-- Two canonical Hom comparisons identify the biduality arrows themselves.
Source: ILO XVII, Proposition 6.2.3.2, formal evaluation argument
(blueprint: lem-per-potential-regular-base-change).

Proof (Step 8 of the node): apply regular_internalHom to (L,K) and (D_K L,K).
Write b and c for these isomorphisms. The double-dual comparison is c followed by
D_(p*K)(b inverse). Uncurry its composite with p*eta_L and precompose with
1 tensor b. The evaluation equations for c and b, and compatibility of the canonical
tensor comparison with the signed symmetry, give the same pairing as eta_(p*L).
Cancel the invertible 1 tensor b and transpose back. No dualizing or pinning
hypothesis on K is used, only the two displayed constructibility hypotheses.
-/
theorem regular_biduality
    (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) (hr : 1 ≤ r)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hY : ∀ U : Y.affineOpens, IsExcellent Γ(Y, U))
    (hℓX : IsUnit (ℓ : Γ(X, ⊤))) (hℓY : IsUnit (ℓ : Γ(Y, ⊤)))
    (p : Y ⟶ X) [Flat p]
    (hreg : ∀ (x : X) (k' : Type u) [Field k']
      [Algebra (X.residueField x) k'] [Module.Finite (X.residueField x) k'],
      IsRegularScheme (pullback (p.fiberToSpecResidueField x)
        (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k')))))
    (L : DerivedCategoryModule (Coefficients.{u} ℓ r) X)
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Coefficients.{u} ℓ r))))
    (hL : DerivedCategory.isBoundedConstructible (Coefficients.{u} ℓ r) X L)
    (hDL : DerivedCategory.isBoundedConstructible (Coefficients.{u} ℓ r) X
      ((dual _ X K.obj).obj (op L))) :
    ∃ (b : (pull ℓ r p).obj ((dual _ X K.obj).obj (op L)) ≅
        (dual _ Y ((pull ℓ r p).obj K.obj)).obj (op ((pull ℓ r p).obj L)))
      (c : (pull ℓ r p).obj
          ((dual _ X K.obj).obj (op ((dual _ X K.obj).obj (op L)))) ≅
        (dual _ Y ((pull ℓ r p).obj K.obj)).obj
          (op ((pull ℓ r p).obj ((dual _ X K.obj).obj (op L))))),
      b.hom = etaleInternalHomPullbackComparison (Coefficients.{u} ℓ r) p L K.obj ∧
      c.hom = etaleInternalHomPullbackComparison (Coefficients.{u} ℓ r) p
        ((dual _ X K.obj).obj (op L)) K.obj ∧
      (pull ℓ r p).map (biduality _ X K.obj L) ≫ c.hom ≫
        (dual _ Y ((pull ℓ r p).obj K.obj)).map b.inv.op =
      biduality _ Y ((pull ℓ r p).obj K.obj) ((pull ℓ r p).obj L) := by
  sorry

/-- Exactness and preservation of bounded constructibility by inverse image.
Source: ILO XVII, 4.2.2 and 6.2.3.2
(blueprint: lem-per-potential-regular-base-change).

Proof (Step 1): geometric inverse image with constant coefficients preserves finite
limits and colimits by lem-trf-geometric-inverse-image-exact. Hence it commutes
with kernels, images and cohomology, and its derived functor is t-exact.
Pull back each finite locally closed stratification and its etale finite-constant
trivializations, using prop-constructible-pullback. Cohomological bounds are unchanged.
This argument applies to every scheme morphism, without regularity.
-/
theorem pullback_exact_constructible
    (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) (hr : 1 ≤ r)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hY : ∀ U : Y.affineOpens, IsExcellent Γ(Y, U))
    (hℓX : IsUnit (ℓ : Γ(X, ⊤))) (hℓY : IsUnit (ℓ : Γ(Y, ⊤)))
    (p : Y ⟶ X) :
    PreservesFiniteLimits (upperStar (ModuleCat.{u + 1} (Coefficients.{u} ℓ r)) p) ∧
    PreservesFiniteColimits (upperStar (ModuleCat.{u + 1} (Coefficients.{u} ℓ r)) p) ∧
    ∀ L : DerivedCategoryModule (Coefficients.{u} ℓ r) X,
      DerivedCategory.isBoundedConstructible (Coefficients.{u} ℓ r) X L →
        DerivedCategory.isBoundedConstructible (Coefficients.{u} ℓ r) Y
          ((pull ℓ r p).obj L) := by
  sorry

/-- Strict localizations are regular, Noetherian, excellent and finite dimensional.
Source: ILO I, Theorem 8.1(iv), and XVII, beginning of 6.5
(blueprint: lem-per-potential-regular-base-change).

Proof (Steps 9--10): identify the affine pointed-neighbourhood colimit with the
algebraic strict henselization using lem-weil-pbc-etale-local-ring-triples,
lem-weil-pbc-strict-henselization-triples and lem-exc-affine-strict-local-ring-comparison.
The pair and triple indexing categories agree by taking the kernel prime and its
residue embedding. The local ring is Noetherian by localization, hence its strict
henselization is Noetherian by lem-sc-strict-henselization-noetherian.
It is ind-etale, hence weakly etale by lem-weil-pbc-ind-etale-stability. Excellence
ascends by lem-exc-weakly-etale-excellent. Its finite dimension follows from
lem-weil-pbc-noetherian-local-finite-krull-dimension and the spectrum dimension convention.
Flatness follows from weak etaleness. After any finite residue-field extension,
the fibre remains weakly etale and Noetherian. By lem-weil-pbc-weak-etale-field it
is a union of finite etale algebras, so each element t satisfies t=t^2 u.
Its local rings are therefore fields and regular; use def-weil-regular-scheme.
-/
theorem strict_localization_geometry
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [IsNoetherian X]
    (hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hℓX : IsUnit (ℓ : Γ(X, ⊤)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Flat (Scheme.strictHenselizationStructuralMap s) ∧
    IsNoetherian (Scheme.strictHenselizationScheme s) ∧
    (∀ U : (Scheme.strictHenselizationScheme s).affineOpens,
      IsExcellent Γ(Scheme.strictHenselizationScheme s, U)) ∧
    (∃ d : ℕ, topologicalKrullDim (Scheme.strictHenselizationScheme s) ≤ d) ∧
    (∃ d : ℕ, ringKrullDim (Scheme.strictHenselizationRing s) ≤ d) ∧
    ∀ (x : X) (k' : Type u) [Field k']
      [Algebra (X.residueField x) k'] [Module.Finite (X.residueField x) k'],
      IsRegularScheme
        (pullback ((Scheme.strictHenselizationStructuralMap s).fiberToSpecResidueField x)
          (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k')))) := by
  sorry

/-- Pullback to all strict localizations detects isomorphisms of arbitrary etale complexes.
Source: ILO XVII, beginning of 6.5
(blueprint: lem-per-potential-regular-base-change).

Proof (Step 11): the closed geometric point of each strict localization has the same
stalk as its original point by lem-weil-pbc-inverse-image-stalk-germ.
Exact inverse image commutes with cohomology, so invertibility of every localized
map gives invertibility of every geometric stalk of every cohomology map.
Apply lemma-weil-pbc-geometric-stalk-conservative and the localization criterion
for derived-category isomorphisms. No bound or constructibility of either complex
is required. For the empty scheme the family is empty and its derived category is zero.
-/
theorem isIso_of_strict_localizations
    (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) (hr : 1 ≤ r)
    (X : Scheme.{u}) [IsNoetherian X]
    (hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hℓX : IsUnit (ℓ : Γ(X, ⊤)))
    {M N : DerivedCategoryModule (Coefficients.{u} ℓ r) X} (a : M ⟶ N)
    (ha : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      IsIso ((pull ℓ r (Scheme.strictHenselizationStructuralMap s)).map a)) :
    IsIso a := by
  sorry

end AlgebraicGeometry.Etale.PotentialRegularBaseChange
