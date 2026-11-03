/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.QuasiFinite.Basic
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedFiniteEvaluation.CondensedFiniteFibreEvaluationData
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedFiniteEvaluation.CondensedFiniteFibreEvaluationExistence
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedFiniteEvaluation.CondensedFiniteFibreFrobeniusNaturality
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativePointFibreFunctor
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.DeligneLaumon.CondensedFibresExact
public import WeilConjectures.DeligneLaumon.FiniteGeometricModel
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.TopInvariance
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius

/-! # Condensed finite-fibre evaluation and Frobenius orbits

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/sec-deligne-laumon-a1/
sec-the-weight-bound-on-the-affine-line/sk-thm-dl-a1-upper/lem-zl-finite-pushforward.proof.md,
Exactness and stalks and the Frobenius-orbit sentences
(blueprint: lem-zl-condensed-finite-fibre-evaluation).

The derived comparison is characterized on H⁰ by the actual restriction of sections.
The geometric cycle and the local return use the semilinear point convention, even
when the module is zero. No reducedness, purity or semisimplicity is imposed.

## Main definitions

`Evaluation` records the canonical finite sum and derived comparison.
`Frobenius` records the geometric cycles and their specified local returns.
`Naturality` records functoriality for module maps and semilinear diagrams.

## Main statements

`condensed_finite_fibre_evaluation` asserts these comparisons and compatibilities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj DirectSum

namespace WeilConjectures.CondensedFiniteEvaluation

attribute [local irreducible] NativeCondensedModule.transport NativeCondensedModule.operator

variable (D : FiniteFieldDatum.{u}) (T₀ : Over (Spec (.of D.k₀))) [IsFinite T₀.hom]
  (l : ℕ) [Fact l.Prime]

/-- The standard degree-zero embedding of ordinary coefficient modules.
Source: latest blueprint, the notation F_z[0] in D(Omega)
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
def coefficientSingle :=
  DerivedCategory.singleFunctor (ModuleCat.{u + 1} (CondensedRing.CohomologyScalar.{u} l)) 0

/-- Derived sections applied to degree-zero native modules.
Source: latest blueprint, RΓ(T,F) for a degree-zero coefficient module
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
def derivedOnModules :=
  DerivedCategory.singleFunctor (NativeCondensedModule.Modules l (Tgeom).left) 0 ⋙
    sectionsComplex D T₀ l

/-- Canonical comparison for point pullbacks around a commuting scheme square.
Source: latest blueprint, naturality for semilinear finite-scheme diagrams
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
def diagramComparison (l : ℕ) [Fact l.Prime] {S' S T' T : Scheme.{u}}
    (a : T' ⟶ T) (b : S' ⟶ S) (z' : S' ⟶ T') (z : S ⟶ T)
    (h : z' ≫ a = b ≫ z) (M : NativeCondensedModule.Modules l T) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z').obj
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M) ≅
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) b).obj
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj M) :=
  (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) z' a).symm.app M ≪≫
    (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l) h).app M ≪≫
    (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) b z).app M

set_option maxHeartbeats 600000 in
-- The coherent pullback comparison has large concrete module-object types.
end WeilConjectures.CondensedFiniteEvaluation

namespace WeilConjectures.CondensedFiniteEvaluation

/-- Canonical derived evaluation on a finite geometric scheme, with Frobenius cycles.
Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/sec-deligne-laumon-a1/
sec-the-weight-bound-on-the-affine-line/sk-thm-dl-a1-upper/lem-zl-finite-pushforward.proof.md,
Exactness and stalks, Frobenius orbits and return maps
(blueprint: lem-zl-condensed-finite-fibre-evaluation).

Proof in words:
1. Finite over a field is affine with finite-dimensional coordinate algebra. Its spectrum
is finite with all points closed, and its residue fields are finite extensions.
2. Base change gives B₀ tensor k. Its reduction is a finite product of k: residue fields
are k by algebraic closedness, and the Chinese remainder theorem applies to its finitely
many pairwise comaximal maximal ideals. Thus the reduction is a disjoint union of points.
3. Its reduction immersion is a surjective closed immersion, hence a universal
homeomorphism. Pro-etale topological invariance and cartesian coefficients identify module
sections with sections on this reduction, through the canonical adjunction restriction.
4. The finite disjoint-cover sheaf axiom identifies these sections with the product of
point restrictions. Module pullback composition identifies each with the stated z^*M.
This is the actual evaluation map and respects the constant Omega action; the empty cover
has zero module sections. Finite products identify canonically with finite direct sums.
5. Point pullback and point sections are exact. Hence finite evaluation makes sections
on T exact. Total right derivation is termwise sections, so the same evaluation is an
isomorphism in D(Omega), normalized on H⁰ by the displayed restriction maps.
6. Constructibility makes each point fibre finite dimensional. The geometric points over
x are the embeddings of its finite residue field into k. Finite-field Galois theory makes
these a torsor for the d distinct q-power automorphisms. Consequently their number is d.
7. Put h=Spec(gamma), g=id times h. The permutation tau(z)=h⁻¹ z g changes the embedding
by q-power Frobenius, so every block is one d-cycle and z g^d=h^d z.
8. Restriction naturality and the coherent pullback comparisons give
 e_z F=A_z e_tau(z), where A_z is precisely NativeCondensedModule.transport with one iterate.
The global operator is restriction along g followed by theta. It is invertible.
The degree-zero derived comparison gives its unique lift to an automorphism of RΓ;
its H⁰ normalization is exactly derivedFormula.
9. Iterate that equation d times. The point returns to z, and the coherent product of
the d transports is exactly NativeCondensedModule.operator, defined by d Weil iterates and the
single point reparametrization h^d. This gives e_z F^d=F_x,z e_z, without semisimplicity.
10. For module maps, evaluation commutes with pullback and sections. For a diagram with
a field isomorphism, both composites restrict along the same scheme map. The inverse-image
unit and composition coherences give the stated diagram equation, preserving scalars.
The H⁰-normalized derived comparison inherits these equations, since both complexes lie
in degree zero. This proves naturality and includes semilinear diagrams. -/
theorem condensed_finite_fibre_evaluation (hl : l ≠ D.p) :
    ∃ E : Evaluation D T₀ l, Nonempty (Frobenius D T₀ l E) ∧ Naturality D T₀ l E := by
  obtain ⟨E, hE⟩ := finite_fibre_evaluation_data D T₀ l hl
  obtain ⟨hF, hN⟩ := finite_fibre_frobenius_naturality D T₀ l hl E hE
  exact ⟨E, hF, hN⟩

end WeilConjectures.CondensedFiniteEvaluation
