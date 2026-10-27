/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q96
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.CurveModuliGroupoids
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.OpenStackAlgebraicLfp
import Sheaf.AlgebraicGeometry.ProjectiveHilbertPolynomialRepresentability
import Sheaf.AlgebraicGeometry.StackPointTopology
import Sheaf.TraceFormula.ProjectiveBundleProper
import Mathlib.AlgebraicGeometry.Noetherian

/-! # The bounded arithmetic open substack of stable genus-g curves

Source: Stacks Project, moduli-curves.tex, Tags 0E76, 0E78 and 0E9B; curves.tex,
Tag 0E8X (blueprint: lem-sfb-arithmetic-stable-open-bounded).

The geometric-fibre condition is imposed on the existing algebraic-space families.
Scheme representability and a finite locally free projective-bundle embedding are
conclusions. The base schemes need not be Noetherian, reduced, connected or quasi-compact.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A stable scheme family represents the actual presheaf base change of a proper
algebraic-space family. The isomorphism respects the projection to the test base;
the base isomorphism permits the same family with a different bundled base object.
Source: Stacks Project, moduli-curves.tex, Tag 0E76, scheme tests in section-open
(blueprint: lem-sfb-arithmetic-stable-open-bounded). -/
def StablePointedModuli.RepresentsProperCurvePullback {S : Scheme.{u}} {g : ℕ}
    {T T' : Over S} (Y : StablePointedModuli S g 0) (X : ProperCurveFamily T)
    (a : T' ⟶ T) : Prop :=
  ∃ (b : Y.base ≅ T')
    (e : yoneda.obj (Over.mk (Y.projection ≫ Y.base.hom)) ≅
      Limits.pullback X.projection (yoneda.map a)),
    e.hom ≫ Limits.pullback.snd X.projection (yoneda.map a) =
      yoneda.map ((Over.homMk Y.projection rfl) ≫ b.hom)

/-- Every geometric fibre, as an actual presheaf over its field, is a stable
unpointed genus-g scheme curve. Stability, connectedness, nodality and arithmetic
genus use `StablePointedModuli`, without assuming a schematic total space.
Source: Stacks Project, moduli-curves.tex, Tags 0E76 and 0E78
(blueprint: lem-sfb-arithmetic-stable-open-bounded). -/
def ProperCurveFamily.HasStableGeometricFibres {S : Scheme.{u}} {T : Over S}
    (X : ProperCurveFamily T) (g : ℕ) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ T.left),
    ∃ Y : StablePointedModuli S g 0,
      Y.RepresentsProperCurvePullback X
        (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T)

/-- Stable connected genus-g geometric fibres define a quasi-compact open algebraic
substack of the arithmetic curve stack. Its scheme tests commute with every base
change, and stable families are schemes embedded in finite locally free projective bundles.
Source: Stacks Project, moduli-curves.tex, Tags 0E76, 0E78 and 0E9B; curves.tex, Tag 0E8X
(blueprint: lem-sfb-arithmetic-stable-open-bounded).

Proof, following the eight steps of the DAG node:
1. Apply lem-sfb-arithmetic-nodal-curve-stack-smooth over Spec Z. For any family
restrict to its nonempty nodal open. The scalar-H0 and rank-g stratum of
lem-sfb-curve-h0-genus-strata is precisely its geometrically connected genus-g open.
Both operations commute with arbitrary base change, including the empty base.
2. On this stratum take the relative dualizing line of lem-sfb-nodal-relative-dualizing-line.
Its fibrewise ample locus is the open of lem-sfb-space-relative-ample-locus, which also
makes the total space schematic. By lem-sfb-nodal-canonical-positivity-tricanonical,
ampleness is exactly the genus-zero and genus-one component stability inequalities.
3. The same positivity theorem makes the cube of the dualizing line fibrewise very
ample with H1 zero. Apply lem-sfb-fibrewise-very-ample-evaluation: its direct image is
finite locally free and evaluation embeds the family in its projective bundle over
any base. This argument does not require quasi-compactness or reducedness of the base.
4. These opens have the asserted universal factoring property for all test schemes.
Conversely a stable family is proper by lem-trf-projective-bundle-proper and lies in
these same successive opens. Representing the total space by the stable scheme family
identifies the full subcategory with StablePointedModuli over schemes. Yoneda identifies
all cartesian arrows as well, retaining every automorphism.
5. The open scheme tests give an OpenModuliSubstack, and lem-sfb-open-stack-algebraic-lfp
makes it algebraic. Its containment in the nonempty nodal locus was built into step 1.
6. For boundedness set n = 5g-6 and P(t) = (6g-6)t+1-g. By
lem-sfb-stable-curve-pluricanonical-linear-series each field-valued stable curve embeds
tricanonically in projective n-space with polynomial P. Apply
lem-sfb-projective-hilbert-polynomial-representability. The universal Hilbert family is
proper, flat and finitely presented, and its fibres are nonempty of dimension one by
lem-sfb-projective-hilbert-polynomial-dimension. Steps 1-4 give its stable genus-g open V.
7. The fixed-polynomial Hilbert scheme is of finite type over Spec Z, hence Noetherian
by lem-weil-pbc-finite-type-over-noetherian. Its open V is quasi-compact by
lem-weil-pbc-noetherian-open-subscheme-noetherian. Choosing a basis of tricanonical
sections shows that V maps onto every field-valued stable point class.
8. By lem-sfb-stack-point-topology this map is continuous for the smooth-atlas topology.
Pull an arbitrary open cover back to V, extract a finite subcover there, and use point
surjectivity to descend it to the stable stack. This is CompactSpace of its point space. -/
theorem arithmetic_stable_open_bounded (g : ℕ) (hg : 2 ≤ g) :
    ∃ U : OpenModuliSubstack (ProperCurveModuli.category (Spec (.of (ULift.{u} ℤ)))),
      (∀ X : ProperCurveModuli (Spec (.of (ULift.{u} ℤ))),
        U.property X ↔ X.family.HasStableGeometricFibres g) ∧
      IsAlgebraicModuliStack U.category ∧
      (∀ X : ProperCurveModuli (Spec (.of (ULift.{u} ℤ))),
        U.property X → X.family.HasNonemptyNodalGeometricFibres) ∧
      (∃ W : ∀ X : ProperCurveModuli (Spec (.of (ULift.{u} ℤ))), X.base.left.Opens,
        (∀ (X : ProperCurveModuli (Spec (.of (ULift.{u} ℤ))))
            (T' : Over (Spec (.of (ULift.{u} ℤ)))) (a : T' ⟶ X.base),
          (∃ b : T'.left ⟶ (W X).toScheme, b ≫ (W X).ι = a.left) ↔
            ∃ Y : StablePointedModuli (Spec (.of (ULift.{u} ℤ))) g 0,
              Y.RepresentsProperCurvePullback X.family a) ∧
        (∀ {X Y : ProperCurveModuli (Spec (.of (ULift.{u} ℤ)))} (a : X ⟶ Y),
          W X = TopologicalSpace.Opens.comap ⟨a.base.left, a.base.left.continuous⟩ (W Y)) ∧
        ∀ X : ProperCurveModuli (Spec (.of (ULift.{u} ℤ))),
          ∃ Y : StablePointedModuli (Spec (.of (ULift.{u} ℤ))) g 0,
            Y.RepresentsProperCurvePullback X.family
              (Over.homMk (W X).ι rfl : Over.mk ((W X).ι ≫ X.base.hom) ⟶ X.base) ∧
            ∃ (E : Y.base.left.Modules) (hE : E.IsQuasicoherent),
              E.IsFiniteLocallyFree ∧
                ∃ i : Y.curve ⟶ (@SymmetricAlgebraSheaf.gradedAlgebraData Y.base.left E hE).relProj,
                  IsClosedImmersion i ∧
                    i ≫ (@SymmetricAlgebraSheaf.gradedAlgebraData Y.base.left E hE).relProjHom =
                      Y.projection) ∧
      (∃ e : BasedFunctor
        (BasedCategory.ofFunctor (StablePointedModuli.forget (Spec (.of (ULift.{u} ℤ))) g 0))
        U.category, e.toFunctor.IsEquivalence) ∧
      CompactSpace (ModuliPoints U.category) := by
  sorry

end AlgebraicGeometry
