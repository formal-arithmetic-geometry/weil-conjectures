/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.Modules.Ample
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAmpleLocal
import Sheaf.AlgebraicGeometry.AmpleIffNormalizedComponentDegreePos
import Sheaf.TraceFormula.AmpleNeighbourhood
import Sheaf.TraceFormula.ProjectiveBundleSeparated
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple

/-! # Positive fibre degrees give a projective-bundle embedding

Source: Stacks Project, Varieties, Tag 0B5Y; More on Morphisms, Tag 0D2S;
Morphisms, Tags 01VR and 01VU; Cohomology of Schemes, Tag 02O5
(blueprint: lem-trf-proper-fibrewise-ample-projective).

Reduced components are represented by integral closed immersions whose images are
irreducible components. The degree is taken on their actual normalization. The
projective bundle uses the canonical symmetric graded algebra. Its degree-one twist
is specified by the existing normalized and compatible affine twist charts.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The degree of the pullback of L to the normalization of a component of a geometric
fibre. Its field structure map is the normalization map, component inclusion and fibre
projection, in that order. This is an explicit use of the recorded degree and normalization.
Source: Stacks Project, Varieties, Tags 0AYR and 0B5Y
(blueprint: lem-trf-proper-fibrewise-ample-projective). -/
noncomputable def normalizedFibreComponentDegree {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : Y.Modules) (K : Type u) [Field K] (x : Spec (.of K) ⟶ X)
    {Z : Scheme.{u}} [IsIntegral Z] (i : Z ⟶ pullback f x) : ℤ :=
  @Scheme.Modules.degree K _ Z.normalization
    ⟨Z.fromNormalization ≫ i ≫ pullback.snd f x⟩
    ((Scheme.Modules.pullback (Z.fromNormalization ≫ i ≫ pullback.fst f x)).obj L)

/-- Positive degrees on the normalized one-dimensional components of all geometric fibres
make an invertible module relatively ample and give a projective-bundle closed embedding.
The module O1 in the conclusion is the degree-one twist, specified by the normalized
compatible charts TautologicalTwistData on the canonical relative Proj of Sym(E).
Source: Stacks Project, Tags 0B5Y, 0D2S, 01VR, 01VU and 02O5
(blueprint: lem-trf-proper-fibrewise-ample-projective).

Proof:
1. Proper base change preserves properness. Each geometric fibre is of finite type over
   a field, hence Noetherian (lem-pc-proper-base-change and
   lem-weil-pbc-finite-type-over-noetherian). Reduction preserves its components.
2. Apply lem-trf-fibre-degree-ample-criterion to the geometric fibre and the positive
   normalized component degrees. Descend ampleness to the residue-field fibre by
   lem-pc-very-ample-descends. Zero-dimensional fibres have no degree tests.
3. Apply lem-trf-ample-neighbourhood at each point. Choose a finite affine refinement by
   quasi-compactness; lem-trf-algebraic-space-ample-local gives ampleness on the preimage
   of every affine base open.
4. Apply lem-trf-relative-ample-very-ample to obtain a positive common tensor power.
   Its evaluation map gives the immersion into P(f_*L^n) and pulls O(1) back to L^n.
5. The tensor power is locally free of rank one. On Noetherian affines its relation
   kernels are finite by lem-weil-pbc-noetherian-submodule-finite. Glue coherence by
   lem-weil-pbc-coherent-module-local-on-open-cover. Proper coherent pushforward
   lem-pc-coherent-hi makes E finite type and quasi-coherent. The ambient projective
   bundle is separated by lem-trf-projective-bundle-separated; thus
   lem-weil-pbc-proper-to-separated and lem-weil-pbc-proper-immersion-closed make the
   evaluation immersion closed.
6. These witnesses give the claimed tensor-power embedding and, by its recorded
   definition def-trf-projective-bundle-morphism, projective-bundle projectivity. -/
theorem proper_fibrewise_ample_projective {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (f : Y ⟶ X) [IsProper f]
    (L : Y.Modules) [L.IsInvertible]
    (hdim : ∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ X),
      topologicalKrullDim ↥(pullback f x) ≤ 1)
    (hdegree : ∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ X)
      (Z : Scheme.{u}) [IsIntegral Z] (i : Z ⟶ pullback f x),
      IsClosedImmersion i → Set.range i ∈ irreducibleComponents ↥(pullback f x) →
      topologicalKrullDim Z = 1 → 0 < normalizedFibreComponentDegree f L K x i) :
    (∀ U : X.Opens, IsAffineOpen U →
      Scheme.Modules.IsAmple (f ⁻¹ᵁ U).toScheme
        ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj L)) ∧
    (∃ n : ℕ, 0 < n ∧ ∃ (E : X.Modules) (hE : E.IsQuasicoherent), E.IsFiniteType ∧
      ∃ i : Y ⟶ (@SymmetricAlgebraSheaf.gradedAlgebraData X E hE).relProj,
        IsClosedImmersion i ∧
        i ≫ (@SymmetricAlgebraSheaf.gradedAlgebraData X E hE).relProjHom = f ∧
        ∃ O1 : (@SymmetricAlgebraSheaf.gradedAlgebraData X E hE).relProj.Modules,
          Nonempty (TautologicalTwistData X
            (@SymmetricAlgebraSheaf.gradedAlgebraData X E hE) O1) ∧
          Nonempty ((Scheme.Modules.pullback i).obj O1 ≅ L.tensorPow n)) ∧
    IsProjectiveBundle f := by
  sorry

end AlgebraicGeometry
