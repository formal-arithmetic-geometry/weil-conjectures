module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-! # Constructible fibre-codimension bounds for a smooth closed pair

Source: Stacks Project, More on Morphisms, Tag 05F9; EGA IV2, Corollary 6.1.4,
printed p.136; the codimension calculation in EGA IV4, 21.14.3(ii)
(blueprint: lem-sfb-smooth-closed-fibre-codimension-locus).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The set `G_c` introduced in the smooth closed-pair codimension statement: the local
ring of the fibre has dimension at least `c` at every point lying in `Z`.
This definition imposes no condition on the base, so it also defines the locus after
an arbitrary base change. Source: EGA IV4, 21.14.3(ii), codimension calculation;
Stacks Project, Tag 05F9
(blueprint: lem-sfb-smooth-closed-fibre-codimension-locus). -/
def Scheme.Hom.fibreCodimensionLocus {X S : Scheme.{u}} (f : X ⟶ S)
    (Z : Set X) (c : ℕ) : Set S :=
  {s | ∀ z : f.fiber s, f.fiberι s z ∈ Z →
    (c : WithBot ℕ∞) ≤ ringKrullDim ((f.fiber s).presheaf.stalk z)}

/-- Constructibility, field-extension invariance, arbitrary base-change compatibility,
and the codimension-one criterion for the locus `G_c` of a smooth closed pair.
Empty fibres and empty inverse images of `Z` satisfy every bound.

Source: Stacks Project, Tags 05F9, 02G1, 02G2, 0A21, 02FY and 02IZ;
EGA IV2, Corollary 6.1.4, printed p.136, and IV4, 21.14.3(ii)
(blueprint: lem-sfb-smooth-closed-fibre-codimension-locus).

Proof:
1. Finite presentation makes `X` Noetherian. Give `Z` a closed subscheme structure.
   The smooth fibre dimension is locally constant (02G1, 02G2), so quasi-compactness
   partitions `X` into finitely many clopen constant-relative-dimension pieces `X_d`.
   Restrict the smooth map and the closed subscheme to each piece.
2. Opens and closed immersions in a Noetherian scheme are of finite presentation
   (lem-sfb-noetherian-open-closed-finite-presentation). Composition and qcqs permanence
   give finite presentation of each restricted closed subscheme `C_d` over `S`.
3. In a fibre `M` of `X_d`, let `W_j` be the finitely many irreducible components of
   the closed subset `A` coming from `C_d`, and let `eta_j` be their generic points.
   The dimension formula (lem-kun-dimension-formula) and the closed irreducible
   dimension/trdeg formula give `dim O_{M,eta_j} = d - dim W_j`. Chains of
   generalizations (02IZ) show that local ring dimension cannot decrease under
   specialization. Thus the all-points bound is equivalent to `dim W_j <= d-c`
   for every component.
4. The dimension of a finite closed union is the maximum of its component dimensions:
   every irreducible closed chain lies in a component containing its largest member.
   Hence for `d >= c` the criterion is `dim A <= d-c`; for `d < c` it is emptiness.
   This also handles empty `A`, whose dimension is minus infinity.
5. By lem-sfb-finite-presentation-fibre-dimension-levels (05F9), each nonnegative
   dimension level of the fibres of `C_d` is constructible. Chevalley makes its image
   constructible, so its empty-fibre locus is constructible too. The good locus is
   that empty-fibre locus together with the finitely many levels from zero to `d-c`
   when `d >= c`. Intersect these constructible sets over the finitely many pieces.
6. A field-extension projection is surjective. Fibre dimension at points is invariant
   under field extension (02FY). Taking suprema of local topological dimensions
   therefore preserves the dimension of a finite-type scheme and detects emptiness.
7. Field extension preserves smooth relative dimension and closedness. Apply the
   criterion of steps 3 and 4 before and after extension; step 6 preserves precisely
   its dimension and emptiness conditions. This gives the all-points equivalence.
8. Over `s'` the base-changed fibre is the original fibre over `v s'` extended to
   `kappa(s')` (02FY). The pullback projections identify the inverse images of `Z`.
   Step 7 gives equality of the loci, without requiring a Noetherian new base.
9. By 02IZ, a local ring has dimension zero exactly at a point with no strict
   generalization. Sobriety identifies these with generic points of components.
   A closed subset contains such a point exactly when it contains its component.
   This gives the criterion for one. The empty cases follow from the universal
   quantifier in the definition of `G_c`; for zero, all local dimensions are nonnegative. -/
theorem smooth_closed_fibre_codimension_locus {X S : Scheme.{u}}
    [IsLocallyNoetherian S] [CompactSpace S] (f : X ⟶ S)
    [Smooth f] [QuasiCompact f] [QuasiSeparated f] (Z : Set X) (hZ : IsClosed Z) (c : ℕ) :
    Topology.IsConstructible (f.fibreCodimensionLocus Z c) ∧
    (∀ (s : S) (K : Type u) [Field K] [Algebra (S.residueField s) K],
      s ∈ f.fibreCodimensionLocus Z c ↔
        ∀ z : ↥(pullback (f.fiberToSpecResidueField s)
            (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)))),
          f.fiberι s (pullback.fst (f.fiberToSpecResidueField s)
            (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K))) z) ∈ Z →
          (c : WithBot ℕ∞) ≤ ringKrullDim
            ((pullback (f.fiberToSpecResidueField s)
              (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)))).presheaf.stalk
                z)) ∧
    (∀ (S' : Scheme.{u}) (v : S' ⟶ S),
      (pullback.snd f v).fibreCodimensionLocus ((pullback.fst f v) ⁻¹' Z) c =
        v ⁻¹' f.fibreCodimensionLocus Z c) ∧
    (∀ s : S, s ∈ f.fibreCodimensionLocus Z 1 ↔
      ∀ W ∈ irreducibleComponents (f.fiber s), ¬ W ⊆ (f.fiberι s) ⁻¹' Z) ∧
    (∀ s : S, IsEmpty (f.fiber s) → s ∈ f.fibreCodimensionLocus Z c) ∧
    (∀ s : S, (f.fiberι s) ⁻¹' Z = ∅ → s ∈ f.fibreCodimensionLocus Z c) := by
  sorry

end AlgebraicGeometry
