/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import Sheaf.RingTheory.ReducedPolynomialModuleGenericFreeness
import Sheaf.RingTheory.GeometricReducednessFiniteInseparableTest
import WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.NoetherianSpace
import Mathlib.Order.WellFounded
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-!
# The canonical filtration of separable points by smooth free strata

Source: Bosch–Lütkebohmert–Raynaud, Néron Models, 3.3 Lemma 4 and the proof of
3.4 Theorem 2, printed pp.67, 72–73; the coherent-module generalization of the
restriction of relative differentials (blueprint: lem-sfb-separable-point-cotangent-filtration).

The helpers construct the reduced closure, the largest smooth finite locally free
open, and the remaining points. Index `n` in `remaining` represents the paper's `P_(n+1)`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.SeparablePointCotangentFiltration

variable {k Ks : Type u} [Field k] [Field Ks] {Z : Scheme.{u}}

/-- The closed closure of the images of the specified separable points.
Source: BLR 3.4 Theorem 2 proof, p.72
(blueprint: lem-sfb-separable-point-cotangent-filtration). -/
def closedHull (Q : Set (Spec (.of Ks) ⟶ Z)) : Closeds Z :=
  ⟨closure ((fun p : Spec (.of Ks) ⟶ Z ↦ p (IsLocalRing.closedPoint Ks)) '' Q),
    isClosed_closure⟩

/-- The canonical reduced induced closed subscheme on the closure of `Q`.
Source: BLR 3.4 Theorem 2 proof, p.72; Stacks 01J4
(blueprint: lem-sfb-separable-point-cotangent-filtration). -/
noncomputable def hull (Q : Set (Spec (.of Ks) ⟶ Z)) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal (closedHull Q)).subscheme

/-- The canonical closed immersion of the reduced closure into the ambient scheme.
Source: BLR 3.4 Theorem 2 proof, p.72; Stacks 01J4
(blueprint: lem-sfb-separable-point-cotangent-filtration). -/
noncomputable def hullι (Q : Set (Spec (.of Ks) ⟶ Z)) : hull Q ⟶ Z :=
  (Scheme.IdealSheafData.vanishingIdeal (closedHull Q)).subschemeι

/-- The union of all smooth opens where the pulled-back module is finite locally free;
the finite ranks may vary between neighbourhoods.
Source: BLR 3.4 Theorem 2 proof, p.72, with a coherent module in place of differentials
(blueprint: lem-sfb-separable-point-cotangent-filtration). -/
noncomputable def goodOpen (f : Z ⟶ Spec (.of k)) (M : Z.Modules)
    (Q : Set (Spec (.of Ks) ⟶ Z)) : (hull Q).Opens :=
  sSup {V : (hull Q).Opens | Smooth (V.ι ≫ hullι Q ≫ f) ∧
    (((Scheme.Modules.tensorPullback (hullι Q)).obj M).over V).IsFiniteLocallyFree}

/-- Recursively remove the points landing in the largest smooth finite locally free open.
Here `remaining f M P n` is `P_(n+1)` in the node, so `n = 0` is the initial set.
Source: BLR 3.4 Theorem 2 proof, p.72
(blueprint: lem-sfb-separable-point-cotangent-filtration). -/
noncomputable def remaining (f : Z ⟶ Spec (.of k)) (M : Z.Modules)
    (P : Set (Spec (.of Ks) ⟶ Z)) : ℕ → Set (Spec (.of Ks) ⟶ Z)
  | 0 => P
  | n + 1 => {p ∈ remaining f M P n | p (IsLocalRing.closedPoint Ks) ∉
      hullι (remaining f M P n) '' (goodOpen f M (remaining f M P n) : Set _)}

/-- Evaluation of a section at a `Ks`-valued point landing in its open domain, using the
scheme morphism on sections and the canonical global-sections isomorphism for `Spec Ks`.
Source: BLR 3.3 Lemma 4, schematic density on p.67
(blueprint: lem-sfb-separable-point-cotangent-filtration). -/
noncomputable def evaluation {Y : Scheme.{u}} (q : Spec (.of Ks) ⟶ Y) (V : Y.Opens)
    (hV : ⊤ ≤ q ⁻¹ᵁ V) : Γ(Y, V) →+* Ks :=
  ((q.appLE V ⊤ hV) ≫ (Scheme.ΓSpecIso (.of Ks)).hom).hom

/-- The reduced closures of successive remaining separable points are geometrically
reduced, have dense smooth finite locally free opens, and have jointly injective affine
evaluations. The next closure lies in the complement, the process terminates, and the
successive differences partition the initial points. At the least termination index,
precisely the remaining points lie in the last closure, and they lie in its good open.

Source: BLR 3.3 Lemma 4, p.67; 3.4 Theorem 2 proof, pp.72–73, with a coherent module
in place of the restriction of relative differentials
(blueprint: lem-sfb-separable-point-cotangent-filtration).

Proof (the node's seven steps):
1. Every reduced closed closure is finite type over the field and Noetherian, hence
   locally finitely presented, by finite-type Noetherianity and finite presentation.
2. On an affine open its specified points are dense. Their evaluation kernels intersect
   in a radical ideal whose zero locus is the entire open, hence in zero by reducedness.
3. Expand an element after a finite purely inseparable extension in a finite field basis.
   Joint injectivity of evaluation survives this extension; the target rings are reduced
   by separably-generated tensor reducedness. The finite-inseparable test and the affine
   base-change charts give geometric reducedness after every field extension.
4. Coherence is quasi-coherence of finite type on this Noetherian scheme. These properties
   survive tensor pullback. The affine finite-type criterion and reduced polynomial-module
   generic freeness with zero variables give a dense finite locally free open, using the
   tilde localization theorem. Geometric reducedness gives a dense smooth open. Their
   intersection is the open `goodOpen`, and is dense.
5. The next points avoid this open, so their closed closure lies in its closed complement.
   Radical-ideal inclusion gives the closed immersion of the reduced closures. Whenever
   points remain this descent is strict, since the dense open is nonempty.
6. The minimal-closed-subset property of a Noetherian scheme rules out infinite strict
   descent. Telescoping the recursive differences gives a disjoint partition; for the
   empty initial set the termination index is zero.
7. At the least termination index all last remaining points lie in the last good open.
   A point removed earlier lies in an earlier good open and cannot lie in a later closure,
   by step 5. This proves exactly the claimed final membership equivalence. -/
theorem separable_point_cotangent_filtration (k Ks : Type u) [Field k] [Field Ks]
    [Algebra k Ks] [IsSepClosure k Ks] (Z : Scheme.{u}) (f : Z ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] (M : Z.Modules)
    (hM : RingedSpace.IsCoherent Z.toRingedSpace M) (P : Set (Spec (.of Ks) ⟶ Z))
    (hP : ∀ p ∈ P, p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Ks))) :
    (∀ n : ℕ,
      GeometricallyReduced (hullι (remaining f M P n) ≫ f) ∧
      Dense (goodOpen f M (remaining f M P n) : Set (hull (remaining f M P n))) ∧
      (∀ V : (hull (remaining f M P n)).affineOpens,
        (⨅ (p : Spec (.of Ks) ⟶ Z) (_ : p ∈ remaining f M P n)
          (q : Spec (.of Ks) ⟶ hull (remaining f M P n))
          (_ : q ≫ hullι (remaining f M P n) = p) (hV : ⊤ ≤ q ⁻¹ᵁ V.1),
          RingHom.ker (evaluation q V.1 hV)) = ⊥) ∧
      (∃ j : hull (remaining f M P (n + 1)) ⟶ hull (remaining f M P n),
        IsClosedImmersion j ∧
        j ≫ hullι (remaining f M P n) = hullι (remaining f M P (n + 1)) ∧
        Set.range j ⊆ (goodOpen f M (remaining f M P n) : Set _)ᶜ)) ∧
    (∃ t : ℕ, remaining f M P t = ∅ ∧
      P = ⋃ i : Fin t, remaining f M P i.val \ remaining f M P (i.val + 1) ∧
      Pairwise (fun i j : Fin t ↦ Disjoint
        (remaining f M P i.val \ remaining f M P (i.val + 1))
        (remaining f M P j.val \ remaining f M P (j.val + 1)))) ∧
    (P.Nonempty → ∀ t : ℕ, remaining f M P t = ∅ →
      (∀ s : ℕ, s < t → remaining f M P s ≠ ∅) →
      ∀ p ∈ P,
        (p (IsLocalRing.closedPoint Ks) ∈ Set.range (hullι (remaining f M P (t - 1))) ↔
          p ∈ remaining f M P (t - 1)) ∧
        (p ∈ remaining f M P (t - 1) → p (IsLocalRing.closedPoint Ks) ∈
          hullι (remaining f M P (t - 1)) ''
            (goodOpen f M (remaining f M P (t - 1)) : Set _))) := by
  sorry

end AlgebraicGeometry.SeparablePointCotangentFiltration
