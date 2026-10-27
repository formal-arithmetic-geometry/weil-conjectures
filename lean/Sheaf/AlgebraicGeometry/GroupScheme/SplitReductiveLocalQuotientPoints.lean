module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Connected.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Sheaf.AlgebraicGeometry.GroupScheme.SplitReductiveLocalGaussAtlas
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Scheme

/-! # Split reductive points lift across local quotients

Source: Alper--Halpern-Leistner--Heinloth, Cartan--Iwahori--Matsumoto decompositions,
Theorem 4.1, proof, p.7, approximation input; the DAG strengthens this input using
the relative Gauss atlas and explicit coordinate lifting. Open factorization uses
Stacks Project, Tag 01J6, final paragraph of the proof.
(blueprint: lem-sfb-split-reductive-local-quotient-points).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- Reduction is surjective on points of a reductive group with a specified split
geometrically maximal torus over a nonzero Noetherian local ring. The source of an
A-point is the terminal A-scheme; the quotient point is obtained by precomposing
with the structure morphism Spec(A/J) → Spec A, via `toUnit`.

Source: AHLH, Theorem 4.1, proof, p.7 (approximation input, strengthened in the DAG);
Stacks Project, Tag 01J6, final proof paragraph
(blueprint: lem-sfb-split-reductive-local-quotient-points).

Proof plan:
1. Apply lem-sfb-split-reductive-local-gauss-atlas to obtain finitely many open
   charts Spec A[x_1,...,x_d,z_1^±,...,z_r^±] → H covering H.
2. Set B = A/J. Since J lies in the maximal ideal, B is nonzero local with maximal
   ideal m/J. For h : Spec B → H over A, choose a chart containing the image of
   the closed point. Its inverse image is an open containing the closed point of
   Spec B, hence the whole spectrum: a basic open D(b) containing that point has
   b a unit. Factor h through that open chart using def-weil-open-immersion,
   as in the final paragraph of Stacks 01J6.
3. By def-weil-affine-spectrum the factored point is an A-algebra map from the
   chart ring to B. Lift the polynomial coordinates arbitrarily. For each Laurent
   coordinate u_bar, lift it and its inverse to u,v in A. Then uv = 1+j with j in
   J. Since j lies in m, 1+j lies outside m and is a unit, so u is a unit with
   inverse v(1+j)⁻¹. These coordinates define an A-algebra map to A whose reduction
   is the original map, by equality on constants and all generators.
4. Contravariant functoriality of def-weil-affine-spectrum gives an A-point of
   the chart reducing to the factored point. Compose with the chart to lift h.
   The empty coordinate lists, J=0, J=m and the trivial group are included;
   neither henselianity, completeness nor nilpotence of J is used.
-/
theorem splitReductive_local_quotient_points
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (J : Ideal A) (hJ : J ≤ IsLocalRing.maximalIdeal A)
    (H S : Grp (Over (Spec (.of A))))
    [Smooth H.X.hom] [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    (i : S ⟶ H) [IsClosedImmersion i.hom.hom.left]
    (r : ℕ) (e : S ≅ RingGroupSchemes.splitTorus A r)
    (hred : ∀ (F : Type u) [Field F] [IsAlgClosed F] (f : A →+* F),
      ReductiveTorusCentralizer.IsReductive
        ((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.obj H))
    (hmax : ∀ (F : Type u) [Field F] [IsAlgClosed F] (f : A →+* F),
      ReductiveTorusCentralizer.IsMaximalTorus
        ((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.map i)) :
    Function.Surjective
      (fun g : 𝟙_ (Over (Spec (.of A))) ⟶ H.X ↦
        toUnit (Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) ≫ g) := by
  sorry

end AlgebraicGeometry
