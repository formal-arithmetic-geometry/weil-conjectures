module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.RingTheory.Artinian.Module
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # Semisimplicity of the source of an isogeny

Source: Milne, Algebraic Groups (2017), Lemma 19.14, printed p.400.
(blueprint: lem-sfb-semisimple-isogeny-invariance)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The source of a faithfully flat homomorphism of smooth connected affine finite-type
 group schemes with finite scheme-theoretic kernel is semisimple when the target is.

Source: Milne, Algebraic Groups (2017), Lemma 19.14, printed p.400.
(blueprint: lem-sfb-semisimple-isogeny-invariance)

Proof plan:
1. Let N be a smooth connected solvable normal closed subgroup of G1. Apply
   lem-sfb-affine-homomorphism-flat-image to its composite with f, obtaining a faithfully
   flat map q : N → I and a closed immersion j : I → G0. By
   lem-sfb-solvable-normal-image-geometry, I is smooth, connected and solvable, and j
   identifies it with a normal closed subgroup of G0.
2. Semisimplicity of G0 makes I trivial. Thus f restricted to N is the identity section
   composed with the structure morphism of N. The pullback defining the scheme kernel
   K = ker f gives a factorization N → K, retaining all scheme structure.
3. On A = F[G1], factorization says that the ideal of K is contained in the ideal of N.
   Hence F[K] → F[N] is surjective and N → K is closed
   (def-weil-closed-immersion). Since F[K] is finite-dimensional, so is B = F[N].
4. Smoothness makes B reduced (sbc-lem-smooth-geometrically-reduced). Descending chains
   of ideals stabilize by finite dimension, so B is Artinian. By
   lem-sfb-reduced-artinian-residue-product, B is the finite product of its residue
   fields. Each is F by clause 1 of lem-wf-affine-nullstellensatz-vanishing.
   The identity section excludes the empty product; connectedness excludes two or more
   factors, since their coordinate idempotents partition Spec B into nonempty clopens.
5. Therefore B is F as an F-algebra, so N is terminal over Spec F and its inclusion is
   the trivial subgroup. Every such N is trivial. The smoothness, connectedness,
   affineness and finite-type conditions on G1 are hypotheses, proving semisimplicity.
   The kernel itself need not be reduced or central. -/
theorem isSemisimpleGroupScheme_of_faithfullyFlat_finite_kernel
    {F : Type u} [Field F] [IsAlgClosed F]
    (G1 G0 : Over (Spec (.of F))) [GrpObj G1] [GrpObj G0]
    [IsAffine G1.left] [IsAffine G0.left]
    [LocallyOfFiniteType G1.hom] [QuasiCompact G1.hom]
    [LocallyOfFiniteType G0.hom] [QuasiCompact G0.hom]
    [Smooth G1.hom] [Smooth G0.hom]
    [ConnectedSpace G1.left] [ConnectedSpace G0.left]
    (f : G1 ⟶ G0) [IsMonHom f] (hff : f.left.appTop.hom.FaithfullyFlat)
    [IsFinite (GrpObj.ker f).hom] (hG0 : IsSemisimpleGroupScheme G0) :
    IsSemisimpleGroupScheme G1 := by
  sorry

end AlgebraicGeometry
