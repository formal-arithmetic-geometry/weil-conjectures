module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Monoidal.Grp
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis
import Sheaf.AlgebraicGeometry.GroupScheme.TangentDimensionSmoothness
import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-! # Smooth normalizers of subgroups containing a Cartan subgroup

Source: Milne, Algebraic Groups (2017), Lemma 17.47, printed p.366;
Proposition 1.83, pp.30--31; Proposition 10.34, pp.197--198.
(blueprint: lem-sfb-cartan-containing-normalizer-smooth)

The normalizer is characterized on every algebra and every further algebra extension.
The equality of identity components is an isomorphism commuting with their inclusions
into the ambient group, so it identifies their subgroup scheme structures.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- The normalizer of a smooth subgroup containing a maximal-torus centralizer is
smooth and has the same identity component as that subgroup.
Source: Milne, Lemma 17.47, p.366, Proposition 1.83, pp.30--31, and
Proposition 10.34, pp.197--198.
(blueprint: lem-sfb-cartan-containing-normalizer-smooth)

Proof plan, following the node's eight steps:
1. Affine groups are separated: their diagonals correspond to the surjections
   R tensor R to R. Use lem-weil-pbc-fibre-product-affine-spectra,
   def-weil-closed-immersion and def-weil-proper-morphism.
2. Apply lem-sfb-constant-source-closed-factorization-locus to conjugation and
   inverse conjugation of H in G. Intersect the two closed loci using the sum of
   their ideals. This gives an affine finite-type closed subscheme N of G.
3. Test factorization on the universal H-point after base extension. The two
   containments are equality of conjugate subgroup functors over every algebra,
   including nonreduced ones. This condition is preserved by multiplication and
   inverse, and contains H, so N is a closed subgroup scheme.
4. By lem-sfb-torus-centralizer-smooth-connected and
   lem-sfb-lie-normalizer-centralizer-invariants, Lie(C_G(T)) = g^T lies in h,
   and n/h = (g/h)^H. Also T lies in C_G(T), hence in H.
5. Apply lem-sfb-gm-representation-weight-basis successively to the coordinates
   of the split torus. The commuting actions give a simultaneous weight
   decomposition, including rank zero. Universal Laurent coefficients show
   that h decomposes by the same weights and that g^T is the zero-weight space.
6. The zero-weight space of g/h vanishes because g^T lies in h. Thus its
   H-invariants, being T-invariant, vanish too, and n = h.
7. Use lem-sfb-group-tangent-dimension-smoothness: dim h = dim H is at most
   dim N, which is at most dim n = dim h. Hence N is smooth and dim N = dim H.
8. By lem-sfb-group-neutral-component-translates the identity components have
   equal dimension. By lem-sfb-locally-algebraic-group-identity-component the
   identity component of N is irreducible. Apply lem-wf-affine-dimension-drop
   to rule out a proper closed image of H's identity component. Smoothness
   gives reducedness by sbc-lem-smooth-geometrically-reduced; uniqueness in
   lem-weil-pbc-reduced-induced-closed-subscheme identifies their scheme structures.
-/
theorem cartanContaining_normalizer_smooth
    (F : Type u) [Field F] [IsAlgClosed F]
    (G T H : Grp (Over (Spec (.of F))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    [Smooth H.X.hom]
    (iT : T ⟶ G) (iH : H ⟶ G)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    [IsClosedSubgroupScheme iH.hom.hom]
    (hcontains : ∀ (A : Type u) [CommRing A] [Algebra F A],
      ReductiveTorusCentralizer.centralizerPoints iT A ⊆
        Set.range (fun h : StandardGroupSchemes.affine F A ⟶ H.X ↦ h ≫ iH.hom.hom)) :
    ∃ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ G),
      IsClosedSubgroupScheme iN.hom.hom ∧ IsAffine N.X.left ∧
      ∃ (_ : LocallyOfFiniteType N.X.hom) (_ : QuasiCompact N.X.hom),
        Smooth N.X.hom ∧
        (∀ (A : Type u) [CommRing A] [Algebra F A],
          Set.range (fun n : StandardGroupSchemes.affine F A ⟶ N.X ↦ n ≫ iN.hom.hom) =
            {g : StandardGroupSchemes.affine F A ⟶ G.X |
              ∀ (B : Type u) [CommRing B] [Algebra F B] (f : A →ₐ[F] B),
              (fun h : StandardGroupSchemes.affine F B ⟶ G.X ↦
                (StandardGroupSchemes.map F f ≫ g) * h *
                  (StandardGroupSchemes.map F f ≫ g)⁻¹) ''
                    Set.range (fun h : StandardGroupSchemes.affine F B ⟶ H.X ↦
                      h ≫ iH.hom.hom) =
                    Set.range (fun h : StandardGroupSchemes.affine F B ⟶ H.X ↦
                      h ≫ iH.hom.hom)}) ∧
        ∃ e : GrpObj.identityComponent H.X ≅ GrpObj.identityComponent N.X,
          e.hom ≫ GrpObj.identityComponentι N.X ≫ iN.hom.hom =
            GrpObj.identityComponentι H.X ≫ iH.hom.hom := by
  sorry

end AlgebraicGeometry
