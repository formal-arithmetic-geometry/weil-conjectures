module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Sheaf.RingTheory.PrincipalRegularLocalCompletionDVR
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import WeilConjectures.RingTheory.FlatLocalExtensionGivenResidueField

/-! # Potential finite smooth covers of group schemes over traits

Source: Prasad--Yu, On quasi-reductive group schemes, Proposition 3.1, first paragraph,
and Conrad's Appendix, Corollary A.4 and the reduction after Lemma A.9
(blueprint: lem-sfb-trait-group-finite-smooth-cover).

The group scheme is a group object over the trait. Its base change uses the canonical
finite-product-preserving pullback functor, including its induced group operations.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A separated flat finite-type group scheme over a DVR admits, after a faithfully flat
injective local extension to a strictly henselian DVR with algebraically closed residue field,
a finite surjective homomorphism from a separated smooth finite-type group scheme.
The extension of traits is also explicitly a singleton fpqc covering.

Source: Prasad--Yu, Proposition 3.1, first paragraph (p.5); Conrad, Appendix Corollary A.4
(p.29), Remark A.1, and the residue-field extension after Lemma A.9 (pp.31--32)
(blueprint: lem-sfb-trait-group-finite-smooth-cover).

Proof:
1. Choose a uniformizer pi and an algebraic closure of the residue field. Apply
lem-weil-pbc-flat-local-extension-given-residue-field to obtain a flat local algebra T
with maximal ideal pi T and that residue field. Flatness makes pi regular in T.
By lem-sfb-principal-regular-local-completion-dvr its completion D is a complete DVR
with the same residue field. The local map R -> D is injective: each nonzero element
of R is a unit times a power of pi, whose image is nonzero in D.
2. Base change G to D. Flatness, separatedness and finite type persist by
lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-separated-base-change and
lem-sfb-finite-type-composition-base-change. The pullback functor carries the group
operations and their diagrams to the base change. Apply
lem-sfb-complete-trait-normalized-reduced-fibres to obtain a finite extension of Frac D,
its complete DVR V, the reduction H of G_V, and its finite surjective normalization
nu : N -> H. Both H and N are flat separated finite-type V-schemes; H has geometrically
reduced generic fibre and N has geometrically reduced special fibre.
3. Apply lem-sfb-trait-normalization-group-structure to give H and N their compatible
group laws and identify their generic fibres. Both fibres of N are geometrically
reduced finite-type groups, hence smooth by lem-sfb-geometrically-reduced-group-smooth.
4. Finite type over the Noetherian DVR V implies local finite presentation by
lem-weil-pbc-finite-type-noetherian-finite-presentation. The two fibres are smooth,
so sbc-lem-smooth-criterion makes N smooth over V.
5. Compose nu with H -> G_V. The reduction inclusion is surjective and a closed
immersion by lem-weil-pbc-reduction-universal-homeomorphism, hence finite by
lem-weil-pbc-closed-immersion-finite. By lem-weil-pbc-finite-composition the composite
q is finite; it is surjective and a group homomorphism because both factors are.
6. Put R' = V. The local injection R -> D -> V is torsion free, hence flat by
lem-weil-pbc-pid-torsion-free-module-flat and faithfully flat by
lem-weil-pbc-flat-local-hom-faithfully-flat. Its spectrum map is flat by
lem-weil-pbc-flat-ring-map-iff-flat-affine and surjective. It is an affine morphism,
hence quasi-compact, so its singleton is an fpqc covering by def-weil-pbc-fpqc-covering.
7. Completeness makes V henselian by lem-weil-pbc-complete-pair-henselian. Its residue
field is finite over the algebraically closed residue field of D, hence is that field.
It is therefore algebraically closed, and V is strictly henselian by
def-weil-pbc-henselian-terminology. No affineness, generic smoothness, connectedness,
or excellence assumption is used. -/
theorem exists_trait_group_finite_smooth_cover
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (G : Grp (Over (Spec (.of R))))
    [Flat G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R')
      (_ : IsDiscreteValuationRing R') (_ : Algebra R R'),
      Function.Injective (algebraMap R R') ∧
      IsLocalHom (algebraMap R R') ∧
      Module.FaithfullyFlat R R' ∧
      IsStrictlyHenselianLocalRing R' ∧
      IsAlgClosed (IsLocalRing.ResidueField R') ∧
      Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧
      Presieve.singleton (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∈
        Scheme.fpqcPrecoverage (Spec (.of R)) ∧
      ∃ (N : Grp (Over (Spec (.of R')))),
        IsSeparated N.X.hom ∧ LocallyOfFiniteType N.X.hom ∧ QuasiCompact N.X.hom ∧
        Smooth N.X.hom ∧
        ∃ q : N ⟶ (Over.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap R R')))).mapGrp.obj G,
          IsFinite q.hom.hom.left ∧ Surjective q.hom.hom.left := by
  sorry

end AlgebraicGeometry
