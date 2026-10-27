module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.AlgebraicGeometry.DensePoints
import Sheaf.RingTheory.HenselianSmoothAlgebraLifting

/-! # Integral translates of the fibrewise identity subgroup

Source: component argument for BLR, Neron Models, 10.1 Proposition 7, pp. 292-293;
Stacks Project, Tags 056U, 0363 and 0H74
(blueprint: lem-sfb-strict-local-group-component-translates).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- Integral translates of the open subgroup representing geometric identity components
cover a smooth separated group over a strictly henselian DVR with connected generic fibre.
Every point over a nonzero local D-algebra therefore lies in one integral translate.

Source: component input to BLR, Neron Models, 10.1 Proposition 7, pp. 292-293;
Stacks Project, Tags 056U, 0363 and 0H74
(blueprint: lem-sfb-strict-local-group-component-translates).

Proof:
1. Put k = D/m. Strict henselianity makes k separably closed. The smooth special fibre
is locally of finite type, hence locally Noetherian by pqf-lem-locnoeth-lft.
Its affine open neighbourhoods are Noetherian by pqf-lem-affine-open-locnoeth and
lem-sc-affine-noetherian-underlying-space. Their components are open by
lem-sfb-noetherian-connected-components-open, so the special fibre's components are open.
2. The special fibre of Q is the identity component: after an algebraic closure it is
so by assumption. Surjectivity of field extension and base change
(lem-pc-field-extension-surjective, lem-weil-pbc-surjective-base-change) descends
connectedness and inclusions. Conversely the identity component is geometrically
connected over k by lem-weil-separably-closed-geometrically-connected.
3. Each nonempty open component is smooth by
lem-weil-pbc-smooth-restrict-open-subschemes. By lem-pc-dense-separable-points it has a
closed point with finite separable residue extension, which is k since k is separably
closed. Thus every component has a k-point.
4. Choose an affine open neighbourhood of this point in M. The point factors through
it by lem-weil-pbc-morphism-factors-through-open-subscheme. Its algebra is smooth over
D by lem-weil-pbc-smooth-ring-map-iff-smooth-affine. Apply
lem-trf-henselian-smooth-algebra-lifting to lift the k-point to m in M(D).
5. Left translation by m is an isomorphism with inverse translation by its inverse.
It sends Q_k to the chosen special-fibre component. Hence the translates cover the
special fibre. They cover the generic fibre since Q_F = M_F. A DVR has only its generic
and closed points (lem-weil-pbc-dvr-unit-times-uniformizer-power), so they cover M.
Their maps are open immersions, and their images are open.
6. For a local map D to nonzero local C, choose a translate containing the image under
z of the closed point of Spec C. Every open neighbourhood of that closed point is all
of Spec C: a basic open neighbourhood is defined by a unit. Thus z factors through
the translate by lem-weil-pbc-morphism-factors-through-open-subscheme. Inverse
translation gives u in Q(C), and the group diagrams give z = m_C u. -/
theorem strictLocalGroup_component_translates
    (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [IsStrictlyHenselianLocalRing D]
    (F : Type u) [Field F] [Algebra D F] [IsFractionRing D F]
    (M Q : Over (Spec (.of D))) [GrpObj M] [GrpObj Q]
    [Smooth M.hom] [LocallyOfFiniteType M.hom]
    [IsClosedImmersion (pullback.diagonal M.hom)]
    (i : Q ⟶ M) [IsMonHom i] [IsOpenImmersion i.left]
    (_hgeneric : ∀ (K : Type u) [Field K] (ψ : F →+* K),
      ConnectedSpace (pullback M.hom
        (Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap D F)))) : Scheme.{u}))
    (_hcomponents : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (φ : D →+* Ω),
      (pullback.fst M.hom (Spec.map (CommRingCat.ofHom φ))) ⁻¹' Set.range i.left =
        connectedComponent
          ((sectionBaseChange M.hom (η[M]).left (η[M]).w
            (Over.mk (Spec.map (CommRingCat.ofHom φ)))) (default : Spec (.of Ω)))) :
    (∀ m : 𝟙_ (Over (Spec (.of D))) ⟶ M,
      IsOpen (Set.range (((toUnit Q ≫ m) * i).left))) ∧
    (⋃ m : 𝟙_ (Over (Spec (.of D))) ⟶ M,
      Set.range (((toUnit Q ≫ m) * i).left)) = Set.univ ∧
    ∀ (C : Type u) [CommRing C] [IsLocalRing C] [Nontrivial C]
      (φ : D →+* C) [IsLocalHom φ]
      (z : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ M),
      ∃ (m : 𝟙_ (Over (Spec (.of D))) ⟶ M)
        (u : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ Q),
        z = (toUnit (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫ m) * (u ≫ i) := by
  sorry

end AlgebraicGeometry
