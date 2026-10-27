module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Topology.Connected.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # Affineness of groups with semisimple geometric fibres

Source: Conrad, Reductive Group Schemes, proof of Proposition 6.3.16, printed p.229.
(blueprint: lem-sfb-relative-semisimple-affineness)

The geometric fibre carries the canonical group structure transported by the
pullback functor, rather than an independently specified group law.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth separated group of finite presentation over a one-dimensional Noetherian
normal domain is affine if all its geometric fibres are connected affine semisimple groups.
Source: Conrad, Reductive Group Schemes, proof of Proposition 6.3.16, printed p.229.
(blueprint: lem-sfb-relative-semisimple-affineness)

Proof:
1. Apply lem-sfb-smooth-group-relative-adjoint to H over Spec B. It constructs the finite
   projective tangent module E and the finite-type adjoint homomorphism a : H → GL(E).
   The target is smooth, separated, affine and of finite presentation. No affineness
   assumption on H is used in this construction.
2. The base-change clause of that lemma identifies a on each geometric fibre with its
   usual adjoint representation. Apply lem-sfb-semisimple-adjoint-kernel-finite to the
   assumed semisimple fibre to see that its scheme-theoretic kernel is finite. This
   includes positive characteristic; the kernel is not asserted smooth or reduced.
3. By lem-pc-smooth-flat the source and target are flat, and their finite presentations
   imply finite type. Apply lem-sfb-dedekind-finite-kernel-hom-affine to a, using the
   given Noetherian integrally closed one-dimensional domain and the finite kernels
   of step 2. Thus a is affine.
4. Compose a with the affine structure morphism GL(E) → Spec B and apply
   lem-weil-pbc-affine-composition. Their composite is H's structure morphism.
   The argument includes the trivial group, for which E = 0. -/
theorem isAffineHom_of_semisimple_geometricFibres
    (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (hdim : ringKrullDim B = 1)
    (H : Grp (Over (Spec (.of B))))
    [Smooth H.X.hom] [IsSeparated H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] [QuasiCompact H.X.hom] [QuasiSeparated H.X.hom]
    (hgeom : ∀ (k : Type u) [Field k] [IsAlgClosed k] (φ : B →+* k),
      IsSemisimpleGroupScheme
        (((Over.pullback (Spec.map (CommRingCat.ofHom φ))).mapGrp.obj H).X)) :
    IsAffineHom H.X.hom := by
  sorry

end AlgebraicGeometry
