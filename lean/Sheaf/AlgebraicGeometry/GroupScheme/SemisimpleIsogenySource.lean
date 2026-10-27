module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! # Semisimplicity ascends along isogenies

Source: Milne, Algebraic Groups (2017), Lemma 19.14, printed p.400, semisimple case.
(blueprint: lem-sfb-semisimple-isogeny-source)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A faithfully flat homomorphism of smooth connected affine groups of finite type
with finite-dimensional kernel coordinate algebra has semisimple source when its
target is semisimple. The kernel may be nonreduced and need not be central.

Source: Milne, Algebraic Groups (2017), Lemma 19.14, printed p.400, semisimple case.
(blueprint: lem-sfb-semisimple-isogeny-source)

Proof:
Apply lem-sfb-semisimple-isogeny-invariance with G1 = H1, G0 = H2 and the given f.
The smoothness, connectedness, affineness and finite-type hypotheses agree exactly.
Faithful flatness is faithful flatness of the coordinate-algebra map; finite kernel
means finite-dimensionality of its coordinate algebra with the canonical F-action.
Both statements use the same semisimplicity predicate: every smooth connected
solvable normal closed subgroup is trivial, with solvability defined by termination
of the scheme-theoretic derived series. Its conclusion is therefore precisely that
H1 is semisimple. No smoothness, reducedness or centrality of the kernel is used.
-/
theorem semisimpleGroupScheme_of_faithfullyFlat_finite_kernel
    {F : Type u} [Field F] [IsAlgClosed F]
    (H1 H2 : Over (Spec (.of F))) [GrpObj H1] [GrpObj H2]
    [Smooth H1.hom] [Smooth H2.hom]
    [ConnectedSpace H1.left] [ConnectedSpace H2.left]
    [IsAffine H1.left] [IsAffine H2.left]
    [LocallyOfFiniteType H1.hom] [QuasiCompact H1.hom]
    [LocallyOfFiniteType H2.hom] [QuasiCompact H2.hom]
    (f : H1 ⟶ H2) [IsMonHom f]
    (hflat : f.left.appTop.hom.FaithfullyFlat)
    (hfinite : @Module.Finite F Γ((GrpObj.ker f).left, ⊤) _ _
      (GrpObj.ker f).hom.ΓAlgebra.toModule)
    (hH2 : IsSemisimpleGroupScheme H2) : IsSemisimpleGroupScheme H1 := by
  sorry

end AlgebraicGeometry
