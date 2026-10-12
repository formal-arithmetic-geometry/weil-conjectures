module

public import Sheaf.Algebra.Homology.DoubleComplexVerticalTowerMaps

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The positive endpoint reduction for the strict cutoff comparison.
Source: Stacks Project, Homology, Section 12.15, tag 0118.
(blueprint: lem-sp-vertical-cutoff-column-quasiiso-strict-positive)
Proof: put E = L extended by zero and I = image of E.d (a - 1) a.
Monicity of the upper cutoff inclusion forces g to be the canonical nested
inclusion. Degreewise cokernels show that its quotient is zero below a - 1,
is I in degree a - 1, and is the upper cutoff in degrees at least a.
The equation hq makes q zero in degree a - 1, the quotient by I in degree a,
and an isomorphism above a. When b = a + 1, its degree-a component is the
projection from cycles to homology; when b > a + 1, it is the projection from
E.X a to opcycles. Both are epimorphisms with kernel I. Thus q is degreewise
epic, and its kernel has I only in degrees a - 1 and a, with differential
an isomorphism between them. The inverse differential contracts this kernel.
Since 0 < a, both degrees remain after restriction to the naturals. The
homology exact sequence of the kernel-source-window short exact sequence
then makes every homology map of q an isomorphism. This specializes the
canonical truncations of Stacks tag 0118; the kernel argument is agent-written.
-/
theorem verticalCutoff_column_quasiIso_strict_positive
    (L : CochainComplex C ℕ) (a b : ℤ) (hab : a < b) (ha : 0 < a)
    (g : (verticalCutoff a).obj L ⟶ (verticalCutoff b).obj L)
    (hg : g ≫ (verticalCutoffι b).app L = (verticalCutoffι a).app L)
    (q : cokernel g ⟶ (verticalWindow a b).obj L)
    (hq : cokernel.π g ≫ q = HomologicalComplex.restrictionMap
      (CochainComplex.truncLEMap
        (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a) (b - 1))
      ComplexShape.embeddingUpNat) : QuasiIso q := by
  sorry

end HomologicalComplex₂
