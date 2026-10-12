module

public import Sheaf.RingTheory.KoszulConormalComparison
public import Sheaf.RingTheory.KoszulRegularSequence
import Sheaf.RingTheory.KoszulConormalBasis
import Sheaf.Paper.KoszulComplex
import Sheaf.RingTheory.KoszulDualComplex

/-!
# Construction of the normalized dual Koszul comparison

Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext, local Koszul computation.
(blueprint: new-s3-koszul-conormal-comparison-map).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

/-- A determinant-normalized comparison map exists.
Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext, local computation;
Tag 062I, lemma-H1-regular-quasi-regular, first paragraph, for the conormal basis.
(blueprint: new-s3-koszul-conormal-comparison-map).

Proof: Set E = A^r and B = A/I. By `exists_koszul_conormal_basis`, the classes
c_i of the generators form a B-basis of I/I^2. Let c_i^* be its dual basis,
e_top the ordered wedge of the standard basis of E, and s = (-1)^(r*(r-1)/2).
Send a top-degree functional x to s times its value on e_top reduced modulo I,
times the ordered wedge of the c_i^*. This is A-linear, with the target A-action
restricted from B. Transport it along singleObjXSelf to the degree-r term of
the single complex, and put zero in all other degrees.

The only nontrivial chain-map equation is that the degree-(r-1) differential
is killed. The dual differential is signed precomposition with Koszul d_r;
d_r(e_top) is a signed sum of complementary basis wedges with coefficients f_i.
Thus its evaluation by any functional belongs to I and vanishes in B. The
outgoing differential of the target is zero. These equations give the map phi.

For v_1,...,v_r in E, their top wedge is det(v) times e_top. Their conormal
classes have the same coordinate matrix reduced to B. The determinant pairing
of the ordered dual conormal wedge with their wedge is therefore det(v) mod I.
Multiplying by s and x(e_top) mod I gives exactly IsKoszulConormalComparison.
For r = 0 the empty determinant is 1, I = 0, and this is the identity on A.
For I = A all target modules are zero and the formula still defines the map. -/
theorem exists_koszul_conormal_comparison_map
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I) :
    ∃ φ : koszulDualComplex A r f ⟶
        (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
          (koszulNormalDeterminant A I r),
      IsKoszulConormalComparison A I r f hf φ := by
  sorry

end ExteriorAlgebra
