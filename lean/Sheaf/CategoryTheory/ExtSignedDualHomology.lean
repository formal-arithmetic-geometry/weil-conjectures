module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-! # Ext and an explicit signed dual of a projective resolution

Source: Stacks Project, Tag 0BQZ, computation by the total Hom complex;
Mathlib's ProjectiveResolution.extAddEquivCohomologyClass and
HomComplex.Cochain.toSingleEquiv implement the two comparison steps.
(blueprint: new-j3-ext-signed-dual-homology).
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory.ProjectiveResolution

/-- Any cochain complex identified termwise with the signed dual of a projective
resolution computes Ext. Source: Stacks Project, Tag 0BQZ, total Hom computation.
(blueprint: new-j3-ext-signed-dual-homology).

Proof: Apply ProjectiveResolution.extAddEquivCohomologyClass to P and Y.
A degree-n cochain from P.cochainComplex to Y[0] has only the component from
P_n to Y, since all other target terms are zero. Evaluation at that component
is the additive equivalence Cochain.toSingleEquiv, using P.cochainComplexXIso
to identify degree -n with P_n. The formula Cochain.δ_toSingleMk gives
(-1)^(n+1) times precomposition with d_(n+1) as its differential. The displayed
compatibility hd and the component isomorphisms e identify kernels with the
cycles of L and images with its boundaries. Explicitly, send a cocycle to e_n
inverse applied to its evaluated component; conversely, apply e_n to an
L-cycle and use Cochain.toSingleMk to put it in the unique component. The
cocycle condition follows from hd. For n > 0 the same maps in degree n-1
carry a coboundary to the differential of its image, and conversely lift any
L-boundary to that cochain, by hd. Thus the inverse maps descend to the
quotients and remain inverses. The preceding degree for n = 0
is zero because P.cochainComplex has zero terms in positive degrees, matching
L's zero incoming differential. Pass to the kernel/image quotient to obtain
an additive equivalence with L.homology n.
To check A-linearity, represent an Ext class by P.extMk of a cocycle g.
Ext.smul_eq_comp_mk₀ and ProjectiveResolution.extMk_comp_mk₀ show that
multiplication by a is represented by g followed by a times id_Y, which is a*g.
Component evaluation, each e_i, and passage to the quotient commute with this
scalar multiplication. ExtMk surjectivity proves scalar compatibility on every
class, so the additive equivalence is A-linear. This argument uses neither
Koszul regularity nor an exterior basis: those are used only to produce P. -/
theorem exists_ext_signed_dual_homology_equiv
    (A : Type u) [CommRing A] [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    {X Y : ModuleCat.{u} A} (P : ProjectiveResolution X)
    (L : CochainComplex (ModuleCat.{u} A) ℕ)
    (e : ∀ i, L.X i ≅ ModuleCat.of A (P.complex.X i ⟶ Y))
    (hd : ∀ i, L.d i (i + 1) ≫ (e (i + 1)).hom =
      (e i).hom ≫ ModuleCat.ofHom
        ((-1 : A) ^ (i + 1) • Linear.leftComp A Y (P.complex.d (i + 1) i)))
    (n : ℕ) :
    Nonempty (Abelian.Ext X Y n ≃ₗ[A] L.homology n) := by sorry

end CategoryTheory.ProjectiveResolution
