module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.ChevalleyCharacterCancellation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # A closed normal subgroup is a representation kernel

Source: Milne, Algebraic Groups (2017), Corollary 5.19, printed p.103,
with Lemma 5.17 and the restriction-of-scalars construction of Proposition 5.18,
printed pp.102--103 (blueprint: lem-sfb-normal-subgroup-representation-kernel).

The kernel identification commutes with the inclusions into G. The explicit formula
uses all commutative k-algebras, so it detects scheme structure, including nilpotents.
Naturality is supplied by composition of scheme morphisms and the natural matrix-point
identification GeneralLinearGroup.homMulEquiv.
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every closed normal subgroup of an affine finite-type group scheme over a field
is the scheme-theoretic kernel of a representation of positive dimension.
Source: Milne, Corollary 5.19, Lemma 5.17 and Proposition 5.18, printed pp.102--103
(blueprint: lem-sfb-normal-subgroup-representation-kernel).

Proof:
1. Over an algebraic closure K, apply lem-sfb-normal-subgroup-character-inversion
   and lem-sfb-chevalley-character-cancellation. They give a rational representation V
   and a line L fixed pointwise by N_K whose stabilizer on every K-algebra is N_K.
2. By lem-sfb-rational-fixed-space-base-change, U = V^(N_K) is a rational
   G_K-subrepresentation, its scalar extensions are the full functorial fixed spaces,
   and N_K acts trivially. Since L is contained in U, a point acting identically on U
   stabilizes L and belongs to N_K. The converse follows from the fixed-space property.
   Choosing a basis of U gives alpha_K into GL_n with n >= 1 and kernel N_K.
3. The finite intermediate extensions L/k in K form a directed system with union K.
   By lem-weil-pbc-spec-colimit-limit their spectra have limit Spec K. The bases are
   affine and qcqs. The schemes G, G times G and GL_n are of finite presentation:
   use lem-pc-affine-finite-type-algebra, the fact that fields are Noetherian,
   lem-weil-pbc-finite-type-noetherian-finite-presentation, and the tensor presentation
   of lem-weil-pbc-fibre-product-affine-spectra. Part (2) of thm-pd-spreading-out
   descends alpha_K to alpha_L over some finite L/k.
4. Part (3) of thm-pd-spreading-out descends the multiplication and unit identities
   after enlarging L; preservation of inverses follows from multiplication. Thus
   alpha_L is a homomorphism. Its kernel is N_L, since their defining ideals become
   equal after tensoring with K and faithful scalar extension of vector spaces detects
   ideal equality. No separability assumption is needed.
5. Choose a k-basis b_s of L of size d. For every k-algebra A, let alpha_L(g_L) act on
   (L tensor A)^n viewed as a free A-module of rank nd with basis b_s e_i. Replace each
   matrix entry by its multiplication matrix in this basis. This constructs a scheme
   homomorphism beta into GL_(nd): the coefficients lie in k[G], the same substitution
   gives its inverse, and the construction commutes with all algebra homomorphisms.
6. This A-linear operator is the identity exactly when alpha_L(g_L) is the identity,
   as is seen on the standard vectors e_i. By step 4 this says g_L belongs to N_L.
   The map A into L tensor A is injective: a k-linear functional t with t(1) = 1
   gives a retraction t tensor id. Hence the defining ideal of N vanishes at g_L
   exactly when it vanishes at g. This gives the stated pointwise kernel equality,
   naturally in A, and therefore an isomorphism N with the scheme-theoretic kernel
   commuting with its inclusion into G. Since n,d >= 1, r = nd >= 1; alternatively
   a trivial summand ensures positive dimension. -/
theorem normal_subgroup_representation_kernel
    {k : Type u} [Field k] (G N : Over (Spec (.of k))) [GrpObj G] [GrpObj N]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (i : N ⟶ G) [IsClosedSubgroupScheme i] [IsNormalSubgroupScheme i] :
    ∃ (r : ℕ), 1 ≤ r ∧
      ∃ (ρ : G ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} r) k)
        (_ : IsMonHom ρ),
        (∃ e : N ≅ GrpObj.ker ρ, e.hom ≫ GrpObj.kerι ρ = i) ∧
        ∀ (A : Type u) [CommRing A] [Algebra k A]
          (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G),
          (∃ h : (Spec (.of A)).asOver (Spec (.of k)) ⟶ N, h ≫ i = g) ↔
            GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} r) k A (g ≫ ρ) =
              1 := by
  sorry

end AlgebraicGeometry
