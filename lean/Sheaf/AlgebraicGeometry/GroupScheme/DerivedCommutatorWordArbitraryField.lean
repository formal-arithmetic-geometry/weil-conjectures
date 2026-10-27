module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.AlgebraicGeometry.GroupScheme.AffinePointedMapGeneratedSubgroup
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Group.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Derived subgroups and dominant commutator words over arbitrary fields

Source: Milne, Algebraic Groups (2017), Corollary 6.19(b),(d),(e),
Propositions 6.20(a) and 6.21, pp.129--130; Theorem 16.58, p.345.
(blueprint: lem-sfb-derived-commutator-word-arbitrary-field)

The existing derived-subgroup predicate retains minimality among closed subgroups.
The existing pointed word map on `n + 1` copies of `G × G` is the ordered product
of `n + 1` commutators, with source canonically `G` to the power `2 * (n + 1)`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The derived subgroup of a smooth geometrically connected affine finite type group
exists over any field. A positive finite commutator word dominates it, its inclusion
commutes with field extension, and it is the kernel of the commutative quotient.
The index `n` denotes the positive word length `r = n + 1`.

Source: Milne, Corollary 6.19(b),(d),(e), Propositions 6.20(a) and 6.21,
pp.129--130; Theorem 16.58, p.345.
(blueprint: lem-sfb-derived-commutator-word-arbitrary-field)

Proof:
1. For X = G × G the commutator c is pointed and inversion stable, since
   c(x,y) inverse equals c(y,x). Smooth base change (lem-pc-proper-base-change)
   and smooth composition (lem-trf-smooth-composition) make X smooth.
   The node sbc-lem-smooth-geometrically-reduced makes it geometrically reduced;
   lem-weil-pbc-geometrically-connected-product-components gives its geometric
   connectedness. The identity tuple gives nonemptiness.
2. Apply lem-sfb-affine-pointed-map-generated-subgroup: the intersection I of
   the kernels I_n of positive commutator words defines the smallest closed
   subgroup D = Spec(k[G]/I), geometrically reduced and geometrically connected.
   It is smooth by lem-sfb-geometrically-reduced-group-smooth.
3. For every K/k choose a k-basis of K. Comparing its finitely many coefficients
   in each tensor gives ker(w_n tensor K) = I_n tensor K, identifies quotient
   coordinate rings, and reflects equality of extended ideals. Use the affine
   pullback formula lem-weil-pbc-fibre-product-affine-spectra. No infinite
   intersection is exchanged with tensor product.
4. Choose an algebraic closure (lem-pc-algebraic-closure-exists-unique).
   Apply lem-sfb-pointed-word-kernel-stabilization there to c with exponent 2.
   Descend eventual equality of the I_n using step 3. Inserting identity pairs
   gives a descending chain, hence I = I_N for some N at least 1. The induced
   word G^(2N) to D has injective coordinate pullback.
5. The same calculation after every K/k gives the defining ideal I_N tensor K
   for the derived subgroup of G_K. Thus the pulled-back inclusion is derived.
   Over the algebraic closure the word is dense by stabilization. Descend density
   along D over the algebraic closure to D, using
   lem-weil-pbc-field-extension-base-change-faithfully-flat and
   lem-weil-pbc-faithfully-flat-surjective-spectrum: every nonempty open pulls
   back to a nonempty open and meets the word image. Set n = N - 1.
6. On every k-algebra R, for g in G(R) and d in D(R), the commutator [g,d]
   belongs to D(R), so gdg inverse = [g,d]d belongs to D(R). Apply the same
   argument to g inverse. This is normality in def-sc-group-scheme-subgroup,
   including nonreduced test algebras.
7. Any homomorphism to a commutative affine finite type group kills all words.
   Injectivity of the word pullback from step 4 implies that its restriction
   to D is identity valued: the difference of the two pullbacks of each target
   coordinate vanishes. Use def-weil-affine-spectrum to recover map equality.
8. Apply lem-sfb-affine-normal-quotient-geometry to D in G. Two quotient
   sections lift to G after a common fppf refinement. Their commutator is
   identity since commutators lie in the kernel D. Sheaf descent proves the
   quotient commutative. If G is commutative, c factors through the identity
   subgroup; minimality makes D that subgroup, canonically Spec k. This also
   includes the trivial group, where the length-one word has dense image. -/
theorem exists_derived_commutator_word_arbitrary_field
    {k : Type u} [Field k] (G : Grp (Over (Spec (.of k))))
    [Smooth G.X.hom] [GeometricallyConnected G.X.hom]
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] :
    ∃ (D : Grp (Over (Spec (.of k)))) (i : D ⟶ G),
      IsDerivedGroupScheme i.hom.hom ∧
      IsNormalSubgroupScheme i.hom.hom ∧
      Smooth D.X.hom ∧ GeometricallyConnected D.X.hom ∧
      IsAffine D.X.left ∧ LocallyOfFiniteType D.X.hom ∧ QuasiCompact D.X.hom ∧
      (∃ (n : ℕ) (w : (∏ᶜ fun _ : Fin (n + 1) ↦ G.X ⊗ G.X) ⟶ D.X),
        w ≫ i.hom.hom = affinePointedWordMap (groupSchemeCommutator G.X) n ∧
        DenseRange w.left) ∧
      (∀ (K : Type u) [Field K] [Algebra k K],
        IsDerivedGroupScheme
          (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.map
            i).hom.hom)) ∧
      (∀ (C : Grp (Over (Spec (.of k)))) [IsCommMonObj C.X]
        [IsAffine C.X.left] [LocallyOfFiniteType C.X.hom] [QuasiCompact C.X.hom]
        (f : G ⟶ C), i.hom.hom ≫ f.hom.hom = 1) ∧
      (∃ (Q : Grp (Over (Spec (.of k)))) (q : G ⟶ Q),
        IsAffine Q.X.left ∧ LocallyOfFiniteType Q.X.hom ∧ QuasiCompact Q.X.hom ∧
        IsFppfGroupQuotient i q ∧ IsCommMonObj Q.X) ∧
      (IsCommMonObj G.X → IsIso (toUnit D.X)) := by
  sorry

end AlgebraicGeometry
