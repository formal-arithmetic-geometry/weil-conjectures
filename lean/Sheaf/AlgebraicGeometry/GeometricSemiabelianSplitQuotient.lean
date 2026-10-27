module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.FieldTheory.Galois.Basic

import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.EtaleFieldGsets
import Sheaf.AlgebraicGeometry.FpqcAffineDescent
import Mathlib.RingTheory.Flat.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Mathlib.RingTheory.FinitePresentation
import Sheaf.AlgebraicGeometry.NagataMorphismDescends
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf
import Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus
import Sheaf.AlgebraicGeometry.ProperMorphismFpqcDescent

/-!
# A split torus quotient of a geometric semiabelian group

Source: Conrad, Semistable Reduction for Abelian Varieties, Theorem 3.1, pp.7--8;
Milne, Algebraic Groups (2017), Definition 12.14 and Theorem 12.18(d)
(blueprint: lem-sfb-geometric-semiabelian-split-quotient).

The hypothesis retains the rank and the exact fppf extension over the algebraic closure.
The conclusion specifies the scheme-theoretic kernel and the two projections of the
right-translation torsor isomorphism. Products and pullbacks are in schemes over the field.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A geometric semiabelian group admits a split torus kernel and abelian quotient after
finite Galois extension, with its actual right-translation torsor isomorphism.

Source: Conrad, Semistable Reduction for Abelian Varieties, Theorem 3.1, pp.7--8;
Milne, Algebraic Groups (2017), Definition 12.14, Theorem 12.18(d), Corollary 12.19
(blueprint: lem-sfb-geometric-semiabelian-split-quotient).

Proof plan, following all nine steps of the DAG node:
1. Choose a separable closure inside the algebraic closure and a prime different from
   the characteristic. By lem-sfb-smooth-group-invertible-multiplication the prime-power
   torsion is etale. The classification lem-exc-etale-field-gsets over a separably closed
   field makes every geometric torsion point rational there. Take the union S of the
   points belonging to the given geometric torus; the nested torsion subsets form a group.
2. These points are dense in the torus: multiply a vanishing Laurent polynomial by a
   monomial, choose a sufficiently large prime power N exceeding every variable degree,
   and use the grid of N distinct roots of unity. Successive polynomial root bounds
   force the polynomial to vanish. This includes rank zero.
3. Apply lem-sfb-dense-rational-closed-subscheme-descent to this reduced closed torus.
   Affineness descends by lem-weil-pbc-fpqc-descend-affine. Multiplication, inverse and
   identity factor through it because they do after extension to the algebraic closure;
   lem-sfb-field-extension-tensor-injective detects the vanishing defining equations.
   Uniqueness through the closed immersion gives the group identities.
4. The descended group is a torus by def-sfb-tori-multiplicative-type. Apply
   lem-sfb-multiplicative-character-antiduality over the separably closed field. Its
   finite separable splitting extension is trivial. The character lattice is Z^r by
   lem-sfb-split-torus-hom-matrices, so its group algebra gives the rank-r split torus.
5. The finite Galois intermediate fields form a directed union equal to the separable
   closure by lem-weil-pbc-finite-set-in-finite-galois-subextension. Their spectra have
   the required limit by lem-weil-pbc-limit-affine-transition. Finite type over a field
   gives finite presentation by lem-weil-pbc-finite-type-noetherian-finite-presentation.
   Apply lemma-nagata-morphism-descends to descend the split torus inclusion to K.
6. Its group equations descend by lem-a1-algebraic-space-fpqc-sheaf. Equality of points
   over every K-algebra is detected after faithfully flat extension, so the inclusion
   is monic on all algebra points. The node
   lem-sfb-algebraic-group-monomorphism-closed-immersion makes it a closed immersion.
7. Smooth geometric connectedness gives geometric integrality by
   lem-trf-smooth-connected-fibre-normal-integrality. The split torus has the same
   properties by Laurent coordinates and lem-sfb-multiplicative-type-largest-subtorus.
   Apply lem-sfb-smooth-commutative-subgroup-quotient to obtain the smooth surjective
   quotient q of finite presentation, its kernel square and translation isomorphism.
   Smoothness gives flatness, so q is faithfully flat of finite presentation.
8. Over the algebraic closure the original quotient and this quotient have the same
   kernel. Lift sections fppf locally, apply the other quotient map, and glue; two
   lifts differ by the kernel, so the result is independent of lifts. Doing this in
   both directions gives inverse isomorphisms. Use lem-trf-fppf-covering-base-change,
   lem-trf-fppf-covering-is-fpqc and lem-a1-algebraic-space-fpqc-sheaf for gluing and
   equality detection. Thus the geometric quotient is the original proper group.
9. Properness descends by lem-weil-pbc-proper-morphism-fpqc-descent. The quotient is
   proper, smooth and connected, hence an abelian variety by def-sc-abelian-variety.
   The K from step 5 and q from step 7 give every asserted clause with the same rank.
-/
theorem geometric_semiabelian_split_quotient
    {k : Type u} [Field k] (H : Grp (Over (Spec (.of k))))
    [IsCommMonObj H.X] [Smooth H.X.hom] [IsSeparated H.X.hom]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    [GeometricallyConnected H.X.hom] (r : ℕ)
    (hgeom : ∃ (B : Grp (Over (Spec (.of (AlgebraicClosure k)))))
      (i : MultiplicativeType.splitTorus (AlgebraicClosure k) r ⟶
        (MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj H)
      (p : (MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj H ⟶ B),
      IsCommMonObj B.X ∧ IsProper B.X.hom ∧ Smooth B.X.hom ∧
      GeometricallyConnected B.X.hom ∧
      IsPullback i.hom.hom
        (toUnit (MultiplicativeType.splitTorus (AlgebraicClosure k) r).X)
        p.hom.hom η[B.X] ∧
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of (AlgebraicClosure k))))
        (yoneda.map p.hom.hom)) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      FiniteDimensional k K ∧ IsGalois k K ∧
      ∃ (A : Grp (Over (Spec (.of K))))
        (i : MultiplicativeType.splitTorus K r ⟶
          (MultiplicativeType.baseChange (k := k) (K := K)).obj H)
        (q : (MultiplicativeType.baseChange (k := k) (K := K)).obj H ⟶ A),
        IsAbelianVariety A.X ∧ Smooth q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
        IsPullback i.hom.hom (toUnit (MultiplicativeType.splitTorus K r).X)
          q.hom.hom η[A.X] ∧
        Flat q.hom.hom.left ∧ LocallyOfFinitePresentation q.hom.hom.left ∧
        QuasiCompact q.hom.hom.left ∧ QuasiSeparated q.hom.hom.left ∧
        ∃ e : ((MultiplicativeType.baseChange (k := k) (K := K)).obj H).X ⊗
            (MultiplicativeType.splitTorus K r).X ≅ pullback q.hom.hom q.hom.hom,
          e.hom ≫ pullback.fst _ _ =
            fst ((MultiplicativeType.baseChange (k := k) (K := K)).obj H).X
              (MultiplicativeType.splitTorus K r).X ∧
          e.hom ≫ pullback.snd _ _ =
            lift (fst ((MultiplicativeType.baseChange (k := k) (K := K)).obj H).X
                (MultiplicativeType.splitTorus K r).X)
              (snd ((MultiplicativeType.baseChange (k := k) (K := K)).obj H).X
                (MultiplicativeType.splitTorus K r).X ≫ i.hom.hom) ≫
              μ[((MultiplicativeType.baseChange (k := k) (K := K)).obj H).X] := by
  sorry

end AlgebraicGeometry
