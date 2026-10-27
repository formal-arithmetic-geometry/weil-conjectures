module

public import Sheaf.AlgebraicGeometry.RegularGroupSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # Finite translates of a fibrewise nonempty open

Source: Deligne, Le lemme de Gabber, Lemma 4.6, printed p.144
(blueprint: lem-sfb-group-finite-translate-cover).

The geometric hypotheses reuse the existing group-space predicates, which do not
require a commutative group law. The group law itself is Mathlib's group-object
structure on the presheaf. A cover by open translates is tested on geometric points.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.AlgebraicSpace

/-- Etale locally on the base, finitely many left translates of a quasi-compact open
meeting every geometric fibre cover a smooth separated finitely presented group space
with integral geometric fibres. No commutativity or scheme representability is assumed.
Source: Deligne, Le lemme de Gabber, Lemma 4.6, printed p.144
(blueprint: lem-sfb-group-finite-translate-cover).

Proof:
1. On the empty base use the empty family. Otherwise fix a base point and use
   lem-sfb-group-open-arithmetic-model to descend the group and open to a nonempty
   finite-type arithmetic affine base T, with integral fibres of dimension d.
   Write D = dim T and n = d + D + 1.
2. By lem-sfb-translate-bad-tuple-dimension the bad tuples in the n-fold group power
   form a constructible locus whose geometric-fibre closures have dimension at most
   nd - n + d = nd - (D + 1). Bad means a geometric point is missed by every translate.
3. Apply lem-sfb-constructible-closure-fibre-avoidance with c = D + 1 > D.
   The complement of the closure is smooth surjective. Pull it back to the chosen
   neighbourhood, using lem-sfb-stack-chartwise-smooth-etale-calculus.
4. Apply lem-sfb-smooth-space-cover-etale-sections to obtain an etale scheme covering
   and sections of this complement. Their n projections give the translating sections.
   Every geometric tuple avoids the bad locus, so the translates cover its entire fibre.
5. A missed point of the union would yield a missed geometric point after passing to
   an algebraic closure of its residue field. Translation by g is an automorphism
   with inverse translation by its inverse, by the group identities alone. Assemble
   over all base points and compose etale morphisms with the open neighbourhoods,
   using lem-sfb-stack-chartwise-smooth-etale-calculus. -/
theorem exists_etale_finite_left_translate_cover
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    (G : AlgebraicSpace S) [GrpObj G.obj.obj]
    (hG : IsSmoothIntegralGroupSpace G) (V : OpenSubspace G)
    (hVqc : CompactSpace (Point V.val.toFunctor))
    (hV : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
      Nonempty (V.val.obj (op (Over.mk s)))) :
    ∃ (I : Type (u + 1)) (T : I → Over S),
      (∀ a : I, Etale (T a).hom) ∧
      (∀ s : S, ∃ (a : I) (t : (T a).left), (T a).hom.base t = s) ∧
      ∀ a : I, ∃ (n : ℕ) (g : Fin n → (yoneda.obj (T a) ⟶ G.obj.obj)),
        ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ (T a).left)
          (x : yoneda.obj (Over.mk (s ≫ (T a).hom)) ⟶ G.obj.obj),
          ∃ (j : Fin n)
            (v : yoneda.obj (Over.mk (s ≫ (T a).hom)) ⟶ V.val.toFunctor),
            (yoneda.map (Over.homMk s rfl) ≫ g j) * (v ≫ V.val.ι) = x := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
