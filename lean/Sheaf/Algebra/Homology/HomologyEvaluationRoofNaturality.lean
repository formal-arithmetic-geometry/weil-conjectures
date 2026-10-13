module

public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits

/-! # Naturality of cycle-compatible Hom evaluation -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- Two cycle-compatible evaluations agree after passage through a common source.

Source: Stacks Project, Tag 0A8X, product projections and the Hom differential.
(blueprint: new-e3-homology-evaluation-roof-naturality).

The projection family is assumed to obey the Hom differential and naturality
identities, as supplied by `homComplex_projections_exists`.

Proof: Denote the homology precomposition maps induced by q and p by Q and P.
First descend the evaluation pairing for Hom(L,K): on Hom cycles and L cycles,
the Hom differential makes the value a K cycle. Evaluating a Hom boundary on a
cycle or a Hom cycle on an L boundary gives a K boundary (with the usual integer
sign). Thus the pairing descends through both homology quotients to an evaluation
h for L. This is a proof construction using kernels and cokernels, not a choice
of arbitrary comparison isomorphisms. Naturality of the supplied product projections
under precomposition shows that evaluation on q(z) equals evaluation of the
precomposed Hom cycle on z, and likewise for p. The two identities for d identify
g on cycle classes with this pairing, giving g followed by Hom(H(q),1) = Q
followed by h. The two identities for c similarly give f followed by
Hom(H(p),1) = P followed by h. To check these equalities, cancel the epimorphism
from Hom cycles to homology and use local lifts of source homology classes to
cycles; equality on the lifts glues because the target is a sheaf. Since P is
invertible, the second equation gives h = P inverse followed by f followed by
Hom(H(p),1). Substitute in the first equation. No quasi-isomorphism of q or p,
K-injectivity, or scheme is needed beyond the explicitly assumed invertibility
of P. The argument includes zero homology, zero complexes and empty sites. -/
theorem homologyEvaluation_roof_naturality
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    {R : Sheaf S CommRingCat.{u}}
    (A E L K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (π : ∀ (B M : CochainComplex (SheafOfModules.{u}
        ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (n a b : ℤ), a + n = b →
        ((homComplex (R := R) B M).X n ⟶
          SheafOfModules.homObj (R := R) (B.X a) (M.X b)))
    (hπdiff : ∀ (B M : CochainComplex (SheafOfModules.{u}
        ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (n m a b b' a' : ℤ) (_hnm : n + 1 = m)
      (hab : a + m = b) (hb' : a + n = b') (ha' : a' + n = b),
      (homComplex (R := R) B M).d n m ≫ π B M m a b hab =
        π B M n a b' hb' ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (M.d b' b) -
          n.negOnePow • (π B M n a' b ha' ≫
            SheafOfModules.homObjMap (R := R) (B.d a a') (𝟙 _)))
    (hπnat : ∀ (B B' M M' : CochainComplex (SheafOfModules.{u}
        ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (t : B' ⟶ B) (s : M ⟶ M') (n a b : ℤ) (hab : a + n = b),
      ((((homComplexFunctor (R := R)).map t.op).app M) ≫
          ((homComplexFunctor (R := R)).obj (op B')).map s).f n ≫ π B' M' n a b hab =
        π B M n a b hab ≫ SheafOfModules.homObjMap (R := R) (t.f a) (s.f b))
    (n : ℤ) (q : L ⟶ A) (p : L ⟶ E)
    [IsIso (HomologicalComplex.homologyMap
      (((homComplexFunctor (R := R)).map p.op).app K) n)] :
    let Q := homComplex (R := R) A K
    let P := homComplex (R := R) E K
    ∀ (g : Q.homology n ⟶ SheafOfModules.homObj (R := R)
        (A.homology (-n)) (K.homology 0))
      (d : Q.cycles n ⟶ SheafOfModules.homObj (R := R) (A.cycles (-n)) (K.cycles 0))
      (f : P.homology n ⟶ SheafOfModules.homObj (R := R)
        (E.homology (-n)) (K.homology 0))
      (c : P.cycles n ⟶ SheafOfModules.homObj (R := R) (E.cycles (-n)) (K.cycles 0)),
      d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
        Q.iCycles n ≫ π A K n (-n) 0 (by omega) ≫
          SheafOfModules.homObjMap (R := R) (A.iCycles (-n)) (𝟙 _) →
      d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0) =
        Q.homologyπ n ≫ g ≫
          SheafOfModules.homObjMap (R := R) (A.homologyπ (-n)) (𝟙 _) →
      c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
        P.iCycles n ≫ π E K n (-n) 0 (by omega) ≫
          SheafOfModules.homObjMap (R := R) (E.iCycles (-n)) (𝟙 _) →
      c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0) =
        P.homologyπ n ≫ f ≫
          SheafOfModules.homObjMap (R := R) (E.homologyπ (-n)) (𝟙 _) →
      g ≫ SheafOfModules.homObjMap (R := R)
          (HomologicalComplex.homologyMap q (-n)) (𝟙 _) =
        HomologicalComplex.homologyMap
            (((homComplexFunctor (R := R)).map q.op).app K) n ≫
          inv (HomologicalComplex.homologyMap
            (((homComplexFunctor (R := R)).map p.op).app K) n) ≫
          f ≫ SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.homologyMap p (-n)) (𝟙 _) := by
  sorry

end CategoryTheory
