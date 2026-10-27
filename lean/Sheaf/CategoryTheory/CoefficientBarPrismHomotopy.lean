/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.CategoryTheory.PresheafBarResolution
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.DerivedColimitBar
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Order.Fin.Basic

/-! # The coefficient-sensitive category-bar prism

Source: Stacks Project, Tag 08PH, example-morphism-categories, and the explicit
natural-transformation extension in the DAG
(blueprint: lem-trf-coefficient-bar-prism-homotopy).

The direct sums, faces and alternating differential are the existing `PresheafBar`
constructions. The prism chains and their linear maps are constructed below, including
coefficient restriction at the terminal face. The final record specifies their realization
as integer cochain complexes and the resulting homotopy, without choosing any data from
its postponed existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v r s d

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CoefficientBarPrism

variable {E D : Type u} [SmallCategory E] [SmallCategory D]
variable {R : Type r} [CommRing R]

/-- Vertices of the chain with the component of eta inserted after vertex r from the left.
Source: Tag 08PH, prism expansion
(blueprint: lem-trf-coefficient-bar-prism-homotopy). -/
def vertex (v w : E ⥤ D) {n : ℕ} (c : ComposableArrows E n) (a : Fin (n + 1))
    (i : Fin (n + 2)) : D :=
  if i.val ≤ a.val then v.obj (c.obj (a.predAbove i))
  else w.obj (c.obj (a.predAbove i))

/-- The adjacent arrows are those of v and w, with eta at the crossing.
Source: Tag 08PH, prism expansion
(blueprint: lem-trf-coefficient-bar-prism-homotopy). -/
def edge (v w : E ⥤ D) (η : v ⟶ w) {n : ℕ}
    (c : ComposableArrows E n) (a : Fin (n + 1)) (i : Fin (n + 1)) :
    vertex v w c a i.castSucc ⟶ vertex v w c a i.succ := by
  classical
  unfold vertex
  split_ifs with hi hj hj
  · exact v.map (c.map (homOfLE
      ((Fin.predAboveOrderHom a).monotone (Fin.castSucc_le_succ i))))
  · exact η.app (c.obj (a.predAbove i.castSucc)) ≫
      w.map (c.map (homOfLE
        ((Fin.predAboveOrderHom a).monotone (Fin.castSucc_le_succ i))))
  · simp only [Fin.val_castSucc, Fin.val_succ] at *
    omega
  · exact w.map (c.map (homOfLE
      ((Fin.predAboveOrderHom a).monotone (Fin.castSucc_le_succ i))))

/-- The actual chain vU_n → ... → vU_(n-r) → wU_(n-r) → ... → wU_0.
Source: Tag 08PH, prism expansion
(blueprint: lem-trf-coefficient-bar-prism-homotopy). -/
def chain (v w : E ⥤ D) (η : v ⟶ w) {n : ℕ}
    (c : ComposableArrows E n) (a : Fin (n + 1)) : ComposableArrows D (n + 1) :=
  ComposableArrows.mkOfObjOfMapSucc (vertex v w c a) (edge v w η c a)

/-- Transport to the final vertex of the prism. Its underlying arrow is the identity
at wU_0; this formulation avoids dependent casts of coefficient elements.
Source: Tag 08PH, coefficient-sensitive prism expansion
(blueprint: lem-trf-coefficient-bar-prism-homotopy). -/
def coefficient (v w : E ⥤ D) (η : v ⟶ w) (G : PresheafBar.Presheaves.{u, v} D R)
    {n : ℕ} (c : ComposableArrows E n) (a : Fin (n + 1)) :
    G.obj (op (w.obj c.right)) ⟶ G.obj (op (chain v w η c a).right) := by
  change G.obj (op (w.obj c.right)) ⟶ G.obj (op (vertex v w c a (Fin.last (n + 1))))
  unfold vertex
  split_ifs with h
  · simp only [Fin.val_last] at h
    omega
  · exact G.map (w.map (c.map (homOfLE (Fin.le_last _)))).op

/-- The generator map K(u,t), extended over the actual direct sum.
Source: Tag 08PH, generator formula
(blueprint: lem-trf-coefficient-bar-prism-homotopy). -/
def reindex (f : E ⥤ D) {F : PresheafBar.Presheaves.{u, v} E R}
    {G : PresheafBar.Presheaves.{u, v} D R} (t : F ⟶ f.op ⋙ G) (n : ℕ) :
    PresheafBar.colimitTerm F n ⟶ PresheafBar.colimitTerm G n := by
  classical
  exact ModuleCat.ofHom (DirectSum.toModule R _ _ (fun c ↦
    (t.app (op c.right) ≫ PresheafBar.colimitι G n (c ⋙ f)).hom))

/-- The coefficient-sensitive insertion map p_r on the direct sums.
Source: Tag 08PH, prism expansion
(blueprint: lem-trf-coefficient-bar-prism-homotopy). -/
def insertion (v w : E ⥤ D) (η : v ⟶ w)
    {F : PresheafBar.Presheaves.{u, v} E R} {G : PresheafBar.Presheaves.{u, v} D R}
    (t : F ⟶ w.op ⋙ G) (n : ℕ) (a : Fin (n + 1)) :
    PresheafBar.colimitTerm F n ⟶ PresheafBar.colimitTerm G (n + 1) := by
  classical
  exact ModuleCat.ofHom (DirectSum.toModule R _ _ (fun c ↦
    (t.app (op c.right) ≫ coefficient v w η G c a ≫
      PresheafBar.colimitι G (n + 1) (chain v w η c a)).hom))

/-- The signed prism H_n = sum_r (-1)^r p_r, with finitely many terms for each n.
Source: Tag 08PH, prism expansion
(blueprint: lem-trf-coefficient-bar-prism-homotopy). -/
def signed (v w : E ⥤ D) (η : v ⟶ w)
    {F : PresheafBar.Presheaves.{u, v} E R} {G : PresheafBar.Presheaves.{u, v} D R}
    (t : F ⟶ w.op ⋙ G) (n : ℕ) :
    PresheafBar.colimitTerm F n ⟶ PresheafBar.colimitTerm G (n + 1) :=
  ∑ a : Fin (n + 1), (-1 : ℤ) ^ a.val • insertion v w η t n a

/-- The precise prism assertion, including all faces, the degree-zero equation, the
integer cochain realization and its generator-normalized homotopy. All term and map data
are determined by the existing direct sums and the formulas above.
Source: Tag 08PH, natural-transformation extension, all clauses
(blueprint: lem-trf-coefficient-bar-prism-homotopy). -/
structure Realization (v w : E ⥤ D) (η : v ⟶ w)
    (F : PresheafBar.Presheaves.{u, v} E R) (G : PresheafBar.Presheaves.{u, v} D R)
    (t : F ⟶ w.op ⋙ G) [HasDerivedCategory.{d} (ModuleCat.{max u v} R)] where
  K : CochainComplex (ModuleCat.{max u v} R) ℤ
  L : CochainComplex (ModuleCat.{max u v} R) ℤ
  sourceTerm : ∀ n : ℕ, PresheafBar.colimitTerm F n ≅ K.X (-(n : ℤ))
  targetTerm : ∀ n : ℕ, PresheafBar.colimitTerm G n ≅ L.X (-(n : ℤ))
  positive : ∀ i : ℤ, 0 < i → IsZero (K.X i) ∧ IsZero (L.X i)
  sourceDifferential : ∀ n : ℕ,
    (sourceTerm (n + 1)).hom ≫ K.d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      PresheafBar.colimitDifferential F n ≫ (sourceTerm n).hom
  targetDifferential : ∀ n : ℕ,
    (targetTerm (n + 1)).hom ≫ L.d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      PresheafBar.colimitDifferential G n ≫ (targetTerm n).hom
  fw : K ⟶ L
  fv : K ⟶ L
  wFormula : ∀ n : ℕ, (sourceTerm n).hom ≫ fw.f (-(n : ℤ)) =
    reindex w t n ≫ (targetTerm n).hom
  vFormula : ∀ n : ℕ, (sourceTerm n).hom ≫ fv.f (-(n : ℤ)) =
    reindex v (t ≫ Functor.whiskerRight (NatTrans.op η) G) n ≫ (targetTerm n).hom
  before : ∀ (n : ℕ) (a : Fin (n + 1)) (j : Fin (n + 2)), j.val ≤ a.val →
    insertion v w η t (n + 1) a.succ ≫ PresheafBar.colimitFace G (n + 1) j.castSucc =
      PresheafBar.colimitFace F n j ≫ insertion v w η t n a
  after : ∀ (n : ℕ) (a : Fin (n + 1)) (j : Fin (n + 2)), a.val < j.val →
    insertion v w η t (n + 1) a.castSucc ≫ PresheafBar.colimitFace G (n + 1) j.succ =
      PresheafBar.colimitFace F n j ≫ insertion v w η t n a
  junction : ∀ (n : ℕ) (a : Fin (n + 1)),
    insertion v w η t (n + 1) a.castSucc ≫
        PresheafBar.colimitFace G (n + 1) a.castSucc.succ =
      insertion v w η t (n + 1) a.succ ≫
        PresheafBar.colimitFace G (n + 1) a.castSucc.succ
  first : ∀ n : ℕ,
    insertion v w η t n 0 ≫ PresheafBar.colimitFace G n 0 = reindex w t n
  last : ∀ n : ℕ,
    insertion v w η t n (Fin.last n) ≫ PresheafBar.colimitFace G n (Fin.last (n + 1)) =
      reindex v (t ≫ Functor.whiskerRight (NatTrans.op η) G) n
  equation : ∀ n : ℕ,
    signed v w η t (n + 1) ≫ PresheafBar.colimitDifferential G (n + 1) +
        PresheafBar.colimitDifferential F n ≫ signed v w η t n =
      reindex w t (n + 1) -
        reindex v (t ≫ Functor.whiskerRight (NatTrans.op η) G) (n + 1)
  degreeZero : signed v w η t 0 ≫ PresheafBar.colimitDifferential G 0 =
    reindex w t 0 - reindex v (t ≫ Functor.whiskerRight (NatTrans.op η) G) 0
  degreeZeroGenerator : ∀ (U : E) (x : F.obj (op U)),
    (signed v w η t 0 ≫ PresheafBar.colimitDifferential G 0)
        (PresheafBar.colimitι F 0 (ComposableArrows.mk₀ U) x) =
      PresheafBar.colimitι G 0 (ComposableArrows.mk₀ (w.obj U)) (t.app (op U) x) -
        PresheafBar.colimitι G 0 (ComposableArrows.mk₀ (v.obj U))
          (G.map (η.app U).op (t.app (op U) x))
  homotopy : Homotopy fw fv
  homotopyFormula : ∀ n : ℕ,
    (sourceTerm n).hom ≫ homotopy.hom (-(n : ℤ)) (-((n + 1 : ℕ) : ℤ)) =
      signed v w η t n ≫ (targetTerm (n + 1)).hom
  augmentedZero : homotopy.hom 1 0 = 0
  derivedEquality : DerivedCategory.Q.map fw = DerivedCategory.Q.map fv

/-- The displayed coefficient-sensitive category-bar prism exists, also for semilinear
coefficient maps after scalar restriction. The same-ring assertion is the instance
S = R, phi = id. No category is required to be finite or nonempty.

Source: Stacks Project, Tag 08PH (`example-morphism-categories`), explicit
natural-transformation extension (blueprint: lem-trf-coefficient-bar-prism-homotopy).

Proof (the ten steps of the DAG):
1. Extend the two endpoint formulas and every insertion formula linearly over direct
sums. Naturality of eta and of t makes G(eta)t natural, including the coefficient face.
2. Deleting two vertices in opposite orders agrees by associativity and contravariance
at the coefficient end. The signs cancel in d squared. Functoriality and naturality
make both endpoint formulas cochain maps.
3. For j < r, deletion before the crossing is insertion at r-1 after face j.
4. For j > r+1, deletion after the crossing is insertion at r after face j-1.
For the terminal face the coefficient equality is precisely naturality of t.
5. At the junction the arrows w(a) eta = eta v(a) agree by naturality of eta.
6. The first face leaves the all-w chain; the last face restricts the coefficient
along eta, leaving the all-v chain with coefficient G(eta)t.
7. Expand dH+Hd. The before and after terms cancel with the corresponding Hd terms.
The junction terms cancel in adjacent insertions. The endpoints remain with signs +,-.
8. At n=0 the boundary is (wU,t x)-(vU,G(eta)t x). Positive cochain terms vanish;
set all other homotopy components to zero, including H_(-1).
9. Homotopic maps agree in the homotopy category, hence after its quasi-isomorphism
localization in def-weil-abstract-derived-category, giving the stated derived equality.
10. Restriction of scalars changes none of the underlying groups, sums or formulas.
A semilinear t is a linear natural map to the restricted coefficients. The same proof
therefore applies. Each insertion sum has n+1 terms; identity arrows and empty
categories cause no exception. -/
theorem exists_realization {S : Type s} [CommRing S] (φ : R →+* S)
    (v w : E ⥤ D) (η : v ⟶ w) (F : PresheafBar.Presheaves.{u, v} E R)
    (G : PresheafBar.Presheaves.{u, v} D S)
    (t : F ⟶ w.op ⋙ G ⋙ ModuleCat.restrictScalars φ)
    [HasDerivedCategory.{d} (ModuleCat.{max u v} R)] :
    Nonempty (Realization v w η F (G ⋙ ModuleCat.restrictScalars φ) t) := by
  sorry

end CategoryTheory.CoefficientBarPrism
