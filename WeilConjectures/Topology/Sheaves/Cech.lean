/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Sheaves.Stalks

/-!
# The Čech complex of a finite family of open subsets

Let `X` be a topological space, `U : Fin n → Opens X` a finite family of open subsets and `P` a
presheaf of abelian groups on `X`. The (ordered) Čech complex `Č(U, P)` has in degree `k` the
cochains `c = (c y)_y`, indexed by the tuples `y : Fin (k + 1) → Fin n`, with
`c y ∈ P(U (y 0) ⊓ ⋯ ⊓ U (y k))`; the differential is the alternating sum of the restrictions
`(d c) y = ∑ i, (-1) ^ i • c (y ∘ Fin.succAbove i)`.

We show that `Č(U, P)` is exact in positive degrees in two situations: when restricting to one
of the members `U j` of the family is bijective on the sections over all the finite
intersections (in particular when `U j` contains all the other members), and when `P` is the
underlying presheaf of an injective abelian sheaf.

## Implementation notes

Mathlib's `CategoryTheory.cechComplexFunctor` builds the Čech complex of a family of objects of
any category with finite products through formal coproducts; its cochains are elements of
categorical products, which makes elementwise computations cumbersome. Here the cochains are
dependent functions, and the complex is the alternating coface map complex of an explicit
cosimplicial abelian group `TopCat.Presheaf.cechCosimplicialObject`.

## Main definitions

- `TopCat.Presheaf.cechComplex`: the Čech complex `Č(U, P)`, as a functor of `P`.
- `TopCat.Presheaf.godement`: the presheaf of all (not necessarily continuous) sections of a
  family of abelian groups indexed by the points of `X`.

## Main statements

- `TopCat.Presheaf.exactAt_cechComplex_of_bijective`: `Č(U, P)` is exact in positive degrees if
  restricting to some `U j` is bijective on the sections over the finite intersections.
- `TopCat.Presheaf.exactAt_cechComplex_of_le`: `Č(U, P)` is exact in positive degrees if some
  member of the family contains all the others.
- `TopCat.Presheaf.exactAt_cechComplex_of_injective`: the Čech complex of an injective abelian
  sheaf is exact in positive degrees.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {n : ℕ} (U : Fin n → Opens X)

lemma iInf_le_iInf_comp {k m : ℕ} (y : Fin (m + 1) → Fin n) (θ : Fin (k + 1) → Fin (m + 1)) :
    ⨅ l, U (y l) ≤ ⨅ l, U ((y ∘ θ) l) :=
  le_iInf fun l ↦ iInf_le _ (θ l)

/-- The Čech cochains of degree `k` of the family `U` with values in `P`: the families of
sections `c y ∈ P(U (y 0) ⊓ ⋯ ⊓ U (y k))` indexed by the tuples `y : Fin (k + 1) → Fin n`. -/
abbrev CechCochain (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (k : ℕ) : Type u :=
  ∀ y : Fin (k + 1) → Fin n, P.obj (op (⨅ l, U (y l)))

/-- The Čech cosimplicial abelian group of the family `U` with values in a presheaf `P`, as a
functor of `P`. In degree `k` it is the group `CechCochain U P k`, and a map `θ` of the simplex
category acts by `c ↦ (y ↦ c (y ∘ θ))`, restricted to the smaller intersection. -/
@[simps]
noncomputable def cechCosimplicialObject :
    ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ CosimplicialObject AddCommGrpCat.{u} where
  obj P :=
    { obj k := AddCommGrpCat.of (CechCochain U P k.len)
      map {k m} θ := AddCommGrpCat.ofHom (AddMonoidHom.pi fun y ↦
        (P.map (homOfLE (iInf_le_iInf_comp U y θ.toOrderHom)).op).hom.comp
          (Pi.evalAddMonoidHom _ (y ∘ θ.toOrderHom)))
      map_id := sorry
      map_comp := sorry }
  map φ :=
    { app k := AddCommGrpCat.ofHom (AddMonoidHom.pi fun y ↦
        (φ.app _).hom.comp (Pi.evalAddMonoidHom _ y))
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- The Čech complex `Č(U, P)` of the family `U` with values in a presheaf `P`, as a functor
of `P`: the alternating coface map complex of `cechCosimplicialObject U`. -/
noncomputable def cechComplex :
    ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  cechCosimplicialObject U ⋙ AlgebraicTopology.alternatingCofaceMapComplex _

variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})

/-- The Čech differential is the alternating sum of the restrictions of the faces. -/
lemma cechComplex_d_apply (k : ℕ) (c : CechCochain U P k) (y : Fin (k + 2) → Fin n) :
    ((cechComplex U).obj P).d k (k + 1) c y =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        P.map (homOfLE (iInf_le_iInf_comp U y i.succAbove)).op (c (y ∘ i.succAbove)) :=
  sorry

@[simp]
lemma cechComplex_map_f_apply {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q) (k : ℕ)
    (c : CechCochain U P k) (y : Fin (k + 1) → Fin n) :
    ((cechComplex U).map φ).f k c y = φ.app _ (c y) :=
  sorry

/-- Exactness of the Čech complex in degree `q + 1`, in terms of cochains: every cocycle is a
coboundary. -/
lemma exactAt_cechComplex_iff (q : ℕ) :
    ((cechComplex U).obj P).ExactAt (q + 1) ↔
      ∀ c : CechCochain U P (q + 1), ((cechComplex U).obj P).d (q + 1) (q + 2) c = 0 →
        ∃ b : CechCochain U P q, ((cechComplex U).obj P).d q (q + 1) b = c :=
  sorry

/-- If for some index `j` restricting to `U j` is bijective on the sections of `P` over all the
finite intersections of the family, then the Čech complex `Č(U, P)` is exact in positive
degrees: inserting the index `j` in the first slot, `(h c) y = c (Fin.cons j y)`, is a
contraction. -/
theorem exactAt_cechComplex_of_bijective {j : Fin n}
    (hj : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      Function.Bijective (P.map (homOfLE (inf_le_left : (⨅ l, U (y l)) ⊓ U j ≤ _)).op))
    (q : ℕ) : ((cechComplex U).obj P).ExactAt (q + 1) :=
  sorry

/-- If some member `U j` of the family contains all the others, then the Čech complex
`Č(U, P)` is exact in positive degrees. -/
theorem exactAt_cechComplex_of_le {j : Fin n} (hj : ∀ i, U i ≤ U j) (q : ℕ) :
    ((cechComplex U).obj P).ExactAt (q + 1) :=
  sorry

/-- The presheaf of all, not necessarily continuous, sections of a family `S` of abelian groups
indexed by the points of `X`: its sections over `W` are the families `(s x)_{x ∈ W}`. -/
@[simps]
noncomputable def godement (S : X → Type u) [∀ x, AddCommGroup (S x)] :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj W := AddCommGrpCat.of (∀ x : W.unop, S x)
  map {W W'} f := AddCommGrpCat.ofHom (AddMonoidHom.pi fun x : W'.unop ↦
    Pi.evalAddMonoidHom (fun x : W.unop ↦ S x) ⟨x.1, f.unop.le x.2⟩)
  map_id := sorry
  map_comp := sorry

/-- The Čech complex of the presheaf of all sections of a family of abelian groups is exact in
positive degrees. -/
theorem exactAt_cechComplex_godement (S : X → Type u) [∀ x, AddCommGroup (S x)] (q : ℕ) :
    ((cechComplex U).obj (godement S)).ExactAt (q + 1) :=
  sorry

/-- The map from an abelian sheaf to the presheaf of all sections of its stalks, sending a
section to its germs. -/
noncomputable def toGodement (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    F.obj ⟶ godement fun x : X ↦ (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.obj x : Type u) where
  app W := AddCommGrpCat.ofHom (AddMonoidHom.pi fun x : W.unop ↦
    (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) F.obj W.unop x.1 x.2).hom)
  naturality := sorry

instance (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : Mono (toGodement F) :=
  sorry

/-- The Čech complex of an injective abelian sheaf is exact in positive degrees: the sheaf is a
direct summand of the presheaf of all sections of its stalks, whose Čech complex is exact. -/
theorem exactAt_cechComplex_of_injective (I : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective I]
    (q : ℕ) : ((cechComplex U).obj I.obj).ExactAt (q + 1) :=
  sorry

end TopCat.Presheaf
