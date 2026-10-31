/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RelativeCyclicTotal
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import Mathlib.Algebra.Homology.TotalComplexShift
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.CategoryTheory.AdditiveLocalizationDescent

/-! # Signed cyclic totalization and triangulated descent

Source: main-20261015, six-functors direct-images proof, paragraph (3), auxiliary
relative cyclic calculation, extracted steps 7--8; Stacks homology.tex,
definition-shift-cochain, and derived.tex, definition-cone, Tags 05RT, 05RU, 05R7
(blueprint: lem-sfb-cyclic-total-triangulated).

The existing `TotalModel` specifies the actual two coordinates, differential, maps and
invariant augmentation. The predicates below specify its signed shift and localization
comparison. No comparison with derived invariants is assumed or asserted here.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CondensedBar

namespace CategoryTheory.RelativeCyclic

variable (A : CondensedBar.Ring.{u}) (G : Type u)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The existing shift of a cyclic total has coordinates `(x, (-1)^s y)`.
Source: extracted cyclic calculation, step 3, Stacks definition-shift-cochain
(blueprint: lem-sfb-cyclic-total-triangulated). -/
def HasSignedTotalShift (K : TotalModel A G) : Prop :=
  ∀ (N : CochainComplex (Equivariant A (G × Z.{u})) ℤ) (s n : ℤ),
    ((K.functor.commShiftIso s).hom.app N).f n ≫
        ((K.functor.obj N).shiftFunctorObjXIso s n (n + s) rfl).hom ≫
        (K.coordinates N (n + s)).hom =
      (K.coordinates ((shiftFunctor _ s).obj N) n).hom ≫
        biprod.map
          ((retainResidual A G Z).map (N.shiftFunctorObjXIso s n (n + s) rfl).hom)
          (s.negOnePow • (retainResidual A G Z).map
            (N.shiftFunctorObjXIso s (n - 1) ((n + s) - 1) (by omega)).hom)

/-- A triangulated descent of the cyclic total, with its localization comparison commuting
with the specified shifts. The target is the actual cohomologically bounded-below category.
Source: extracted cyclic calculation, step 7, Stacks Tags 05RU, 05R7
(blueprint: lem-sfb-cyclic-total-triangulated). -/
def IsTotalDescent (K : TotalModel A G)
    (F : DerivedCategory.Plus (Equivariant A (G × Z.{u})) ⥤
      DerivedCategory.Plus (Equivariant A G)) [F.CommShift ℤ] : Prop :=
  F.Additive ∧ F.IsTriangulated ∧
    ∃ e : plusQ A (G × Z) ⋙ F ⋙ DerivedCategory.Plus.ι ≅
        CochainComplex.Plus.ι _ ⋙ K.functor ⋙ DerivedCategory.Q,
      NatTrans.CommShift e.hom ℤ

/-- The two-coordinate cyclic complex exists, is additive, takes `h` to `(h,-h)`,
preserves bounded-below quasi-isomorphisms, and has a triangulated descent to `D+`.
Its differential, diagonal maps and invariant augmentation are the fields of `TotalModel`.
Source: extracted cyclic calculation, steps 1--7; Stacks Tags 0117, 05RT, 05RU, 05R7
(blueprint: lem-sfb-cyclic-total-triangulated).

Proof:
1. Restrict along `g ↦ (g,0)`. The action/injective infrastructure makes restriction
   additive and exact, also for the discrete integer factor. The positive generator
   commutes with the residual action. Kernel-fixed sections are precisely `ker(T-1)`:
   use integer powers and a finite clopen partition for a map to discrete integers.
2. The differential squares to zero because `(T-1)d=d(T-1)`. Diagonal maps commute
   with it, preserve sums, identities and composition. The homotopy `(h,-h)` has
   mixed term `(T-1)h-h(T-1)=0`. The invariant inclusion gives `(inclusion,0)`.
3. Direct substitution proves the signed shift formula; `(-1)^(s+t)` gives coherence.
4. The signed cone permutation `(b,a,c,e) ↦ (b,c,a,-e)` intertwines differentials
   and all three cone arrows, with the final arrow the negative projection.
5. The degreewise split sequence `UN[-1] → KN → UN` and the long exact homology
   sequence (lem-weil-pbc-complex-ses-homology-long-exact) preserve lower bounds
   and acyclicity.
6. Exact restriction and the cone comparison reduce preservation of quasi-isomorphisms
   to lem-pur-quasi-iso-cone-acyclic.
7. Descend first on unbounded derived categories by the localization universal property;
   descend shifts and their coherence too. Additivity follows from
   lem-sfb-derived-localization-additive and lem-pur-additive-localization-descent.
   The cone-arrow comparison preserves distinguished triangles. The homology bound
   then restricts the descent to cohomologically bounded-below objects, without choosing
   termwise bounded representatives.
-/
theorem exists_signed_cyclicTotal :
    ∃ K : TotalModel A G,
      K.functor.Additive ∧ HasSignedTotalShift A G K ∧
      (∀ (N P : CochainComplex (Equivariant A (G × Z.{u})) ℤ)
        (f g : N ⟶ P) (h : Homotopy f g),
        ∃ H : Homotopy (K.functor.map f) (K.functor.map g),
          ∀ i j : ℤ, H.hom i j ≫ (K.coordinates P j).hom =
            (K.coordinates N i).hom ≫ biprod.map
              ((retainResidual A G Z).map (h.hom i j))
              (-((retainResidual A G Z).map (h.hom (i - 1) (j - 1))))) ∧
      (∀ (N P : CochainComplex (Equivariant A (G × Z.{u})) ℤ),
        CochainComplex.plus _ N → CochainComplex.plus _ P →
          ∀ f : N ⟶ P, QuasiIso f → QuasiIso (K.functor.map f)) ∧
      (∃ (F : DerivedCategory.Plus (Equivariant A (G × Z.{u})) ⥤
          DerivedCategory.Plus (Equivariant A G)) (σ : F.CommShift ℤ),
        @IsTotalDescent A G _ _ _ _ _ _ K F σ) := by
  sorry

/-- The signed cone permutation has coordinates `(b,a,c,e) ↦ (b,c,a,-e)`.
The last two equalities retain the inclusion and the negative third cone arrow;
the first triangle arrow is already `K(f)` by functoriality.
Source: extracted cyclic calculation, step 4, Stacks definition-cone
(blueprint: lem-sfb-cyclic-total-triangulated).

Proof: use the existing cone projections to reorder the four coordinates. The differentials
on both sides give `(db+fa, (T-1)b-dc-fe, -da, -(T-1)a-de)`. Undoing the same
permutation and sign is the inverse. It is identity on the target inclusion. The negative
projection followed by the signed shift is `(-a,e)`, exactly the target negative projection.
-/
theorem cyclicTotal_cone (K : TotalModel A G) (hK : HasSignedTotalShift A G K)
    {N P : CochainComplex (Equivariant A (G × Z.{u})) ℤ} (f : N ⟶ P) :
    ∃ e : K.functor.obj (CochainComplex.mappingCone f) ≅
        CochainComplex.mappingCone (K.functor.map f),
      (∀ n : ℤ,
        e.hom.f n ≫ HomologicalComplex.homotopyCofiber.sndX (K.functor.map f) n ≫
            (K.coordinates P n).hom =
          (K.coordinates (CochainComplex.mappingCone f) n).hom ≫ biprod.map
            ((retainResidual A G Z).map (HomologicalComplex.homotopyCofiber.sndX f n))
            ((retainResidual A G Z).map
              (HomologicalComplex.homotopyCofiber.sndX f (n - 1)))) ∧
      (∀ n : ℤ,
        e.hom.f n ≫ HomologicalComplex.homotopyCofiber.fstX (K.functor.map f)
            n (n + 1) rfl ≫ (K.coordinates N (n + 1)).hom =
          (K.coordinates (CochainComplex.mappingCone f) n).hom ≫ biprod.map
            ((retainResidual A G Z).map
              (HomologicalComplex.homotopyCofiber.fstX f n (n + 1) rfl))
            (-((retainResidual A G Z).map
              (HomologicalComplex.homotopyCofiber.fstX f (n - 1) ((n + 1) - 1)
                (by change (n - 1) + 1 = (n + 1) - 1; omega))))) ∧
      K.functor.map (CochainComplex.mappingCone.inr f) ≫ e.hom =
        CochainComplex.mappingCone.inr (K.functor.map f) ∧
      K.functor.map (CochainComplex.mappingCone.triangle f).mor₃ ≫
          (K.functor.commShiftIso (1 : ℤ)).hom.app N =
        e.hom ≫ (CochainComplex.mappingCone.triangle (K.functor.map f)).mor₃ := by
  sorry

/-- The cyclic total is the total of its two commuting columns, with both column
identifications and the horizontal map fixed. This connects the generic signed total
comparisons below to the actual cyclic functor.
Source: extracted cyclic calculation, step 8, Stacks double-complex total convention
(blueprint: lem-sfb-cyclic-total-triangulated).

Proof: put `UN` in columns zero and one, `T-1` between them, and zero elsewhere.
Naturality of the generator makes this a commuting bicomplex. Each diagonal has at
most two nonzero terms. Their coproduct identifies with the coordinates of `K`; the
signed total differential is `(dx,(T-1)x-dy)`, precisely the specified differential.
-/
theorem cyclicTotal_twoColumn (K : TotalModel A G)
    (N : CochainComplex (Equivariant A (G × Z.{u})) ℤ) :
    ∃ (D : HomologicalComplex₂ (Equivariant A G) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
      (c₀ : D.X 0 ≅ ((retainResidual A G Z).mapHomologicalComplex (.up ℤ)).obj N)
      (c₁ : D.X 1 ≅ ((retainResidual A G Z).mapHomologicalComplex (.up ℤ)).obj N),
      (∀ a q : ℤ, a ≠ 0 → a ≠ 1 → IsZero ((D.X a).X q)) ∧
      (∀ n : ℤ, (c₀.inv ≫ D.d 0 1 ≫ c₁.hom).f n = generatorEnd (N.X n) - 𝟙 _) ∧
      D.HasTotal (ComplexShape.up ℤ) ∧
      ∀ [hD : D.HasTotal (ComplexShape.up ℤ)],
        ∃ e : D.total (ComplexShape.up ℤ) ≅ K.functor.obj N,
          (∀ n : ℤ, D.ιTotal (ComplexShape.up ℤ) 0 n n (by simp) ≫ e.hom.f n ≫
              (K.coordinates N n).hom = c₀.hom.f n ≫ biprod.inl) ∧
          (∀ n : ℤ, D.ιTotal (ComplexShape.up ℤ) 1 (n - 1) n (by dsimp; omega) ≫
              e.hom.f n ≫ (K.coordinates N n).hom = c₁.hom.f (n - 1) ≫ biprod.inr) := by
  sorry

/-- Moving a vertical lower bound to zero has sign `(-1)^(a*b)` on column `a`.
The canonical total comparison is written as `Tot(D_b) ≅ Tot(D)[b]`, equivalently
`Tot(D) ≅ Tot(D_b)[-b]`. Its square for every bicomplex map includes row augmentations,
and its column-zero formula has sign one.
Source: extracted cyclic calculation, step 8, Stacks double-complex total convention
(blueprint: lem-sfb-cyclic-total-triangulated).

Proof: finite diagonal sums exist since `a ≥ 0` and `q ≥ b`. The signed vertical shift
is first-quadrant. Multiplication on column `a` by `(-1)^(a*b)` obeys
`theta_(a+1)=(-1)^b theta_a`; the vertical chain equation is immediate. These diagonal
signs commute with every comparison map. The comparison is a chain isomorphism, so
quasi-isomorphisms correspond under its naturality square and the shift. At `a=0` its
sign is one, including the row augmentation.
-/
theorem cyclicTotal_lowerBound
    (D : HomologicalComplex₂ (Equivariant A G) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (b : ℤ) (hD : ∀ a q : ℤ, a < 0 ∨ q < b → IsZero ((D.X a).X q)) :
    D.HasTotal (ComplexShape.up ℤ) ∧
    ∀ [hTotal : D.HasTotal (ComplexShape.up ℤ)],
      (∀ a q : ℤ, a < 0 ∨ q < 0 →
        IsZero ((((HomologicalComplex₂.shiftFunctor₂ (Equivariant A G) b).obj D).X a).X q)) ∧
      (∀ (a q n : ℤ) (h : a + q = n),
        ((HomologicalComplex₂.shiftFunctor₂ (Equivariant A G) b).obj D).ιTotal
            (ComplexShape.up ℤ) a q n h ≫ (D.totalShift₂Iso b).hom.f n ≫
            (CochainComplex.shiftFunctorObjXIso
              (D.total (ComplexShape.up ℤ)) b n (n + b) rfl).hom =
          (a * b).negOnePow • (D.shiftFunctor₂XXIso a q b (q + b) rfl).hom ≫
            D.ιTotal (ComplexShape.up ℤ) a (q + b) (n + b) (by dsimp; omega)) ∧
      (∀ q : ℤ,
        ((HomologicalComplex₂.shiftFunctor₂ (Equivariant A G) b).obj D).ιTotal
            (ComplexShape.up ℤ) 0 q q (by simp) ≫ (D.totalShift₂Iso b).hom.f q ≫
            (CochainComplex.shiftFunctorObjXIso
              (D.total (ComplexShape.up ℤ)) b q (q + b) rfl).hom =
          (D.shiftFunctor₂XXIso 0 q b (q + b) rfl).hom ≫
            D.ιTotal (ComplexShape.up ℤ) 0 (q + b) (q + b) (by simp)) ∧
      (∀ (E : HomologicalComplex₂ (Equivariant A G)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)) [hE : E.HasTotal (ComplexShape.up ℤ)]
        (f : D ⟶ E),
        HomologicalComplex₂.total.map
            ((HomologicalComplex₂.shiftFunctor₂ (Equivariant A G) b).map f)
            (ComplexShape.up ℤ) ≫ (E.totalShift₂Iso b).hom =
          (D.totalShift₂Iso b).hom ≫ (shiftFunctor _ b).map
            (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) ∧
        (QuasiIso (HomologicalComplex₂.total.map
            ((HomologicalComplex₂.shiftFunctor₂ (Equivariant A G) b).map f)
            (ComplexShape.up ℤ)) ↔
          QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)))) := by
  sorry

/-- Transposition has sign `(-1)^(a*q)`, is natural for every comparison map, and
has sign one on both augmentation axes. Thus it identifies row and column augmentations
and carries their quasi-isomorphism comparisons along.
Source: extracted cyclic calculation, step 9, Stacks double-complex total convention
(blueprint: lem-sfb-cyclic-total-triangulated).

Proof: reorder the diagonal summands. The horizontal equality is
`eta_(a+1,q)=(-1)^q eta_(a,q)` and the vertical equality is
`(-1)^a eta_(a,q+1)=eta_(a,q)`. They give the signed chain isomorphism, whose square is
the identity. Naturality is checked on each summand. On `a=0` and `q=0` the sign is one,
so the axis augmentation maps are unchanged. Isomorphism conjugation preserves and
reflects quasi-isomorphisms. For a lower vertical bound first apply the preceding theorem.
-/
theorem cyclicTotal_transpose
    (D : HomologicalComplex₂ (Equivariant A G) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [hD : D.HasTotal (ComplexShape.up ℤ)] :
    (∀ (a q n : ℤ) (h : a + q = n),
      D.ιTotal (ComplexShape.up ℤ) a q n h ≫ (D.totalFlipIso (ComplexShape.up ℤ)).inv.f n =
        (a * q).negOnePow • D.flip.ιTotal (ComplexShape.up ℤ) q a n
          (by dsimp at h ⊢; omega)) ∧
    (∀ q : ℤ, D.ιTotal (ComplexShape.up ℤ) 0 q q (by simp) ≫
        (D.totalFlipIso (ComplexShape.up ℤ)).inv.f q =
      D.flip.ιTotal (ComplexShape.up ℤ) q 0 q (by simp)) ∧
    (∀ a : ℤ, D.ιTotal (ComplexShape.up ℤ) a 0 a (by simp) ≫
        (D.totalFlipIso (ComplexShape.up ℤ)).inv.f a =
      D.flip.ιTotal (ComplexShape.up ℤ) 0 a a (by simp)) ∧
    (∀ (E : HomologicalComplex₂ (Equivariant A G)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)) [hE : E.HasTotal (ComplexShape.up ℤ)]
      (f : D ⟶ E),
      HomologicalComplex₂.total.map f (ComplexShape.up ℤ) ≫
          (E.totalFlipIso (ComplexShape.up ℤ)).inv =
        (D.totalFlipIso (ComplexShape.up ℤ)).inv ≫ HomologicalComplex₂.total.map
          ((HomologicalComplex₂.flipFunctor _ _ _).map f) (ComplexShape.up ℤ) ∧
      (QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) ↔
        QuasiIso (HomologicalComplex₂.total.map
          ((HomologicalComplex₂.flipFunctor _ _ _).map f) (ComplexShape.up ℤ)))) := by
  sorry

end CategoryTheory.RelativeCyclic
