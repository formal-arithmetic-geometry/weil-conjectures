/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.CategoryTheory.ExactCouple
import Sheaf.CategoryTheory.Filtration

/-!
# Convergence of bigraded exact couples

Source: blueprint, def-sp-convergence; Stacks Project, Homology, Sections 12.20 and 12.21,
and Definition 12.24.9 (Tag 012U) (blueprint: def-sp-convergence).

The natural-number index `r` below represents page `r + 2`. Colimits and inverse limits
are expressed by their universal properties on the consecutive arrows of the integer chain.
No infinite (co)limits or complete lattice of subobjects are assumed in the ambient category.
-/

universe u v

open CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Cycles and boundaries inside the initial page, with its canonical quotient maps.
The successor projection is induced by the preceding projection on cycles; this rules out
arbitrary identifications of the quotient with the next page.
Source: blueprint def-sp-convergence, cycle/boundary recursion; Stacks Section 12.20
(blueprint: def-sp-convergence). -/
structure CycleBoundaryTower (X : BigradedExactCouple C 0) where
  Z : ℕ → ∀ p q : ℤ, Subobject (X.E p q)
  B : ℕ → ∀ p q : ℤ, Subobject (X.E p q)
  B_le_Z : ∀ r p q, B r p q ≤ Z r p q
  Z_zero : ∀ p q, Z 0 p q = ⊤
  B_zero : ∀ p q, B 0 p q = ⊥
  projection : ∀ r p q, (Z r p q : C) ⟶ (X.pageCouple r).E p q
  projection_epi : ∀ r p q, Epi (projection r p q)
  projection_kernel : ∀ r p q,
    kernelSubobject (projection r p q) =
      Subobject.mk (Subobject.ofLE (B r p q) (Z r p q) (B_le_Z r p q))
  projection_zero : ∀ p q, projection 0 p q = (Z 0 p q).arrow
  Z_succ : ∀ r p q, Z (r + 1) p q =
    (Subobject.«exists» (Z r p q).arrow).obj
      ((Subobject.pullback (projection r p q)).obj
        (kernelSubobject ((X.pageCouple r).d p q)))
  B_succ : ∀ r p q, B (r + 1) p q =
    (Subobject.«exists» (Z r p q).arrow).obj
      ((Subobject.pullback (projection r p q)).obj
        (imageSubobject ((X.pageCouple r).dInto p q)))
  Z_decreasing : ∀ r p q, Z (r + 1) p q ≤ Z r p q
  B_increasing : ∀ r p q, B r p q ≤ B (r + 1) p q
  cycleLift : ∀ r p q,
    (Z (r + 1) p q : C) ⟶ kernel ((X.pageCouple r).d p q)
  cycleLift_comm : ∀ r p q,
    cycleLift r p q ≫ kernel.ι ((X.pageCouple r).d p q) =
      Subobject.ofLE _ _ (Z_decreasing r p q) ≫ projection r p q
  projection_succ : ∀ r p q,
    projection (r + 1) p q =
      cycleLift r p q ≫ (X.pageCouple r).derivedEProjection p q

/-- The canonical cycle/boundary tower exists. Start with the whole initial page and zero,
with its identity quotient. Inductively pull back the kernel and image of the differential
along the quotient, and embed these pullbacks in the initial page. Since the differential
squares to zero, boundaries lie in cycles. The epimorphic quotient of the lifted cycles by
the lifted boundaries is the homology object defining the next derived couple. Its projection
is the kernel lift followed by `derivedEProjection`. Pullback along an epimorphism preserves
these quotient presentations. This also gives the decreasing and increasing inclusions.
Source: blueprint def-sp-convergence; Stacks Sections 12.20--12.21
(blueprint: def-sp-convergence). -/
theorem cycleBoundaryTower_exists (X : BigradedExactCouple C 0) :
    Nonempty (CycleBoundaryTower X) := by
  sorry

/-- The cycle/boundary tower constructed recursively from the exact couple.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
noncomputable def cycleBoundaryTower (X : BigradedExactCouple C 0) : CycleBoundaryTower X :=
  Classical.choice (cycleBoundaryTower_exists X)

/-- Regularity means eventual constancy of cycles at every bidegree, with a bound that may
vary with the bidegree. Source: blueprint def-sp-convergence; Stacks Section 12.20
(blueprint: def-sp-convergence). -/
def IsRegular (X : BigradedExactCouple C 0) : Prop :=
  ∀ p q : ℤ, ∃ r : ℕ, ∀ t : ℕ, r ≤ t →
    X.cycleBoundaryTower.Z t p q = X.cycleBoundaryTower.Z r p q

/-- Iterate `alpha` to the left along a fixed total degree.
Source: blueprint def-sp-convergence, completeness clause (blueprint: def-sp-convergence). -/
def alphaIter (X : BigradedExactCouple C 0) :
    ∀ (r : ℕ) (p q : ℤ), X.D p q ⟶ X.D (p - r) (q + r)
  | 0, p, q => eqToHom (by congr 1 <;> omega)
  | r + 1, p, q => X.alpha p q ≫ alphaIter X r (p - 1) (q + 1) ≫
      eqToHom (by congr 1 <;> omega)

/-- The incoming `r`-fold iterate, with its endpoint transported to `(p,q)`.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
def incomingAlphaIter (X : BigradedExactCouple C 0) (r : ℕ) (p q : ℤ) :
    X.D (p + r) (q - r) ⟶ X.D p q :=
  X.alphaIter r (p + r) (q - r) ≫ eqToHom (by congr 1 <;> omega)

/-- Completeness of the couple: the intersection of all incoming `alpha` images is zero.
Expressing this as every common lower bound being zero does not assume other intersections.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
def IsComplete (X : BigradedExactCouple C 0) : Prop :=
  ∀ (p q : ℤ) (S : Subobject (X.D p q)),
    (∀ r : ℕ, S ≤ imageSubobject (X.incomingAlphaIter r p q)) → S = ⊥

/-- Boundedness requires finite support on each total-degree diagonal of the initial page.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
def IsBounded (X : BigradedExactCouple C 0) : Prop :=
  ∀ n : ℤ, Set.Finite {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero (X.E pq.1 pq.2)}

/-- The limiting cycles and boundaries, when their greatest lower and least upper bounds
exist. Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
structure LimitSubobjects (X : BigradedExactCouple C 0) where
  Z : ∀ p q : ℤ, Subobject (X.E p q)
  B : ∀ p q : ℤ, Subobject (X.E p q)
  Z_glb : ∀ p q, IsGLB (Set.range (fun r ↦ X.cycleBoundaryTower.Z r p q)) (Z p q)
  B_lub : ∀ p q, IsLUB (Set.range (fun r ↦ X.cycleBoundaryTower.B r p q)) (B p q)

/-- Every limiting boundary lies in every limiting cycle. For any two finite indices,
move to their maximum: increasing boundaries lie in the cycles there, which lie in the
earlier cycles. The universal properties of the union and intersection give the result.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
theorem limitBoundary_le_cycle (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (p q : ℤ) : L.B p q ≤ L.Z p q := by
  sorry

/-- The infinite page is the quotient of limiting cycles by limiting boundaries.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
noncomputable def pageInfinity (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (p q : ℤ) : C :=
  cokernel (Subobject.ofLE (L.B p q) (L.Z p q) (limitBoundary_le_cycle X L p q))

/-- The initial `g`, transported from its type-zero target to `(p,q)`.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
def initialG (X : BigradedExactCouple C 0) (p q : ℤ) : X.D p q ⟶ X.E p q :=
  X.g p q ≫ eqToHom (by congr 1 <;> omega)

/-- The initial `g` lands in every finite cycle object, hence in their intersection.
The exact-couple cycle formula is `Z_{r+2} = f⁻¹(im alpha^r)` inside the initial page,
with the component indices determined by the bidegrees. Prove it by induction from
`Z₂ = E₂`, using the derived-couple restriction equations and the successor projection.
Since `g ≫ f = 0`, the image of the initial `g` lies in every such inverse image:
the zero morphism factors through each incoming iterate of `alpha`. Thus its image is
a common lower bound of the finite cycles, so `L.Z_glb` places it below `L.Z`.
The image factorization then gives the required morphism into the limiting cycles.
Source: blueprint def-sp-convergence; Stacks Section 12.21
(blueprint: def-sp-convergence). -/
theorem g_factors_limitCycles (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (p q : ℤ) : (L.Z p q).Factors (X.initialG p q) := by
  sorry

/-- The canonical map from `D` to the infinite page, induced by `g`.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
noncomputable def toPageInfinity (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (p q : ℤ) : X.D p q ⟶ X.pageInfinity L p q :=
  (L.Z p q).factorThru (X.initialG p q) (g_factors_limitCycles X L p q) ≫
    cokernel.π (Subobject.ofLE (L.B p q) (L.Z p q) (limitBoundary_le_cycle X L p q))

/-- The consecutive transition on the total-degree-`n` diagonal.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
def alphaDiagonal (X : BigradedExactCouple C 0) (n p : ℤ) :
    X.D (p + 1) (n - (p + 1)) ⟶ X.D p (n - p) :=
  X.alpha (p + 1) (n - (p + 1)) ≫ eqToHom (by congr 1 <;> omega)

/-- A colimit of the `D` diagonal along `alpha`, directed towards negative infinity.
The universal property for consecutive arrows is the colimit universal property: every
arrow of the ordered integer chain is a finite composite of these arrows.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
structure AlphaColimit (X : BigradedExactCouple C 0) (n : ℤ) where
  obj : C
  ι : ∀ p : ℤ, X.D p (n - p) ⟶ obj
  comm : ∀ p, X.alphaDiagonal n p ≫ ι p = ι (p + 1)
  isColimit : ∀ (T : C) (f : ∀ p : ℤ, X.D p (n - p) ⟶ T),
    (∀ p, X.alphaDiagonal n p ≫ f p = f (p + 1)) →
    ∃! h : obj ⟶ T, ∀ p, ι p ≫ h = f p

/-- The image filtration is decreasing. The cocone equation factors the next canonical
map through the current one, so its image is contained in the current image. Iterating
this inclusion a finite number of times proves antitonicity for arbitrary integers.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
theorem imageFiltration_antitone (X : BigradedExactCouple C 0) (n : ℤ)
    (A : AlphaColimit X n) : Antitone (fun p ↦ imageSubobject (A.ι p)) := by
  sorry

/-- The decreasing filtration on the alpha-colimit by images of its canonical maps.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
noncomputable def imageFiltration (X : BigradedExactCouple C 0) (n : ℤ)
    (A : AlphaColimit X n) : DecreasingFiltration A.obj where
  step p := imageSubobject (A.ι p)
  antitone_step := imageFiltration_antitone X n A

/-- The canonical map from `D^{p,q}` onto the graded piece of its image filtration.
Source: blueprint def-sp-convergence (blueprint: def-sp-convergence). -/
noncomputable def toGradedPiece (X : BigradedExactCouple C 0)
    (A : ∀ n : ℤ, AlphaColimit X n) (p q : ℤ) :
    X.D p q ⟶ (X.imageFiltration (p + q) (A (p + q))).gradedPiece p :=
  eqToHom (by congr 1; omega) ≫ factorThruImageSubobject ((A (p + q)).ι p) ≫
    cokernel.π (Subobject.ofLE _ _
      ((X.imageFiltration (p + q) (A (p + q))).antitone_step (by omega)))

/-- Weak convergence: the two canonical maps are epimorphic and have identical kernels.
Source: blueprint def-sp-convergence; Stacks Tag 012U (blueprint: def-sp-convergence). -/
def WeaklyConvergesTo (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) : Prop :=
  ∀ p q : ℤ, Epi (X.toPageInfinity L p q) ∧ Epi (X.toGradedPiece A p q) ∧
    kernelSubobject (X.toPageInfinity L p q) = kernelSubobject (X.toGradedPiece A p q)

/-- The canonical associated-graded isomorphisms induced by weak convergence exist.
Both targets are the quotient of `D^{p,q}` by the same kernel, because both maps are
epimorphisms in an abelian category. The first isomorphism theorem gives their unique
comparison isomorphism commuting with the two quotient maps.
Source: blueprint def-sp-convergence; Stacks Tag 012U (blueprint: def-sp-convergence). -/
theorem weakConvergence_comparison (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) (h : X.WeaklyConvergesTo L A) (p q : ℤ) :
    ∃! e : X.pageInfinity L p q ≅
      (X.imageFiltration (p + q) (A (p + q))).gradedPiece p,
      X.toPageInfinity L p q ≫ e.hom = X.toGradedPiece A p q := by
  sorry

/-- Abutting means weak convergence and separated, exhaustive image filtrations.
Source: blueprint def-sp-convergence; Stacks Tag 012U (blueprint: def-sp-convergence). -/
def AbutsTo (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) : Prop :=
  X.WeaklyConvergesTo L A ∧ ∀ n : ℤ,
    (X.imageFiltration n (A n)).IsSeparated ∧ (X.imageFiltration n (A n)).IsExhaustive

/-- A later filtration step is killed by the earlier quotient map: its inclusion factors
through the earlier step, whose composite with its cokernel projection is zero.
Source: blueprint def-sp-convergence, inverse-limit clause (blueprint: def-sp-convergence). -/
theorem filtrationStep_comp_quotient_zero {T : C} (F : DecreasingFiltration T) (p : ℤ) :
    (F.step (p + 1)).arrow ≫ cokernel.π (F.step p).arrow = 0 := by
  sorry

/-- The transition `A/F^{p+1} → A/F^p` of the inverse system of quotients.
Source: blueprint def-sp-convergence; Stacks Tag 012U (blueprint: def-sp-convergence). -/
noncomputable def quotientTransition {T : C} (F : DecreasingFiltration T) (p : ℤ) :
    cokernel (F.step (p + 1)).arrow ⟶ cokernel (F.step p).arrow :=
  cokernel.desc (F.step (p + 1)).arrow (cokernel.π (F.step p).arrow)
    (filtrationStep_comp_quotient_zero F p)

/-- The canonical cone `A → A/F^p` is an inverse limit. This is equivalent to the
canonical map `A → lim_p A/F^p` being an isomorphism, and includes existence of that limit.
Source: blueprint def-sp-convergence; Stacks Tag 012U (blueprint: def-sp-convergence). -/
def IsInverseLimit {T : C} (F : DecreasingFiltration T) : Prop :=
  ∀ (S : C) (f : ∀ p : ℤ, S ⟶ cokernel (F.step p).arrow),
    (∀ p, f (p + 1) ≫ quotientTransition F p = f p) →
    ∃! h : S ⟶ T, ∀ p, h ≫ cokernel.π (F.step p).arrow = f p

/-- Convergence means regularity, abutting, and completeness of every abutment filtration
in the inverse-limit sense. Completeness of the couple itself is the separate predicate
`IsComplete` above. Source: blueprint def-sp-convergence; Stacks Tag 012U
(blueprint: def-sp-convergence). -/
def ConvergesTo (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) : Prop :=
  X.IsRegular ∧ X.AbutsTo L A ∧ ∀ n : ℤ, IsInverseLimit (X.imageFiltration n (A n))

end CategoryTheory.BigradedExactCouple
