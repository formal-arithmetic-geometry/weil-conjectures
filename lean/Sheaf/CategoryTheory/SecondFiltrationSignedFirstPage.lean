/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.CategoryTheory.FilteredComplexPageDifferential
import Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries

/-! # The signed row comparison for one concrete quotient page

Source: Stacks Project, Homology, Tag 0130, `lemma-ss-double-complex`, clauses 2 and 4,
and Tag 012K, the representative formula for a filtered-complex differential.
(blueprint: lem-sp-second-filtration-signed-first-page).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The first concrete cycle/boundary quotient page is row cohomology, and the
representative differential carries the totalization sign. This concerns a single
page with specified differential, without constructing a spectral sequence or
asserting anything about higher pages.
Source: Stacks Project, Homology, Tag 0130, `lemma-ss-double-complex`, clauses 2 and 4,
and Tag 012K, the displayed representative differential formula.
(blueprint: lem-sp-second-filtration-signed-first-page).

Proof. Write J for the flipped mapped bicomplex and n = s+r. The diagonal
coprojection from J^(r,s) lifts to the filtration step L^s in degree n. Modulo
L^(s+1), the other diagonal summands disappear. Projecting this lift gives the
canonical isomorphism from J^(r,s) to gr^s L in degree n: its inverse is the
projection onto that summand, which kills every summand in L^(s+1). These maps
are inverse by the coproduct universal property. The total differential on
J^(r,s) has a resolution component and a complex-index component; the latter
lands in L^(s+1), so the graded differential is the resolution differential.
Thus its kernel and image identify with the row cycles and boundaries. The
first filtered cycles and boundaries are exactly that kernel and image.
Taking their cokernel identifies the actual object filteredComplexPageObject
at (s,r) with row cohomology. Extension by zero from the natural numbers
preserves cohomology in degree r, including degree zero.

To compute the differential, restrict the same diagonal lift to row cycles.
Its resolution component is zero. Its remaining total differential is
(-1)^r times the complex-index map J^(r,s) to J^(r,s+1). This is again a row
cycle since the bicomplex differentials commute. Apply D.on_representatives
with these two lifts and their graded cycle classes. The result is the desired
equation after precomposition with the epic row-cycles-to-homology projection;
cancel that epimorphism. Row boundaries map to row boundaries because the
complex-index differential is a row chain map, so the induced map is exactly
HomologicalComplex.homologyMap of F(I.d s (s+1)). Scalars commute with the
quotient projections by preadditivity. The construction uses only the
specified representative differential and the diagonal coprojections, not any
choice of arbitrary isomorphisms between page objects. -/
theorem secondFiltration_signed_firstPage
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (hbelow : ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero (I.X s))
    (L : DecreasingFiltration
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
        (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).secondFiltration n).step
        p)
    (D : FilteredComplexPageDifferential
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
        (ComplexShape.up ℤ)) L 1) :
    ∃ e : ∀ (r : ℕ) (s : ℤ), D.page.X (s, (r : ℤ)) ≅
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).homology r,
      ∀ (r : ℕ) (s : ℤ),
        D.page.d (s, (r : ℤ)) (s + 1, (r : ℤ)) ≫ (e r (s + 1)).hom =
          (r : ℤ).negOnePow • ((e r s).hom ≫ HomologicalComplex.homologyMap
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (I.d s (s + 1))) r) := by sorry

end CategoryTheory.Functor
