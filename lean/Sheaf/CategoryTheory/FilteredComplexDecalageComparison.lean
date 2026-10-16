/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.CategoryTheory.FilteredComplexCanonicalModel
public import Sheaf.CategoryTheory.FilteredComplexDecalageTower
public import Sheaf.CategoryTheory.SpectralObjectPageTwoFunctor

/-! # Decalage and the canonical quotient sequence

Source: Stacks Project, Tags 012K and 015X.
(blueprint: lem-sp-filtered-complex-decalage-comparison).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The canonical sequence of a filtered complex is the sequence of the mapping-cone
spectral object of its decalage tower, naturally on the first page.
Source: Stacks Project, Tag 012K (cycle and boundary quotients) and Tag 015X,
Remark 13.26.15 (second filtration).
(blueprint: lem-sp-filtered-complex-decalage-comparison).

Proof. Write D for the decalage of F. Its tower at the integer q is D^(1-q).
The mapping cone of D^(1-a) -> D^(1-b), for a <= b, is quasi-isomorphic to its
cokernel, since the step inclusion is monic. Thus interval cohomology is the
cohomology of D^(1-b)/D^(1-a), compatibly with inclusions and connecting maps.
Substitute D^a K^n = F^(a+n) K^n intersect d^-1(F^(a+n+1) K^(n+1)).
Write Z_s(F)^(p,n) = F^p K^n intersect d^-1(F^(p+s) K^(n+1)). Its page
denominator is Z_(s-1)(F)^(p+1,n) plus d Z_(s-1)(F)^(p-s+1,n-1).
For a=p-n and r>=2, substitution and d squared equal to zero identify
Z_(r-1)(D)^(a,n) with Z_r(F)^(p,n), and identify their two denominator
terms respectively. Thus E_(r-1)(D)^(a,n-a) is E_r(F)^(p,n-p).
The spectral-object r-page is this (r-1)-page of D, with a=-q and n=p+q.
Its differential changes (a,n) to (a+r-1,n+1), hence (p,q) to
(p+r,q+1-r), as required. The identification sends a
representative to its own class; its differential is therefore represented
by the same differential of K. The next-page homology isomorphism sends a
successor cycle to its quotient class on both sides. Cancel the epimorphisms
from representative objects to prove these two compatibilities and assemble
the isomorphism of sequences. For a filtered map, its chain-map equation
preserves these representatives. Cancel the same epimorphisms to obtain the
page-two square. Infinite endpoints are zero and K by construction and do
not occur in these finite-page calculations. No boundedness assumption enters. -/
theorem filteredComplex_decalage_comparison
    (C : Type u) [Category.{v} C] [Abelian C] :
    ∃ e : ∀ U : FilteredObject (CochainComplex C ℤ),
      (filteredComplexCanonicalModel C).S.obj U ≅
        ((filteredComplexDecalageSpectralObjectFunctor C).obj U).E₂SpectralSequence,
      ∀ {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V) (p q : ℤ),
        (((filteredComplexCanonicalModel C).S.map t).hom 2).f (p, q) ≫
            (Abelian.SpectralObject.pageTwoComparison
              ((filteredComplexDecalageSpectralObjectFunctor C).obj V)
              (e V) p q (p + q) rfl).hom =
          (Abelian.SpectralObject.pageTwoComparison
            ((filteredComplexDecalageSpectralObjectFunctor C).obj U)
            (e U) p q (p + q) rfl).hom ≫
            (((filteredComplexDecalageSpectralObjectFunctor C).map t).hom (p + q)).app
              (ComposableArrows.mk₁
                (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt)))) := by
  sorry

end CategoryTheory
