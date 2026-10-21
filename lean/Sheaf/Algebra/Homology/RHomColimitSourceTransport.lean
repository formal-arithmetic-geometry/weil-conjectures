/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.DerivedInternalHomFilteredColimitData
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.HomComplexShiftLeft

/-! # Source transport of the internal-Hom colimit comparison

Source: Stacks Project, Cohomology on Sites, Tags 0A8X, 0A95, 08J7 and 08JC;
the source-localization and signed-cocone calculation in the node
(blueprint: lem-sfb-rhom-colimit-source-transport).

The source of the comparison is the localization of the termwise colimit of the
fixed complex models. It is not defined as a colimit in the derived category.
The factorization and its natural comparison express independence of representatives.
The last clause specifies the shift transport as the image of a chain-level colimit map.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedHomUniverses

namespace CategoryTheory.RingedHomColimitTransport

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]
  {I : Type (max c v r)} [SmallCategory I]
  [HasColimitsOfShape I (Modules.{c, v, r} J R)]

/-- The termwise colimit of the fixed Hom models, followed by derived localization.
Source: Stacks 0A8X, 0A95 and the node's proof, steps 1--3
(blueprint: lem-sfb-rhom-colimit-source-transport).
This is functorial in the source complex and the entire target diagram. -/
noncomputable def strictColimit :
    (Complex.{c, v, r} J R)ᵒᵖ ⥤ (I ⥤ Complex.{c, v, r} J R) ⥤ D.{c, v, r, w} J R :=
  homComplexFunctor.{c, v, max c v r, max c v r} (R := R) ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (WeilConjectures.coefficientHomResolution.{r, c, v} J R) ⋙
    Functor.whiskeringRight I _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj (colim ⋙ DerivedCategory.Q)

/-- The target of the comparison, with a derived source and a complex target diagram.
Source: Stacks 08J7 and the node's definition of H(A,N_infinity)
(blueprint: lem-sfb-rhom-colimit-source-transport). -/
noncomputable def target :
    (D.{c, v, r, w} J R)ᵒᵖ ⥤ (I ⥤ Complex.{c, v, r} J R) ⥤ D.{c, v, r, w} J R :=
  Functor.curry.obj (derivedInternalHomOfUniverses.{c, v, r, w} J R) ⋙
    (Functor.whiskeringLeft _ _ _).obj (colim ⋙ DerivedCategory.Q)

/-- The actual Hom-colimit comparison descends in its source, commutes with every
source isomorphism, and commutes with the signed source shift, naturally in diagrams.
Source: Stacks 0A8X, 0A95, 08J7 and 08JC; the node's explicit cocone calculation
(blueprint: lem-sfb-rhom-colimit-source-transport).

Here G is the localized termwise-colimit model, rho identifies its complex-source
restriction, alpha is the canonical comparison, and t is its source-shift transport.
All of these are natural in the entire target diagram. The first equation fixes
alpha to Q(colimit.post), using the existing localization factorization. The second
is the source-isomorphism square; its vertical arrows are images of isomorphisms.
The third is the source-shift square with the already normalized signed sourceShift.
The final formula fixes t to the image under Q of the colimit of the signed chain
isomorphisms followed by the termwise colimit-shift identification, as a chain map;
LeftFormula specifies (-1)^(n*q).

Proof:
1. Put B_L(T)=Hom(L,J(T)) for the fixed functorial K-injective replacement.
The canonical map a_L=colimit.post N B_L is determined by a_L iota_i=B_L(u_i).
Precomposition commutes with postcomposition on each product component of Hom.
Testing on iota_i proves the source naturality square for every chain map.
2. Mod(R) is Grothendieck abelian with exact filtered colimits. Apply
src-weil-homology-preserves-exact-colimits in each integer degree: termwise
filtered colimits preserve objectwise quasi-isomorphisms without boundedness.
3. Stacks 0A95 (lem-pur-rhom-well-defined) makes B_v(T) a quasi-isomorphism
for a source quasi-isomorphism v. Step 2 does the same for its termwise colimit.
Thus L -> Q(a_L), as a functor into arrows of target-diagram functors, inverts
source quasi-isomorphisms. Localize it to obtain G, rho and alpha. The right
endpoint is the recorded derived internal Hom by its factorization comparison.
The localization universal property makes the representative identifications canonical.
4. Apply this localized functor to a source isomorphism and its inverse. This gives
the second equation and both inverse vertical maps, even without a chain-map lift.
5. On Hom degree q reindex p'=p+n and multiply by (-1)^(n*q). The inverse has
the same sign. The identity c_(q+1)=(-1)^n*c_q matches the cochain differential
on Hom(L[n],J(T)) with that on Hom(L,J(T))[-n]. These chain isomorphisms commute
with postcomposition by J(h); their sign depends only on n and q. This is precisely
LeftFormula and the normalization of sourceShift in the imported shift interface.
6. Take their colimit. In each degree the termwise colimit-shift identification
is the identity after reindexing; differentials agree with the same shift sign.
The last displayed formula is the image of this chain map. Testing the two chain-level
composites on the injections gives the shift square, and localizing retains it.
7. For a natural transformation of target diagrams, test on its colimit injections.
Functoriality of J, source precomposition and the signed reindexing commute with
these maps. All squares are therefore natural in the target diagram. Their vertical
maps are isomorphisms, so the horizontal maps are conjugate. No continuity or
boundedness assumption was used; filteredness was needed only in step 2. -/
theorem source_transport [IsFiltered I] :
    ∃ (G : (D.{c, v, r, w} J R)ᵒᵖ ⥤
        (I ⥤ Complex.{c, v, r} J R) ⥤ D.{c, v, r, w} J R)
      (rho : DerivedCategory.Q.op ⋙ G ≅ strictColimit.{c, v, r, w} J R)
      (alpha : G ⟶ target.{c, v, r, w} J R)
      (t : ∀ (A : D.{c, v, r, w} J R) (n : ℤ),
        G.obj (op (A⟦n⟧)) ≅ G.obj (op A) ⋙ shiftFunctor _ (-n)),
      (∀ (L : Complex.{c, v, r} J R) (N : I ⥤ Complex.{c, v, r} J R),
        (alpha.app (op (DerivedCategory.Q.obj L))).app N =
          (rho.hom.app (op L)).app N ≫
            DerivedCategory.Q.map (colimit.post N
              (WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L)) ≫
            (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R L
              (colimit N)).inv) ∧
      (∀ (A A' : D.{c, v, r, w} J R) (e : A ≅ A')
        (N : I ⥤ Complex.{c, v, r} J R),
        (G.mapIso e.op).hom.app N ≫ (alpha.app (op A)).app N =
          (alpha.app (op A')).app N ≫
            ((target.{c, v, r, w} J R).mapIso e.op).hom.app N) ∧
      (∀ (A : D.{c, v, r, w} J R) (n : ℤ)
        (N : I ⥤ Complex.{c, v, r} J R),
        (alpha.app (op (A⟦n⟧))).app N ≫
            (sourceShift.{c, v, r, w} J R A n).inv.app
              (DerivedCategory.Q.obj (colimit N)) =
          (t A n).hom.app N ≫ ((alpha.app (op A)).app N)⟦-n⟧') ∧
      (∀ (L : Complex.{c, v, r} J R) (n : ℤ),
        ∃ sigma : WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R (L⟦n⟧) ≅
            WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L ⋙
              shiftFunctor _ (-n),
          (∀ M : Complex.{c, v, r} J R,
            LeftFormula.{c, v, r} J R L
              ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj M) n
              (sigma.symm.app M)) ∧
          ∀ N : I ⥤ Complex.{c, v, r} J R,
            (rho.inv.app (op (L⟦n⟧))).app N ≫
                (G.map ((DerivedCategory.Q.commShiftIso n).inv.app L).op).app N ≫
                (t (DerivedCategory.Q.obj L) n).hom.app N =
              DerivedCategory.Q.map (colim.map (Functor.whiskerLeft N sigma.hom) ≫
                  (preservesColimitIso (shiftFunctor (Complex.{c, v, r} J R) (-n))
                    (N ⋙ WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r}
                      J R L)).inv) ≫
                (DerivedCategory.Q.commShiftIso (-n)).hom.app
                  (colimit (N ⋙ WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r}
                    J R L)) ≫
                ((rho.inv.app (op L)).app N)⟦-n⟧') := by
  sorry

end CategoryTheory.RingedHomColimitTransport
