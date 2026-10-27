module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCompactPerfectGenerator
import Sheaf.AlgebraicGeometry.SpacePerfectLocalizingGeneration
import WeilConjectures.CategoryTheory.CompactObject
import Sheaf.CategoryTheory.FunctorPreservesSequentialHomotopyColimit

/-! # A perfect telescope for countable quasi-coherent cohomology

Source: Stacks Project, spaces-perfect.tex, Tag 0CRV, implication (2) to (1);
derived.tex, Tags 090Z and 0CRH (blueprint: lem-sfb-space-countable-telescope).

The existing small affine ringed model represents the original small etale module topos.
Countability is tested on every affine object of the original etale site. A coproduct
is supplied by its cofan and universal property in the ambient derived category, so no
coproduct-existence hypothesis is imposed. The telescope triangle is the triangle of
`IsSequentialHomotopyColimit`, with its second arrow fixed by the specified legs.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Countable affine etale structure rings and countable cohomology sections give a
sequential perfect telescope, including the compatible maps to the given object.
Source: Stacks Project, spaces-perfect.tex, Tag 0CRV, implication (2) to (1),
and derived.tex, Tags 090Z and 0CRH (blueprint: lem-sfb-space-countable-telescope).

Proof:
1. Choose a compact perfect generator G of D_QCoh by
   lem-sfb-space-compact-perfect-generator. Apply lem-sfb-space-generator-dg-equivalence
   to obtain an exact equivalence F with the derived category of a DG algebra A and
   quasi-inverse T. It identifies H^i(A) with Hom(G,G[i]) and H^i(F(K)) with Hom(G,K[i]).
2. The affine countability hypotheses and lem-sfb-space-countable-perfect-ext, applied
   with E = G, make both groups countable in every degree. Thus
   lem-sfb-dg-countable-compact-telescope gives compact Q_m, transitions and compatible
   legs to F(K), with their telescope triangle.
3. An equivalence preserves coproducts: its Hom bijections identify maps from the image
   of a coproduct with families of maps from its summands. The same bijections preserve
   compactness (def-pc-compact-object). Therefore P_m = T(Q_m) are compact in D_QCoh,
   and lem-sfb-space-compact-objects-perfect makes them perfect. By
   lem-sfb-space-perfect-localizing-generation, these coproducts are ambient derived sums.
4. Apply lem-kun-functor-preserves-hocolim to T. Compose the transported legs with the
   counit T(F(K)) ≅ K. Functoriality and naturality retain their compatibility. The
   coproduct comparison transports the first arrow to 1-shift and the second arrow to
   the coproduct of these legs. The resulting distinguished triangle has third object
   K, exactly as in def-kun-truncations. Its coproduct universal property supplies B,
   the coprojections and hc below; hc.desc is the canonical map with those restrictions.
-/
theorem exists_perfect_telescope_of_countable
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules]
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : X.IsAbsolutelyQuasiSeparated)
    (hO : ∀ V : X.EtaleSite, IsAffine (X.etaleForget.obj V) →
      Countable (X.structureSheaf.obj.obj (op V)))
    (K : X.DerivedQCoh)
    (hK : ∀ (i : ℤ) (V : X.EtaleSite), IsAffine (X.etaleForget.obj V) →
      Countable (((X.smallModuleEquivalence.inverse).obj
        ((DerivedCategory.homologyFunctor X.SmallModules i).obj K.obj)).val.obj (op V))) :
    ∃ (P : ℕ → X.DerivedQCoh)
      (t : ∀ m : ℕ, (P m).obj ⟶ (P (m + 1)).obj)
      (a : ∀ m : ℕ, (P m).obj ⟶ K.obj)
      (B : X.DerivedModules) (ι : ∀ m : ℕ, (P m).obj ⟶ B)
      (hc : IsColimit (Cofan.mk B ι)) (q : K.obj ⟶ B⟦(1 : ℤ)⟧),
      (∀ m : ℕ, SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, 0, w}
        X.smallStructureSheaf (P m).obj) ∧
      (∀ m : ℕ, t m ≫ a (m + 1) = a m) ∧
      Triangle.mk (𝟙 B - (@id (B ⟶ B)
        (hc.desc (Cofan.mk B (fun m : ℕ ↦ t m ≫ ι (m + 1))))))
        (hc.desc (Cofan.mk K.obj a)) q ∈ distTriang X.DerivedModules := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
