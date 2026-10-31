/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.RelativeEtaleZariskiDerived
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Relative quasi-coherent étale/Zariski cohomology-sheaf comparison

Source: Stacks Project, Étale Cohomology, Tag 03P2; Cohomology of Schemes,
Tag 02KH; Cohomology on Sites, Tag 07A8; Derived Categories, Tag 015F
(blueprint: lem-fd-qcoherent-relative-etale-zariski-cohomology).

The comparison is cohomology of the canonical derived comparison, preceded by
its exact change-of-topology cohomology identification. The target is written
as H^q of abelian derived direct image, the definition of the higher direct image.
The coefficient universe and canonical sectionwise lift are those of the derived
comparison; no new topology-change or Frobenius construction is chosen here.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical degree-q comparison: first identify U_S epsilon_S^* R^q f_Zar,* M
with H^q(U_S epsilon_S^* Rf_Zar,* M[0]), then apply H^q to the canonical derived arrow.
Its target is R^q f_Et,*^Ab(U_X M_Et), expressed as cohomology of derived direct image.
This definition uses the normalized derived arrow, not an independently chosen isomorphism.

Source: Stacks Project, Tags 03P2, 02KH, 07A8 and 015F
(blueprint: lem-fd-qcoherent-relative-etale-zariski-cohomology). -/
def RelativeEtaleZariskiContext.cohomologyArrow
    {X S : Scheme.{u}} {f : X ⟶ S} (c : RelativeEtaleZariskiContext f)
    (M : X.Modules) (q : ℕ) :
    (c.target.extension ⋙ relativeEtaleForgetModules S).obj
      (((pushforward f).rightDerived q).obj M) ⟶
    (DerivedCategory.Plus.homologyFunctor (RelativeEtaleAbelianSheaves S) q).obj
      ((Etale.lowerStar AddCommGrpCat.{u+1} f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (RelativeEtaleAbelianSheaves X) 0).obj
          ((c.source.extension ⋙ relativeEtaleForgetModules X).obj M))) :=
  (c.homologyIdentification M q).hom ≫
    (DerivedCategory.Plus.homologyFunctor (RelativeEtaleAbelianSheaves S) q).map (c.arrow M)

/-- For a quasi-compact quasi-separated f and a quasi-coherent module F, the canonical
cohomology comparisons are isomorphisms in every nonnegative degree, natural in every
O_X-linear map F → G of quasi-coherent modules. For F = O_X in prime characteristic p,
they intertwine additive Frobenius, whose source action is p-semilinear on all local
sections of the small étale site.

Source: Stacks Project, Tags 03P2, 02KH, 07A8 and 015F
(blueprint: lem-fd-qcoherent-relative-etale-zariski-cohomology).

Proof: 1. Use lem-fd-qcoherent-relative-etale-zariski-derived to obtain the exact
change-of-topology functors and the canonical invertible derived arrow c_F. Forgetting
module structure is exact: def-weil-sheaf-of-modules-category computes kernels sectionwise
and cokernels by sheafifying sectionwise cokernels, both unchanged after forgetting.
Apply lem-weil-pbc-exact-functor-bounded-below to E = U_S epsilon_S^*. Its canonical
cohomology isomorphism, together with the derived-direct-image cohomology identification,
is c.homologyIdentification.

2. Define beta_F^q by this identification followed by H^q(c_F), precisely cohomologyArrow.
Its inverse is H^q(c_F inverse) followed by the inverse identification. The definitions
of derived cohomology sheaves, abelian higher direct image, and ringed-space derived
module direct image identify its two endpoints with the displayed sheaves of the node.

3. Apply H^q to the derived naturality square for F → G and use the naturality of the
exact-functor cohomology identification. This gives the naturality equation below.

4. For prime p with p O_S = 0 and F = O_X, use the separate additive Frobenius clause of
the derived comparison. Apply H^q to its commuting square and conjugate the source action
by c.homologyIdentification. This is exactly t.homologyAction, so the cohomology square
commutes. The derived node's local section clause gives t.sectionAction(a • e) =
a^p • t.sectionAction(e). Frobenius is never treated as an O_X-linear endomorphism. -/
theorem relativeEtaleZariskiCohomologyComparison
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] [QuasiCompact f] [QuasiSeparated f] :
    ∃ c : RelativeEtaleZariskiContext f,
      (∀ q : ℕ, IsIso (c.cohomologyArrow F q)) ∧
      (∀ (G : X.Modules) [G.IsQuasicoherent] (g : F ⟶ G) (q : ℕ),
        (c.target.extension ⋙ relativeEtaleForgetModules S).map
            (((pushforward f).rightDerived q).map g) ≫ c.cohomologyArrow G q =
          c.cohomologyArrow F q ≫
            (DerivedCategory.Plus.homologyFunctor (RelativeEtaleAbelianSheaves S) q).map
              ((Etale.lowerStar AddCommGrpCat.{u+1} f).rightDerivedFunctorPlus.map
                ((DerivedCategory.Plus.singleFunctor (RelativeEtaleAbelianSheaves X) 0).map
                  ((c.source.extension ⋙ relativeEtaleForgetModules X).map g)))) ∧
      (∀ (p : ℕ), p.Prime → (p : S.ringCatSheaf.obj.obj (op ⊤)) = 0 →
        F = SheafOfModules.unit X.ringCatSheaf →
        ∃ t : RelativeEtaleZariskiFrobeniusSquare c p,
          (∀ q : ℕ,
            t.homologyAction q ≫
                c.cohomologyArrow (SheafOfModules.unit X.ringCatSheaf) q =
              c.cohomologyArrow (SheafOfModules.unit X.ringCatSheaf) q ≫
                (DerivedCategory.Plus.homologyFunctor (RelativeEtaleAbelianSheaves S) q).map
                  t.targetAction) ∧
          ∀ (q : ℕ) (V : S.Etale) (a : (smallEtaleModuleRing S).obj.obj (op V))
            (e : (c.target.extension.obj
              (((pushforward f).rightDerived q).obj
                (SheafOfModules.unit X.ringCatSheaf))).val.obj (op V)),
            t.sectionAction q V (a • e) = a ^ p • t.sectionAction q V e) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
