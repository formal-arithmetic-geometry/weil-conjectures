/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.SemiSimplicialHypercover.Cohomology
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# Étale hypercovers of quasi-compact quasi-separated schemes

Let `X` be a quasi-compact quasi-separated scheme. A *qcqs hypercover* of `X` is a
semi-simplicial hypercover `U` of the small étale site of `X` all of whose terms `U_n` are
quasi-compact and quasi-separated (`AlgebraicGeometry.Scheme.IsQcqsHypercover`). These are the
finite hypercovers of blueprint `def-weil-pbc-finite-split-hypercover`, except that we work with
semi-simplicial hypercovers (face maps only), which is all the computation of cohomology uses.

Local lifting requirements can be met after refinement within qcqs hypercovers
(`AlgebraicGeometry.Scheme.IsQcqsHypercover.exists_refinement_lift`, blueprint
`lem-weil-pbc-hypercover-refinement`): a section of a quotient sheaf over `U_p` lifts after
replacing `U_p` by a finite disjoint union of affine étale schemes on which it lifts, and the
higher terms by the relative coskeleta `M_k(V) ×_{M_k(U)} U_k`. Hence the étale cohomology of `X`
with coefficients in sheaves of `Λ`-modules is computed by qcqs hypercovers
(`AlgebraicGeometry.Scheme.exists_cohomologyClass_eq_of_isQcqsHypercover`,
`AlgebraicGeometry.Scheme.exists_isCoboundary_of_isQcqsHypercover`, blueprint
`thm-weil-pbc-hypercover-cohomology`).

We also record the behaviour of hypercovers and of their cohomology classes under base change
along a morphism `g : Y ⟶ X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- A *qcqs hypercover* of `X`: a semi-simplicial hypercover of the small étale site of `X` all of
whose terms are quasi-compact and quasi-separated. (blueprint
`def-weil-pbc-finite-split-hypercover`) -/
structure IsQcqsHypercover (U : SemiSimplicialObject X.Etale) : Prop where
  isHypercover : U.IsHypercover X.smallEtaleTopology
  compactSpace (n : ℕ) : CompactSpace (U.obj n).left
  quasiSeparatedSpace (n : ℕ) : QuasiSeparatedSpace (U.obj n).left

/-- A quasi-compact quasi-separated scheme has a qcqs hypercover: the constant one on the terminal
object. -/
lemma exists_isQcqsHypercover [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ U : SemiSimplicialObject X.Etale, IsQcqsHypercover U :=
  sorry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Local lifting after refinement** (blueprint `lem-weil-pbc-hypercover-refinement`): a section
of a quotient sheaf over a term `U_p` of a qcqs hypercover lifts, after refinement of the
hypercover within qcqs hypercovers. -/
theorem IsQcqsHypercover.exists_refinement_lift [CompactSpace X] [QuasiSeparatedSpace X]
    {U : SemiSimplicialObject X.Etale} (hU : IsQcqsHypercover U) (p : ℕ)
    {G Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : G ⟶ Q) [Epi φ]
    (w : Q.obj.obj (op (U.obj p))) :
    ∃ (V : SemiSimplicialObject X.Etale) (_ : IsQcqsHypercover V) (f : V ⟶ U)
      (w' : G.obj.obj (op (V.obj p))), (φ.hom.app _).hom w' = (Q.obj.map (f.app p).op).hom w :=
  sorry

/-- **Étale cohomology is computed by qcqs hypercovers**: every class is the class of a cocycle
on a qcqs hypercover. (blueprint `thm-weil-pbc-hypercover-cohomology`) -/
theorem exists_cohomologyClass_eq_of_isQcqsHypercover [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (x : Ext (SemiSimplicialObject.constSheaf X.smallEtaleTopology Λ) F q) :
    ∃ (U : SemiSimplicialObject X.Etale) (hU : IsQcqsHypercover U) (z : F.obj.obj (op (U.obj q)))
      (hz : U.IsCocycle F q z), hU.isHypercover.cohomologyClass F q z hz = x :=
  sorry

/-- **A hypercover cocycle with vanishing class is a coboundary after refinement** within qcqs
hypercovers. (blueprint `thm-weil-pbc-hypercover-cohomology`) -/
theorem exists_isCoboundary_of_isQcqsHypercover [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    {U : SemiSimplicialObject X.Etale} (hU : IsQcqsHypercover U) (z : F.obj.obj (op (U.obj q)))
    (hz : U.IsCocycle F q z) (h : hU.isHypercover.cohomologyClass F q z hz = 0) :
    ∃ (V : SemiSimplicialObject X.Etale) (_ : IsQcqsHypercover V) (f : V ⟶ U),
      V.IsCoboundary F q ((F.obj.map (f.app q).op).hom z) :=
  sorry

section BaseChange

variable {Y : Scheme.{u}} (g : Y ⟶ X)

/-- The base change `U ×_X Y` of a semi-simplicial étale `X`-scheme along `g : Y ⟶ X`. -/
noncomputable abbrev _root_.CategoryTheory.SemiSimplicialObject.baseChange
    (U : SemiSimplicialObject X.Etale) : SemiSimplicialObject Y.Etale :=
  U.map (MorphismProperty.Over.pullback @Etale ⊤ g)

/-- Base change of hypercovers. -/
lemma _root_.CategoryTheory.SemiSimplicialObject.IsHypercover.baseChange
    {U : SemiSimplicialObject X.Etale} (hU : U.IsHypercover X.smallEtaleTopology) :
    (U.baseChange g).IsHypercover Y.smallEtaleTopology :=
  sorry

/-- Base change of qcqs hypercovers along a quasi-compact quasi-separated morphism. -/
lemma IsQcqsHypercover.baseChange [QuasiCompact g] [QuasiSeparated g]
    {U : SemiSimplicialObject X.Etale} (hU : IsQcqsHypercover U) :
    IsQcqsHypercover (U.baseChange g) :=
  sorry

/-- The pullback of a section of `F` over an étale `X`-scheme `V` to a section of `g^* F` over
`V ×_X Y`: the unit `F ⟶ g_* g^* F` evaluated at `V`. -/
noncomputable def _root_.AlgebraicGeometry.Etale.pullbackSection
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale) :
    F.obj.obj (op V) →ₗ[Λ] ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V)) :=
  (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app F).hom.app
    (op V)).hom

/-- The restriction map `H^q(X, F) ⟶ H^q(Y, g^* F)` of étale cohomology along `g : Y ⟶ X`:
pull back extension classes along the exact functor `g^*`, which preserves the constant sheaf
`Λ`. -/
noncomputable def _root_.AlgebraicGeometry.Etale.cohomologyRestrict
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    Ext (SemiSimplicialObject.constSheaf X.smallEtaleTopology Λ) F q →+
      Ext (SemiSimplicialObject.constSheaf Y.smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj F) q :=
  sorry

/-- Base change is compatible with classes of hypercover cocycles. -/
theorem _root_.AlgebraicGeometry.Etale.cohomologyRestrict_cohomologyClass
    {U : SemiSimplicialObject X.Etale} (hU : U.IsHypercover X.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (z : F.obj.obj (op (U.obj q)))
    (hz : U.IsCocycle F q z) :
    Etale.cohomologyRestrict Λ g F q (hU.cohomologyClass F q z hz) =
      (hU.baseChange g).cohomologyClass _ q (Etale.pullbackSection Λ g F (U.obj q) z)
        (by sorry) :=
  sorry

end BaseChange

end AlgebraicGeometry.Scheme
