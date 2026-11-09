/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverGeometry
public import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
public import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSiteLimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSubsite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.CategoryTheory.SiteFiniteBasisHypercoverExistence
public import Mathlib.CategoryTheory.Sites.Precoverage
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import WeilConjectures.CategoryTheory.ProperFaceMatchingObject
public import WeilConjectures.CategoryTheory.SiteFiniteBasisHypercoverStep
public import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtension
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionBase
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Data.Finite.Sigma
public import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionConstruction
public import WeilConjectures.AlgebraicGeometry.SiteHypercoverAttachmentComposition
public import WeilConjectures.AlgebraicGeometry.SiteHypercoverAttachmentOperators
public import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionSplit
public import Mathlib.Data.Finite.Sum
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import WeilConjectures.AlgebraicGeometry.ProEtaleQcAffineContractibleCover
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverWeak
public import WeilConjectures.AlgebraicGeometry.ProEtale.Hypercover.ProEtaleHypercoverTotal
public import Mathlib.Algebra.Homology.CochainComplexPlus
import WeilConjectures.AlgebraicGeometry.ProEtale.Hypercover.ProEtaleHypercoverQuasiIso
import WeilConjectures.AlgebraicGeometry.ProEtale.Hypercover.ProEtaleHypercoverInjectiveComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Hypercover.ProEtaleHypercoverInjectiveRow
import Mathlib.Algebra.Homology.HomotopyCofiber
public import WeilConjectures.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex

/-!
# Bounded-below derived evaluation by weakly contractible hypercovers

Source: Stacks Project, proetale.tex, Tag 09A2, lemma-compute-cohomology;
sites-cohomology.tex, Tag 0946, lemma-w-contractible
(blueprint: lem-weil-pbc-proetale-hypercover-computes-bounded-complex).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

-- Explicit derived comparisons expand the section and evaluation functor compositions.
set_option backward.isDefEq.respectTransparency false in
/-- A weakly contractible hypercover computes bounded-below derived evaluation.
Source: Stacks Project, Tags 09A2 and 0946, with ringed-module coefficients
(blueprint: lem-weil-pbc-proetale-hypercover-computes-bounded-complex).

The first conjunct gives a comparison for every bounded-below complex and every
bounded-below termwise-injective chain resolution. Its target is precisely the
resolution definition of derived evaluation in the node. The comparisons are
natural under coefficient chain maps and resolution maps commuting up to homotopy.
Taking an identity coefficient map gives independence of the resolution. The
second conjunct is invariance of total sections under bounded-below quasi-isomorphisms.
`CochainComplex.Plus` imposes strict boundedness of terms, not just of cohomology.
No affineness or qcqs hypothesis is imposed on the given hypercover or its base.

Proof: evaluation at each weakly contractible U_p preserves homology of module
complexes. Restriction of scalars to R(W) is exact, so the section columns carry
coefficient quasi-isomorphisms to quasi-isomorphisms. Truncation at an outer degree
larger than the degree under consideration reduces total comparison to finitely
many columns. The source library proves that finite comparison, giving T(i) and
the last conjunct directly, without reindexing the coefficient degree.

For each injective I, matching-map local lifting makes the existing ringed
hypercover augmentation theorem applicable. Transport the pro-etale site along
ULiftHom so its object and morphism universes agree; pull back its precoverage and
transport I along the module-sheaf equivalence. The exact alternating section
sequence is the row augmentation quasi-isomorphism, including the zero extension
in negative degrees. Apply the same total comparison to flipped bicomplexes and
the single-column source to prove that the explicitly constructed natural
augmentation alpha:J(W)→T(J) is a quasi-isomorphism.

Define the comparison by Q(T(i)) followed by the inverse of Q(alpha_J). For
naturality, the augmentation commutes strictly with every coefficient chain map.
Any functor inverting bounded-below quasi-isomorphisms identifies homotopic maps:
the cylinder stays bounded below, its projection is a homotopy equivalence, and
its two inclusions become equal after inverting that projection. Apply this to
T followed by Q, then cancel Q(alpha_L). Resolutions, comparison maps and their
homotopy are inputs to this declaration, so neither resolution existence nor
K-injective comparison is used. -/
theorem hypercover_computes_boundedBelow_complex (X : Scheme.{u})
    (R : Sheaf (topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U : SimplicialObject (Over W))
    [HasDerivedCategory.{w} (ModuleCat.{u + 1}
      (((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj (op W)))]
    (hweak : ∀ (n : ℕ) (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (U _⦋n⦌).left)))
    (hzero : Epi ((topology X).yoneda.map (U _⦋0⦌).hom))
    (hone : ∃ c : Fan (fun _ : Fin 2 ↦ U _⦋0⦌), Nonempty (IsLimit c) ∧
      ∃ μ : U _⦋1⦌ ⟶ c.pt,
        (∀ i : Fin 2, μ ≫ c.proj i = U.δ i) ∧
        Epi ((topology X).yoneda.map μ.left))
    (hhigher : ∀ n : ℕ,
      ∃ c : Cone (SimplicialObject.matchingBoundaryIndex U n).multicospan,
        Nonempty (IsLimit c) ∧ ∃ μ : U _⦋n + 2⦌ ⟶ c.pt,
          (∀ i : Fin (n + 3), μ ≫ c.π.app (WalkingMulticospan.left i) = U.δ i) ∧
          Epi ((topology X).yoneda.map μ.left)) :
    (∃ c : ∀ (E J : CochainComplex.Plus (ringedSiteModules.{u + 1}
          ((sheafCompose (topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))),
      (∀ n : ℤ, Injective (J.obj.X n)) →
      (i : E.obj ⟶ J.obj) → QuasiIso i →
      (DerivedCategory.Q.obj ((hypercoverTotal X R W U).obj E.obj) ≅
        DerivedCategory.Q.obj (((SheafOfModules.evaluation _ (op W)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J.obj)),
      ∀ (E F J L : CochainComplex.Plus (ringedSiteModules.{u + 1}
          ((sheafCompose (topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
        (hJ : ∀ n : ℤ, Injective (J.obj.X n))
        (hL : ∀ n : ℤ, Injective (L.obj.X n))
        (i : E.obj ⟶ J.obj) (j : F.obj ⟶ L.obj)
        (hi : QuasiIso i) (hj : QuasiIso j) (f : E ⟶ F) (a : J ⟶ L),
        Nonempty (Homotopy (i ≫ a.hom) (f.hom ≫ j)) →
        DerivedCategory.Q.map ((hypercoverTotal X R W U).map f.hom) ≫
            (c F L hL j hj).hom =
          (c E J hJ i hi).hom ≫ DerivedCategory.Q.map
            (((SheafOfModules.evaluation _ (op W)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map a.hom)) ∧
    (∀ (E F : CochainComplex.Plus (ringedSiteModules.{u + 1}
          ((sheafCompose (topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) (f : E ⟶ F),
      QuasiIso f.hom → QuasiIso ((hypercoverTotal X R W U).map f.hom)) := by
  let T := hypercoverTotal X R W U
  let ev := (SheafOfModules.evaluation.{u + 1}
    ((sheafCompose (topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)).mapHomologicalComplex
        (.up ℤ)
  let α := hypercoverAugmentation X R W U
  have hT := hypercoverTotal_map_quasiIso_of_weaklyContractible X R W U hweak
  have hα (J : CochainComplex.Plus (ringedSiteModules.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
      (hJ : ∀ n : ℤ, Injective (J.obj.X n)) : QuasiIso (α.app J.obj) := by
    apply hypercoverAugmentation_quasiIso_of_injective_rows X R W U ?_ J hJ
    intro I hI
    exact hypercoverRowAugmentationComplex_quasiIso_of_injective
      X R W U hzero hone hhigher I
  let c (E J : CochainComplex.Plus (ringedSiteModules.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
      (hJ : ∀ n : ℤ, Injective (J.obj.X n))
      (i : E.obj ⟶ J.obj) (hi : QuasiIso i) :
      DerivedCategory.Q.{w}.obj (T.obj E.obj) ≅ DerivedCategory.Q.{w}.obj (ev.obj J.obj) := by
    have := hT E J ⟨i⟩ hi
    have := hα J hJ
    exact asIso (DerivedCategory.Q.{w}.map (T.map i)) ≪≫
      (asIso (DerivedCategory.Q.{w}.map (α.app J.obj))).symm
  refine ⟨⟨c, ?_⟩, hT⟩
  intro E F J L hJ hL i j hi hj f a ⟨h⟩
  have := hα J hJ
  have := hα L hL
  have hnat : DerivedCategory.Q.{w}.map (ev.map a.hom) ≫
        DerivedCategory.Q.{w}.map (α.app L.obj) =
      DerivedCategory.Q.{w}.map (α.app J.obj) ≫ DerivedCategory.Q.{w}.map (T.map a.hom) := by
    rw [← DerivedCategory.Q.{w}.map_comp, ← DerivedCategory.Q.{w}.map_comp]
    exact congrArg DerivedCategory.Q.{w}.map (α.naturality a.hom)
  have hhom : DerivedCategory.Q.{w}.map (T.map (i ≫ a.hom)) =
      DerivedCategory.Q.{w}.map (T.map (f.hom ≫ j)) := by
    apply map_eq_of_boundedBelow_homotopy (T ⋙ DerivedCategory.Q.{w}) ?_ E L _ _ h
    intro K M g hg
    have := hT K M g hg
    change IsIso (DerivedCategory.Q.{w}.map (T.map g.hom))
    infer_instance
  apply (cancel_mono (DerivedCategory.Q.{w}.map (α.app L.obj))).mp
  dsimp only [c, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hnat, IsIso.inv_hom_id_assoc]
  simpa only [Functor.map_comp] using hhom.symm

end AlgebraicGeometry.Scheme.ProEt
