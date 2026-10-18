/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import Sheaf.RepresentationTheory.ProfiniteStableLattice
import Sheaf.Paper.GaloisLisseRepresentations
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.RepresentationTheory.Rep.Basic
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.Paper.LisseAdicFiberFunctors
import Sheaf.Paper.LisseModuleSheaves
import Sheaf.Paper.LisseTensorScalarExtension
import Sheaf.RepresentationTheory.LAdic
import Sheaf.SixFunctors.IntegralLisseReductionEquivalence
import Sheaf.AlgebraicGeometry.LisseLatticeCoefficientsSized

/-!
# Global integral lattices on smooth geometric fibres

Source: Bhatt--Scholze, Lemmas 7.4.7 and 7.4.10 and Proposition 6.8.4(1),(4);
Stacks Project, Tags 056T, 01VB and 0BQ3
(blueprint: lem-a1-smooth-lisse-integral-lattice).

The integral ring is the recorded inverse limit of finite constant coefficient sheaves.
The rational ring is its sheaf localization at the recorded uniformizer. A lattice is
an actual subobject of the restriction of the given rational sheaf. The normalization
on `1 ⊗ m` says that its rationalization isomorphism is induced by that inclusion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor
open scoped ChangeOfRings

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})

/-- Forgetting abelian groups preserves the smaller filtered colimits used on this site.
Source: the size convention in Bhatt--Scholze, Definition 6.8.3
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
instance (priority := 100000) smoothLatticeForgetAbFiltered [UnivLE.{u + 1, w}] :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1} (forget AddCommGrpCat.{w}) :=
  preservesFilteredColimitsOfSize_of_univLE.{w, w, u + 1, u + 1}
    (forget AddCommGrpCat.{w})

/-- Sheafification in any universe containing the pro-etale site, by transport of
the existing Grothendieck-abelian construction on a small model.
Source: Bhatt--Scholze, Definition 6.8.3, size convention
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
instance (priority := 100000) smoothLatticeSiteAbSheafify (T : Scheme.{u})
    [Small.{w} T.ProEt] [LocallySmall.{w} T.ProEt] :
    HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{w} :=
  letI : EssentiallySmall.{w} T.ProEt := inferInstance
  letI : HasSheafify ((equivSmallModel.{w} T.ProEt).inverse.inducedTopology
      (Scheme.ProEt.topology T)) AddCommGrpCat.{w} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  hasSheafifyEssentiallySmallSite.{u, w, u + 1, w + 1, w} _ _

/-- Sheafification on each slice in the common coefficient universe. This transports
the existing small-site construction without identifying object and arrow universes.
Source: the size convention for Bhatt--Scholze, Definition 6.8.3
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
instance (priority := 100000) smoothLatticeSliceAbSheafify (T : Scheme.{u}) (U : T.ProEt)
    [Small.{w} (Over U)] [LocallySmall.{w} (Over U)] :
    HasSheafify ((Scheme.ProEt.topology T).over U) AddCommGrpCat.{w} :=
  letI : EssentiallySmall.{w} (Over U) := inferInstance
  letI : HasSheafify
      ((equivSmallModel.{w} (Over U)).inverse.inducedTopology
        ((Scheme.ProEt.topology T).over U)) AddCommGrpCat.{w} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  hasSheafifyEssentiallySmallSite.{u, w, u + 1,
    w + 1, w} _ _

/-- Local bijectivity on the same slices supplies the ordinary module sheafification API.
Source: the size convention for Bhatt--Scholze, Definition 6.8.3
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
instance (priority := 100000) smoothLatticeSliceAbLocallyBijective
    (T : Scheme.{u}) (U : T.ProEt)
    [Small.{w} (Over U)] [LocallySmall.{w} (Over U)] :
    ((Scheme.ProEt.topology T).over U).WEqualsLocallyBijective
      AddCommGrpCat.{w} :=
  letI : EssentiallySmall.{w} (Over U) := inferInstance
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Local bijectivity for the base site in the common coefficient universe.
Source: Bhatt--Scholze, Definition 6.8.3, size convention
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
instance (priority := 100000) smoothLatticeSiteAbLocallyBijective (T : Scheme.{u})
    [Small.{w} T.ProEt] [LocallySmall.{w} T.ProEt] :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{w} :=
  letI : EssentiallySmall.{w} T.ProEt := inferInstance
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- The uniformizer as a global section of the completed coefficient ring, obtained
from its constant section through the canonical quotient-cone map.
Source: Bhatt--Scholze, Section 6.8
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
def smoothLatticeUniformizerSection :
    ((WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj ⋙
      forget CommRingCat).sections :=
  (Functor.sectionsFunctor T.ProEtᵒᵖ).map
    (whiskerRight
      (whiskerRight
        (toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))))
        (forget₂ CommRingCat.{max v (u + 1)} RingCat.{max v (u + 1)}) ≫
        (WeilConjectures.integralConstantToCompletionOfUniverses l E T).hom)
      (forget RingCat))
    ⟨fun _ ↦ ULift.up (Padic.coefficientExtensionUniformizer l E), fun _ ↦ rfl⟩

/-- The rational coefficient sheaf `B_T[1/varpi]`, by actual sheafified localization.
Source: Bhatt--Scholze, Definition 6.8.1 and Lemma 6.8.2(2)
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
def smoothLatticeRationalRing :
    Sheaf (Scheme.ProEt.topology T) CommRingCat.{max v (u + 1)} :=
  ringedLocalizationRingOfUniverses.{max v (u + 1), u + 1, u}
    (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (smoothLatticeUniformizerSection l E T)

/-- The canonical coefficient localization map, with no choice of rational realization.
Source: Bhatt--Scholze, Lemma 6.8.2(2)
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
def smoothLatticeCoefficientMap :
    WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T ⟶
      smoothLatticeRationalRing l E T :=
  ringedLocalizationRingUnitOfUniverses.{max v (u + 1), u + 1, u}
    (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (smoothLatticeUniformizerSection l E T)

/-- Every locally finite free rational sheaf on a smooth geometric fibre contains a
locally finite free integral subobject whose inclusion induces its rationalization.
The monomorphism `i` presents the submodule sheaf, and the equation on pure tensors
fixes the induced isomorphism, rather than merely giving an abstract integral model.
Source: Bhatt--Scholze, Lemmas 7.4.7, 7.4.10 and Proposition 6.8.4(1),(4), pp. 59--71
(blueprint: lem-a1-smooth-lisse-integral-lattice).

Proof following the seven DAG steps:
1. Base-change permanence gives separated finite type over K. A field is Noetherian,
so finite-type-over-Noetherian gives a Noetherian T. Smooth geometric normality
(lem-trf-smooth-geometrically-normal, Stacks 056T) gives normal local domains for
every field extension K/K0. The inverse of l in K0 stays an inverse on T.
2. The Noetherian closed-subset minimum principle and
lem-sfb-noetherian-connected-components-open give finitely many clopen connected
components. Each open component is Noetherian, separated and normal. Restriction
to its open slice preserves the constant quotient sheaves, their limit, and localization.
The empty scheme already has the zero lattice.
3. On a nonempty component choose a geometric point and apply
lem-a1-normal-proetale-monodromy. Normality makes the monodromy group profinite,
and the sheaf corresponds to a continuous finite-dimensional E-representation V.
4. By lem-pod-profinite-stable-lattice choose a stable finite free A-lattice in V.
Its quotients are continuous finite free A/varpi^n representations. Clause (1) of
cor-galois-lisse-representations, including coefficient compatibility and full
faithfulness, gives their normalized tower of finite locally constant etale sheaves.
5. By lem-per-lisse-completed-system-comparison, its pro-etale inverse limit N is
locally finite free over the completed B. The integral normalization of the
monodromy equivalence and its full faithfulness give N[1/varpi] isomorphic to L.
6. The coefficient comparison of lem-sfb-integral-lisse-reduction-equivalence
identifies B with continuous A-valued functions. These are varpi-torsion free,
pointwise, since A embeds in E. On free charts this makes N torsion free, so
N maps monomorphically into N[1/varpi]. Compose with the preceding isomorphism
and take the image in L. It is isomorphic to N and its inclusion induces exactly
the displayed rationalization, characterized by sending 1 tensor m to i(m).
7. Glue these submodules over the finite disjoint clopen components, using products
on sections and componentwise restrictions. Their local trivializations and their
inclusion-induced isomorphisms glue. Ranks may differ between components and may
be zero; on the empty scheme the empty product is the zero module sheaf. -/
theorem exists_smooth_lisse_integral_lattice
    (K₀ K : Type u) [Field K₀] [Field K] [Algebra K₀ K]
    (T₀ : Scheme.{u}) (f : T₀ ⟶ Spec (.of K₀))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : K₀))
    (E : Type v) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : ringedSiteModules.{max v (u + 1)}
      ((sheafCompose _ (forget₂ CommRingCat.{max v (u + 1)} RingCat.{max v (u + 1)})).obj
        (smoothLatticeRationalRing l E
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K)))))))
    (_hL : L.IsFiniteLocallyFree) :
    ∃ (M : ringedSiteModules.{max v (u + 1)}
        (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K))))))
      (i : M ⟶ (SheafOfModules.restrictScalars
        ((sheafCompose _ (forget₂ CommRingCat.{max v (u + 1)} RingCat.{max v (u + 1)})).map
          (smoothLatticeCoefficientMap l E
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K))))))).obj L),
      Mono i ∧ M.IsFiniteLocallyFree ∧
      ∃ e : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, max v (u + 1), max v (u + 1)}
          (smoothLatticeCoefficientMap l E
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K))))) M ≅ L,
        ∀ (U : (Scheme.ProEt
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K)))))ᵒᵖ)
          (m : M.val.obj U),
          e.hom.val.app U
            (((PresheafOfModules.sheafificationAdjunction
                (R := (sheafCompose _
                  (forget₂ CommRingCat.{max v (u + 1)} RingCat.{max v (u + 1)})).obj
                    (smoothLatticeRationalRing l E
                      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K))))))
                (𝟙 _)).unit.app
              (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1,
                max v (u + 1), max v (u + 1)}
                (smoothLatticeCoefficientMap l E
                  (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K))))) M)).app U
              ((1 : (smoothLatticeRationalRing l E
                  (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K))))).obj.obj U)
                ⊗ₜ[_, ((smoothLatticeCoefficientMap l E
                  (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K))))).hom.app U).hom]
                  m)) = i.val.app U m := by
  sorry

end AlgebraicGeometry.ProEtale
