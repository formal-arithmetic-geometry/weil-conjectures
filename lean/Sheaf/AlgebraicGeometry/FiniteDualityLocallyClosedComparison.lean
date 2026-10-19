/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction
public import Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.RingedTopoiModuleAdjunctionRepair
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Sheaf.Paper.BoundedSiteAdjunctionTranspose
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.SixFunctors.FiniteDualityClosedComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Locally closed exceptional comparison with its adjunction normalization

Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-weil-finite-duality-site-comparison.proof.md, second paragraph
(blueprint: lem-weil-finite-duality-locally-closed-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Coordinates for the two ambient closed right adjoints. Each functor is determined
up to the unique counit-compatible adjoint isomorphism, rather than freely chosen data.
Source: blueprint locally closed exceptional comparison, closed factor
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
structure LocallyClosedComparisonAdjoints (A : Type (u + 1)) [CommRing A]
    {S V : Scheme.{u}} (c : S ⟶ V) where
  etale : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
    DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
  proetale : DerivedCategory (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A)) ⥤
    DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))
  etaleAdjunction : (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor ⊣ etale
  proetaleAdjunction : (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor ⊣ proetale

/-- The etale closed-then-open extension on ordinary derived categories.
Source: blueprint locally closed exceptional comparison, F_et
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
abbrev locallyClosedEtaleExtension (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T) [IsOpenImmersion v] :=
  (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor ⋙
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory

/-- The pro-etale closed-then-open extension on ordinary derived categories.
Source: blueprint locally closed exceptional comparison, F_proet
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
abbrev locallyClosedProEtaleExtension (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T) [IsOpenImmersion v] :=
  (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor ⋙
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory

namespace LocallyClosedComparisonAdjoints

variable {A : Type (u + 1)} [CommRing A] {S V T : Scheme.{u}} {c : S ⟶ V}

/-- Open restriction followed by the ambient closed etale right adjoint.
Source: blueprint locally closed exceptional comparison, J_et
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
abbrev etaleRight (a : LocallyClosedComparisonAdjoints A c) (v : V ⟶ T)
    [IsOpenImmersion v] :=
  (Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⋙ a.etale

/-- Open restriction followed by the ambient closed pro-etale right adjoint.
Source: blueprint locally closed exceptional comparison, J_proet
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
abbrev proetaleRight (a : LocallyClosedComparisonAdjoints A c) (v : V ⟶ T)
    [IsOpenImmersion v] :=
  (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⋙ a.proetale

/-- The literal pasted etale adjunction, fixing its unit and counit.
Source: blueprint locally closed exceptional comparison, pasted adjunction
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
def etalePasted (a : LocallyClosedComparisonAdjoints A c) (v : V ⟶ T)
    [IsOpenImmersion v] : locallyClosedEtaleExtension A c v ⊣ a.etaleRight v :=
  a.etaleAdjunction.comp
    (Etale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) v).mapDerivedCategoryAdjunction

/-- The literal pasted pro-etale adjunction, fixing its unit and counit.
Source: blueprint locally closed exceptional comparison, pasted adjunction
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
def proetalePasted (a : LocallyClosedComparisonAdjoints A c) (v : V ⟶ T)
    [IsOpenImmersion v] : locallyClosedProEtaleExtension A c v ⊣ a.proetaleRight v :=
  a.proetaleAdjunction.comp
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) v).mapDerivedCategoryAdjunction

end LocallyClosedComparisonAdjoints

/-- Delta is the specified closed counit mate followed by open extension comparison.
Source: blueprint locally closed exceptional comparison, Delta
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
def locallyClosedExtensionComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] :
    DerivedCategory.Plus.ι ⋙ locallyClosedEtaleExtension A c v ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ≅
      DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory ⋙
        locallyClosedProEtaleExtension A c v :=
  Functor.isoWhiskerLeft
      (DerivedCategory.Plus.ι ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor)
      ((Functor.mapDerivedCategoryCompIso
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v)
        (comparisonUpperStar (ModuleCat.{u + 1} A) T)).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) v) ≪≫
        Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.isoWhiskerRight (fixedDirectImageComparisonIso A c)
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory

/-- The scheme-theoretic closure compactification of an immersion. No density or
nonemptiness assumption is imposed.
Source: blueprint locally closed exceptional comparison, closure factorization
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
def locallyClosedImageCompactification {S T : Scheme.{u}} (s : S ⟶ T)
    [IsImmersion s] [QuasiCompact s] : Compactification s where
  Z := s.image
  i := s.toImage
  g := s.imageι
  comm := s.toImage_imageι.symm
  isOpenImmersion := inferInstance
  isProper := inferInstance

/-- The unique identity-on-the-source sheaf comparison, oriented from closed/open
extension to closure extension. The existing theorem specifies uniqueness by the open
unit and closed counit, so this choice cannot introduce a scalar twist.
Source: Stacks 0GJ1; blueprint locally closed exceptional comparison, Step 7
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
def locallyClosedEtaleSheafIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] [IsNoetherian T] [QuasiCompact (c ≫ v)] :
    Etale.lowerStar (ModuleCat.{u + 1} A) c ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v ≅
      Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) (c ≫ v).toImage ⋙
        Etale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v).imageι :=
  (((((etale_locallyClosed_extension_comparison (A := A) T (𝟙 T) v).2 (c ≫ v)).choose_spec).1
    c v rfl).choose).symm

/-- The normalized identification with etale compact support at the closure
compactification. Both closed direct images are exact; the comparison is the
localization of the preceding uniquely normalized sheaf map.
Source: Stacks 0GJ1; blueprint locally closed exceptional comparison, Step 7
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
def locallyClosedEtaleSupportIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] [IsNoetherian T] [QuasiCompact (c ≫ v)] :
    locallyClosedEtaleExtension A c v ≅
      Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (locallyClosedImageCompactification (c ≫ v)) :=
  Functor.isoWhiskerRight
      (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (locallyClosedEtaleSheafIso A c v) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((Etale.lowerStar (ModuleCat.{u + 1} A)
        (c ≫ v).imageι).rightDerivedFunctorIsoMapDerivedCategory).symm

/-- The existing Brown-adjoint theorem at the closure compactification. The
Noetherian and compact hypotheses it needs follow from the immersion into T; they
are constructed here rather than imposed on the statement as additional assumptions.
Source: blueprint locally closed exceptional comparison, Step 7
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
instance locallyClosedImage_isLeftAdjoint (A : Type (u + 1)) [CommRing A] [Finite A]
    {S T : Scheme.{u}} (s : S ⟶ T) [IsImmersion s] [QuasiCompact s] [IsNoetherian T] :
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (locallyClosedImageCompactification s)).IsLeftAdjoint :=
  letI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian s
  letI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace s
  letI : IsLocallyNoetherian s.image := LocallyOfFiniteType.isLocallyNoetherian s.imageι
  letI : CompactSpace s.image := QuasiCompact.compactSpace_of_compactSpace s.imageι
  Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A
    (locallyClosedImageCompactification s)

/-- The ordinary etale exceptional right adjoint in closure coordinates.
Source: blueprint locally closed exceptional comparison, s-times
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
abbrev locallyClosedEtaleExceptional (A : Type (u + 1)) [CommRing A] [Finite A]
    {S T : Scheme.{u}} (s : S ⟶ T) [IsImmersion s] [QuasiCompact s] [IsNoetherian T] :=
  (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (locallyClosedImageCompactification s)).rightAdjoint

/-- The counit-compatible etale adjoint identification induced by the normalized
left-adjoint comparison, with no independently chosen right-adjoint isomorphism.
Source: blueprint locally closed exceptional comparison, Step 7
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
def locallyClosedEtaleRightIso {A : Type (u + 1)} [CommRing A] [Finite A]
    {S V T : Scheme.{u}} {c : S ⟶ V} (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] [IsNoetherian T] [QuasiCompact (c ≫ v)]
    (a : LocallyClosedComparisonAdjoints A c) :
    a.etaleRight v ≅ locallyClosedEtaleExceptional A (c ≫ v) :=
  (a.etalePasted v).rightAdjointUniq
    ((Adjunction.ofIsLeftAdjoint _).ofNatIsoLeft (locallyClosedEtaleSupportIso A c v).symm)

/-- All clauses of locally closed exceptional comparison, on exactly bounded
constructible targets and bounded-below etale-origin tests. The natural transformations
are fixed by the counit and comparison-unit equations. The relative Hom equation is
required for every witness of etale origin and every normalized comparison-class datum.
Source: blueprint locally closed exceptional comparison, Steps 1--12
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
structure LocallyClosedExceptionalComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] [IsNoetherian T] [QuasiCompact (c ≫ v)] where
  adjoints : LocallyClosedComparisonAdjoints A c
  bounded (M : Etale.BoundedConstructibleDerivedCategory A T) :
    _root_.DerivedCategory.TStructure.t.plus ((adjoints.etaleRight v).obj M.obj)
  gamma :
    (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙ adjoints.etaleRight v ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory ≅
      (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        adjoints.proetaleRight v
  counit (M : Etale.BoundedConstructibleDerivedCategory A T) :
    (locallyClosedExtensionComparison A c v).hom.app
        ⟨(adjoints.etaleRight v).obj M.obj, bounded M⟩ ≫
      (locallyClosedProEtaleExtension A c v).map (gamma.hom.app M) ≫
      (adjoints.proetalePasted v).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) =
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
        ((adjoints.etalePasted v).counit.app M.obj)
  transport :
    (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        adjoints.proetaleRight v ≅
      (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        sfFiniteExceptionalAt A (locallyClosedImageCompactification (c ≫ v))
  unit_normalization (M : Etale.BoundedConstructibleDerivedCategory A T) :
    gamma.hom.app M ≫ transport.hom.app M =
      (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.map
        ((locallyClosedEtaleRightIso v adjoints).hom.app M.obj ≫
          (locallyClosedEtaleExceptional A (c ≫ v)).map
            ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M.obj))
  relative_hom
      (B : FixedComparisonClassAdjunction A (c ≫ v)
        (locallyClosedImageCompactification (c ≫ v))
        (locallyClosedEtaleExceptional A (c ≫ v))
        (Adjunction.ofIsLeftAdjoint _)
        (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) S)
        _root_.DerivedCategory.TStructure.t.plus)
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
      (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) S K)
      (M : Etale.BoundedConstructibleDerivedCategory A T)
      (hM : _root_.DerivedCategory.TStructure.t.plus
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj))
      (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (w : (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj L.obj ≅ K)
      (h : (locallyClosedProEtaleExtension A c v).obj K ⟶
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) :
    ((adjoints.proetalePasted v).homEquiv _ _) h ≫ transport.hom.app M =
      B.homEquiv (locallyClosedImageCompactification (c ≫ v)) K hK
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) hM
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
            (locallyClosedImageCompactification (c ≫ v))).map w.inv ≫
          (fixedCompactSupportComparisonIso A
            (locallyClosedImageCompactification (c ≫ v))).hom.app L ≫
          (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
            ((locallyClosedEtaleSupportIso A c v).inv.app L.obj) ≫
          (locallyClosedExtensionComparison A c v).hom.app L ≫
          (locallyClosedProEtaleExtension A c v).map w.hom ≫ h)

/-- Locally closed exceptional inverse image commutes with etale/pro-etale comparison,
with the specified counit, relative adjunction, comparison-unit normalization and
factorization coherence. Positive levels are indexed by `n + 1`, hence cover all n >= 1.
The existential typeclass witnesses are consequences of finite type, not extra premises.
Source: Weil blueprint, main-20261015, locally closed comparison sentence in the second
paragraph of lem-weil-finite-duality-site-comparison.proof.md
(blueprint: lem-weil-finite-duality-locally-closed-comparison).

Proof plan (the node's twelve steps):
1. Write $C_W=\nu_W^*$, $I_e=Rc_{et}^!$, $I_p=Rc_{proet}^!$, $N=v_{et}^*M$ and $H=I_eN$. The
schemes $S,T$ are Noetherian: a field has only the ideals $0,1$, so its spectrum is Noetherian,
and finite type over it is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. The open-
subscheme theorem gives Noetherian $V$ and quasi-compactness of all the complementary opens. The
open $V$ is still finite type over $k$: cover $T$ by finitely many affine finite-type charts, and
cover the intersection of $V$ with each chart by finitely many principal opens, possible by this
quasi-compactness. Their rings are localizations of finite-type $k$-algebras at one element,
hence generated by the original generators and that inverse. Separatedness restricts to an open
subscheme by restriction of the closed diagonal. Exact inverse image and [lem-weil-pbc-exact-
functor-bounded-below] give $\mathcal H^r(N)=v^*\mathcal H^r(M)$; constructible pullback
therefore gives $N\in D^b_c(V_{et},A)$ [prop-constructible-pullback]. Apply [lem-weil-finite-
duality-closed-comparison] to $c$ and $N$. Its bounded-below conclusion gives $H=J_{et}M\in
D^+(S_{et},A)$, so the named closed direct-image comparison can be evaluated at $H$.

2. Use $b:C_Vv_{et}^*\xrightarrow{\sim}v_{proet}^*C_T$ for [lem-weil-pbc-comparison-pullback] and
$o:C_Tv_{et,!}\xrightarrow{\sim}v_{proet,!}C_V$ for [lem-cbc-proetale-extension-zero-comparison].
Their open unit normalization is [lem-sf-open-comparison-unit-normalization]. These sheaf
comparisons and their normalization hold also on ordinary derived categories: the two open
extensions are exact [lem-weil-pbc-extension-by-zero-exact, lem-weil-extension-by-zero-exact],
and comparison and open restriction are exact inverse images [lem-sf-comparison-pullback-exact,
prop-weil-pbc-inverse-image-modules-exact, prop-weil-pbc-proetale-constant-exact]. Apply the
comparisons degreewise. The termwise-adjunction theorem carries the units, counits and triangle
identities to complexes; the localization universal property descends these transformations and
their equalities, since the exact functors preserve quasi-isomorphisms. Thus, writing
$r=v_{et}^*$ and $t=v_{proet}^*$ and the open units as $u^e,u^p$, we have
$$t(o_L)\,b_{v_{et,!}L}\,C_V(u^e_L)=u^p_{C_VL}.$$ This uses the specified $b,o$, rather than
choices of isomorphisms with the same endpoints.

3. Let $e^e,e^p$ be the open counits. The preceding unit equation implies
$$e^p_{C_TM}\,v_{proet,!}(b_M)\,o_{rM}=C_T(e^e_M).$$ Indeed, transpose $C_T(e^e_M)o_{rM}^{-1}$
under the pro-etale open adjunction. Its transpose is $$tC_T(e^e_M)\,t(o_{rM}^{-1})u^p_{C_VrM}
=tC_T(e^e_M)\,b_{v_{et,!}rM}C_V(u^e_{rM}) =b_M C_V\bigl(r(e^e_M)u^e_{rM}\bigr)=b_M.$$ The first
equality is the unit normalization, the second naturality of $b$, and the third the etale
triangle identity. Inverse transposition gives the displayed counit equation.

4. The closed comparison theorem gives the natural isomorphism $$\alpha_N:C_S
I_eN\xrightarrow{\sim}I_p C_VN$$ and the equation
$$k^p_{C_VN}\,c_{proet,*}(\alpha_N)\,\delta_H=C_V(k^e_N),$$ where $k^e,k^p$ are the closed
counits and $\delta:C_Vc_{et,*}\xrightarrow{\sim}c_{proet,*}C_S$ is the specified closed direct-
image comparison. Define $$\gamma_M=I_p(b_M)\,\alpha_N:C_SJ_{et}M\longrightarrow
I_pv_{proet}^*C_TM=J_{proet}C_TM.$$ Both factors are natural isomorphisms. The closed theorem
applies because Step 1 proved exactly its bounded constructible input hypothesis; no assertion
about closed ordinary restriction commuting with internal Hom is used.

5. For bounded-below $L$ set $$\Delta_L=v_{proet,!}(\delta_L)\,o_{c_{et,*}L}.$$ This is exactly
the named comparison in the statement: the closed map is [lem-weil-pbc-comparison-direct-image-
canonical-mate], and the open map is [lem-cbc-proetale-extension-zero-comparison]. Since $c$ is
finite [lem-weil-pbc-closed-immersion-finite], its exact etale direct image preserves the lower
bound [lemma-weil-pbc-finite-direct-image-exact], also for constant-$A$ modules by the
underlying-sheaf functor. The maps are therefore defined at every such $L$, in particular at $H$.
By the composite adjunction formula,
$$\epsilon^\tau_M=e^\tau_M\,v_{\tau,!}(k^\tau_{v_\tau^*M}),$$ and the corresponding unit is the
pasted unit. These are the adjunctions fixed in the statement.

6. Expand $\gamma,\Delta$ and the pasted counit in the left side of the required equation.
Naturality of $k^p$ at $b_M:C_VN\to v_{proet}^*C_TM$, followed by Step 4, gives $$\begin{aligned}
\epsilon^p_{C_TM}F_p(\gamma_M)\Delta_H
&=e^p_{C_TM}\,v_{proet,!}(b_M)\,v_{proet,!}\bigl(C_V(k^e_N)\bigr)\,o_{c_{et,*}H}\\
&=e^p_{C_TM}\,v_{proet,!}(b_M)\,o_N\,C_T\bigl(v_{et,!}(k^e_N)\bigr)\\
&=C_T(e^e_M)\,C_T\bigl(v_{et,!}(k^e_N)\bigr) =C_T(\epsilon^e_M). \end{aligned}$$ The second
equality is naturality of $o$ at $k^e_N:c_{et,*}H\to N$; the third is precisely Step 3. This
proves the counit identity for the specified comparisons, not merely existence of an abstract
comparison. Transposition in $F_p\dashv J_p$ says equivalently that $\gamma_M$ is the unique
transpose of $C_T(\epsilon^e_M)\Delta_H^{-1}$.

7. Identify $F_e$ with ordinary etale compact support for $s$. Let $\bar S$ be the scheme-
theoretic closure of $S$ in $T$, with $u:S\hookrightarrow\bar S$ open and $i:\bar
S\hookrightarrow T$ closed. Here $i$ is proper directly from the closed-immersion definition:
affine base change is quotient by the extended ideal, hence closed; its diagonal is an
isomorphism, and the quotient algebra is generated by $1$ as a module. The closure is finite type
over $k$, since on the finite-type affine charts of $T$ its rings are quotients. The normalized
comparison of [lem-sfb-etale-locally-closed-extension-comparison] is $v_!c_*\cong i_*u_!$ on
sheaves. Both sides are exact: open extension is exact and closed direct image is exact by
finiteness. Hence the termwise comparison descends to all derived complexes [lem-weil-pbc-exact-
functor-derived-factorization, lem-weil-pbc-localization-universal-property]. In the closure
compactification, [def-amb-etale-compact-support] gives $Rs_!=Ri_*u_!=i_*u_!$; exactness of $i_*$
means that applying it to a quasi-isomorphism into a K-injective resolution is a quasi-
isomorphism, so this equality holds unboundedly as well. The adjoint exists by [thm-amb-etale-
exceptional-adjoint]. Right-adjoint uniqueness, with its unit and counit normalization [lem-cat-
right-adjoint-composition, def-weil-pbc-adjunction-conjugate], identifies $J_e$ with $s^\times$
compatibly with the chosen identification of left adjoints. On pro-etale categories the
corresponding normalized identification $F_p\cong i_*u_!$ and factorization independence are
supplied by [lem-sfb-locally-closed-extension-coherence].

8. First justify the termwise interpretation of the closed comparison. For either closed
immersion $h=c$ or $h=i$, both $h_{e,*}$ and $h_{p,*}$ are exact: use closed finiteness and
finite etale direct-image exactness, and the pro-etale ringed open/closed theorem. Their
complements are quasi-compact by Noetherianity. The pullbacks and $C$ are exact as in Step 2. At
the sheaf level form the $h_p^*\dashv h_{p,*}$ transpose $\delta_h^0$ of
$$C(\varepsilon^e_{h,L})a_{h,h_{e,*}L}^{-1}.$$ The module adjunction supplies this transpose.
Termwise adjunction and localization carry its defining counit equation to derived categories;
exact-functor factorization identifies $Rh_{\tau,*}$ with termwise $h_{\tau,*}$. Consequently the
descended $\delta_h^0$ is the unique transpose defining $\delta_h$ in [lem-weil-pbc-comparison-
direct-image-canonical-mate]. Thus the named derived comparison equals the termwise sheaf mate on
$D^+$. Its sheaf counit equation is $$\varepsilon^p_{h,C
L}\,h_p^*(\delta^0_{h,L})\,a_{h,h_{e,*}L}=C(\varepsilon^e_{h,L}).$$ Both closed restriction
counits are invertible by [lem-kun-04ca, lem-weil-pbc-proetale-ringed-open-closed]. The equation
therefore says precisely that restriction of $\delta_h$ to the closed source is the identity
under those counits and the specified $a_h$. This normalization holds termwise on complexes. The
open comparison has the analogous normalization by Step 2.

9. Write $E_\tau=i_{\tau,*}u_{\tau,!}$ for the closure compactification and
$q_\tau:F_\tau\xrightarrow{\sim}E_\tau$ for Step 7's identifications, restricting to the identity
on $S$. For $L\in D^+(S_{et},A)$ the closure comparison is $$C_{\bar
s,L}=i_{p,*}(o_{u,L})\,\delta_{i,u_{e,!}L}:C_TE_eL\xrightarrow{\sim}E_pC_SL.$$ This is exactly
the specified $B_{s,L}$ in [lem-pur-bounded-site-adjunction-transpose], for compactification
$(u,i)$: the proper comparison there is the counit-mate comparison for the closed $i$. Exactness
identifies its derived direct image with $i_*$. Define $$D_L=q_{p,C_SL}^{-1}\,C_{\bar
s,L}\,C_T(q_{e,L}):C_TF_eL\longrightarrow F_pC_SL.$$ Step 8 and the open unit normalization show
that both $D_L$ and $\Delta_L$ restrict to $1_{C_SL}$: each closed factor restricts by its
counit, each open factor by its unit, and each $q_\tau$ by its stated identity normalization. The
pullback-composition compatibility of [lem-weil-pbc-comparison-pullback] ensures these use the
same identification $s_p^*C_T\cong C_Ss_e^*$ for both factorizations. Hence the endomorphism
$D_L\Delta_L^{-1}$ of $F_pC_SL$ restricts to the identity. The restriction Hom bijection of [lem-
sfb-locally-closed-extension-coherence], with both arguments $C_SL$, makes this endomorphism the
identity. We have proved the required equality of named maps: $$q_{p,C_SL}\,\Delta_L=C_{\bar
s,L}\,C_T(q_{e,L}).$$

10. Now compute the specified comparison-class transpose. Choose a nonnegative dimension bound
for $\bar S$ by [lem-kun-dimension-finite-type], using $0$ if it is empty. Apply [lem-pur-
bounded-site-adjunction-transpose] to $f=s$, compactification $(u,i)$ and $K=M$. Its hypotheses
hold: these are finite-type $k$-schemes with the same finite coefficient $A$, $s$ is separated
finite type, $M\in D^+$, and $s^\times M$ is bounded below by Steps 1 and 7. Put $B=J_eM$ and
write $$\rho_M=C_S\bigl(s^\times(\eta_M)\bigr)$$ under Step 7's counit-compatible $J_e\cong
s^\times$. For $L\in D^+(S_{et},A)$ and $h:F_pC_SL\to C_TM$, full faithfulness of $C_T$ gives a
unique $h_0:F_eL\to M$ with $h\Delta_L=C_T(h_0)$; $F_eL$ is bounded below by exactness. Let
$g_0:L\to B$ be its etale adjoint. Step 6 and naturality of $\Delta$ give
$$\epsilon^p_{C_TM}F_p(\gamma_MC_Sg_0)=C_T(h_0)\Delta_L^{-1}=h.$$ Thus the ambient transpose of
$h$ is $\gamma_MC_Sg_0$. For closure left adjoints take $a_e=h_0q_{e,L}^{-1}$ and
$a_p=hq_{p,C_SL}^{-1}$. Step 9 gives $$a_pC_{\bar s,L}=C_T(a_e).$$ Use the current statement's
explicit Hom formula with $U_T=R\nu_{T,*}$ and the same closure compactification. Naturality of
the comparison unit gives $$U_T(a_pC_{\bar
s,L})\eta_{T,E_eL}=U_TC_T(a_e)\eta_{T,E_eL}=\eta_Ma_e.$$ Its etale transpose is
$s^\times(\eta_M)\operatorname{adj}_e(a_e)$. Conjugation by $q_e$ identifies
$\operatorname{adj}_e(a_e)$ with $g_0$. Applying $C_S$ in the specified Hom formula therefore
gives exactly $\rho_MC_Sg_0$. Thus both the explicit Hom formula and the cited transpose
conclusion use the comparison unit and the named $B_{s,L}=C_{\bar s,L}$ of Step 9.

11. Since $\eta_M:M\xrightarrow{\sim}R\nu_{T,*}C_TM$ is invertible, define
$$\theta_M=C_S\bigl(s^\times(\eta_M)\bigr)\gamma_M^{-1}:J_pC_TM\xrightarrow{\sim}C_Ss^\times
R\nu_{T,*}C_TM=G_s(C_TM),$$ with Step 7's adjoint identification understood. Step 10 proves that
postcomposition by $\theta_M$ identifies the two Hom bijections. An arbitrary bounded-below
etale-origin test object is isomorphic to $C_SL$; precomposing by this witness proves the same
assertion for it, independently of the witness, as in [thm-sf-ambient-adjoint-class]. In
particular the composite from $C_SJ_eM$ to the transported value is exactly $C_Ss^\times(\eta_M)$
under Step 7, as claimed. The unit is the image of the identity of a left-adjoint value under its
Hom bijection, and the counit is the inverse image of an identity of a right-adjoint value
wherever that comparison-class map is defined. Equality of the Hom bijections therefore
identifies these maps. The ambient $F_\tau\dashv J_\tau$ units and counits are the pasted ones by
the composite adjunction formula. This argument does not assert a compact-support adjunction on
arbitrary pro-etale objects.

12. Finally change the closed-then-open factorization. The normalized etale factorization maps
are given by [lem-sfb-etale-locally-closed-extension-comparison], and the pro-etale maps by [lem-
sfb-locally-closed-extension-coherence]. For any second factorization repeat Steps 8-9 with the
same closure $(u,i)$. Each site's $q_\tau$ restricts to the identity, and its closed/open
comparison is termwise with the specified normalization, so the same restriction Hom bijection
gives $$q'_{p}\Delta'=C_{\bar s}C_T(q'_e),\qquad q_p\Delta=C_{\bar s}C_T(q_e).$$ Cancelling the
common closure map proves equality of the comparison paths after the canonical factorization
identifications. No derived mate is being presumed to be a sheaf map: Step 8 established that
equality before using it here. Conjugation of the normalized left-adjoint identifications gives
canonical right-adjoint identifications, respecting identities and composition [def-weil-pbc-
adjunction-conjugate]. Step 6 uniquely characterizes $\gamma_M$ as a counit transpose, so it
respects these identifications. Their units and counits are the pasted ones by [lem-cat-right-
adjoint-composition, def-weil-pbc-composite-adjunction]. Step 11's transported identification has
the same coherence, since it is the image of the natural comparison unit under the normalized
etale right adjoints followed by $C_S$. This proves independence of the factorization for the
maps and adjunction data on the stated comparison class.
-/
theorem finiteDuality_locallyClosed_comparison
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {S V T : Scheme.{u}}
    (aS : S ⟶ Spec (.of D.k)) (aT : T ⟶ Spec (.of D.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (c : S ⟶ V) (v : V ⟶ T) [IsClosedImmersion c] [IsOpenImmersion v]
    (_hs : (c ≫ v) ≫ aT = aS) :
    ∃ hT : IsNoetherian T, ∃ hqc : QuasiCompact (c ≫ v),
      Nonempty (@LocallyClosedExceptionalComparison
        (Padic.coefficientExtensionRing l E (n + 1)) inferInstance
        (Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))
        S V T c v inferInstance inferInstance hT hqc) := by
  sorry

/-- The normalized comparisons between two closed/open factorizations are unique.
Consequently identity comparisons and composition comparisons satisfy the cocycle law.
`HEq` expresses equality after the equality of the two composite scheme morphisms;
it does not introduce an independently chosen identification of the transported functors.
The first equation fixes the etale map by counit-compatible adjoint uniqueness, the second
fixes the pro-etale map by the transported value, and the last is the gamma square.
Source: blueprint locally closed exceptional comparison, Step 12
(blueprint: lem-weil-finite-duality-locally-closed-comparison).

Proof: identify both left adjoints with closure extension by the unique sheaf maps
restricting to the identity on S. Their localizations have the same normalization.
Step 8 identifies the named derived closed mate with its termwise sheaf mate. The open
unit equation and the restriction Hom bijection of locally closed extension coherence
then give q_p Delta = B C(q_e) for each factorization (Step 9). Transport the normalized
left-adjoint identification by right-adjoint uniqueness to obtain the etale isomorphism.
The counit equation uniquely characterizes gamma as a transpose, hence gives its square.
The formula gamma theta = C(s-times(eta)) gives the transported-value square. Each of the
first two normalizations uniquely determines its isomorphism by cancellation; thus the
identity and composites are the same normalized maps. This is exactly Step 12, using
lem-sfb-etale-locally-closed-extension-comparison, lem-sfb-locally-closed-extension-coherence,
def-weil-pbc-adjunction-conjugate, lem-cat-right-adjoint-composition,
def-weil-pbc-composite-adjunction and thm-weil-pbc-site-comparison. -/
theorem locallyClosed_comparison_factorization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V V' T : Scheme.{u}} [IsNoetherian T]
    (c : S ⟶ V) (v : V ⟶ T) (c' : S ⟶ V') (v' : V' ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v]
    [IsClosedImmersion c'] [IsOpenImmersion v']
    [QuasiCompact (c ≫ v)] [QuasiCompact (c' ≫ v')]
    (_hs : c ≫ v = c' ≫ v')
    (z : LocallyClosedExceptionalComparison A c v)
    (z' : LocallyClosedExceptionalComparison A c' v') :
    ∃! e : (z.adjoints.etaleRight v ≅ z'.adjoints.etaleRight v') ×
        ((Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙
            (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
            z.adjoints.proetaleRight v ≅
          (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙
            (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
            z'.adjoints.proetaleRight v'),
      HEq (e.1 ≪≫ locallyClosedEtaleRightIso v' z'.adjoints)
          (locallyClosedEtaleRightIso v z.adjoints) ∧
        HEq (e.2 ≪≫ z'.transport) z.transport ∧
        ∀ M : Etale.BoundedConstructibleDerivedCategory A T,
          (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.map
              (e.1.hom.app M.obj) ≫ z'.gamma.hom.app M =
            z.gamma.hom.app M ≫ e.2.hom.app M := by
  sorry

end AlgebraicGeometry.ProEtale
