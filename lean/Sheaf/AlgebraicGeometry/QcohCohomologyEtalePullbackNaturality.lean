/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale

import Sheaf.AlgebraicGeometry.ZariskiEtaleTensorSections
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.CategoryTheory.Sites.DirectImageInjectiveEvaluationAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Canonical quasi-coherent comparison and étale pullback

Source: Stacks Project, Descent, Tags 03DW(2), 03LC(1), and 071N
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w va vb

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Resolution roofs used below, with global sections compared before taking homology.
Source: Stacks 01FB and 03DW(2)
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality).
The section isomorphism is normalized separately for each of the two ringed morphisms.
All complexes are indexed by naturals, hence zero in negative degrees. -/
structure QcohComparisonRoof
    {A : Type v} {B : Type w} [Category.{va} A] [Category.{vb} B] [Abelian A] [Abelian B]
    {RA RB : Type u} [Ring RA] [Ring RB]
    (P : A ⥤ B) [P.Additive]
    (SA : A ⥤ ModuleCat.{u} RA) [SA.Additive]
    (SB : B ⥤ ModuleCat.{u} RB) [SB.Additive]
    (F : A) (G : B) (φ : G ⟶ P.obj F) where
  /-- An injective resolution of the target coefficient. -/
  I : InjectiveResolution F
  /-- An injective resolution of the source coefficient. -/
  J : InjectiveResolution G
  /-- The bounded below injective replacement of the pushed-forward resolution. -/
  K : CochainComplex B ℕ
  /-- Every replacement term is injective. -/
  injective : ∀ n : ℕ, Injective (K.X n)
  /-- The replacement map. -/
  lambda : (P.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K
  /-- The replacement is a quasi-isomorphism. -/
  quasiIso : QuasiIso lambda
  /-- A lift of the coefficient map. -/
  beta : J.cocomplex ⟶ K
  /-- Both lifts extend the same coefficient map. -/
  compatible : J.ι.f 0 ≫ beta.f 0 = φ ≫ P.map (I.ι.f 0) ≫ lambda.f 0
  /-- Comparison of the actual section complexes. -/
  sections : ((SA ⋙ forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex ≅
    ((SB ⋙ forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj
      ((P.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
  /-- Applying global sections to the replacement induces an isomorphism. -/
  invertible : ∀ q : ℕ, IsIso (HomologicalComplex.homologyMap
    (sections.hom ≫ ((SB ⋙ forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex
      (.up ℕ)).map lambda) q)

/-- The prescribed roof map, including the canonical comparisons with right derivation.
Source: Stacks 01FB and 03DW(2)
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality). -/
def QcohComparisonRoof.map
    {A : Type v} {B : Type w} [Category.{va} A] [Category.{vb} B] [Abelian A] [Abelian B]
    [EnoughInjectives A] [EnoughInjectives B]
    {RA RB : Type u} [Ring RA] [Ring RB]
    {P : A ⥤ B} [P.Additive]
    {SA : A ⥤ ModuleCat.{u} RA} [SA.Additive]
    {SB : B ⥤ ModuleCat.{u} RB} [SB.Additive]
    {F : A} {G : B} {φ : G ⟶ P.obj F}
    (D : QcohComparisonRoof P SA SB F G φ) (q : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).obj ((SB.rightDerived q).obj G) ⟶
      (forget₂ _ AddCommGrpCat.{u}).obj ((SA.rightDerived q).obj F) :=
  (forget₂ _ AddCommGrpCat.{u}).map (D.J.isoRightDerivedObj SB q).hom ≫
    ((((SB.mapHomologicalComplex (.up ℕ)).obj D.J.cocomplex).sc q).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).inv ≫
    HomologicalComplex.homologyMap
      (((SB ⋙ forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).map D.beta) q ≫
    inv (I := D.invertible q) (HomologicalComplex.homologyMap
      (D.sections.hom ≫ ((SB ⋙ forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℕ)).map D.lambda) q) ≫
    ((((SA.mapHomologicalComplex (.up ℕ)).obj D.I.cocomplex).sc q).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).hom ≫
    (forget₂ _ AddCommGrpCat.{u}).map (D.I.isoRightDerivedObj SA q).inv

/-- Sections on the identity étale object, with their usual scalar ring.
Source: Stacks 03DW(2)
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality). -/
abbrev qcohEtaleSections (Z : Scheme.{u}) :=
  SheafOfModules.evaluation.{u} (smallEtaleModuleRing Z) (op (Scheme.Etale.mk (𝟙 Z)))

/-- Evaluation is additive, as the composite of module forgetting and evaluation.
Source: Stacks 03FD
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality). -/
instance qcohEtaleSections_additive (Z : Scheme.{u}) : (qcohEtaleSections Z).Additive :=
  inferInstanceAs ((SheafOfModules.forget.{u} (smallEtaleModuleRing Z) ⋙
    PresheafOfModules.evaluation.{u} (smallEtaleModuleRing Z).obj
      (op (Scheme.Etale.mk (𝟙 Z)))).Additive)

/-- Restriction is additive section by section.
Source: Stacks 03FH
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality). -/
instance qcohEtaleRestriction_additive {Z : Scheme.{u}}
    (c : ZariskiEtaleModuleContext Z) : c.restriction.Additive where
  map_add := rfl

/-- Étale direct image is additive section by section.
Source: Stacks 03LC(1)
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality). -/
instance qcohEtalePushforward_additive {U Z : Scheme.{u}} (a : U ⟶ Z) :
    (smallEtaleModulePushforward a).Additive where
  map_add := rfl

/-- Proof data for right derivation in all small étale structure-sheaf modules.
Source: Stacks 03DW(2), injective-resolution proof
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality).
This contains no chosen module, map, functor, or categorical structure. -/
structure QcohEtaleCohomologyContext (Z : Scheme.{u}) where
  /-- Enough injectives in the category of all modules. -/
  enoughInjectives : EnoughInjectives (SmallEtaleModules Z)

/-- Module cohomology on the small étale site, computed by injective module resolutions.
Source: Stacks 03DW(2) and 03FD
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality). -/
def QcohEtaleCohomologyContext.cohomology {Z : Scheme.{u}}
    (k : QcohEtaleCohomologyContext Z) (q : ℕ) :=
  letI := k.enoughInjectives
  (qcohEtaleSections Z).rightDerived q

/-- The comparison roof for epsilon and its adjunction unit on F.
Source: Stacks 03DW(2)
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality). -/
abbrev qcohEtaleComparisonRoof {Z : Scheme.{u}}
    (c : ZariskiEtaleModuleContext Z) (F : Z.Modules) :=
  @QcohComparisonRoof (SmallEtaleModules Z) Z.Modules _ _ _ _
    ((smallEtaleModuleRing Z).obj.obj (op (Scheme.Etale.mk (𝟙 Z))))
    (Z.ringCatSheaf.obj.obj (op ⊤)) _ _
    c.restriction inferInstance (qcohEtaleSections Z) inferInstance
    (RingedSpace.globalSectionsFunctor Z.toRingedSpace)
    (RingedSpace.globalSectionsFunctor_additive Z.toRingedSpace)
    (c.extension.obj F) F (c.adjunction.unit.app F)

/-- The section identification in an epsilon roof is restriction to the top open.
Source: Stacks 03DW(2)
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality). -/
def qcohEtaleRoofNormalized {Z : Scheme.{u}} {c : ZariskiEtaleModuleContext Z}
    {F : Z.Modules} (D : qcohEtaleComparisonRoof c F) : Prop :=
  letI : (RingedSpace.globalSectionsFunctor Z.toRingedSpace).Additive :=
    RingedSpace.globalSectionsFunctor_additive Z.toRingedSpace
  ∀ n : ℕ, D.sections.hom.f n =
    (D.I.cocomplex.X n).val.presheaf.map (AlgebraicGeometry.gabberTopEtaleIso Z).hom.op

/-- The epsilon roof map, on the recorded Zariski module cohomology.
Source: Stacks 03DW(2) and 01FB
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality). -/
def qcohEtaleComparisonRoofMap {Z : Scheme.{u}} {c : ZariskiEtaleModuleContext Z}
    (k : QcohEtaleCohomologyContext Z) {F : Z.Modules}
    (D : qcohEtaleComparisonRoof c F) (q : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.moduleCohomology Z.toRingedSpace q).obj F) ⟶
      (forget₂ _ AddCommGrpCat.{u}).obj ((k.cohomology q).obj (c.extension.obj F)) :=
  letI := k.enoughInjectives
  letI : EnoughInjectives Z.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives Z.toRingedSpace).2
  letI : (RingedSpace.globalSectionsFunctor Z.toRingedSpace).Additive :=
    RingedSpace.globalSectionsFunctor_additive Z.toRingedSpace
  D.map q

/-- The coefficient map adjoint to the canonical pullback identification.
Source: Stacks 03LC(1), with the normalized square of 03FH
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality). -/
def qcohEtalePullbackCoefficient {U Z : Scheme.{u}} (a : U ⟶ Z)
    (cU : ZariskiEtaleModuleContext U) (cZ : ZariskiEtaleModuleContext Z)
    (hp : (smallEtaleModulePushforward a).IsRightAdjoint)
    (r : smallEtaleModulePushforward a ⋙ cZ.restriction ≅
      cU.restriction ⋙ pushforward a) (F : Z.Modules) :
    cZ.extension.obj F ⟶
      (smallEtaleModulePushforward a).obj (cU.extension.obj ((tensorPullback a).obj F)) :=
  (smallEtaleModuleAdjunction a hp).unit.app (cZ.extension.obj F) ≫
    (smallEtaleModulePushforward a).map
      ((zariskiEtalePullbackComparison a cU cZ hp r).inv.app F)

/-- The roof for the actual étale coefficient map.
Source: Stacks 03LC(1), 071N, and 01FB
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality). -/
abbrev qcohEtalePullbackRoof {U Z : Scheme.{u}} (a : U ⟶ Z)
    (cU : ZariskiEtaleModuleContext U) (cZ : ZariskiEtaleModuleContext Z)
    (hp : (smallEtaleModulePushforward a).IsRightAdjoint)
    (r : smallEtaleModulePushforward a ⋙ cZ.restriction ≅
      cU.restriction ⋙ pushforward a) (F : Z.Modules) :=
  QcohComparisonRoof (smallEtaleModulePushforward a)
    (qcohEtaleSections U) (qcohEtaleSections Z)
    (cU.extension.obj ((tensorPullback a).obj F)) (cZ.extension.obj F)
    (qcohEtalePullbackCoefficient a cU cZ hp r F)

/-- The section identification for an étale map is the identity-pullback identification.
Source: Stacks 03LC(1), 071N
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality). -/
def qcohEtalePullbackRoofNormalized {U Z : Scheme.{u}} {a : U ⟶ Z}
    {cU : ZariskiEtaleModuleContext U} {cZ : ZariskiEtaleModuleContext Z}
    {hp : (smallEtaleModulePushforward a).IsRightAdjoint}
    {r : smallEtaleModulePushforward a ⋙ cZ.restriction ≅
      cU.restriction ⋙ pushforward a} {F : Z.Modules}
    (D : qcohEtalePullbackRoof a cU cZ hp r F) : Prop :=
  ∀ n : ℕ, D.sections.hom.f n =
    (D.I.cocomplex.X n).val.presheaf.map
      (AlgebraicGeometry.gabberIdentityEtaleIso a).inv.op

/-- Pullback computed by the canonical coefficient-map roof on the étale sites.
Source: Stacks 03LC(1), 071N, and 01FB
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality). -/
def qcohEtalePullbackRoofMap {U Z : Scheme.{u}} {a : U ⟶ Z}
    (kU : QcohEtaleCohomologyContext U) (kZ : QcohEtaleCohomologyContext Z)
    {cU : ZariskiEtaleModuleContext U} {cZ : ZariskiEtaleModuleContext Z}
    {hp : (smallEtaleModulePushforward a).IsRightAdjoint}
    {r : smallEtaleModulePushforward a ⋙ cZ.restriction ≅
      cU.restriction ⋙ pushforward a} {F : Z.Modules}
    (D : qcohEtalePullbackRoof a cU cZ hp r F) (q : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).obj ((kZ.cohomology q).obj (cZ.extension.obj F)) ⟶
      (forget₂ _ AddCommGrpCat.{u}).obj
        ((kU.cohomology q).obj (cU.extension.obj ((tensorPullback a).obj F))) :=
  letI := kU.enoughInjectives
  letI := kZ.enoughInjectives
  D.map q

/-- The canonical degree-zero augmentation on Zariski module cohomology.
Source: Stacks 01DZ and 03DW(2)
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality). -/
def qcohZariskiAugmentation (Z : Scheme.{u}) (F : Z.Modules) :
    (RingedSpace.globalSectionsFunctor Z.toRingedSpace).obj F ⟶
      (RingedSpace.moduleCohomology Z.toRingedSpace 0).obj F :=
  letI : EnoughInjectives Z.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives Z.toRingedSpace).2
  (RingedSpace.globalSectionsFunctor Z.toRingedSpace).toRightDerivedZero.app F

/-- The canonical degree-zero augmentation on étale module cohomology.
Source: Stacks 03DW(2) and 03FD
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality). -/
def qcohEtaleAugmentation {Z : Scheme.{u}} (k : QcohEtaleCohomologyContext Z)
    (E : SmallEtaleModules Z) :
    (qcohEtaleSections Z).obj E ⟶ (k.cohomology 0).obj E :=
  letI := k.enoughInjectives
  (qcohEtaleSections Z).toRightDerivedZero.app E

/-- The resolution-normalized comparisons are linear isomorphisms, identity on sections
in degree zero, natural in coefficients and in every étale pullback. The universal roof
formulas express independence of all resolution choices. Both étale coefficient maps
and their section identifications are fixed by the canonical ringed-site square.
For étale a, the associated ringed-topos morphism is localization at the object a;
its unit is restriction to that object. Thus the last roof is restriction followed
by the canonical tensor-pullback identification, as required in the node.

Source: Stacks Project, Descent, Tags 03DW(2), 03LC(1), and 071N
(blueprint: lem-sfb-qcoh-cohomology-etale-pullback-naturality).

Proof, with the six steps of the DAG:
1. Use the ringed morphism $\epsilon_Z$ whose direct image is restriction to open subschemes.
The quasi-coherent equivalence identifies $\epsilon_{Z,*}F_{\mathrm{et}}=F$ by the identity on
open sections. Work in a common universe for the sites and coefficients; module sheaves are
Grothendieck abelian and therefore have enough injectives. Apply the ringed-site coefficient-map
calculus to $f=\epsilon_Z$ and $\phi=\mathrm{id}_F$. Its formula is exactly the $\lambda,\beta$
roof specified in the statement, so it defines $c^q_{Z,F}$ independently of the resolutions; in
particular $\Gamma(\lambda)$ is a quasi-isomorphism. It is linear over $\Gamma(Z,\mathcal O_Z)$
and in degree zero is the identity. This application is to ringed-site module cohomology, not to
constant-ring module cohomology.
Dependencies: lem-trf-zariski-etale-tensor-sections, lem-trf-scheme-zariski-etale-quasi-
coherent-equivalence, lem-weil-pbc-ring-sheaves-grothendieck, lem-sp-grothendieck-enough-
injectives, lem-sfb-ringed-site-cohomology-fmap-calculus.
2. Choose a nonnegative injective module resolution $F_{\mathrm{et}}\to I^\bullet$ and put
$K^\bullet=\epsilon_{Z,*}I^\bullet$. For every affine open $V\subseteq Z$, the associated sheaf
restricted to $V_{\mathrm{et}}$ is $(F|_V)_{\mathrm{et}}$ and is quasi-coherent. The
module/abelian evaluation comparison and its slice version identify $H^q(I^\bullet(V))$ with
$H^q(V_{\mathrm{et}},(F|_V)_{\mathrm{et}})$. Affine etale vanishing makes this zero for $q>0$;
for $q=0$ it is $F(V)$. Thus the augmented section complex $0\to F(V)\to K^0(V)\to
K^1(V)\to\cdots$ is exact for every affine open $V$. Affine opens form a basis. An arbitrary
local cocycle may therefore be restricted around each point to an affine open, where it is a
boundary; the resulting local primitives show exactness of the augmented complex of Zariski
sheaves $F\to K^\bullet$. No assertion that arbitrary intersections of affines are affine is
used.
Dependencies: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence, lem-weil-pbc-module-
pullback-quasi-coherent, lem-weil-pbc-etale-site-localization-open, lem-pe-ringed-site-derived-
evaluation-slice, lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison, lem-sc-etale-
affine-qcoherent, lem-weil-pbc-affine-opens-basis.
3. The direct-image acyclicity theorem, applied to $\epsilon_Z$ and each injective $I^n$, says
that $K^n=\epsilon_{Z,*}I^n$ is acyclic for evaluation on every Zariski open, in particular for
global sections on $Z$. Its hypotheses hold because the inclusion of opens presents the ringed-
site morphism from Step 1; no structural-map flatness is needed. Hence the acyclic-resolution
criterion gives the canonical isomorphism
$$d^q:H^q(\Gamma(Z,K^\bullet))\xrightarrow{\sim}H^q(Z,F).$$ The normalized coefficient-map
calculus identifies $c^q_{Z,F}$ with $(d^q)^{-1}$, using the section identity
$\Gamma(Z,K^\bullet)=\Gamma(Z_{\mathrm{et}},I^\bullet)$. Consequently every $c^q_{Z,F}$ is an
isomorphism. This is the inverse of the restriction-resolution map in the proof of the source
proposition. The module/abelian evaluation comparison gives its interpretation in etale abelian
cohomology. Its naturality in $F$ follows from coefficient naturality in the calculus and from
the natural identity on open sections in the quasi-coherent equivalence; it is therefore a
canonical family with the properties asserted by the existing cohomology-comparison node.
Dependencies: lem-weil-pbc-ringed-site-direct-image-injective-evaluation-acyclic, lemma-weil-
pbc-leray-acyclicity, lem-sfb-ringed-site-cohomology-fmap-calculus, lem-weil-pbc-ringed-site-
module-abelian-evaluation-comparison, lem-trf-scheme-zariski-etale-quasi-coherent-equivalence.
4. Fix an etale $a:Z'\to Z$ and put $F'=a^*F$, $E=F_{\mathrm{et}}$, $E'=F'_{\mathrm{et}}$.
Pullback preserves quasi-coherence. Let $\alpha:E\to a_{\mathrm{et},*}E'$ be the transpose of
the canonical comparison $a_{\mathrm{et}}^*E\simeq E'$, and let $\eta:F\to a_*F'$ be the tensor-
pullback unit. Write $e:F\to\epsilon_{Z,*}E$ and $e':F'\to\epsilon_{Z',*}E'$ for the identity-
on-opens maps. The underived ringed square identifies $\epsilon_{Z,*}a_{\mathrm{et},*}$ with
$a_*\epsilon_{Z',*}$ and normalizes the adjoint pullback comparison by these adjunctions. Under
this identification, $$\epsilon_{Z,*}(\alpha)\circ e=a_*(e')\circ\eta.$$ Indeed on an open
$W\subseteq Z$, both maps take $s\in F(W)$ to its tensor-pullback section $a^*s\in F'(a^{-1}W)$.
Locally this is $1\otimes s$, with coefficients acting by $a^\sharp$; the identity-on-open-
sections maps do nothing further. Equality for every $W$ proves equality of the module maps.
Only the unrestricted first clause of the square theorem is used, never its quasi-compact
separated direct-image clause.
Dependencies: lem-weil-pbc-module-pullback-quasi-coherent, lem-trf-scheme-zariski-etale-quasi-
coherent-equivalence, lem-trf-zariski-etale-functor-comparison-square, def-pc-module-pullback.
5. The site $Z'_{\mathrm{et}}$ identifies with $Z_{\mathrm{et}}/Z'$: an object is precisely an
etale $Z$-scheme factoring through $Z'$. The localized ring and $\mathcal O_{Z',\mathrm{et}}$
have the same value $\Gamma(V,\mathcal O_V)$ and the same restrictions on every such object. The
associated module has value $\Gamma(V,(a v)^*F)$, identified with $\Gamma(V,v^*F')$ by tensor-
pullback composition. Thus $a_{\mathrm{et}}$ is the ringed localization, and $\alpha$ is its
unit followed by this identification. The localization normalization of the calculus says that
$T_{a_{\mathrm{et}}}^q(\alpha)$ is exactly the restriction map denoted $a^*_{\mathrm{et}}$ in
the statement, including its module/abelian interpretation. The same calculus applied to the
scheme's Zariski ringed-site morphism and the unit $\eta$ is the recipe of the module-
cohomology-map definition, so $T_a^q(\eta)=a^*_{\mathrm{Zar}}$. These identifications specify
the actual maps, not just isomorphic source and target groups.
Dependencies: lem-weil-pbc-etale-site-localization-open, def-pur-localized-ringed-site, lem-trf-
scheme-zariski-etale-quasi-coherent-equivalence, lem-sfb-ringed-site-cohomology-fmap-calculus,
def-weil-pbc-module-cohomology-fmap.
6. Apply the composition rule of the calculus to the equality of coefficient maps in Step 4,
using the section-preserving ringed-square comparison. The path through $Z_{\mathrm{et}}$ gives
$T_{a_{\mathrm{et}}}^q(\alpha)\,T_{\epsilon_Z}^q(e)$; the path through $Z'_{\mathrm{Zar}}$ gives
$T_{\epsilon_{Z'}}^q(e')\,T_a^q(\eta)$. Steps 1 and 5 identify these respectively with
$a^*_{\mathrm{et}}c^q_{Z,F}$ and $c^q_{Z',F'}a^*_{\mathrm{Zar}}$, proving the required equality.
The coefficient maps are linear for the structural maps of ring sheaves, so the calculus makes
both composites semilinear over $\Gamma(Z,\mathcal O_Z)\to\Gamma(Z',\mathcal O_{Z'})$. The proof
used affine opens only around individual points, injective resolutions in all module sheaves,
and the unrestricted ringed square. It therefore imposes no quasi-compactness or separatedness
condition on $Z$ or $a$.
Dependencies: lem-sfb-ringed-site-cohomology-fmap-calculus, lem-trf-zariski-etale-functor-
comparison-square.
-/
theorem qcoh_cohomology_etale_pullback_naturality :
    ∃ (z : ∀ Z : Scheme.{u}, ZariskiEtaleModuleContext Z)
      (k : ∀ Z : Scheme.{u}, QcohEtaleCohomologyContext Z),
      ∃ c : ∀ (Z : Scheme.{u}) (F : Z.Modules) [F.IsQuasicoherent] (q : ℕ),
        ((RingedSpace.moduleCohomology Z.toRingedSpace q).obj F) ≃+
          (((k Z).cohomology q).obj ((z Z).extension.obj F)),
      (∀ (Z : Scheme.{u}) (F : Z.Modules) [F.IsQuasicoherent],
        (∃ D : qcohEtaleComparisonRoof (z Z) F, qcohEtaleRoofNormalized D) ∧
        ∀ (D : qcohEtaleComparisonRoof (z Z) F), qcohEtaleRoofNormalized D →
          ∀ (q : ℕ) (x : (RingedSpace.moduleCohomology Z.toRingedSpace q).obj F),
            c Z F q x = qcohEtaleComparisonRoofMap (k Z) D q x) ∧
      (∀ (Z : Scheme.{u}) (F : Z.Modules) [F.IsQuasicoherent] (s : Γ(F, ⊤)),
        c Z F 0 (qcohZariskiAugmentation Z F s) =
          qcohEtaleAugmentation (k Z) ((z Z).extension.obj F)
            (((z Z).extension.obj F).val.presheaf.map
              (AlgebraicGeometry.gabberTopEtaleIso Z).inv.op
                (((z Z).adjunction.unit.app F).app ⊤ s))) ∧
      (∀ (Z : Scheme.{u}) (F : Z.Modules) [F.IsQuasicoherent] (q : ℕ)
          (r : Γ(Z, ⊤)) (x : (RingedSpace.moduleCohomology Z.toRingedSpace q).obj F),
        c Z F q (r • x) = r • c Z F q x) ∧
      (∀ (Z : Scheme.{u}) (F G : Z.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
          (φ : F ⟶ G) (q : ℕ)
          (x : (RingedSpace.moduleCohomology Z.toRingedSpace q).obj F),
        c Z G q (((RingedSpace.moduleCohomology Z.toRingedSpace q).map φ).hom x) =
          ((((k Z).cohomology q).map ((z Z).extension.map φ)).hom (c Z F q x))) ∧
      ∀ (U Z : Scheme.{u}) (a : U ⟶ Z) [Etale a],
        ∃ (hp : (smallEtaleModulePushforward a).IsRightAdjoint)
          (r : smallEtaleModulePushforward a ⋙ (z Z).restriction ≅
            (z U).restriction ⋙ pushforward a),
          (∀ (E : SmallEtaleModules U) (W : Z.Opens),
            (r.hom.app E).app W =
              E.val.presheaf.map (AlgebraicGeometry.gabberPreimageEtaleIso a W).hom.op) ∧
          ∀ (F : Z.Modules) [F.IsQuasicoherent],
            ∃ h : ((tensorPullback a).obj F).IsQuasicoherent,
              (∃ D : qcohEtalePullbackRoof a (z U) (z Z) hp r F,
                qcohEtalePullbackRoofNormalized D) ∧
              ∀ (D : qcohEtalePullbackRoof a (z U) (z Z) hp r F),
                qcohEtalePullbackRoofNormalized D →
                  (∀ (q : ℕ)
                    (x : (RingedSpace.moduleCohomology Z.toRingedSpace q).obj F),
                    @c U ((tensorPullback a).obj F) h q (moduleCohomologyPullback a F q x) =
                      qcohEtalePullbackRoofMap (k U) (k Z) D q (c Z F q x)) ∧
                  (∀ (q : ℕ) (s : Γ(Z, ⊤))
                    (y : ((k Z).cohomology q).obj ((z Z).extension.obj F)),
                    qcohEtalePullbackRoofMap (k U) (k Z) D q (s • y) =
                      a.appTop.hom s •
                        (@id (((k U).cohomology q).obj
                          ((z U).extension.obj ((tensorPullback a).obj F)))
                            (qcohEtalePullbackRoofMap (k U) (k Z) D q y))) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
