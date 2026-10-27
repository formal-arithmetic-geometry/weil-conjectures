/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.CategoryTheory.FreeRepresentableDerivedFunctions
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

/-! # Colimits of free representable function models

Source: Stacks Project, sites-cohomology.tex, Tags 08J7 and 03FD;
sites.tex, Tag 00WJ; sites-modules.tex, Tags 03DB and 03CO.
(blueprint: lem-sfb-free-functions-colimit-model-comparison).

The module uses the existing ordinary ringed-site modules and free representable Hom.
All colimits are termwise complex colimits, localized only afterwards. The presheaf
comparison uses the underlying module-injective resolutions as acyclic representatives
of Rι; it does not assume that their underlying abelian sheaves are injective.

The evaluation isomorphism is the underived generator evaluation from the recorded
free-representable model. Applying it termwise is not a lift of a derived isomorphism.
For an injective resolution, its cohomology is the cohomology of the recorded derived
comparison: composing with any compatible abelian resolution comparison is exactly
that model's comparisonMap. Exactness of sheafification and precomposition gives the
cohomology identifications below. No sheaf/presheaf colimit is identified without a.

## Main statements

* `comparison_quasiIso`: the conditional criterion and invertibility after localization.
* `comparison_homology`: its canonical cohomology normalization with a t_P.
* `presheafComparison_homology`: the arrow in that normalization is H^q(δ).
* `comparison_naturality`, `comparison_parameterNaturality`: the two comparison squares.
* `cohomologyComparison_negative`: vanishing in negative degrees.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u wA wM wP

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.FreeRepresentableDerivedFunctions

namespace CategoryTheory.FreeFunctionsColimitModelComparison

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{u}) [HasFiniteProducts C]

/-- The existing forgetful functor U on ordinary module sheaves.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
def underlying : modules J R ⥤ Sheaf J AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ring J R)

/-- Reuse additivity of U; no new categorical structure is chosen.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
instance underlyingAdditive : (underlying J R).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf (ring J R)).Additive
/-- Reuse exactness of U on finite limits.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
instance underlyingLimits : PreservesFiniteLimits (underlying J R) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf (ring J R)))
/-- Reuse preservation of small colimits by U, including their coprojections.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
instance underlyingColimits (A : Type u) [SmallCategory A] :
    PreservesColimitsOfShape A (underlying J R) :=
  inferInstanceAs (PreservesColimitsOfShape A (SheafOfModules.toSheaf.{u} (ring J R)))

/-- Apply ιU termwise. On the supplied nonnegative module-injective resolutions this
is an acyclic model for Rι(UM[0]), by Stacks 03FD and the acyclic-resolution theorem.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
def raw : CochainComplex (modules J R) ℤ ⥤ CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ :=
  (underlying J R ⋙ sheafToPresheaf J AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)
/-- Apply the existing H_P termwise, with H_P the sheaf Hom out of R[P].

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
def onComplexes (P : C) : CochainComplex (modules J R) ℤ ⥤
    CochainComplex (modules J R) ℤ :=
  (hom J R P).mapHomologicalComplex (.up ℤ)
/-- Apply the existing U termwise to module complexes.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
def abelianComplexes : CochainComplex (modules J R) ℤ ⥤
    CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ :=
  (underlying J R).mapHomologicalComplex (.up ℤ)
/-- Reuse termwise preservation of colimits by U.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
instance abelianComplexesColimits (A : Type u) [SmallCategory A] :
    PreservesColimitsOfShape A (abelianComplexes J R) :=
  inferInstanceAs (PreservesColimitsOfShape A
    ((underlying J R).mapHomologicalComplex (.up ℤ)))

/-- The exact functor a t_P on abelian presheaves; both factors are the recorded ones.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
def transform (P : C) : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ Sheaf J AddCommGrpCat.{u} :=
  precomp P ⋙ presheafToSheaf J AddCommGrpCat.{u}
/-- Reuse additivity of precomposition and abelian sheafification.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
instance transformAdditive (P : C) : (transform J P).Additive :=
  inferInstanceAs ((precomp P ⋙ presheafToSheaf J AddCommGrpCat.{u}).Additive)
/-- Reuse finite-limit preservation by precomposition and sheafification.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
instance transformLimits (P : C) : PreservesFiniteLimits (transform J P) :=
  inferInstanceAs (PreservesFiniteLimits (precomp P ⋙ presheafToSheaf J AddCommGrpCat.{u}))
/-- Reuse sectionwise colimits for precomposition and the sheafification adjunction.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
instance transformColimits (P : C) : PreservesColimitsOfSize.{u, u} (transform J P) :=
  inferInstanceAs (PreservesColimitsOfSize.{u, u}
    ((Functor.whiskeringLeft _ _ _).obj (prod.functor.flip.obj P).op ⋙
      presheafToSheaf J AddCommGrpCat.{u}))

variable [HasDerivedCategory.{wA} (Sheaf J AddCommGrpCat.{u})] [J.Subcanonical]

/-- The canonical underived generator evaluation of the recorded model, followed by
the sheafification counit. Its data are determined by evaluation on the free generators.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
def evaluation (P : C) : homAbelian J R P ≅ underlying J R ⋙ sections J P :=
  sheafEvaluationIso J R P ((free_representable_derived_functions_model J R).choose P)


/-- Apply the underived evaluation termwise, inserting only the standard composition
isomorphisms. This is not an assumed lift of a derived-category isomorphism.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
def evaluationComplex (P : C) :
    onComplexes J R P ⋙ abelianComplexes J R ≅
      raw J R ⋙ (transform J P).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl (homAbelian J R P)) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex (evaluation J R P) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (underlying J R ⋙ sections J P)) (.up ℤ)).symm

variable {I : Type u} [SmallCategory I]

/-- The chain map c is colimit.desc of the actual H_P-image of the supplied cocone.
Composing with its i-th coprojection therefore gives H_P(k_i), by the colimit property.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
def comparison (P : C) {K : I ⥤ CochainComplex (modules J R) ℤ} (c : Cocone K) :
    colimit (K ⋙ onComplexes J R P) ⟶ (onComplexes J R P).obj c.pt :=
  colimit.desc (K ⋙ onComplexes J R P) ((onComplexes J R P).mapCocone c)

/-- The chain representative of δ: colimit.desc of the ιU-image of the supplied
cocone. Under augmentation-compatible acyclic-resolution comparison its components
are precisely Rι of the original underlying module coprojections.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
def presheafComparison {K : I ⥤ CochainComplex (modules J R) ℤ} (c : Cocone K) :
    colimit (K ⋙ raw J R) ⟶ (raw J R).obj c.pt :=
  colimit.desc (K ⋙ raw J R) ((raw J R).mapCocone c)

/-- Transport the termwise colimit using U-colimit preservation, the actual underived
evaluation, and a t_P-colimit preservation. Every isomorphism is normalized on
colimit coprojections. No abelian-injective resolution diagram is chosen.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
def sourceIso (P : C) (K : I ⥤ CochainComplex (modules J R) ℤ) :
    (abelianComplexes J R).obj (colimit (K ⋙ onComplexes J R P)) ≅
      ((transform J P).mapHomologicalComplex (.up ℤ)).obj (colimit (K ⋙ raw J R)) :=
  preservesColimitIso (abelianComplexes J R) (K ⋙ onComplexes J R P) ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft K (evaluationComplex J R P)) ≪≫
    (preservesColimitIso ((transform J P).mapHomologicalComplex (.up ℤ))
      (K ⋙ raw J R)).symm

/-- Take cohomology of the source identification and use the canonical exact-functor
cohomology isomorphism H^q(a t_P L) ≅ a t_P H^q(L).

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
def sourceHomologyIso (P : C) (K : I ⥤ CochainComplex (modules J R) ℤ) (q : ℤ) :
    ((abelianComplexes J R).obj (colimit (K ⋙ onComplexes J R P))).homology q ≅
      (transform J P).obj ((colimit (K ⋙ raw J R)).homology q) :=
  (HomologicalComplex.homologyFunctor _ (.up ℤ) q).mapIso (sourceIso J R P K) ≪≫
    ((transform J P).mapHomologicalComplexHomologyIso (.up ℤ) q).app
      (colimit (K ⋙ raw J R))

/-- Take cohomology of generator evaluation on the target and apply the canonical
exact-functor cohomology isomorphism. On injective representatives this is the
cohomology of the recorded derived model, as its comparisonMap normalization states.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
def targetHomologyIso (P : C) (K : CochainComplex (modules J R) ℤ) (q : ℤ) :
    ((abelianComplexes J R).obj ((onComplexes J R P).obj K)).homology q ≅
      (transform J P).obj (((raw J R).obj K).homology q) :=
  (HomologicalComplex.homologyFunctor _ (.up ℤ) q).mapIso
      ((evaluationComplex J R P).app K) ≪≫
    ((transform J P).mapHomologicalComplexHomologyIso (.up ℤ) q).app ((raw J R).obj K)

variable [IsFiltered I]

/-- The arrow colim h^q(UM_i) → h^q(UM∞), computed on the given acyclic module
resolutions. Its legs are cohomology of ιU(k_i); augmentation compatibility identifies
these with h^q of the original module coprojections.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
def cohomologyComparison {K : I ⥤ CochainComplex (modules J R) ℤ} (c : Cocone K) (q : ℤ) :
    colimit ((K ⋙ raw J R) ⋙ HomologicalComplex.homologyFunctor _ (.up ℤ) q) ⟶
      ((raw J R).obj c.pt).homology q :=
  colimit.desc ((K ⋙ raw J R) ⋙ HomologicalComplex.homologyFunctor _ (.up ℤ) q)
    ((HomologicalComplex.homologyFunctor _ (.up ℤ) q).mapCocone ((raw J R).mapCocone c))

/-- The normalized source identification with a t_P colim h^q(UM_i), using exact
filtered-colimit preservation of cohomology in abelian presheaves.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
def sourceCohomologyIso (P : C) (K : I ⥤ CochainComplex (modules J R) ℤ) (q : ℤ) :
    ((abelianComplexes J R).obj (colimit (K ⋙ onComplexes J R P))).homology q ≅
      (transform J P).obj (colimit ((K ⋙ raw J R) ⋙
        HomologicalComplex.homologyFunctor _ (.up ℤ) q)) :=
  sourceHomologyIso J R P K q ≪≫
    (transform J P).mapIso
      (preservesColimitIso (HomologicalComplex.homologyFunctor _ (.up ℤ) q) (K ⋙ raw J R))

variable
  [HasDerivedCategory.{wM} (modules J R)]
  [HasDerivedCategory.{wP} (Cᵒᵖ ⥤ AddCommGrpCat.{u})]

/-- The normalization H^q(Uc) = a t_P(colim h^q(UM_i) → h^q(UM∞)) under the
specified canonical source and target isomorphisms. On resolution diagrams these
are cohomology of the recorded derived model, not chosen identifications of objects.

Proof: by module-sheaves-colimits-forgetful U preserves the termwise colimit.
Use generator evaluation from lem-sfb-free-representable-derived-functions-model.
Naturality on each cocone leg identifies its two images. Exact a and t_P commute
with cohomology; exact filtered presheaf colimits do also, by
src-weil-homology-preserves-exact-colimits. After each coprojection the equation is
this naturality square. The colimit universal property gives the equality.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
theorem comparison_homology (P : C)
    {K : I ⥤ CochainComplex (modules J R) ℤ} (c : Cocone K) (q : ℤ) :
    HomologicalComplex.homologyMap ((abelianComplexes J R).map (comparison J R P c)) q ≫
        (targetHomologyIso J R P c.pt q).hom =
      (sourceCohomologyIso J R P K q).hom ≫
        (transform J P).map (cohomologyComparison J R c q) := by
  sorry

/-- The normalized presheaf cohomology comparison is exactly H^q(δ).

Proof: exact filtered presheaf colimits commute with cohomology by
src-weil-homology-preserves-exact-colimits. Check after every coprojection: both
composites are H^q(ιU(k_i)). Uniqueness in def-weil-pbc-category-colimit finishes.
With compatible augmentations, these maps are induced by the coefficient coprojections.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
theorem presheafComparison_homology
    {K : I ⥤ CochainComplex (modules J R) ℤ} (c : Cocone K) (q : ℤ) :
    (preservesColimitIso (HomologicalComplex.homologyFunctor _ (.up ℤ) q)
      (K ⋙ raw J R)).inv ≫
        HomologicalComplex.homologyMap (presheafComparison J R c) q =
      cohomologyComparison J R c q := by
  sorry

/-- For every compatible choice of the supplied nonnegative injective resolutions,
invertibility of the derived-presheaf comparison implies that c is a quasi-isomorphism
and Q(c) is invertible. δ is represented by Q(presheafComparison) on these resolutions.

Proof: (1) U is exact, faithful, and preserves colimits by
lem-weil-pbc-module-sheaves-colimits-forgetful. Sheafification a is exact and
cocontinuous by lem-weil-pbc-sheafification-exact; t_P is exact and cocontinuous
sectionwise. Filtered sheaf and presheaf colimits are exact.
(2) Nonnegative module-injective resolutions compute RH_P. Their underlying abelian
terms are ι-acyclic by Stacks 03FD; lem-sfb-module-resolution-derived-presheaf-comparison
identifies their ι-images, naturally in compatible augmented maps, with Rι(UM[0]).
The derived model of lem-sfb-free-representable-derived-functions-model identifies
D(U)RH_P with D(a)D(t_P)Rι. Its normalization identifies the actual maps, not merely
the objects. Cohomology of its isomorphisms gives targetHomologyIso on these models.
(3) Exact filtered colimits give sourceCohomologyIso, using the original coprojections.
comparison_homology and presheafComparison_homology identify H^q(Uc) with a t_P H^q(δ).
(4) If δ is invertible, all H^q(δ) and hence H^q(Uc) are invertible. U detects
isomorphisms: the inverse of an underlying abelian-sheaf isomorphism is R-linear.
Thus H^q(c) is invertible in every degree. This is QuasiIso; localization inverts c.
(5) Nonnegativity gives negative-degree vanishing. Universally quantifying the
resolutions gives independence of choices; the coefficient and parameter squares
below give the stated naturality, also for the identity coefficient map between
two choices. No finiteness of coverings or cohomological-dimension bound was used.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
theorem comparison_quasiIso (P : C)
    (M : I ⥤ modules J R) (K : I ⥤ CochainComplex (modules J R) ℤ)
    (s : M ⋙ CochainComplex.singleFunctor (modules J R) 0 ⟶ K)
    (c : Cocone K)
    (sLimit : (CochainComplex.singleFunctor (modules J R) 0).obj (colimit M) ⟶ c.pt)
    (hs : ∀ i : I, QuasiIso (s.app i))
    (hI : ∀ (i : I) (n : ℤ), Injective ((K.obj i).X n))
    (hneg : ∀ i : I, (K.obj i).IsStrictlyGE 0)
    (hsLimit : QuasiIso sLimit)
    (hILimit : ∀ n : ℤ, Injective (c.pt.X n))
    (hnegLimit : c.pt.IsStrictlyGE 0)
    (hcompat : ∀ i : I, s.app i ≫ c.ι.app i =
      (CochainComplex.singleFunctor (modules J R) 0).map (colimit.ι M i) ≫ sLimit)
    (hδ : IsIso (DerivedCategory.Q.map (presheafComparison J R c))) :
    QuasiIso (comparison J R P c) ∧
      IsIso (DerivedCategory.Q.map (comparison J R P c)) := by
  sorry

/-- Coefficient naturality on every compatible chain lift; in particular this
applies to augmentation-compatible lifts of coefficient diagrams and their colimit map.
Taking the identity coefficient map includes a change of injective resolutions.

Proof: check the square after each coprojection. The cocone compatibility h and
functoriality of H_P give equality. Uniqueness in def-weil-pbc-category-colimit
gives the equality on colimits. Localization and cohomology preserve this equality;
the recorded derived model gives the same maps by augmentation compatibility.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
theorem comparison_naturality (P : C)
    {K L : I ⥤ CochainComplex (modules J R) ℤ} (c : Cocone K) (d : Cocone L)
    (f : K ⟶ L) (g : c.pt ⟶ d.pt)
    (h : ∀ i : I, f.app i ≫ d.ι.app i = c.ι.app i ≫ g) :
    colimMap (Functor.whiskerRight f (onComplexes J R P)) ≫ comparison J R P d =
      comparison J R P c ≫ (onComplexes J R P).map g := by
  sorry

/-- The actual contravariant parameter map: precompose internal Hom by the existing
free-module map R[P′] → R[P], then apply it termwise.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
def parameterMap {P' P : C} (f : P' ⟶ P) : onComplexes J R P ⟶ onComplexes J R P' :=
  NatTrans.mapHomologicalComplex (F := hom J R P) (G := hom J R P')
    ((SheafOfModules.homFunctor R).map ((free J R).map f).op) (.up ℤ)

/-- Contravariant parameter naturality under every map P′ → P of site objects.

Proof: precomposition in sheaf Hom commutes with coefficient maps. Check this
square on each cocone leg, then use the colimit universal property. The generator
evaluation normalization identifies precomposition with restriction along 1 × f,
as in lem-sfb-free-representable-derived-functions-model. Exact functors and
cohomology preserve the square, proving parameter naturality of the normalization.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
theorem comparison_parameterNaturality {P' P : C} (f : P' ⟶ P)
    {K : I ⥤ CochainComplex (modules J R) ℤ} (c : Cocone K) :
    colimMap (Functor.whiskerLeft K (parameterMap J R f)) ≫ comparison J R P' c =
      comparison J R P c ≫ (parameterMap J R f).app c.pt := by
  sorry

/-- The source and target of the presheaf cohomology comparison vanish in negative
degrees on every supplied nonnegative resolution diagram.

Proof: ιU preserves zero objects, so the raw complexes are nonnegative. Their
negative-degree cohomology objects are zero. The colimit of this zero diagram
is zero by its universal property. The same argument applies to the target.
Exact a t_P and the displayed cohomology identifications give the same vanishing
on the internal-Hom side.

Source: Stacks 08J7, 03FD, 00WJ and 03DB.
(blueprint: lem-sfb-free-functions-colimit-model-comparison). -/
theorem cohomologyComparison_negative
    {K : I ⥤ CochainComplex (modules J R) ℤ} (c : Cocone K)
    (hneg : ∀ i : I, (K.obj i).IsStrictlyGE 0)
    (hnegLimit : c.pt.IsStrictlyGE 0) (q : ℤ) (hq : q < 0) :
    IsZero (colimit ((K ⋙ raw J R) ⋙ HomologicalComplex.homologyFunctor _ (.up ℤ) q)) ∧
      IsZero (((raw J R).obj c.pt).homology q) := by
  sorry

end CategoryTheory.FreeFunctionsColimitModelComparison
