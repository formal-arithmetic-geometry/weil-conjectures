# AlgebraicGeometry.Scheme.adicFiniteComparisonData

## Reason

The four source-backed intermediate theorems need the normalized coefficient constructions
in their statements. Keeping those constructions in the theorem module would produce an
import cycle. Move the existing construction API and all its proved helpers to
Sheaf.Paper.AdicFiniteReductionData and publicly reexport it from the assigned module.
This is an acyclic statement dependency extraction, not a split to evade a compile limit.
Every existing public declaration retains its name, universes, visibility and attributes.
Four normalization predicates are named; unfolding them gives the former signatures.
The assigned theorem's signature is verbatim unchanged. Data-body edits supply the existing finite-limits theorem explicitly to
inverseImageData_exists and derivedPull; proof irrelevance keeps these expressions
definitionally equal to the originals. The additive instance proof directly applies the
existing pull_additive theorem. All previous public imports remain reachable.
No consumer source needs adaptation; no target or mathematical definition changes meaning.
The prior module exceeded the 60-second compile bound before any edits. Profiling is used
to repair that independently: the additive instance directly applies pull_additive instead
of searching for it through the large concrete functor. Finite-limits proofs are also
supplied explicitly. The largest derived comparison proof reuses the existing
resolving-module-square theorem instead of building and comparing two universal lifts.
The normalization aliases are definitionally equal to the old formulas; no instance
attribute changes.

## Old

The following entire construction prefix occupied AdicConstructibleFiniteReductions.lean:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module
public import Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Sheaf.Paper.CompletedPullbackAdjunction
import Sheaf.CategoryTheory.GeometricModuleConstruction
import all Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Sites.ConstantSheaf

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import Sheaf.CategoryTheory.DerivedCategory.ResolvingAdjunction
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
/-! # Finite reductions of a derived-complete constructible complex

Source: Stacks Project, proetale.tex, Tag 09C2, with Tag 09AL for compatible etale origins
(blueprint: lem-sfb-adic-constructible-finite-reductions).

The input and both reduction categories use ConstantCompletion.D on the equivalent
coefficient-sized sites. The coefficient universe is independent of the scheme universe.
Index n means positive exponent n+1. All scalar units and composition comparisons below
are uniquely normalized by the ordinary scalar insertion and their K-flat computations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.defProp false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion

namespace AlgebraicGeometry.Scheme

variable {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}


/-- The ordinary tensor unit is uniquely specified by insertion of 1 on sections.
Proof: scalar insertion is linear over the source ring, natural and compatible with
restrictions. Sheafification gives the map. The underlying-sheaf functor is faithful.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
theorem adicFiniteOrdinaryUnit_existsUnique {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S) :
    ∃! e : 𝟭 (Mod R) ⟶ change f ⋙ res f,
      ∀ M : Mod R, (underlying R).map (e.app M) = insertion f M := by
  let e : 𝟭 (Mod R) ⟶ change f ⋙ res f := (SheafOfModules.tensorAdjunction f).unit
  have he (M : Mod R) : (underlying R).map (e.app M) = insertion f M := by
    apply (insertion_existsUnique f M).unique
    · exact SheafOfModules.tensorUnit_apply f M
    · exact (insertion_existsUnique f M).exists.choose_spec
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply NatTrans.ext
  funext M
  apply (underlying R).map_injective
  exact (he' M).trans (he M).symm

/-- The actual scalar insertion, retaining its unique sectionwise normalization.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteOrdinaryUnit {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S) :
    𝟭 (Mod R) ⟶ change f ⋙ res f :=
  (adicFiniteOrdinaryUnit_existsUnique f).exists.choose

/-- Apply scalar insertion termwise to a complex; all maps are those of the tensor unit.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteOrdinaryUnitComplex {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S)
    (P : Cx R) : P ⟶ ((res f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((change f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) where
  f i := (adicFiniteOrdinaryUnit f).app (P.X i)
  comm' i j _ := ((adicFiniteOrdinaryUnit f).naturality (P.d i j)).symm

/-- Ordinary restriction composition is the identity on underlying sections.
Proof: both actions precompose by the composite ring map, and the identity maps of
additive sheaves are linear. Their inverses are the same identities; faithfulness
of the underlying functor proves uniqueness.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
theorem adicFiniteResComp_existsUnique {R S V : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) :
    ∃! e : res g ⋙ res f ≅ res (f ≫ g),
      ∀ M : Mod V, (underlying R).map (e.hom.app M) = 𝟙 _ := by
  refine ⟨Iso.refl _, ?_, ?_⟩
  · intro M
    rfl
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (underlying R).map_injective
    exact (he M).trans (by rfl)

/-- The sectionwise restriction composition isomorphism.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteResComp {R S V : Sheaf T CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ V) :
    res g ⋙ res f ≅ res (f ≫ g) :=
  (adicFiniteResComp_existsUnique f g).exists.choose

/-- Exact derived restriction composition, obtained from the sectionwise identity.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteDresComp {R S V : Sheaf T CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ V) :
    dres g ⋙ dres f ≅ dres (f ≫ g) :=
  letI := HasDerivedCategory.standard (Mod R)
  letI := HasDerivedCategory.standard (Mod S)
  letI := HasDerivedCategory.standard (Mod V)
  letI := (siteRestrictScalars_exact f).1
  letI := (siteRestrictScalars_exact f).2
  letI := (siteRestrictScalars_exact g).1
  letI := (siteRestrictScalars_exact g).2
  letI := (siteRestrictScalars_exact (f ≫ g)).1
  letI := (siteRestrictScalars_exact (f ≫ g)).2
  (Functor.mapDerivedCategoryCompIso (res g) (res f)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (adicFiniteResComp f g)

private def adicFiniteHomEquiv
    {C : Type w} [SmallCategory C] {JC : GrothendieckTopology C}
    {R S : Sheaf JC CommRingCat.{w}} (f : R ⟶ S) (M : Mod R) (N : Mod S) :
    ((change f).obj M ⟶ N) ≃ (M ⟶ (res f).obj N) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)).homEquiv _ _).trans
    (SheafOfModules.tensorPresheafHomEquiv f M N)

private theorem adicFiniteHomEquiv_apply
    {C : Type w} [SmallCategory C] {JC : GrothendieckTopology C}
    {R S : Sheaf JC CommRingCat.{w}} (f : R ⟶ S) (M : Mod R) (N : Mod S)
    (a : (change f).obj M ⟶ N) (U : Cᵒᵖ) (m : M.val.obj U) :
    (adicFiniteHomEquiv f M N a).val.app U m =
      a.val.app U (tensorSection f M U 1 m) := by
  rfl

private def adicFiniteAdjunction
    {C : Type w} [SmallCategory C] {JC : GrothendieckTopology C}
    {R S : Sheaf JC CommRingCat.{w}} (f : R ⟶ S) : change f ⊣ res f :=
  SheafOfModules.tensorAdjunction f

private theorem adicFiniteAdjunction_homEquiv {R S : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (M : Mod R) (N : Mod S) (a : (change f).obj M ⟶ N) :
    (adicFiniteAdjunction f).homEquiv M N a = adicFiniteHomEquiv f M N a := by
  simp only [adicFiniteAdjunction, SheafOfModules.tensorAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adicFiniteAdjunction_unit {R S : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) : (adicFiniteAdjunction f).unit = adicFiniteOrdinaryUnit f := by
  apply NatTrans.ext
  funext M
  apply (underlying R).map_injective
  calc
    _ = insertion f M := by
      apply (insertion_existsUnique f M).unique
      · intro U m
        change ((adicFiniteAdjunction f).unit.app M).val.app U m = _
        rw [← Adjunction.homEquiv_id, adicFiniteAdjunction_homEquiv]
        rfl
      · exact (insertion_existsUnique f M).exists.choose_spec
    _ = _ := ((adicFiniteOrdinaryUnit_existsUnique f).exists.choose_spec M).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The derived quotient unit, uniquely specified on K-flat complexes.
Proof: derive the ordinary tensor/restriction adjunction. Exact restriction has the
resFactors comparison; on K-flat models the universal tensor comparison is invertible.
The displayed formula therefore determines the unit there and hence on all derived objects.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
theorem adicFiniteUnit_existsUnique {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S) :
    ∃! e : 𝟭 (ConstantCompletion.D R) ⟶ extend f ⋙ dres f,
      ∀ P : Cx R, CochainComplex.IsKFlatIndependentCoefficients (J := T) (R := R) P →
        e.app ((Q R).obj P) ≫ (dres f).map ((extendComparison f).app P) =
          (Q R).map (adicFiniteOrdinaryUnitComplex f P) ≫
            (resFactors f).hom.app
              (((change f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  let := (siteRestrictScalars_exact f).1
  let := (siteRestrictScalars_exact f).2
  obtain ⟨E, hobj, hmap, _, hpres, _⟩ :=
    SheafOfModules.derivedChangeOfRingsIndependentCoefficients f
  have hE : E = change f := CategoryTheory.Functor.ext hobj (fun _ _ a ↦ hmap a)
  have hpres' : ∀ {P Q : Cx R} (a : P ⟶ Q),
      P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients →
        QuasiIso a → QuasiIso (((change f).mapHomologicalComplex (.up ℤ)).map a) := by
    cases hE
    exact hpres
  obtain ⟨_, L, ε, hu, hc, adj, ha⟩ :=
    Adjunction.exists_leftDerived_adjunction (change f) (res f) (adicFiniteAdjunction f)
      (CochainComplex.IsKFlatIndependentCoefficients (R := R))
      (fun P ↦ by
        obtain ⟨Y, s, hY, _, hs, _⟩ :=
          CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
        exact ⟨Y, s, hY, hs⟩) hpres'
  let : L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Mod R) (.up ℤ)) := hu
  let : (extend f).IsLeftDerivedFunctor (extendComparison f)
      (HomologicalComplex.quasiIso (Mod R) (.up ℤ)) := (derivedExtension f).universal
  let i : L ≅ extend f := Functor.leftDerivedUnique (extend f) L ε (extendComparison f)
    (HomologicalComplex.quasiIso (Mod R) (.up ℤ))
  let adj' : extend f ⊣ dres f := adj.ofNatIsoLeft i
  have hi (P : Cx R) : i.hom.app ((Q R).obj P) ≫ (extendComparison f).app P = ε.app P := by
    simpa only [i, Functor.leftDerivedUnique, Functor.leftDerivedNatIso_hom,
      Functor.leftDerivedNatTrans, Iso.refl_hom, NatTrans.id_app, Category.comp_id] using
      (Functor.leftDerived_fac_app (extend f) (extendComparison f)
        (HomologicalComplex.quasiIso (Mod R) (.up ℤ)) L ε P)
  have he (P : Cx R) :
      adj'.unit.app ((Q R).obj P) ≫ (dres f).map ((extendComparison f).app P) =
        (Q R).map (adicFiniteOrdinaryUnitComplex f P) ≫
          (resFactors f).hom.app
            (((change f).mapHomologicalComplex (.up ℤ)).obj P) := by
    have ht := (adj'.homEquiv_unit _ _ ((extendComparison f).app P)).symm
    apply ht.trans
    change (adj.ofNatIsoLeft i).homEquiv _ _ ((extendComparison f).app P) = _
    rw [Adjunction.homEquiv_ofNatIsoLeft_apply, hi]
    have h := ha P (((change f).mapHomologicalComplex (.up ℤ)).obj P) (𝟙 _)
    simp only [CategoryTheory.Functor.map_id, Adjunction.homEquiv_id] at h
    have hunit : ((adicFiniteAdjunction f).mapHomologicalComplex (.up ℤ)).unit.app P =
        adicFiniteOrdinaryUnitComplex f P := by
      ext q
      simp only [Adjunction.mapHomologicalComplex_unit_app_f, adicFiniteAdjunction_unit]
      rfl
    rw [hunit] at h
    change adj.homEquiv ((Q R).obj P)
      (((change f).mapHomologicalComplex (.up ℤ) ⋙ Q S).obj P)
      (ε.app P ≫ 𝟙 _) =
        (Q R).map (adicFiniteOrdinaryUnitComplex f P) ≫
          (resFactors f).hom.app
            (((change f).mapHomologicalComplex (.up ℤ)).obj P) at h
    rw [Category.comp_id] at h
    exact h
  refine ⟨adj'.unit, fun P _ ↦ he P, ?_⟩
  intro e' he'
  apply Localization.natTrans_ext (Q R) (HomologicalComplex.quasiIso (Mod R) (.up ℤ))
  intro P
  obtain ⟨Y, s, hY, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  have := hs
  have : IsIso ((extendComparison f).app Y) := (derivedExtension f).computation Y
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Y).1 hY)
  have hy : e'.app ((Q R).obj Y) = adj'.unit.app ((Q R).obj Y) := by
    apply (cancel_mono ((dres f).map ((extendComparison f).app Y))).1
    exact (he' Y hY).trans (he Y).symm
  apply (cancel_epi ((Q R).map s)).1
  change (𝟭 (ConstantCompletion.D R)).map ((Q R).map s) ≫ e'.app _ =
    (𝟭 (ConstantCompletion.D R)).map ((Q R).map s) ≫ adj'.unit.app _
  rw [e'.naturality, adj'.unit.naturality]
  rw [hy]

/-- The canonical derived tensor unit, with the K-flat normalization retained.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteUnit {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S) :
    𝟭 (ConstantCompletion.D R) ⟶ extend f ⋙ dres f :=
  (adicFiniteUnit_existsUnique f).exists.choose

private def adicFiniteCompositeAdjunction {R S V : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) : change f ⋙ change g ⊣ res (f ≫ g) :=
  (adicFiniteAdjunction f).comp (adicFiniteAdjunction g)

private theorem adicFiniteCompositeAdjunction_homEquiv
    {R S V : Sheaf T CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ V)
    (M : Mod R) (N : Mod V) (a : (change f ⋙ change g).obj M ⟶ N) :
    (adicFiniteCompositeAdjunction f g).homEquiv M N a =
      adicFiniteHomEquiv f M ((res g).obj N)
        (adicFiniteHomEquiv g ((change f).obj M) N a) := by
  simp only [adicFiniteCompositeAdjunction, Adjunction.comp_homEquiv]
  change (adicFiniteAdjunction f).homEquiv M _
    ((adicFiniteAdjunction g).homEquiv ((change f).obj M) N a) = _
  rw [adicFiniteAdjunction_homEquiv, adicFiniteAdjunction_homEquiv]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped ChangeOfRings in
private theorem adicFiniteTensorSection_smul {R S : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (M : Mod R) (U : Dᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    tensorSection f M U s m = s • tensorSection f M U 1 m := by
  let eta := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (siteModuleRings S).obj)).unit.app (SheafOfModules.changeOfRingsPresheaf.{w, w, w} f M)
  have h := (eta.app U).hom.map_smul s
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (f.hom.app U).hom] m)
  change eta.app U ((s * 1) ⊗ₜ[R.obj.obj U, (f.hom.app U).hom] m) = _ at h
  simpa only [mul_one] using! h

private theorem adicFiniteHomEquiv_apply_tensor {R S : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (M : Mod R) (N : Mod S) (a : (change f).obj M ⟶ N)
    (U : Dᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    a.val.app U (tensorSection f M U s m) =
      s • (show N.val.obj U from (adicFiniteHomEquiv f M N a).val.app U m) := by
  rw [adicFiniteTensorSection_smul]
  exact (a.val.app U).hom.map_smul s _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ordinary tensor associativity fixed by pure tensors.
Proof: balancing sends v tensor (s tensor m) to v*g(s) tensor m, with inverse
v tensor m mapped to v tensor (1 tensor m). The formulas respect restrictions
and sheafification. Pure tensors generate locally, proving uniqueness.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
theorem adicFiniteChangeComp_existsUnique {R S V : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) :
    ∃! e : change f ⋙ change g ≅ change (f ≫ g),
      ∀ (M : Mod R) (U : Dᵒᵖ) (s : S.obj.obj U) (v : V.obj.obj U) (m : M.val.obj U),
        (e.hom.app M).val.app U
          (tensorSection g ((change f).obj M) U v (tensorSection f M U s m)) =
            tensorSection (f ≫ g) M U (v * (g.hom.app U) s) m := by
  let adj := adicFiniteCompositeAdjunction f g
  let e : change f ⋙ change g ≅ change (f ≫ g) :=
    adj.leftAdjointUniq (adicFiniteAdjunction (f ≫ g))
  have he0 (M : Mod R) (U : Dᵒᵖ) (m : M.val.obj U) :
      (e.hom.app M).val.app U
        (tensorSection g ((change f).obj M) U 1 (tensorSection f M U 1 m)) =
          tensorSection (f ≫ g) M U 1 m := by
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app adj
      (adicFiniteAdjunction (f ≫ g)) M
    rw [← Adjunction.homEquiv_id] at h
    change (adicFiniteCompositeAdjunction f g).homEquiv M _ (e.hom.app M) = _ at h
    rw [adicFiniteCompositeAdjunction_homEquiv, adicFiniteAdjunction_homEquiv] at h
    have hh := congrArg (fun z ↦ z.val.app U m) h
    exact hh
  have he : ∀ (M : Mod R) (U : Dᵒᵖ) (s : S.obj.obj U) (v : V.obj.obj U)
      (m : M.val.obj U), (e.hom.app M).val.app U
        (tensorSection g ((change f).obj M) U v (tensorSection f M U s m)) =
          tensorSection (f ≫ g) M U (v * (g.hom.app U) s) m := by
    intro M U s v m
    erw [adicFiniteHomEquiv_apply_tensor g ((change f).obj M)
      ((change (f ≫ g)).obj M) (e.hom.app M) U v (tensorSection f M U s m)]
    erw [adicFiniteTensorSection_smul f M U s m]
    erw [(adicFiniteHomEquiv g _ _ (e.hom.app M)).val.app U |>.hom.map_smul]
    change v • ((g.hom.app U s) •
      ((e.hom.app M).val.app U
        (tensorSection g ((change f).obj M) U 1 (tensorSection f M U 1 m)))) = _
    rw [he0, smul_smul, ← adicFiniteTensorSection_smul]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (adicFiniteHomEquiv g ((change f).obj M) _).injective
  apply (adicFiniteHomEquiv f M _).injective
  apply SheafOfModules.hom_ext
  ext U m
  change (e'.hom.app M).val.app U
      (tensorSection g ((change f).obj M) U 1 (tensorSection f M U 1 m)) =
    (e.hom.app M).val.app U
      (tensorSection g ((change f).obj M) U 1 (tensorSection f M U 1 m))
  rw [he', he0, map_one, mul_one]


/-- The ordinary balancing isomorphism, uniquely fixed by its pure-tensor formula.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteChangeComp {R S V : Sheaf T CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ V) :
    change f ⋙ change g ≅ change (f ≫ g) :=
  (adicFiniteChangeComp_existsUnique f g).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adicFiniteDerivedComparison
    {A B : Type*} [Category A] [Category B] [Abelian A] [HasDerivedCategory A]
    (F : CochainComplex A ℤ ⥤ B) (L G : DerivedCategory A ⥤ B)
    (ε : DerivedCategory.Q ⋙ L ⟶ F) (β : DerivedCategory.Q ⋙ G ⟶ F)
    [L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))]
    (hres : ∀ P : CochainComplex A ℤ,
      ∃ (Y : CochainComplex A ℤ) (s : Y ⟶ P),
        QuasiIso s ∧ IsIso (ε.app Y) ∧ IsIso (β.app Y)) :
    ∃ i : G ≅ L, ∀ P : CochainComplex A ℤ,
      i.hom.app (DerivedCategory.Q.obj P) ≫ ε.app P = β.app P := by
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let τ := L.leftDerivedLift ε W G β
  have hτ (K : DerivedCategory A) : IsIso (τ.app K) := by
    let P := DerivedCategory.Q.objPreimage K
    let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
    obtain ⟨Y, s, hs, hε, hβ⟩ := hres P
    let := hs
    let := hε
    let := hβ
    have hfac : τ.app (DerivedCategory.Q.obj Y) ≫ ε.app Y = β.app Y :=
      L.leftDerived_fac_app ε W G β Y
    have : IsIso (τ.app (DerivedCategory.Q.obj Y)) := by
      rw [← isIso_comp_right_iff _ (ε.app Y), hfac]
      infer_instance
    let j : DerivedCategory.Q.obj Y ≅ K := asIso (DerivedCategory.Q.map s) ≪≫ e
    have : IsIso (G.map j.hom ≫ τ.app K) := by
      rw [τ.naturality]
      infer_instance
    exact (isIso_comp_left_iff (G.map j.hom) _).mp this
  let : IsIso τ := (NatTrans.isIso_iff_isIso_app τ).2 hτ
  exact ⟨asIso τ, fun P ↦ L.leftDerived_fac_app ε W G β P⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Derived tensor associativity fixed by the ordinary balancing comparison.
Proof: scalar extension preserves K-flatness by balancing against each acyclic test
complex. Hence on K-flat models all three universal comparisons are invertible.
The displayed composite descends uniquely through localization, and its inverse
is the inverse ordinary balancing composite.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
theorem adicFiniteExtendComp_existsUnique {R S V : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) :
    ∃! e : extend f ⋙ extend g ≅ extend (f ≫ g),
      ∀ P : Cx R, CochainComplex.IsKFlatIndependentCoefficients (J := T) (R := R) P →
        e.hom.app ((Q R).obj P) ≫ (extendComparison (f ≫ g)).app P =
          (extend g).map ((extendComparison f).app P) ≫
            (extendComparison g).app
              (((change f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
            (Q V).map ((NatIso.mapHomologicalComplex (adicFiniteChangeComp f g)
              (ComplexShape.up ℤ)).hom.app P) := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  let := HasDerivedCategory.standard (Mod V)
  let L := extend (f ≫ g)
  let ε := extendComparison (f ≫ g)
  let β : Q R ⋙ (extend f ⋙ extend g) ⟶
      (change (f ≫ g)).mapHomologicalComplex (.up ℤ) ⋙ Q V :=
    Functor.whiskerRight (extendComparison f) (extend g) ≫
      Functor.whiskerLeft ((change f).mapHomologicalComplex (.up ℤ)) (extendComparison g) ≫
        Functor.whiskerRight
          (NatIso.mapHomologicalComplex (adicFiniteChangeComp f g) (.up ℤ)).hom (Q V)
  let : L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Mod R) (.up ℤ)) :=
    (derivedExtension (f ≫ g)).universal
  obtain ⟨i, hi⟩ := adicFiniteDerivedComparison _ L (extend f ⋙ extend g) ε β (fun P ↦ by
    obtain ⟨Y, s, hY, hflat, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
    have hY' := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Y).1 hY
    have hc := (SheafOfModules.changeOfRings_isKFlat_of_flat_terms f Y hY' hflat).1
    have hε := (derivedExtension (f ≫ g)).computation Y hY'
    have hf := (derivedExtension f).computation Y hY'
    have hg := (derivedExtension g).computation
      (((change f).mapHomologicalComplex (.up ℤ)).obj Y) hc
    have hcf : IsIso ((extendComparison f).app Y) := hf
    have hcg : IsIso ((extendComparison g).app
      (((change f).mapHomologicalComplex (.up ℤ)).obj Y)) := hg
    let := hcf
    let := hcg
    refine ⟨Y, s, hs, hε, ?_⟩
    dsimp only [β, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    have h₁ : IsIso ((extend g).map ((extendComparison f).app Y)) := by infer_instance
    have h₂ : IsIso ((extendComparison g).app
      (((change f).mapHomologicalComplex (.up ℤ)).obj Y)) := hg
    have h₃ : IsIso ((Q V).map
      ((NatIso.mapHomologicalComplex (adicFiniteChangeComp f g) (.up ℤ)).hom.app Y)) := by
      infer_instance
    let := h₁
    let := h₂
    let := h₃
    infer_instance)
  refine ⟨i, fun P _ ↦ hi P, ?_⟩
  intro i' hi'
  apply Iso.ext
  apply Localization.natTrans_ext (Q R) (HomologicalComplex.quasiIso (Mod R) (.up ℤ))
  intro P
  obtain ⟨Y, s, hY, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  have := hs
  have : IsIso (ε.app Y) := (derivedExtension (f ≫ g)).computation Y
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Y).1 hY)
  have hy : i'.hom.app ((Q R).obj Y) = i.hom.app ((Q R).obj Y) := by
    apply (cancel_mono (ε.app Y)).1
    exact (hi' Y hY).trans (hi Y).symm
  apply (cancel_epi ((extend f ⋙ extend g).map ((Q R).map s))).1
  rw [i'.hom.naturality, i.hom.naturality, hy]

/-- Canonical derived balancing for a specified composite coefficient map.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteExtendComp {R S V : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) (h : R ⟶ V) (e : h = f ≫ g) :
    extend f ⋙ extend g ≅ extend h :=
  (adicFiniteExtendComp_existsUnique f g).exists.choose ≪≫
    eqToIso (congrArg extend e.symm)

/-- The algebraic lift of the recorded geometric comparison. Its universal specification
retains ring operations, module actions and the natural constant-coefficient isomorphisms.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteComparisonData (X : Scheme.{u}) :=
  Classical.choice (inverseImageData_exists
    (smallModelComparisonPullback.{u, v} X) (smallModelComparisonPushforward.{u, v} X)
    (smallModelProEtaleComparison.{u, v} X))

/-- The ordinary comparison inverse image with its canonical constant-ring map.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteOrdinaryPullback (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    Mod (constant (smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
      Mod (constant (coefficientProEtaleModelTopology.{u, v} X) A) :=
  pull (adicFiniteComparisonData.{u, v} X) (constantMap (adicFiniteComparisonData.{u, v} X) A)

/-- Additivity of the recorded module inverse image.
Source: Stacks Tags 03D2 and 09C2
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
instance adicFiniteOrdinaryPullbackAdditive (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    (adicFiniteOrdinaryPullback.{u, v} X A).Additive :=
  inferInstanceAs ((pull (adicFiniteComparisonData.{u, v} X)
    (constantMap (adicFiniteComparisonData.{u, v} X) A)).Additive)

/-- The derived inverse image of the recorded geometric comparison, with its universal
K-flat computation, on constant coefficients of arbitrary size.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFinitePullback (X : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] :
    ConstantCompletion.D (constant (smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
      ConstantCompletion.D (constant (coefficientProEtaleModelTopology.{u, v} X) A) :=
  (derivedPull (adicFiniteComparisonData.{u, v} X)
    (smallModelComparisonPushforward.{u, v} X) (smallModelProEtaleComparison.{u, v} X)
    (constantMap (adicFiniteComparisonData.{u, v} X) A)).functor

/-- The universally specified comparison on complexes for the derived inverse image.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFinitePullbackComparison (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    Q (constant (smallModelComparisonEtaleTopology.{u, v} X) A) ⋙ adicFinitePullback.{u, v} X A ⟶
      (adicFiniteOrdinaryPullback.{u, v} X A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        Q (constant (coefficientProEtaleModelTopology.{u, v} X) A) :=
  (derivedPull (adicFiniteComparisonData.{u, v} X)
    (smallModelComparisonPushforward.{u, v} X) (smallModelProEtaleComparison.{u, v} X)
    (constantMap (adicFiniteComparisonData.{u, v} X) A)).comparison

/-- The canonical map of constant coefficient sheaves.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteConstantMap {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    {D : Type w} [SmallCategory D] (T : GrothendieckTopology D) :
    constant T R ⟶ constant T S :=
  (constantSheaf T CommRingCat.{w}).map (CommRingCat.ofHom f)

section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048

-- The two routes round a coefficient square have the same right adjoint.
-- Identify their left adjoints, keeping track of tensor insertion throughout.
private noncomputable def adicFiniteRingData
    {C E : Type w} [SmallCategory C] [SmallCategory E]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology E}
    {L : Sheaf JC (Type w) ⥤ Sheaf JD (Type w)}
    (V : Sheaf JD (Type w) ⥤ Sheaf JC (Type w)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (F : InverseImageData L)
    {R : Sheaf JC CommRingCat.{w}} {S : Sheaf JD CommRingCat.{w}}
    (c : F.rings.obj R ⟶ S) :
    RingedToposMorphism.RingData (siteModuleRings S) (siteModuleRings R) := by
  let AI := F.algebra R
  exact
    { inverse := L
      direct := V
      adj := adj
      leftExact := inferInstance
      ringMap := AI.ringUnderlying.hom ≫ (sheafCompose JD (CategoryTheory.forget CommRingCat)).map c
      ring_zero := by
        intro T z hz U t
        change (c.hom.app U).hom
          (AI.ringUnderlying.hom.hom.app U ((L.map z).hom.app U t)) = 0
        exact (congrArg (fun a ↦ (c.hom.app U).hom a)
          (AI.ringZero T z hz U t)).trans (map_zero _)
      ring_one := by
        intro T z hz U t
        change (c.hom.app U).hom
          (AI.ringUnderlying.hom.hom.app U ((L.map z).hom.app U t)) = 1
        exact (congrArg (fun a ↦ (c.hom.app U).hom a)
          (AI.ringOne T z hz U t)).trans (map_one _)
      ring_add := by
        intro T x y z hz U t
        change (c.hom.app U).hom
          (AI.ringUnderlying.hom.hom.app U ((L.map z).hom.app U t)) =
          (c.hom.app U).hom
              (AI.ringUnderlying.hom.hom.app U ((L.map x).hom.app U t)) +
            (c.hom.app U).hom
              (AI.ringUnderlying.hom.hom.app U ((L.map y).hom.app U t))
        exact (congrArg (fun a ↦ (c.hom.app U).hom a)
          (AI.ringAdd T x y z hz U t)).trans (map_add _ _ _)
      ring_mul := by
        intro T x y z hz U t
        change (c.hom.app U).hom
          (AI.ringUnderlying.hom.hom.app U ((L.map z).hom.app U t)) =
          (c.hom.app U).hom
              (AI.ringUnderlying.hom.hom.app U ((L.map x).hom.app U t)) *
            (c.hom.app U).hom
              (AI.ringUnderlying.hom.hom.app U ((L.map y).hom.app U t))
        exact (congrArg (fun a ↦ (c.hom.app U).hom a)
          (AI.ringMul T x y z hz U t)).trans (map_mul _ _ _) }

private theorem adicFiniteTensorUnit_eq
    {C : Type w} [SmallCategory C] {JC : GrothendieckTopology C}
    {R S : Sheaf JC CommRingCat.{w}} (c : R ⟶ S) (M : Mod R) :
    SheafOfModules.tensorUnit c M = insertion c M := by
  ext U m
  exact (SheafOfModules.tensorUnit_apply c M U m).trans
    ((insertion_existsUnique c M).exists.choose_spec U m).symm

private theorem adicFiniteAdjunction_underlying
    {C : Type w} [SmallCategory C] {JC : GrothendieckTopology C}
    {R S : Sheaf JC CommRingCat.{w}} (f : R ⟶ S)
    (M : Mod R) (N : Mod S) (a : (change f).obj M ⟶ N) :
    (underlying R).map ((adicFiniteAdjunction f).homEquiv M N a) =
      insertion f M ≫ (underlying S).map a := by
  rw [adicFiniteAdjunction_homEquiv]
  ext U m
  change (adicFiniteHomEquiv f M N a).val.app U m =
    a.val.app U ((insertion f M).hom.app U m)
  rw [show (insertion f M).hom.app U m = tensorSection f M U 1 m from
    (insertion_existsUnique f M).exists.choose_spec U m]
  exact adicFiniteHomEquiv_apply f M N a U m

private theorem adicFiniteInsertion_apply
    {C : Type w} [SmallCategory C] {JC : GrothendieckTopology C}
    {R S : Sheaf JC CommRingCat.{w}} (f : R ⟶ S) (M : Mod R)
    (U : Cᵒᵖ) (m : M.val.obj U) :
    (insertion f M).hom.app U m = tensorSection f M U 1 m :=
  (insertion_existsUnique f M).exists.choose_spec U m

private theorem adicFiniteChangeComp_insertion
    {C : Type w} [SmallCategory C] {JC : GrothendieckTopology C}
    {R S V : Sheaf JC CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ V) (M : Mod R) :
    insertion f M ≫ insertion g ((change f).obj M) ≫
      (underlying V).map ((adicFiniteChangeComp f g).hom.app M) = insertion (f ≫ g) M := by
  ext U m
  change ((adicFiniteChangeComp f g).hom.app M).val.app U
      ((insertion g _).hom.app U ((insertion f _).hom.app U m)) =
    (insertion (f ≫ g) _).hom.app U m
  rw [adicFiniteInsertion_apply, adicFiniteInsertion_apply, adicFiniteInsertion_apply]
  simpa only [map_one, mul_one] using!
    (adicFiniteChangeComp_existsUnique f g).exists.choose_spec M U 1 1 m

private theorem adicFinitePullScalarSquare
    {C E : Type w} [SmallCategory C] [SmallCategory E]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology E}
    {L : Sheaf JC (Type w) ⥤ Sheaf JD (Type w)}
    (V : Sheaf JD (Type w) ⥤ Sheaf JC (Type w)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (F : InverseImageData L)
    {R S : Sheaf JC CommRingCat.{w}} {A B : Sheaf JD CommRingCat.{w}}
    (f : R ⟶ S) (g : A ⟶ B) (cA : F.rings.obj R ⟶ A) (cB : F.rings.obj S ⟶ B)
    (hsq : F.rings.map f ≫ cB = cA ≫ g) :
    ∃! e : pull F cA ⋙ change g ≅ change f ⋙ pull F cB,
      ∀ M : Mod R,
        L.map (insertion f M) ≫ pullInsertion F cB ((change f).obj M) =
          pullInsertion F cA M ≫ insertion g ((pull F cA).obj M) ≫
            (underlying B).map (e.hom.app M) := by
  let dB := adicFiniteRingData V adj F cB
  let d₀ := adicFiniteRingData V adj F (cA ≫ g)
  have hs : L.map ((sheafCompose JC (CategoryTheory.forget CommRingCat)).map f) ≫ dB.ringMap =
      d₀.ringMap := by
    change L.map ((sheafCompose JC (CategoryTheory.forget CommRingCat)).map f) ≫
      (F.algebra S).ringUnderlying.hom ≫
        (sheafCompose JD (CategoryTheory.forget CommRingCat)).map cB = _
    rw [← Category.assoc, F.ring_naturality f, Category.assoc,
      ← Functor.map_comp, hsq]
    rfl
  obtain ⟨md⟩ := SheafOfModules.ringData_inducedModules B S dB
  let : md.modules.Additive := md.additive
  let md₀ : d₀.Modules :=
    { modules := md.modules ⋙ res f
      additive := inferInstance
      underlying := md.underlying
      module_linear := by
        intro N T a x y z hz U t
        have h := md.module_linear N T
          (a ≫ (sheafCompose JC (CategoryTheory.forget CommRingCat)).map f) x y z hz U t
        change _ = (show N.val.obj U from
          ((L.map (a ≫ (sheafCompose JC (CategoryTheory.forget CommRingCat)).map f)) ≫
            dB.ringMap).hom.app U t • _) + _ at h
        rw [Functor.map_comp, Category.assoc, hs] at h
        exact h }
  let b := dB.withModules md
  let b₀ := d₀.withModules md₀
  have hcB : (sheafCompose JD (CategoryTheory.forget CommRingCat)).map cB =
      (F.algebra S).ringUnderlying.inv ≫ b.ringMap := by
    change _ = _ ≫ ((F.algebra S).ringUnderlying.hom ≫ _)
    rw [Iso.inv_hom_id_assoc]
  have hc₀ : (sheafCompose JD (CategoryTheory.forget CommRingCat)).map (cA ≫ g) =
      (F.algebra R).ringUnderlying.inv ≫ b₀.ringMap := by
    change _ = _ ≫ ((F.algebra R).ringUnderlying.hom ≫ _)
    rw [Iso.inv_hom_id_assoc]
  obtain ⟨aB, haB⟩ := supplied_module_adjunction b (F.rings.obj S) (F.algebra S) cB hcB
  obtain ⟨a₀, ha₀⟩ := supplied_module_adjunction b₀ (F.rings.obj R)
    (F.algebra R) (cA ≫ g) hc₀
  have hB (M : Mod S) (N : Mod B) (k : (pull F cB).obj M ⟶ N) :
      (underlying S).map (aB.homEquiv M N k) ≫ md.underlying.hom.app N =
        adj.homEquiv _ _ (pullInsertion F cB M ≫ (underlying B).map k) := by
    simpa only [pullInsertion, adicFiniteTensorUnit_eq, Category.assoc] using! haB M N k
  have h₀ (M : Mod R) (N : Mod B) (k : (pull F (cA ≫ g)).obj M ⟶ N) :
      (underlying R).map (a₀.homEquiv M N k) ≫ md.underlying.hom.app N =
        adj.homEquiv _ _ (pullInsertion F (cA ≫ g) M ≫ (underlying B).map k) := by
    simpa only [pullInsertion, adicFiniteTensorUnit_eq, Category.assoc] using! ha₀ M N k
  let a : change f ⋙ pull F cB ⊣ b₀.modules := (adicFiniteAdjunction f).comp aB
  have ha (M : Mod R) (N : Mod B) (k : (change f ⋙ pull F cB).obj M ⟶ N) :
      (underlying R).map (a.homEquiv M N k) ≫ md.underlying.hom.app N =
        adj.homEquiv _ _ (L.map (insertion f M) ≫
          pullInsertion F cB ((change f).obj M) ≫ (underlying B).map k) := by
    change (underlying R).map ((adicFiniteAdjunction f).homEquiv M _
      (aB.homEquiv _ N k)) ≫ md.underlying.hom.app N = _
    rw [adicFiniteAdjunction_underlying, Category.assoc, hB]
    exact (adj.homEquiv_naturality_left _ _).symm
  let i : pull F (cA ≫ g) ≅ change f ⋙ pull F cB := a₀.leftAdjointUniq a
  have hi (M : Mod R) :
      pullInsertion F (cA ≫ g) M ≫ (underlying B).map (i.hom.app M) =
        L.map (insertion f M) ≫ pullInsertion F cB ((change f).obj M) := by
    apply (adj.homEquiv _ _).injective
    rw [← h₀]
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app a₀ a M
    change a₀.homEquiv M _ (i.hom.app M) = _ at h
    rw [h, ← Adjunction.homEquiv_id]
    simpa only [Functor.map_id, Category.comp_id] using! ha M _ (𝟙 _)
  let j : pull F cA ⋙ change g ≅ pull F (cA ≫ g) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (F.algebra R).modules (adicFiniteChangeComp cA g)
  have hj (M : Mod R) :
      pullInsertion F cA M ≫ insertion g ((pull F cA).obj M) ≫
        (underlying B).map (j.hom.app M) = pullInsertion F (cA ≫ g) M := by
    change (F.algebra R).moduleUnderlying.inv.app M ≫
        insertion cA ((F.algebra R).modules.obj M) ≫
        insertion g ((change cA).obj ((F.algebra R).modules.obj M)) ≫
        (underlying B).map ((adicFiniteChangeComp cA g).hom.app
          ((F.algebra R).modules.obj M)) =
      (F.algebra R).moduleUnderlying.inv.app M ≫
        insertion (cA ≫ g) ((F.algebra R).modules.obj M)
    exact congrArg ((F.algebra R).moduleUnderlying.inv.app M ≫ ·)
      (adicFiniteChangeComp_insertion cA g ((F.algebra R).modules.obj M))
  let e := j ≪≫ i
  have he (M : Mod R) :
      L.map (insertion f M) ≫ pullInsertion F cB ((change f).obj M) =
        pullInsertion F cA M ≫ insertion g ((pull F cA).obj M) ≫
          (underlying B).map (e.hom.app M) := by
    rw [← hi M, ← hj M]
    change _ = _ ≫ _ ≫ (underlying B).map (j.hom.app M ≫ i.hom.app M)
    rw [Functor.map_comp, Category.assoc, Category.assoc]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (cancel_epi (j.inv.app M)).1
  apply (a₀.homEquiv M _).injective
  apply (underlying R).map_injective
  apply (cancel_mono (md.underlying.hom.app _)).1
  rw [h₀, h₀]
  congr 1
  have hji : pullInsertion F (cA ≫ g) M ≫ (underlying B).map (j.inv.app M) =
      pullInsertion F cA M ≫ insertion g ((pull F cA).obj M) := by
    rw [← hj M]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc, hji]
  exact (he' M).symm.trans (he M)

end

/-- Ordinary comparison commutes with scalar extension, normalized by tensor insertion.
Proof: inverse image preserves the tensor coequalizer. Both sides send a scalar and
a module section to the same sheafified pure tensor. The displayed insertion equation
determines the isomorphism on local generators; the inverse balancing map gives its inverse.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
theorem adicFiniteOrdinaryComparison_existsUnique (X : Scheme.{u})
    {A B : Type (max v (u + 1))} [CommRing A] [CommRing B] (f : A →+* B) :
    ∃! e : adicFiniteOrdinaryPullback.{u, v} X A ⋙
        change (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)) ≅
      change (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) ⋙
        adicFiniteOrdinaryPullback.{u, v} X B,
      ∀ M : Mod (constant (smallModelComparisonEtaleTopology.{u, v} X) A),
        (smallModelComparisonPullback.{u, v} X).map
            (insertion (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) M) ≫
          pullInsertion (adicFiniteComparisonData.{u, v} X)
            (constantMap (adicFiniteComparisonData.{u, v} X) B)
            ((change (adicFiniteConstantMap f
              (smallModelComparisonEtaleTopology.{u, v} X))).obj M) =
        pullInsertion (adicFiniteComparisonData.{u, v} X)
            (constantMap (adicFiniteComparisonData.{u, v} X) A) M ≫
          insertion (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X))
            ((adicFiniteOrdinaryPullback.{u, v} X A).obj M) ≫
          (underlying (constant (coefficientProEtaleModelTopology.{u, v} X) B)).map
            (e.hom.app M) := by
  let : PreservesFiniteLimits (smallModelComparisonPullback.{u, v} X) :=
    smallModelComparisonPullback_preservesFiniteLimits.{u, v} X
  exact adicFinitePullScalarSquare
    (smallModelComparisonPushforward.{u, v} X) (smallModelProEtaleComparison.{u, v} X)
    (adicFiniteComparisonData.{u, v} X)
    (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X))
    (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X))
    (constantMap (adicFiniteComparisonData.{u, v} X) A)
    (constantMap (adicFiniteComparisonData.{u, v} X) B)
    ((adicFiniteComparisonData.{u, v} X).constants.hom.naturality (CommRingCat.ofHom f))

/-- The ordinary scalar/pullback comparison with its insertion normalization.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteOrdinaryComparison (X : Scheme.{u})
    {A B : Type (max v (u + 1))} [CommRing A] [CommRing B] (f : A →+* B) :
    adicFiniteOrdinaryPullback.{u, v} X A ⋙
      change (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)) ≅
    change (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) ⋙
      adicFiniteOrdinaryPullback.{u, v} X B :=
  (adicFiniteOrdinaryComparison_existsUnique.{u, v} X f).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adicFiniteTwoDerivedComparisons
    {A B : Type*} [Category A] [Category B] [Abelian A] [HasDerivedCategory A]
    (F₁ F₂ H : CochainComplex A ℤ ⥤ B) (L G₁ G₂ : DerivedCategory A ⥤ B)
    (ε : DerivedCategory.Q ⋙ L ⟶ H)
    (α₁ : DerivedCategory.Q ⋙ G₁ ⟶ F₁) (α₂ : DerivedCategory.Q ⋙ G₂ ⟶ F₂)
    (j : F₁ ≅ H) (o : F₁ ≅ F₂)
    [L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))]
    (P : CochainComplex A ℤ → Prop)
    (hres : ∀ X : CochainComplex A ℤ,
      ∃ (Y : CochainComplex A ℤ) (s : Y ⟶ X), P Y ∧ QuasiIso s)
    (hc : ∀ X, P X → IsIso (ε.app X) ∧ IsIso (α₁.app X) ∧ IsIso (α₂.app X)) :
    ∃! e : G₁ ≅ G₂, ∀ X, P X →
      e.hom.app (DerivedCategory.Q.obj X) ≫ α₂.app X = α₁.app X ≫ o.hom.app X := by
  let β₁ := α₁ ≫ j.hom
  let β₂ := α₂ ≫ o.inv ≫ j.hom
  obtain ⟨i₁, hi₁⟩ := adicFiniteDerivedComparison H L G₁ ε β₁ (fun X ↦ by
    obtain ⟨Y, s, hY, hs⟩ := hres X
    obtain ⟨hε, h₁, h₂⟩ := hc Y hY
    let := h₁
    refine ⟨Y, s, hs, hε, ?_⟩
    change IsIso (α₁.app Y ≫ j.hom.app Y)
    infer_instance)
  obtain ⟨i₂, hi₂⟩ := adicFiniteDerivedComparison H L G₂ ε β₂ (fun X ↦ by
    obtain ⟨Y, s, hY, hs⟩ := hres X
    obtain ⟨hε, h₁, h₂⟩ := hc Y hY
    let := h₂
    refine ⟨Y, s, hs, hε, ?_⟩
    change IsIso (α₂.app Y ≫ o.inv.app Y ≫ j.hom.app Y)
    infer_instance)
  let e := i₁ ≪≫ i₂.symm
  have he (X : CochainComplex A ℤ) :
      e.hom.app (DerivedCategory.Q.obj X) ≫ α₂.app X = α₁.app X ≫ o.hom.app X := by
    apply (cancel_mono (o.inv.app X ≫ j.hom.app X)).1
    have h : e.hom.app (DerivedCategory.Q.obj X) ≫ β₂.app X = β₁.app X := by
      rw [← hi₂ X]
      change (i₁.hom.app _ ≫ i₂.inv.app _) ≫ i₂.hom.app _ ≫ ε.app X = _
      rw [Category.assoc, Iso.inv_hom_id_app_assoc]
      exact hi₁ X
    simpa only [β₁, β₂, NatTrans.comp_app, Category.assoc,
      Iso.hom_inv_id_app_assoc] using h
  refine ⟨e, fun X _ ↦ he X, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro X
  obtain ⟨Y, s, hY, hs⟩ := hres X
  let := hs
  have hy : e'.hom.app (DerivedCategory.Q.obj Y) = e.hom.app (DerivedCategory.Q.obj Y) := by
    have := (hc Y hY).2.2
    apply (cancel_mono (α₂.app Y)).1
    exact (he' Y hY).trans (he Y).symm
  apply (cancel_epi (G₁.map (DerivedCategory.Q.map s))).1
  rw [e'.hom.naturality, e.hom.naturality, hy]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adicFinitePullChangeComparison
    {E : Type w} [SmallCategory E] {TE : GrothendieckTopology E}
    {L : Sheaf T (Type w) ⥤ Sheaf TE (Type w)} (F : InverseImageData L)
    (U : Sheaf TE (Type w) ⥤ Sheaf T (Type w)) (adj : L ⊣ U)
    [PreservesFiniteLimits L] {R S : Sheaf T CommRingCat.{w}}
    {V W : Sheaf TE CommRingCat.{w}} (f : R ⟶ S) (g : V ⟶ W)
    (cA : F.rings.obj R ⟶ V) (cB : F.rings.obj S ⟶ W)
    (pa : DerivedPull F cA) (pb : DerivedPull F cB) (d : DerivedPull F (cA ≫ g))
    (o : pull F cA ⋙ change g ≅ change f ⋙ pull F cB) :
    ∃! e : pa.functor ⋙ extend g ≅ extend f ⋙ pb.functor,
      ∀ P : Cx R, P.IsKFlatIndependentCoefficients →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        e.hom.app ((Q R).obj P) ≫ pb.functor.map ((extendComparison f).app P) ≫
          pb.comparison.app (((change f).mapHomologicalComplex (.up ℤ)).obj P) =
        (extend g).map (pa.comparison.app P) ≫
          (extendComparison g).app (((pull F cA).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (Q W).map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P) := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  let := HasDerivedCategory.standard (Mod V)
  let := HasDerivedCategory.standard (Mod W)
  let j : pull F cA ⋙ change g ≅ pull F (cA ≫ g) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (adicFiniteChangeComp cA g)
  let jC : (pull F cA ⋙ change g).mapHomologicalComplex (.up ℤ) ⋙ Q W ≅
      (pull F (cA ≫ g)).mapHomologicalComplex (.up ℤ) ⋙ Q W :=
    NatIso.ofComponents (fun P ↦
      (Q W).mapIso ((NatIso.mapHomologicalComplex j (.up ℤ)).app P))
      (fun a ↦ (Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex j (.up ℤ)) (Q W)).hom.naturality a)
  let oC : (pull F cA ⋙ change g).mapHomologicalComplex (.up ℤ) ⋙ Q W ≅
      (change f ⋙ pull F cB).mapHomologicalComplex (.up ℤ) ⋙ Q W :=
    NatIso.ofComponents (fun P ↦
      (Q W).mapIso ((NatIso.mapHomologicalComplex o (.up ℤ)).app P))
      (fun a ↦ (Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex o (.up ℤ)) (Q W)).hom.naturality a)
  let β₁ : Q R ⋙ (pa.functor ⋙ extend g) ⟶
      (pull F cA ⋙ change g).mapHomologicalComplex (.up ℤ) ⋙ Q W :=
    { app := fun P ↦ (extend g).map (pa.comparison.app P) ≫
        (extendComparison g).app (((pull F cA).mapHomologicalComplex (.up ℤ)).obj P)
      naturality := by
        intro P P' a
        exact (Functor.whiskerRight pa.comparison (extend g) ≫
          Functor.whiskerLeft ((pull F cA).mapHomologicalComplex (.up ℤ))
            (extendComparison g)).naturality a }
  let β₂ : Q R ⋙ (extend f ⋙ pb.functor) ⟶
      (change f ⋙ pull F cB).mapHomologicalComplex (.up ℤ) ⋙ Q W :=
    { app := fun P ↦ pb.functor.map ((extendComparison f).app P) ≫
        pb.comparison.app (((change f).mapHomologicalComplex (.up ℤ)).obj P)
      naturality := by
        intro P P' a
        exact (Functor.whiskerRight (extendComparison f) pb.functor ≫
          Functor.whiskerLeft ((change f).mapHomologicalComplex (.up ℤ))
            pb.comparison).naturality a }
  let : d.functor.IsLeftDerivedFunctor d.comparison
      (HomologicalComplex.quasiIso
        (Mod R) (.up ℤ)) :=
    d.universal
  have hcomp (P : Cx R)
      (hP : P.IsKFlatIndependentCoefficients)
      (hf : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) :
      IsIso (d.comparison.app P) ∧ IsIso (β₁.app P) ∧ IsIso (β₂.app P) := by
    have hk := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP
    have hpA : IsIso ((pa.comparison).app P) :=
      pa.computation P hk hf
    have hr : IsIso ((extendComparison f).app P) := (derivedExtension f).computation P hk
    have hchange := SheafOfModules.changeOfRings_isKFlat_of_flat_terms f P hk hf
    have hpB : IsIso ((pb.comparison).app
        (((change f).mapHomologicalComplex (.up ℤ)).obj P)) :=
      pb.computation _
          hchange.1 hchange.2
    have hpull := SheafOfModules.isKFlat_ringedToposPullback
      L U
      adj (F.algebra _) cA
      (pull F cA) (fun _ ↦ rfl)
      (fun a ↦ by
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl) P hP (fun q ↦ by
        exact ObjectProperty.prop_of_iso (exactFunctor _ _)
          (SheafOfModules.siteSheafTensorRightIso _ (P.X q)).symm (hf q))
    have hs : IsIso ((extendComparison g).app
        (((pull F cA).mapHomologicalComplex (.up ℤ)).obj P)) :=
      (derivedExtension g).computation _
        ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp hpull.1)
    let := hpA
    let := hr
    let := hpB
    let := hs
    refine ⟨d.computation P hk hf, ?_, ?_⟩
    · change IsIso ((extend g).map ((pa.comparison).app P) ≫
        (extendComparison g).app _)
      infer_instance
    · change IsIso ((pb.functor).map ((extendComparison f).app P) ≫
        (pb.comparison).app _)
      infer_instance
  obtain ⟨e, he, hu⟩ := adicFiniteTwoDerivedComparisons _ _ _ d.functor
    (pa.functor ⋙ extend g) (extend f ⋙ pb.functor) d.comparison β₁ β₂ jC oC
    (fun P ↦ P.IsKFlatIndependentCoefficients ∧ ∀ q : ℤ, SheafOfModules.IsFlat (P.X q))
    (fun P ↦ by
      obtain ⟨Y, q, hY, hf, hq, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
      exact ⟨Y, q, ⟨hY, hf⟩, hq⟩)
    (fun P hP ↦ hcomp P hP.1 hP.2)
  refine ⟨e, ?_, ?_⟩
  · intro P hP hf
    have h := he P ⟨hP, hf⟩
    change e.hom.app ((Q R).obj P) ≫ pb.functor.map ((extendComparison f).app P) ≫
        pb.comparison.app (((change f).mapHomologicalComplex (.up ℤ)).obj P) =
      ((extend g).map (pa.comparison.app P) ≫
        (extendComparison g).app (((pull F cA).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (Q W).map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P) at h
    exact h.trans (Category.assoc _ _ _)
  · intro e' he'
    apply hu e'
    rintro P ⟨hP, hf⟩
    change e'.hom.app ((Q R).obj P) ≫ pb.functor.map ((extendComparison f).app P) ≫
        pb.comparison.app (((change f).mapHomologicalComplex (.up ℤ)).obj P) =
      ((extend g).map (pa.comparison.app P) ≫
        (extendComparison g).app (((pull F cA).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (Q W).map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P)
    exact (he' P hP hf).trans (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The derived scalar/pullback comparison is specified on flat-term K-flat models.
Proof: exact geometric inverse image preserves flat terms and K-flatness. Scalar
extension preserves K-flatness. All four universal comparisons in the displayed
square are therefore invertible. Descend the uniquely normalized ordinary comparison
through K-flat localization; the ordinary inverse descends too, and uniqueness follows
from the universal localization property.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
theorem adicFiniteComparison_existsUnique (X : Scheme.{u})
    {A B : Type (max v (u + 1))} [CommRing A] [CommRing B] (f : A →+* B) :
    ∃! e : adicFinitePullback.{u, v} X A ⋙
        extend (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)) ≅
      extend (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) ⋙
        adicFinitePullback.{u, v} X B,
      ∀ P : Cx (constant (smallModelComparisonEtaleTopology.{u, v} X) A),
        CochainComplex.IsKFlatIndependentCoefficients
          (R := constant (smallModelComparisonEtaleTopology.{u, v} X) A) P →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        e.hom.app ((Q _).obj P) ≫
          (adicFinitePullback.{u, v} X B).map
            ((extendComparison (adicFiniteConstantMap f
              (smallModelComparisonEtaleTopology.{u, v} X))).app P) ≫
          (adicFinitePullbackComparison.{u, v} X B).app
            (((change (adicFiniteConstantMap f
              (smallModelComparisonEtaleTopology.{u, v} X))).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P) =
        (extend (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X))).map
            ((adicFinitePullbackComparison.{u, v} X A).app P) ≫
          (extendComparison (adicFiniteConstantMap f
            (coefficientProEtaleModelTopology.{u, v} X))).app
            (((adicFiniteOrdinaryPullback.{u, v} X A).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          (Q _).map ((NatIso.mapHomologicalComplex (adicFiniteOrdinaryComparison.{u, v} X f)
            (ComplexShape.up ℤ)).hom.app P) := by
  let : PreservesFiniteLimits (smallModelComparisonPullback.{u, v} X) :=
    smallModelComparisonPullback_preservesFiniteLimits.{u, v} X
  exact adicFinitePullChangeComparison
    (adicFiniteComparisonData.{u, v} X) (smallModelComparisonPushforward.{u, v} X)
    (smallModelProEtaleComparison.{u, v} X)
    (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X))
    (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X))
    (constantMap (adicFiniteComparisonData.{u, v} X) A)
    (constantMap (adicFiniteComparisonData.{u, v} X) B)
    (derivedPull (adicFiniteComparisonData.{u, v} X)
      (smallModelComparisonPushforward.{u, v} X) (smallModelProEtaleComparison.{u, v} X)
      (constantMap (adicFiniteComparisonData.{u, v} X) A))
    (derivedPull (adicFiniteComparisonData.{u, v} X)
      (smallModelComparisonPushforward.{u, v} X) (smallModelProEtaleComparison.{u, v} X)
      (constantMap (adicFiniteComparisonData.{u, v} X) B))
    (derivedPull (adicFiniteComparisonData.{u, v} X)
      (smallModelComparisonPushforward.{u, v} X) (smallModelProEtaleComparison.{u, v} X)
      (constantMap (adicFiniteComparisonData.{u, v} X) A ≫
        adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)))
    (adicFiniteOrdinaryComparison.{u, v} X f)

/-- The canonical derived scalar/pullback balancing comparison.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteComparison (X : Scheme.{u})
    {A B : Type (max v (u + 1))} [CommRing A] [CommRing B] (f : A →+* B) :
    adicFinitePullback.{u, v} X A ⋙
      extend (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)) ≅
    extend (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) ⋙
      adicFinitePullback.{u, v} X B :=
  (adicFiniteComparison_existsUnique.{u, v} X f).exists.choose

/-- The existing positive-power quotient, with no change of coefficient ring.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
abbrev adicFiniteCoeff {A : Type w} [CommRing A] (J : Ideal A) (n : ℕ) :=
  A ⧸ J ^ (n + 1)

/-- The quotient homomorphism at positive exponent n+1.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteQuotient {A : Type w} [CommRing A] (J : Ideal A) (n : ℕ) :
    A →+* adicFiniteCoeff J n := Ideal.Quotient.mk _

/-- The canonical quotient factor homomorphism.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteFactor {A : Type w} [CommRing A] (J : Ideal A)
    {m n : ℕ} (h : n ≤ m) : adicFiniteCoeff J m →+* adicFiniteCoeff J n :=
  Ideal.Quotient.factorPow J (Nat.add_le_add_right h 1)

/-- The quotient-factor identity is the existing ideal quotient identity.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteQuotientComp {A : Type w} [CommRing A] (J : Ideal A)
    {m n : ℕ} (h : n ≤ m) :
    adicFiniteQuotient J n = (adicFiniteFactor J h).comp (adicFiniteQuotient J m) :=
  (Ideal.Quotient.factor_comp_mk
    (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))).symm

/-- The quotient-factor cocycle is the existing factor composition identity.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteFactorComp {A : Type w} [CommRing A] (J : Ideal A)
    {r m n : ℕ} (hnm : n ≤ m) (hmr : m ≤ r) :
    adicFiniteFactor J (hnm.trans hmr) =
      (adicFiniteFactor J hnm).comp (adicFiniteFactor J hmr) :=
  (Ideal.Quotient.factor_comp
    (Ideal.pow_le_pow_right (Nat.add_le_add_right hmr 1))
    (Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1))).symm

/-- Scalar extension in the existing standard localization of a small ringed site.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteExtension {A B : Type w} [CommRing A] [CommRing B]
    {D : Type w} [SmallCategory D] (T : GrothendieckTopology D) (f : A →+* B) :
    ConstantCompletion.D (constant T A) ⥤ ConstantCompletion.D (constant T B) :=
  extend (adicFiniteConstantMap f T)

/-- Functoriality of the existing constant-sheaf construction on ring homomorphisms.
Source: Stacks Tags 06YY and 09C2
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteConstantComp {A B C : Type w} [CommRing A] [CommRing B] [CommRing C]
    {D : Type w} [SmallCategory D] (T : GrothendieckTopology D)
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (e : h = g.comp f) :
    adicFiniteConstantMap h T = adicFiniteConstantMap f T ≫ adicFiniteConstantMap g T :=
  (congrArg (fun k ↦ adicFiniteConstantMap k T) e).trans
    ((constantSheaf T CommRingCat.{w}).map_comp
      (CommRingCat.ofHom f) (CommRingCat.ofHom g))

/-- Canonical scalar reassociation for a specified equality of constant ring maps.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteExtensionComp {A B C : Type w} [CommRing A] [CommRing B] [CommRing C]
    {D : Type w} [SmallCategory D] (T : GrothendieckTopology D)
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (e : h = g.comp f) :
    adicFiniteExtension T f ⋙ adicFiniteExtension T g ≅ adicFiniteExtension T h :=
  adicFiniteExtendComp (adicFiniteConstantMap f T) (adicFiniteConstantMap g T)
    (adicFiniteConstantMap h T)
    (adicFiniteConstantComp T f g h e)

/-- The standard derived category of the constant pro-etale coefficient ring on the
equivalent coefficient-sized site.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
abbrev adicFiniteAmbient (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :=
  ConstantCompletion.D (constant (coefficientProEtaleModelTopology.{u, v} X) A)

/-- Local derived completeness for the kernel of the actual residue quotient.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteComplete (X : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A]
    (J : Ideal A) (N : adicFiniteAmbient.{u, v} X A) : Prop :=
  IsComplete (quotient (coefficientProEtaleModelTopology.{u, v} X) A J 0) N

/-- The existing etale derived category over a positive quotient on the equivalent model.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
abbrev adicFiniteEtale (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (n : ℕ) :=
  ConstantCompletion.D
    (finite (smallModelComparisonEtaleTopology.{u, v} X) A J n)

/-- Derived tensor with the actual positive quotient, using the universal scalar extension.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteReduction (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (N : adicFiniteAmbient.{u, v} X A) (n : ℕ) :
    adicFiniteAmbient.{u, v} X (adicFiniteCoeff J n) :=
  (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X)
    (adicFiniteQuotient J n)).obj N

/-- Canonical balancing after a repeated quotient reduction.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteRho (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (N : adicFiniteAmbient.{u, v} X A) {m n : ℕ} (h : n ≤ m) :
    (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X)
      (adicFiniteFactor J h)).obj (adicFiniteReduction.{u, v} X J N m) ≅
        adicFiniteReduction.{u, v} X J N n :=
  (adicFiniteExtensionComp (coefficientProEtaleModelTopology.{u, v} X)
    (adicFiniteQuotient J m) (adicFiniteFactor J h) (adicFiniteQuotient J n)
    (adicFiniteQuotientComp J h)).app N

/-- The quotient reduction with coefficients restricted to the original ring.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteUnderlying (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (N : adicFiniteAmbient.{u, v} X A) (n : ℕ) : adicFiniteAmbient.{u, v} X A :=
  (dres (quotient (coefficientProEtaleModelTopology.{u, v} X) A J n)).obj
    (adicFiniteReduction.{u, v} X J N n)

/-- The actual quotient transition, from the normalized derived tensor unit, balancing
and exact restriction composition. No transition map is supplied as a parameter.
Source: Stacks Tags 06YY, 09C2 and 09AL
(blueprint: lem-sfb-adic-constructible-finite-reductions). -/
def adicFiniteTransition (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (N : adicFiniteAmbient.{u, v} X A) (n : ℕ) :
    adicFiniteUnderlying.{u, v} X J N (n + 1) ⟶ adicFiniteUnderlying.{u, v} X J N n :=
  let T := coefficientProEtaleModelTopology.{u, v} X
  let f := quotient T A J (n + 1)
  let g := adicFiniteConstantMap (adicFiniteFactor J (Nat.le_succ n)) T
  (dres f).map ((adicFiniteUnit g).app (adicFiniteReduction.{u, v} X J N (n + 1)) ≫
      (dres g).map (adicFiniteRho.{u, v} X J N (Nat.le_succ n)).hom) ≫
    (adicFiniteDresComp f g).hom.app (adicFiniteReduction.{u, v} X J N n) ≫
    (eqToIso (congrArg (fun k ↦ (dres k).obj (adicFiniteReduction.{u, v} X J N n))
      (adicFiniteConstantComp T (adicFiniteQuotient J (n + 1))
        (adicFiniteFactor J (Nat.le_succ n)) (adicFiniteQuotient J n)
        (adicFiniteQuotientComp J (Nat.le_succ n))).symm)).hom

end AlgebraicGeometry.Scheme
```

## New

The original construction prefix is reexported from AdicFiniteReductionData. The original
module imports that companion publicly and the four argument-step modules privately.
No source-library module changes. All original public names, universes, visibility and
attributes stay. The assigned theorem's signature stays verbatim.

The four data/instance bodies below provide explicit finite-limits proofs or use the
already proved additive interface. Proof irrelevance makes the constructions
definitionally equal to the originals. The normalized units, scalar reassociations and
geometric comparisons remain the same uniquely specified constructions.

The proof refactor uses the proved private resolving_module_square_iso,
resolving_comparison_iso, resolving_nat_ext, change_preserves_kFlat_quasiIso,
pull_flat_kFlat and change_flat_kFlat interfaces of ConstantCompletionEquivalence through
a private import all. The private ordinary-functor comparison helpers check termwise
composition conversions before specialization. The unit derives the tensor/restriction
adjunction and transports it along the unique left-derived isomorphism. A proved private
wrapper exposes the latter's computation formula while keeping its construction folded.
Restriction composition uses the existing resCompIso and its section formula. Ordinary
adjunctions, adjunction uniqueness, and the tensor/K-flat definitions stay locally folded
where the proved APIs suffice. A private structure packages the native K-flat property
and termwise flatness. Its proved resolution, scalar preservation, geometric preservation
and computation APIs are used in the two derived comparison proofs; the computation
API also supplies unit uniqueness. Direct applications of those APIs recover the scalar-composition normalization. A
proved generic helper reverses the comparison equation and converts its resolving-class
guard before specializing to native sheaf categories. Private construction helpers use
no_expose; public exposure and visibility are preserved. The scalar Hom equivalence projects from the named adjunction; pointwise
lemmas keep it folded. A private constructed restriction helper separates ring-linearity
from ordinary adjoint uniqueness. The redundant
private two-comparison helper and its unused common derived-pullback parameter are
removed. No proved public declaration is withdrawn or replaced by a hole.

The native Mathlib abelian instance is used directly. The three derived proofs explicitly
retain its native preadditive field in a local copy of that record, as in the adopted
ConstantCompletionEquivalence proof. Those local structures are definitionally equal to
the native structures. A private, locally registered
section-module instance gives the existing ModuleCat.isModule structure explicitly.
A private generic derived-unit theorem performs the adjunction transport and resolving
uniqueness over abstract abelian categories before specializing to module sheaves. Ordinary
adjoint uniqueness and transport of its sectionwise normalization are proved over abstract
categories before specializing to the scalar square.

The new adicFinitePullbackData is the existing derivedPull package with the finite-limits
proof supplied explicitly. Its functor and comparison are precisely the two projections
previously written inline; unfolding the new name recovers their old values.

The new adicFiniteComplexSquare is literally NatIso.mapHomologicalComplex, with explicit
composite functors on complexes in its result type. The scalar-composition formula uses
Mathlib's mapHomologicalComplexCompIso, also literally the original termwise natural
isomorphism. Thus the cochain-functor definition may stay locally irreducible during the
large derived comparisons. The four Formula definitions quote the previous normalization
predicates; the corresponding existsUnique theorem signatures use these constants.
Unfolding them recovers exactly the former predicates. The chosen data are definitionally
equal, rather than arbitrary witnesses of weaker existence statements. The new signatures
and definitions are quoted below. They introduce no mathematical change to consumers.

The old scoped options disabling respectTransparency are removed; the construction
module explicitly enables transparency checks. Section-module structures and supplied
adjunction types are stated explicitly. All irreducibility
and instance-priority attributes used for compilation are local. Unused direct proof
imports are removed as listed in report.md; public import availability is retained.

```lean
def adicFinitePullbackData (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    DerivedPull (adicFiniteComparisonData.{u, v} X)
      (constantMap (adicFiniteComparisonData.{u, v} X) A) :=
  derivedPull (hL := smallModelComparisonPullback_preservesFiniteLimits.{u, v} X)
    (adicFiniteComparisonData.{u, v} X)
    (smallModelComparisonPushforward.{u, v} X) (smallModelProEtaleComparison.{u, v} X)
    (constantMap (adicFiniteComparisonData.{u, v} X) A)


def adicFiniteComparisonData (X : Scheme.{u}) :
    InverseImageData (smallModelComparisonPullback.{u, v} X) :=
  letI := smallModelComparisonPullback_preservesFiniteLimits.{u, v} X
  Classical.choice (inverseImageData_exists
    (smallModelComparisonPullback.{u, v} X) (smallModelComparisonPushforward.{u, v} X)
    (smallModelProEtaleComparison.{u, v} X))

instance adicFiniteOrdinaryPullbackAdditive (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    (adicFiniteOrdinaryPullback.{u, v} X A).Additive :=
  pull_additive (adicFiniteComparisonData.{u, v} X)
    (constantMap (adicFiniteComparisonData.{u, v} X) A)

def adicFinitePullback (X : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] :
    ConstantCompletion.D (constant (smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
      ConstantCompletion.D (constant (coefficientProEtaleModelTopology.{u, v} X) A) :=
  (adicFinitePullbackData.{u, v} X A).functor

def adicFinitePullbackComparison (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    Q (constant (smallModelComparisonEtaleTopology.{u, v} X) A) ⋙ adicFinitePullback.{u, v} X A ⟶
      (adicFiniteOrdinaryPullback.{u, v} X A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        Q (constant (coefficientProEtaleModelTopology.{u, v} X) A) :=
  (adicFinitePullbackData.{u, v} X A).comparison
```

```lean
def adicFiniteComplexSquare
    {A B C E : Type*} [Category A] [Category B] [Category C] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive E]
    {F : A ⥤ B} {G : B ⥤ E} {H : A ⥤ C} {I : C ⥤ E}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [H.PreservesZeroMorphisms] [I.PreservesZeroMorphisms]
    (o : F ⋙ G ≅ H ⋙ I) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ I.mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex o (.up ℤ)
```

```lean
def adicFiniteUnitFormula {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S)
    (e : 𝟭 (ConstantCompletion.D R) ⟶ extend f ⋙ dres f) : Prop :=
  ∀ P : Cx R, CochainComplex.IsKFlatIndependentCoefficients (J := T) (R := R) P →
        e.app ((Q R).obj P) ≫ (dres f).map ((extendComparison f).app P) =
          (Q R).map (adicFiniteOrdinaryUnitComplex f P) ≫
            (resFactors f).hom.app
              (((change f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
```

```lean
def adicFiniteExtendCompFormula {R S V : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V)
    (e : extend f ⋙ extend g ≅ extend (f ≫ g)) : Prop :=
  ∀ P : Cx R, CochainComplex.IsKFlatIndependentCoefficients (J := T) (R := R) P →
        e.hom.app ((Q R).obj P) ≫ (extendComparison (f ≫ g)).app P =
          (extend g).map ((extendComparison f).app P) ≫
            (extendComparison g).app
              (((change f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
            (Q V).map ((Functor.mapHomologicalComplexCompIso (adicFiniteChangeComp f g)
              (ComplexShape.up ℤ)).hom.app P)
```

```lean
def adicFiniteOrdinaryComparisonFormula (X : Scheme.{u})
    {A B : Type (max v (u + 1))} [CommRing A] [CommRing B] (f : A →+* B)
    (e : adicFiniteOrdinaryPullback.{u, v} X A ⋙
        change (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)) ≅
      change (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) ⋙
        adicFiniteOrdinaryPullback.{u, v} X B) : Prop :=
  ∀ M : Mod (constant (smallModelComparisonEtaleTopology.{u, v} X) A),
        (smallModelComparisonPullback.{u, v} X).map
            (insertion (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) M) ≫
          pullInsertion (adicFiniteComparisonData.{u, v} X)
            (constantMap (adicFiniteComparisonData.{u, v} X) B)
            ((change (adicFiniteConstantMap f
              (smallModelComparisonEtaleTopology.{u, v} X))).obj M) =
        pullInsertion (adicFiniteComparisonData.{u, v} X)
            (constantMap (adicFiniteComparisonData.{u, v} X) A) M ≫
          insertion (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X))
            ((adicFiniteOrdinaryPullback.{u, v} X A).obj M) ≫
          (underlying (constant (coefficientProEtaleModelTopology.{u, v} X) B)).map
            (e.hom.app M)
```

```lean
def adicFiniteComparisonFormula (X : Scheme.{u})
    {A B : Type (max v (u + 1))} [CommRing A] [CommRing B] (f : A →+* B)
    (e : adicFinitePullback.{u, v} X A ⋙
        extend (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)) ≅
      extend (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) ⋙
        adicFinitePullback.{u, v} X B) : Prop :=
  ∀ P : Cx (constant (smallModelComparisonEtaleTopology.{u, v} X) A),
        CochainComplex.IsKFlatIndependentCoefficients
          (R := constant (smallModelComparisonEtaleTopology.{u, v} X) A) P →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        e.hom.app ((Q _).obj P) ≫
          (adicFinitePullback.{u, v} X B).map
            ((extendComparison (adicFiniteConstantMap f
              (smallModelComparisonEtaleTopology.{u, v} X))).app P) ≫
          (adicFinitePullbackComparison.{u, v} X B).app
            (((change (adicFiniteConstantMap f
              (smallModelComparisonEtaleTopology.{u, v} X))).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P) =
        (extend (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X))).map
            ((adicFinitePullbackComparison.{u, v} X A).app P) ≫
          (extendComparison (adicFiniteConstantMap f
            (coefficientProEtaleModelTopology.{u, v} X))).app
            (((adicFiniteOrdinaryPullback.{u, v} X A).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          (Q _).map ((adicFiniteComplexSquare
            (adicFiniteOrdinaryComparison.{u, v} X f)).hom.app P)
```

```lean
theorem adicFiniteUnit_existsUnique {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S) :
    ∃! e : 𝟭 (ConstantCompletion.D R) ⟶ extend f ⋙ dres f,
      adicFiniteUnitFormula f e
```

```lean
theorem adicFiniteExtendComp_existsUnique {R S V : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) :
    ∃! e : extend f ⋙ extend g ≅ extend (f ≫ g),
      adicFiniteExtendCompFormula f g e
```

```lean
theorem adicFiniteOrdinaryComparison_existsUnique (X : Scheme.{u})
    {A B : Type (max v (u + 1))} [CommRing A] [CommRing B] (f : A →+* B) :
    ∃! e : adicFiniteOrdinaryPullback.{u, v} X A ⋙
        change (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)) ≅
      change (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) ⋙
        adicFiniteOrdinaryPullback.{u, v} X B,
      adicFiniteOrdinaryComparisonFormula X f e
```

```lean
theorem adicFiniteComparison_existsUnique (X : Scheme.{u})
    {A B : Type (max v (u + 1))} [CommRing A] [CommRing B] (f : A →+* B) :
    ∃! e : adicFinitePullback.{u, v} X A ⋙
        extend (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)) ≅
      extend (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) ⋙
        adicFinitePullback.{u, v} X B,
      adicFiniteComparisonFormula X f e
```

```lean
## Users

The complete transitive downstream list from tools/downstream.py is below. Public
reexport preserves every old declaration and every old public import for all of them.
Each row's effect is the same: definitionally equivalent signatures and constructions;
no consumer adaptation.
No module held by another group is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicConstructibleFiniteReductions | T1 | Public reexport; theorem proved by four steps. |
| Sheaf.Algebra.Homology.KFlatBifunctorTensorHom | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Algebra.Homology.RingedForgetTensorTransposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Algebra.Homology.RingedForgetTwoInjectiveHom | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleHomOfPreserves | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorHomAdjunctionOfPreserves | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierDerivedRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedTransportedHomCounitFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenAdjunctionLocalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedMorphismWeaklyContractibleEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedOpenCounitTensorAction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceCentredChartConstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceChartRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceNormalFrameConstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceReesFrame | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperHeartUniformBound | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleDirectImageScalarExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleKFlatSupportCharacterization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleKFlatSupportComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleKFlatSupportData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleKFlatSupportProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleKFlatSupportRows | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleKFlatSupportStrict | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleScalarFlatModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingProjectionSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTransposeData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingTensorCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingTensorTransposeAssembly | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.NativeAdicAffineOpenZeroStratification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.NativeWeilOpenExactConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineLineTensorCounit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineProjectionReassociation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTensorActions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTowerTensorCounit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1TensorAction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleP1DiagonalComponents | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenComplementSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenRefinementMatePlusCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.SpP1BaseChangeOfNormalized | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.SpP1NormalizedFamilyCore | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.SpP1RationalPointChern | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.CategoryTheory.ConstantCoefficientScalarExtensionPresentations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Compactification.NagataDensityNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.ConstantFieldRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.ConstantFieldRestrictionStalk | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.ContinuousCoefficientGeometricCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.FiniteStageFibreVanishing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.GeometricConstituentOrbit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.MarkedGeometricCurveModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.NormalizedContinuousCoefficientFamily | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.NormalizedStratifiedEmbeddedLattices | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.OrdinarySectionScalarComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.PairEigenvalueGeometricConstituent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.PoweredGeometricPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.PoweredGeometricPullbackStalk | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.ProEtaleIrreducibilityDetector | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicComparisonBridge | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicStrataBridge | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.SemisimpleFrobeniusOrbitDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.SimpleLisseSupportModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCompactificationSheafScalarMap | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleScalarSectionNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafFoldScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.FourierTransform.FourierDeligneTransform | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AcyclicFlatProperCoefficientModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicActualSystemsNormalized | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicClosureScalarCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicCommonStageFibreTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicCommonStageFibreZeroMap | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicCommonStageHeartExactness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicCompleteHomSections | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicCompleteReductionCone | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicCompleteResidueConservative | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicConstructibleLocalModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicEtaleStalkLevels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicFiniteConstructibilityComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicFiniteRealizationCocone | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicFiniteRealizationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicFiniteReductionModelFamily | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicFiniteScalarCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicImmersionCompletedTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicImmersionLiftingInput | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicImmersionResidueComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicImmersionResidueLisse | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicImmersionResidueTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicImmersionSliceComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreCommonStage | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreCommonStageData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreExactness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibrePullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicNormalizedPuritySystems | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPerfectHomCochains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPerfectHomCohomologyComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPerfectModelHomCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPerfectReductionHomML | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPerfectReductionModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensorComponents | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPuritySourceNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPuritySourceTransitionSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicPurityTwistRestrictionComponents | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicRealizationFamilyData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicReindexingCore | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicReindexingFunctoriality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicReindexingHom | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicReindexingTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicResidueAdjointTower | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicResidueAlgebraTower | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicResidueCechQuotientCone | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicResidueCoefficientSequence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicResidueCompletionModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicResidueFiniteLocalModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicResidueKoszulNakayama | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicResidueLiftComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicResidueLissePerfectLift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicResiduePerfectReductionComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicResidueQuotientFiniteProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicResidueQuotientUnitUniversal | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicResidueSliceCompleteness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicResidueStalkTowerFamily | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicResidueVanishingSuccessor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicStratifiedPerfect | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicStratifiedPullbackInterface | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdmissibleCupCoefficientPassages | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdmissibleHomSubstitution | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineCoefficientCounitMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineCoefficientCounitNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineCompactificationComparisonNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineCounitScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineDiagonalDncCoordinateIdentity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineDiagonalDncNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineDiagonalIntegrationConstructions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineDiagonalIntegrationTranslationIntegration | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineDiagonalIntegrationTranslationTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineDiagonalPowerCoefficient | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineDiagonalPresentedBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineDiagonalRawTransposePower | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineDiagonalRestrictedTransposes | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineDiagonalSectionCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineDiagonalTateCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineDiagonalTraceRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineDiagonalTransposePower | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineIntegrationExponentTransition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineLineAdjunctionAssembly | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineLineCanonicalScalarCounit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineLineCompositeTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineLinePuritySource | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineProperSquareStratifiedModule | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineSpacePurityCompositionMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineSpacePurityCoordinateInvariance | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineSpacePurityOrderedBlocks | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineSpaceThomMap | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineTargetDiagonalDnc | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineTowerIntegrationSiteTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AlgClTopologyMateHomBijection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AllStageCtfPullbackUnit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BarrettIndRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BaseChangedLineTraceEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BasicOperationCoefficientCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BasicOperationReductionAndEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundaryFiniteEvaluationRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundaryFiniteSiteData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundaryFiniteSiteRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundaryFiniteTorDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundedConstructibleBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundedFlatCoefficientSiteSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundedFlatTensorContinuity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundedSiteExchangeTransposes | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BoundedSiteTensorTransposes | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BrownTowerBoundedTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BrownTowerGeometricTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BrownTowerRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.BrownTowerSite | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CanonicalDiagonalRightDerived | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CanonicalTateArrowNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CanonicalTateComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CartierRelativeKummerRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CartierSupportedComparisonSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CentredDiagonalSourcePasting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ChartCounitScalarTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ChartDncNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ChartDncSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ChartDncVectorFactorData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ChartEpsilonPasting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ChartExceptionalCounitEquation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ChartGeometricCounitEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ChartIntegrationAdjoints | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ChartNormalIntegrationSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalFiltrationDiagramFibres | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalFiltrationExactDiagram | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalFrontierExistence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonFibres | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonSystem | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseFiniteConstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseFiniteOperations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseIntrinsicFibrePullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseOperations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRawLissePointFibres | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseRealizationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseScalarCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRealizationLocalSpectrum | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRealizationPunctualPurity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalRealizedAnchorEigenvalue | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalSuccessiveRestrictions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalSystemRawLisseRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalTwoFibreCommonData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalTwoFibreScalarData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalWeilCoherentDiagramStages | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationTransportData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiniteDiagramDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalWeilPrescribedIsomorphismLifts | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClassicalWeilRestrictionExistence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClopenCompletedTowerRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClopenCounitAdjointComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClopenPrescribedWeilFiltration | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClopenStrictSystemSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClopenSystemRealizationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClopenSystemRestrictionEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClosedCoefficientTransposeCocycles | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClosedEmbeddingPerfectEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClosedScalarDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClosedSectionCompactOrigin | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClosedSectionCompactOriginData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClosedSectionSourceNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ClosedSupportExceptionalMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefDualizingClosedChart | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefFiniteHomSiteData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefFiniteHomSiteDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefFiniteSiteHomTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefSupportOpenTensorModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefSupportPointSectionsComparisonExistence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefSupportPointSectionsData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefSupportPointSectionsModelExistence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientDualizingOpenAdjoint | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientDualizingOpenTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientEvaluationNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientMapGeometricSquares | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientPathNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientProjectionSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientPushFilteredLegs | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientScalarDerivedTensorSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientScalarSectionRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientScalarTensorData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientScalarTensorRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientTensorNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoefficientUnitTowerNormalized | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CommonProjectionComparisonEquations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CommonStageOpenHeartAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CommonStagePerfectEvaluationDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CommonStagePointReturn | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CommonStageRestrictionTensorDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactExchangeOperationCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientExchangeInvertible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportCompletedProjectionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportCompletedScalarArrow | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportCompositeTransposeDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportExchangeDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteScalarMateNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportLimitEquationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportLimitEquationRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedScalarDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportPathReductionSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionCoefficientChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFieldStages | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFiniteStages | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionIntegralStages | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionRightUnit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportRationalScalarIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationIdentity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportReductionAdjoint | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportScalarLimitReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportScalarShiftNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportScalarShiftStructures | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportScalarShiftWitness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportSiteExchangeSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportStrictScalarComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportStrictScalarMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportStrictScalarRefinement | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportSystemTransposeNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportTermHomFinite | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportTotalLimitRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportTowerReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactificationBOrdinaryProjectionSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactificationBProjectionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactificationBProjectionDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactificationBProjectionReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactificationCompletedRealizationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactificationFiniteProjectionModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactificationOpenLimit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactificationProjectionInverse | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactificationPushLimit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactificationScalarData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactificationStrictRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ComparisonImageClosedSectionNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompatibleFiniteDerivedTrivializations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompleteCompactificationLimitRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompleteCompactificationLimitSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompleteIntegralConstantRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompleteProjectionDescentMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompleteProjectionMateDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompleteProjectionReductionSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompleteResidueLineInverse | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompletedContinuousHomHypotheses | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompletedLocalFibreComparisonData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompletedPullbackFractionDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompletedScalarAssociatorLocalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompletedScalarExactLocalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompositionComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompositionIteratedMateExpansion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompositionSingleMatePresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CompositionTensorMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConcreteOpenScalarTensorSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConcreteProjectionCoefficientCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConcreteProjectionFactorizationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConcreteProjectionReductionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConcreteProjectionReductionSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConcreteProperScalarTensorSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConcreteSupportScalarIsomorphism | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedERealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedERealizationDefinitions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedERealizationSystem | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedERealizationSystemExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedExceptionalCounitRepresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedExceptionalRealizationProperties | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedExceptionalRefinementCounits | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedExceptionalSystemRecognition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedHomChainRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedOpenCoefficientModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedOpenUnitComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedTateIntegralTower | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedTateIntegralTowerData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CondensedTateRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantCompletedOrdinaryAssociativity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantCompletedScalarAssociativity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantDirectImageTowerRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionCyclicSheetPartition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionRestrictionLocalConjugacy | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnExactFunctor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalSpectra | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnTransportComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetCoefficientEquivalences | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetCommonStageEquivalences | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetGeometry | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetTensorSplitting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantFieldResidueTensorBounds | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantGeometricStalkUnit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantScalarTowerAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstantScalarTowerMates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleCoefficientSiteSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientAssemblyData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientStages | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCompositor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCompositorData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalLeftRefinements | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalRefinementMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleLeftCompositorCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleMateCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleRationalHomComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleTensorComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ConstructibleWeilModelSquares | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousAlgClFiniteStageDevissage | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperScalarComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousAlgclScalarConstructibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousAlgclScalarExtensionConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateAdjunctionComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateCartierBoundarySign | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateLineAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateLineAdjunctionMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateLineAugmentationRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateLineConjugateExponents | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateLineCounitTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateProductPresentations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateSectionArrows | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateSectionProductRecursion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjectiveTrace | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateSectionSiteTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateSectionTensorTrace | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateSupportedProductRecursion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateTowerCompactTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateTowerExceptionalCompositors | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationFusion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoordinateZeroBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CtfCoefficientStageSelectors | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CtfLocallyClosedPerfectGeneration | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CurveClassicalFiltrationPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CurveClassicalPullbackExists | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CurveRestrictionLocalPowers | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DerivedDirectImageAssociativity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherenceData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DerivedExchangeExactNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DerivedHomSubstitutionCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DerivedOpenRestrictionMixed | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DerivedOpenRestrictionNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DerivedOpenRestrictionSuccessive | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DerivedOpenSquareRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DerivedScalarRestrictionPullbackMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DerivedTensorRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DerivedWeilOperations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalAffineCounitRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalAffineIntegrationSiteSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalAffineRankZeroActual | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceMapAgreement | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceSiteComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceSiteData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalBaseSquares | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientUniformizerReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCompletedDiagramRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCompletedFrame | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCompletedPushSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalCounitComparisonData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalDncAffineModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalDncChartNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalDncEtaleNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalFiniteRootMap | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalIntegralRootMap | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalNonTorsionBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalOrdinaryChartLift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalOrdinaryOrientationGluing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalOrdinaryOrientationNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalOrdinaryOverlap | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalOrdinaryRealizeRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalOrientationRefinement | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalQuotientBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalTowerCoefficients | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalTraceIntegrationSystems | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalTracePresentationExistence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalTraceResultExistence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalTraceSingleFaithful | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalTraceSources | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DiagonalUniformizerAnnihilator | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DifferenceCoordinateSectionIdentifications | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DifferenceFirstInputRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DifferenceSecondInputRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DirectImageHomEvaluationSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DoubleDiagonalSectionIdentifications | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DualBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DualizingClosedSite | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DualizingCocycleSourceEtale | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DualizingCompositionCoefficientMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DualizingPrimitiveOpenRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DualizingSigmaCocycleLocality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EmbeddedFiniteCoefficientRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EmbeddedFiniteFieldCohomologyCriterion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EmbeddedFiniteFieldPresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EmbeddedFiniteHeartConstructibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EmbeddedFiniteHeartMonoidalPresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EmbeddedFiniteHeartRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EmbeddedFiniteScalarIsIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EmbeddedFirstReductionComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EmbeddedFirstReductionOrdinary | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EmbeddedIntegralCompletenessTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EmbeddedIntegralResidueSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EmbeddedIntegralResidueTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EmbeddedIntegralRestrictionKFlat | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EmbeddedIntegralScalarKernelSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleBrownCoefficientCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleBrownEvaluationMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleBrownGeometricComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleBrownLevelComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleBrownOpenSingletonEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleBrownProjectionRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleBrownProperSingletonEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleBrownSupportTransition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleCartesianTowerTensorComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleCoefficientProperCoproducts | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleCofinalSupportComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleCofinalSupportRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleCompactScalarBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleCompositeEComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleCtfChartDomain | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleDerivedScalarTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleDirectImageScalarComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleDirectScalarProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleGeometricBiduality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleKFlatTensorPresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleLisseHomReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleMiddleTensorAssembly | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleOpenScalarExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleOpenScalarExchangeSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleOpenScalarProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleOriginScalarProjectionSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCompactScalarSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleProEtaleScalarCounitTransposes | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleProEtaleScalarMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleProEtaleScalarMateData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleProEtaleScalarPullbackCube | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleProperCoefficientTensorUnit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleQuotientTensorProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleScalarPullbackIdentityNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleScalarPullbackTensorCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleScalarPullbackUnitCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSingleCoefficientProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSumCoefficientComputation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSumCounitScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSumScalarRepresentative | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSupportedModelCoinduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSystemBrownConstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSystemCoefficientProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSystemCofinalData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSystemCofinalMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSystemDerivedTensorEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSystemEvaluationBound | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSystemImageTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSystemProjectionCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSystemProjectionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSystemProjectionEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSystemProjectionExistence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSystemProjectionPresentationCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSystemQuotientNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSystemScalarMateCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleSystemTensorEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleTensorSourceTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EtaleTowerBrownAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EvenLineBinaryProductNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EvenLineCoefficientProjectionNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EvenLineCoordinateIntertwining | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EvenLineProductIntegrationMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EvenLineProductIntegrationSymmetry | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EvenTateLineSelfSymmetry | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.EvenTensorPositivity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExactProperOpenProjectionMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalAdjointAdmissibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalCoefficientComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalCoefficientLeftUnitCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalCoefficientMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalCoefficientUnitCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalDualizingBaseChangePasting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalFieldDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteIntrinsicBounds | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteOperations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRestrictionAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteScalarMates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalOriginAdjunctionEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalProOriginExactLinear | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalProperOpenOriginComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalSiteOriginComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalSystemInterfaces | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExceptionalSystemTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExchangeFunctoriality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FdCompletedCompositorNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FdPullbackSignedShiftWordTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FdPullbackWeilReturnSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldCohomologyPerfectDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemAdjoints | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemComponents | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemFiniteAdjoint | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemFiniteComposite | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemLaws | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExtensionComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExtensionIntegralComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExtensionIntegralCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExtensionIntegralModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExtensionLimitEquations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExtensionRationalComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExtensionRationalModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExtensionReductionLimits | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExtensionSourceNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExtensionStrictLimits | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExtensionSystemCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldExtensionTowers | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldOrientationSystemComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldOrientationSystemCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldOrientationSystemFiniteOrientation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldOrientationSystemHeart | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldOrientationSystemNormalizations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldProjectionOpenSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldProjectionOriginWitnesses | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldProjectionProperSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldProjectionRefinementSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldProjectionSystemData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldProjectionSystemSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldProjectionTensorConstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldPuritySystemTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldPuritySystemTransposeBase | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldPuritySystemTransposeCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldPurityTransposeArrows | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldPurityTransposeLevelWords | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionCoefficientSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionIntegralComponent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionIntegralNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekSupportEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekSystemCocycle | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekSystemCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekSystemComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekSystemEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekSystemFiniteLaws | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekSystemMixed | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekSystemMixedCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekSystemModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekSystemRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekSystemTransitionWords | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldShriekSystemTransitions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FilteredCondensedCanonicalComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FilteredCondensedCounitBijective | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FilteredCondensedCounitFiniteFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPair | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPairData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDirectImage | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientInputModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientIntrinsicChainTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientKFlatReflection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteTensorNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteTensorPresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCompactSiteCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportCoefficientSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportEvaluationRefinement | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportScalarComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportScalarTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteDiagonalDncReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteExceptionalSiteNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFieldClosedSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFieldHomEtaleWitness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFieldSheafScalarExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFirstRootChart | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteForwardCompactifiedSwap | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteForwardProductCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportGeometricSquares | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportSiteSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeDerivedScalarCalculus | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeHomEvaluationCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeHomLocalCalculation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarCalculusData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarDerivedTensorModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarTensorCalculus | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteFreeTensorCtf | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteGammaEvaluationIsIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteGeometricPurityMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteHomDomainCalculus | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteHomIntrinsicSiteHomIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteHomNativeNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteHomSiteHomRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteHomSiteTensorCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteIdentityCompositionNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteKernelConstructibleLocalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteLevelProjectionFactors | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteLocalizingSmoothLocalFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteMateDomain | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteModelFreeComplexReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteModelOrdinaryFreeComplex | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteModelOrdinaryScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteModelQuotientChartComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteModelSheafQuotientConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteModelTopologyComparisonMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteModelTopologyDerivedHom | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteOrientationReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FinitePointCounitUnitNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FinitePointReconstructedEvaluationSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FinitePositiveChartFrameExt | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FinitePositiveChartRecursion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FinitePositiveRootChartPower | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FinitePositiveRootCharts | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteProductOpenRestrictionPasting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteProductOrdinaryNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteProjectionCompactificationSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteProjectionIdentityNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteProjectionOpenAssembly | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteProjectionPresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteProjectionRefinementLeft | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteProjectionTensorSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteProperBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FinitePublishedRootChartPower | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FinitePuritySourceUnitReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteRationalHeartComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteReductionBaseChangeSource | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteReductionExceptionalFiniteModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteReductionLineChartScalars | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteReductionLineInputConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteReductionReassociation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteReductionShiftedPullbackCube | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteReductionSourceChartIndependence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorSource | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteRestrictionDiagramNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteRingRelativeScalarComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteRootLinePowerTransition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSheafH0Augmentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSignedTwistProducts | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSiteCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSiteTowerPaste | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSiteWordRefinement | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSourceChartPowerTransition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSourceChartScalarTransition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSpanModuleDerivedComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteStageNormalizedAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteStageNormalizedChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteStageNormalizedCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteStageSupportedGeneration | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSupportCompositorCoefficient | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSupportCompositorExistence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTargetChangeCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTateBalancedScalarPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTateScalarSourceData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTateScalarSourceExistence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTateScalarSourceNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTensorComparisonEquations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTensorLineChartReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTensorLineDerivedExistence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTensorPresentationReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTensorProductFrameExt | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTensorProductMap | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTensorProductMapIsIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTensorSemilinearReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftFirst | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftSecond | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTensorSignedReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTripleProductDefinitions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTripleProductNormalForms | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTwistRootTrivialization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FlatCoefficientSquareNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FormalClosedSupportDerived | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FormalClosedSupportSheaves | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ForwardProductCoordinateTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FourierArtinSchreierProperties | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrameworkPbcComparisonData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrameworkPbcComparisonSystem | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrameworkPbcIntegralComparisonLaws | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrameworkPbcPullbackScalarBridge | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrameworkPbcRawComparisonData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrameworkPbcRawComparisonLaws | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FreeInsertionCompactSupportCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.FrobeniusSystemExchangeInverse | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.GeneralLfpAdicInputWitness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.GeometricCommonStageDirectImage | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.GeometricGeneratorProjectionDevissage | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.GeometricQuotientWeilCompositionSeries | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.GermReparametrizationDerivedDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.GlobalIdentityNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.GlobalInternalHomDetection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.GlobalVerdierDualityData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.HigherIdentityCompositionNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.HomFiniteProjective | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IdentificationCoefficientTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IdentityCoefficientTransportData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IdentityCompactificationLimitComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IdentityCompactificationSystemMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IdentityOpenSystemEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IndetaleSupportedHullContinuity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralAdicHomResidueOrigin | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralAdicInputNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionBijection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralAugmentedQuotientTowers | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralBoundedStratumBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralClosedSupportNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralCompositionCoefficientSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralCompositorLimitRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralConstantModelLocalResolution | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionHom | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTowerData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralDualizingExceptionalUnit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralExtensionByZero | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpHomFiniteness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralHeartConstructibleModuleComplete | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralHeartProjectiveLocalModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralHomPresentationEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralLissePullbackNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralModelsEmbedded | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralModelsEmbeddedCoefficientKernels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralModelsEmbeddedCompletion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralModelsEmbeddedCompletionDiagram | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralModelsEmbeddedResidueComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralModelsEmbeddedResidueSections | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralModelsEmbeddedScalarFlat | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralModelsEmbeddedStacksCriterion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralOpenEmptyPullbackVanishing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralOpenSupportNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralOrdinaryProjectionReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralPositiveReductionConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralProjectionRefinementSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralProperReductionBound | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralProperReductionModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralPullbackAugmentationAmbient | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralResidueProperFormulas | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralRoosAugmentationLocalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralRoosChainRepresentatives | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralRoosCompletionIsomorphisms | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralRoosDerivedPullbackUnit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralRoosResolvingCounits | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralScalarIsomorphismExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralSectionsPerfectReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralSemilinearGermSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralStageProjectionReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralStageProjectionStructuralIdentities | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralSupportFunctorNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralSupportLatticeReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralSupportNormalizationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralTensorConstructibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralTensorShriek | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralTowerCompactificationCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralTowerGeometryLimits | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralTowerImageReconstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralTowerProjectionMates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegralTowerPullTensorConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegrationExponentTransposeTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntegrationTransposeScalarMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.InternalHomDualTorAmplitude | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntrinsicConstructibleFibreExactness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IntrinsicLocalLatticeComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IsomorphismFiniteExchangeCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.KummerChartGeometryMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.KummerCoefficientModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.KummerGlobalChart | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.KummerInvariantScalarMap | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.KummerPartialNerveChart | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.KummerPartialNerveMorphism | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.KummerPartialNerveNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.KummerPartialNerveScalarMorphism | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.KummerRefinement | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.KummerScalarInvariantSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.KummerSiteCohomologyNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.KummerStratumChart | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.KummerStratumGeometry | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.KummerStratumScalarMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.KummerStratumScalarMateDetection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedStrictSystems | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LineCounitComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LineKummerFieldRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LineZeroClassExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseLatticeChoiceExistence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseLatticeHeartLift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseLatticeHeartLiftData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseLatticeLisseDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseLatticeNormalizedRealizations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseLatticeRealizationFaithful | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseLatticeSingleComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseLocalizationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseLocalizationExistence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseLocalizationLocalFreeness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseLocalizationRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseLocalizationSlices | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LissePointNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LissePointSectionsRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseRationalRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseTensorPullbackRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LisseTensorPullbackRealizationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCoefficients | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCompositionAssociativity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCompositionCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeScalarTower | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeTransportAddition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeTransportNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeWeilAddition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalFrobeniusStepCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalizationScalarUnit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocallyClosedHomGenerator | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocallyClosedInternalAdjunctionIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocallyClosedOrdinaryComparisonIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocallyClosedPairingCancellation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocallyClosedScalarPasting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocallyConstantPerfectComplex | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocallyConstantPerfectDualCtf | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicConstructibleRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocallyFiniteCoefficientRingRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.LocallyProjectiveCoefficientHom | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MateOpenCompactSupportExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MateOpenProperRestrictionIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MateOpenProperSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MateOpenRestrictionMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MiddleExchangeProjectionBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MixedCompactSupportExchangeData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MixedCupFieldCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MixedCupFieldNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MixedCupFieldOperations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MixedCupNormalizedScalars | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MixedCupOperationComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MixedCupRingedNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MixedCupTensorClosure | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MixedCupTensorComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MixedCupTensorElementary | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MixedCupTensorNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.MixedWeightsStability | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ModelChartOrientationAssembly | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ModelOrientationChartDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ModelOrientationSourceNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ModelOrientationTateDetection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeAdicCompactSupportSums | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeClosedTransposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeCoefficientTensorComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeCompactProjectionFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeConstantSupportModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeDerivedWeilTensorConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeEncodingDerivedOperations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeForgetConstructibleCriterion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeGeometricHomComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeGeometricTensorComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeModuleConstructibilityComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeOpenDerivedTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeReductionCounitKFlat | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeScalarRestrictionComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeWeilClosedForgetful | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeWeilClosedModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeWeilDerivedInductionComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeWeilDualizingHomTransposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeWeilFreeCoproduct | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeWeilHeartProperties | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeWeilInductionComparisonData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeWeilInductionSummands | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeWeilProperNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeWeilRowHomComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NativeWeilTensorTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormAlgClInternalHomBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormAlgclOrderedFiniteModelFiltration | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalSectionIntegrationBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalSectionIntegrationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalSectionIntegrationOrientation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedCommonCoefficientLaws | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedDerivedIsomorphismSectionReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedDerivedIsomorphismTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedEtaleComparisonComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedEtaleRestrictionComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTrace | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedHeartRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedLatticeFiniteFree | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedPullbackCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedPullbackNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedPullbackObjects | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedRationalLeftLaws | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedRingRefinementLaws | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedStageCoefficientCalculus | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedSupportEtalePresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedTateTensorTower | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.NormalizedVectorPurityScalarReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OpenExceptionalScalarLocality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OpenExtensionConstructibleFiniteTor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OpenProEtaleCounitScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OpenProjectionFactorCoefficientChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OpenScalarCounitSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OpenScalarSiteCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OpenSquareSupportScalarCounit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OpenWeilCarrierRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OpenWeilCoefficientFibres | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OpenWeilFiniteStageFrobenius | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OpenWeilGeometricFibres | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OpenWeilPunctualSpectrum | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OperationCoefficientActionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrderedAffineComparisonNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrderedAffineLineTransposeNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrderedAffineTransposeData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrderedAffineTransposeProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrderedAffineTransposeSuccessor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrderedIntegrationComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrderedLineLevelBounds | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrderedTateScalarNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrderedTowerOrientation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrdinaryScalarBalancingLevel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrdinaryScalarReductionGenerators | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrientationCoordinateBoundaryPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrientationCoordinateModelBoundary | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrientationGeometricComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrientationGroundFieldRetagging | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrientationLocalResidue | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrientationPerfectLines | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrientationScalarTowerTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrientedDoubleHomCancellation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OrientedPerfectDuality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.OriginalScalarMateShift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.P1CounitScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.P1KummerChernScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.P1KummerDerivedScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.P1KummerScalarEndpointComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.P1KummerScalarEndpointExistence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.P1KummerScalarEndpoints | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.P1KummerTraceSiteTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.P1SplittingScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PairingData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PartialKummerBoundaryUnitModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PerfectDualPairAndTateStability | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PfReductionProperOpenIdentities | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PodMixedSupportCupProduct | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PodReconstructionCommonStageCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PodReconstructionCommonStageData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PodReconstructionRawRationalNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PodReconstructionScalarRealizations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointFiniteMultiplicationInverse | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointFrobeniusNormalizationDefinitions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointIdentityExchangeRecipe | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointIdentitySupportNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointPullbackConeLocalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointQuotientComparisonCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointQuotientTowerHomotopy | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointRestrictionWholeRoosSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointRootLimitCyclotomicAction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointScalarPunctualSpectrum | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointSectionsCompletionCone | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointSignedCyclotomicAction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointSignedCyclotomicActionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointSignedCyclotomicScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointSystemInsertionComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointSystemNormalizedComparisonData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointSystemRoosComparisonAssembly | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointSystemRoosRestrictionAssembly | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointSystemRoosTransportData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointSystemRoosTransportRepresentative | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointSystemTransportDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointTateCommonStageCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointTateDerivedComparisonCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointTateFiberCanonicalComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointTateFiberCoefficientComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointTateFiberComparisonData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointTateFiniteSectionComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointTateNormalizedSectionGenerators | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointTransportResolutionCancellation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointTransportStrictQuotient | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointWeilAlgebraicFlag | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointWeilHeartFlagData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointWeilPairingCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointWeilTensorRepresentatives | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PointWeilTransportUnitShift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProEtaleAffineLineCounit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProEtaleFrameIntegration | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionIntegration | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProEtaleProjectiveCoefficient | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProEtaleVectorIntegration | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProEtaleVectorIntegrationArrows | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProductCompositionCoordinateComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProductExchangeCoordinateDefinitions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProductExchangeCounitCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProductHorizontalExchangeFactorization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProductOpenAdjunctionNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProductOpenCounitNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProductOpenSupportNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProductOpenTensorProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProductOpenTensorProjectionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectionCompactificationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectionFactorCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectionPurityCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectionReductionPresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectionReductionWitnessedFlatDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectionScalarSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectionSectionNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectionTensorCoefficientCocycles | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectionTensorIntegration | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectionUnitIntegration | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectionWeilTensorDomainBridge | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectiveDiagonalComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProjectiveDiagonalPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperAlgClComparisonDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperCoefficientDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperCoefficientDescentData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperCompactCoefficientActionComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperCompactIntegralComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperCompactRationalFunctorComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperEtaleOriginScalarData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperEtaleOriginScalarIsomorphism | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperHeartBoundTorsion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperIntegralScalarSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperIntegralTowerComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperOpenCoefficientMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperOpenCoefficientRefinement | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperRationalScalarSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperSupportCoefficientAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperSupportFiniteAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperSystemEvaluationTransitions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ProperWeilIterateGermFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PulledOrderedLineSingle | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurCoordinateRepresentingFamily | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurEtaleScalarMateProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurIntegralReductionUniformTor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPairData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurIntegralSupportDerivedComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurIntegralSupportOrdinaryComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurKFlatOpenModelMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurKFlatOpenProjectionModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurSupportPresentationAlpha | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityAffineLineBoundaryRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityCompositionComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityConjugatesTowerReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityFiniteReductionTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityKummerTriangleConcentration | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityPullbackLevelBounds | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityPullbackReductionTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PuritySectionBaseComparisonLaws | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PuritySectionEtaleRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PuritySectionFibreSquares | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PuritySectionNormalizedSpecialization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PuritySectionRestrictionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PuritySectionRestrictionEtaleFunctorial | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PuritySourceTransports | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityTowerReductionComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityWitnessedMateNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.PurityWitnessedOpenChartTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.QbarFiniteDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportFiniteComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportFiniteMates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportImageComplete | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportNormalizedLift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.QcqsIntegralFiniteModelCompleteness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RadicialEtaleRationalUnitRetraction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalAffineTensorCalculus | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalAmbientPullComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalAmbientPullModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalBalancedFreePullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalContinuousComparisonCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalContinuousFiltrationModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalContinuousPullbackTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalCoverReflectsIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalEvaluationCover | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalModuleRealizationFunctor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalOrdinaryCohomologyTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalP1AmbientComposites | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalP1DiagonalTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalP1KernelContractions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalP1Triangle | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalP1UnitCounit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalProjectionComparisonEquations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalPullSingleComputation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalRealizationFiniteConeModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalRealizationHomTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalRealizationScalarCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalReturnBlockPower | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalScalarBalancedLocalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalScalarCompletionUnitSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalScalarMixedUnitCancellation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalStratumPullbackData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalStratumPullbackModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalTatePullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalTwistedPullbackCompositor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RawChartScalarCounitPasting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RealSheafSections | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RealWeights | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ReconstructedBrownMateLaws | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementCommon | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementSingleDegree | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementTraceSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementTraceTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ReductionOpenEtaleOrigin | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ReductionSiteCoefficientPasting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RefinementCoefficientMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RefinementFiniteOriginEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RelativeKummerSiteNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RelativeKunnethClosedFibre | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RelativeKunnethConstructions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RelativeProductCoefficientFactorSquares | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RelativeProductFactorSquaresCore | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RelativeProductFactors | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RelativeProductProperCompatibilityCore | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ResidueControlledFiniteHoms | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RestrictedCoefficientMateProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SbcDatumExchangeComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarCompositeMateAdjunct | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarFibreCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarFibreComponentData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarFibreComponents | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarFibreNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarHomPresentationEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarIteratedMatesAdjunct | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarLimitConstraintShift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarPullTensorCoefficientCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarPullbackComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarPullbackIsoExistence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarPullbackIsoUniqueness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarPullbackRepresentativeData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarReductionTowerBalancing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarRefinementOriginsE | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarRefinementOriginsF | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarSourceCounitUniversal | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarTargetCounitUniversal | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ScalarTensorPullbackNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SectionCompactSourceExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SectionCompactSourceMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SectionEtaleOpenCancellation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SectionSourceEtaleExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SectionSourceProExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SectionSourceProExchangeConstantSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SectionSourceProExchangeTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SectionSupportedComparisonIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SectionSupportedProExchangeIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SectionsRationalModelComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SemilinearCommonOrdinaryCubes | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SemilinearCommonRefinementCubes | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SemilinearCommonSupportCubes | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SemilinearExchangeCubeCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SemilinearExchangeCubeData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SemilinearExchangeReindexing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SemilinearExchangeReindexingData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SemilinearGermIterationDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SemilinearRationalOrdinaryCubes | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SemilinearRationalRefinementCubes | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SemilinearRationalSupportCubes | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfAdicCommonStageDescentEquivalence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfBcCompletedMateDomain | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfCompletedExchangeTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfExactLocalizationTriangle | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfFieldMateDomain | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfIntegralClosedKernelRoos | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfIntegralKernelRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfIntegralLocalizationConstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfIntegralOpenKernelCompactSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfNormalizedCommonStageDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfNormalizedCommonStageWeilSquares | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfNormalizedRationalClosedComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfNormalizedRationalWeilSquares | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfNormalizedRecollementScalarCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfNormalizedRecollementTriangles | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfPackageBaseChangeDomainRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfPackageCommonStageTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfPackageIntegralRecollementSource | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfPackageIntegralSupportTowerNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfPackageQbarAdjunctionMapDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfPositiveFiniteLocalizationConstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfQbarLocalizationCommonStage | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfQbarLocalizationExactDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfQbarLocalizationFiniteCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfQbarLocalizationFiniteData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfRationalLocalizationOrthogonality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfRecollementReductionBoundary | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SfRecollementRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ShiftedCoefficientLinesInvertible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SixFunctorDatum | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothExceptionalTensorPasting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityBaseChangeFactors | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityCompositionFactors | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateChartModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateFoundations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateProjectionModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitPredicates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCtfFibre | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBoundsDomain | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBoundsOperations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartAdjunctionLevels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartAdmissibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCompactBounds | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCompatibleCounitLift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGamma | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGammaData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGlobalChartAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluingData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerOpenHomComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Data | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerRestrictedRepresentingPair | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SourceSectionStalkConeComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.StratifiedFiniteProjectiveTor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.StrictDirectImageMixedUnit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.StrictDirectImageMixedUnitData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.StrictEtaleExceptionalAdjointInterfaces | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.StrictMixedFiniteEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.StrictMixedScalarSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.StrictMixedSystemModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.StrictReductionCompactSupportNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.StrictScalarMateShift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SupportedCartierDerivedPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SupportedCoefficientHomNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SupportedCommonFieldScalarData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SupportedCommonFieldScalarModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SupportedLatticeNormProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SupportedProjectiveChern | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SupportedProjectiveChernComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SupportedRootScalarSiteComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SupportedTriangleMateIdentification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemClopenMateIdentification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemCompactSupportData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemCompactSupportEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemCompactSupportProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemCompactSupportRestrictionCocycle | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemCompactSupportRestrictionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemCompactSupportRestrictionEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemCompactSupportTransitions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemCompatibleCompositorData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemCompatibleCompositorNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemCompositorFiniteWordEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemCompositorRefinementSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemEnrichedProjectionAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemInternalHomRepresentability | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemOpenRestrictionCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemProjectionChangeCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemProjectionTriangleCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemProperRestrictionCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemRefinementConstructibleDomain | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemRestrictionFiniteNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemScalarBasisDistributivity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemScalarRefinementRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemScalarTensorConstituents | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemTensorPresentationCoreExistence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemTensorPresentationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemTensorPresentationIdentification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.SystemTensorSemilinearRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TamePairProperGenerators | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TateScalarPullbackCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TateTwistedProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TensorExchangeCtfDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TensorHeartSpecialization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TensorHomExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TensorMateBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TensorTransposeFiniteEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TensorTransposeTowerNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerAdjointCompositorRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerCompositorFiniteEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerGeometricPurityMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerIntrinsicShriekTransition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerNormalizationPreservation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1CoefficientCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1ComparisonsWithLine | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1CtfData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1DiagonalProjectionFactor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1DiagonalTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1EtaleOriginComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1FiniteAdjunctionAssembly | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1FirstTraceReordering | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1FixedTotalTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1FormulaLevelComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1GeometricCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1KernelFiniteComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1KernelScalarData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1KernelScalarNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1KernelSplittingBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1LevelCtfModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1LevelWords | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1OrdinaryPushCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1ProjectionLevelComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1ProjectionTraceIdentification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1ProjectiveCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1ProperCtf | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1PushCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1SecondTraceReordering | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1SingleLevelConstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1SingleLevelData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1SingleLevelTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1SingleLevelTriangles | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1TensorChainCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1TensorCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1TensorOrdinaryCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1TriangleFactorization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1TriangleWords | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1UniformCtfDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerP1UniformPresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerProjectionDomainEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerPurityAdjointTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerTensorAdjointDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeWords | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TowerUniformEtaleDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceBoundedQuotientStalkRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceStalkCompositorTowerData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceStalkCompositorTowerRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceStalkTowerDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TraceStrictStalkTowers | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TransverseTameOpenShriekExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwConventions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackCofinalModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackLineMembership | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionTower | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackTateReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerBounds | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerDomain | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerDomainDefinitions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerOrigins | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.UniformTowerTensorClosure | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VaryingDimensionDualizingInverse | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorIntegrationUnitTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorModelChartDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorTensorSiteEquations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VectorTraceScalarDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VerdierCompositionMateNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VerdierIdentityProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VerdierPairingThreeTransposes | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilCompactStructureTensorComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilFourierTransform | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilGenericLissity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilGeometricFiberProperties | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilGeometricHomConstructibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilIndOpenRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilIndOpenRepresentability | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilIndProperHigherRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilIndProperHigherRepresentability | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilIndProperOpenHigher | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilInternalHomWeil | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilKernelHenselianInertia | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilPullbackFibreReturn | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WfTateTwist | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionPunctualSpectrum | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionStalkConjugacy | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlFrameworkQuotientAugmentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlImmersionFilteredReductionTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlImmersionRestrictionAssembly | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlOpenCompactSupportRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlOpenExtensionAssembly | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlOpenExtensionTExact | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlOpenWeilUnitEmptyFibre | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlSfPbcNormalizedHeartModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlWeilPullCompositorEquivariance | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.PoincareDuality.ConstructibleSheafBiduality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.PoincareDuality.OpenModuleBalancedProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.PoincareDuality.OpenModuleKFlatProjectionModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.DncCoefficientTransportData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingExponent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteSmoothDualizingScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtensionCore | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.Reduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptionalChart | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptionalConservativity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptionalObjects | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptionalRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionOrientation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.ScalarSectionCompositor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.SectionScalarBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.SupportedScalarTorInterval | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.Transport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.TransportAffineGeometry | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.TransportAffineNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.TransportAffineTrace | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.TransportCompact | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.TransportCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.TransportFamily | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.TransportFiniteLineDerived | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.TransportGeometricOperations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.TransportGeometry | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.TransportScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.TransportScalarCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.TransportScalarLines | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.TransportSources | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SecSmoothPurity.TransportUnits | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.AffineDualizingCoefficient | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenCalculus | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.AmbientUnderivedClopenPasting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CanonicalOpenReductionIsIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CanonicalReductionPullComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CartesianCompactSupportCompositor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefDualizingConstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefDualizingSiteMates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefFinitePairingEvaluationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteDualizingCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionCocycles | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionReductionPairing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralScalarQuotientTransition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefPairingCompactificationModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefPairingFiniteNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefPairingFrameNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefPairingHomRepresentativeComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefPairingSystemDinaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierCore | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierDualizing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierExceptional | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierInternalHom | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefScalarReductionExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefSystemProjectionEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairingData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefWeilExceptionalCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefWeilLeftExchangeCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefWeilNormalizedDuality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefficientDualizingClosedAssembly | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefficientDualizingClosedDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefficientProjectionPointData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefficientSystemSymmetricCalculus | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefficientUnitFiniteTor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CoefficientUnitNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CompactSupportRefinementBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CompactifiedProperTowerExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CompletedOpenCartesianIdentity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeDomains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangePaths | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeSystem | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CompletedSystemPullbackPreservation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CompletedTensorShiftAddOnGood | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CompletedTensorSlotShiftLaws | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ConstantOrdinaryCompactificationComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ConstructibleReductionGood | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.DetSfCompBaseChangeDefs | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.DualizingOpenMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.EtaleHomComparisonModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.EtaleHomThickLocus | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.EtaleHomTransposeExact | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.EtaleOpenExtensionNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.EtaleOpenKFlat | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.EtaleOpenMixedTensorScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.EtaleOpenScalarCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.EtaleOpenTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.EtaleOpenTensorDefs | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.EtaleRestrictionCompositor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionCoefficientUnitData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionGeometricRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemDuality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemEnriched | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdierData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteCounitRestrictionSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizingAffineRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizingCoefficientNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizingData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizingScalarRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptionalData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptionalDomain | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptionalQuotientCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptionalQuotientIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteFreeComparisonTransitivity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteFreeEtaleProEtaleTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteFreeImageComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicBidualComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunctionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentIsIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteOpenCartesianCalculus | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteOpenDirectImageCtf | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteReductionCompletionUnit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteTorOrdinaryPullComplete | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteTorOrdinaryTensorComplete | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteVerdierCoefficientDiagrams | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FiniteVerdierProEtaleLeftTor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FrobeniusAffineEqualizerPresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyRealizationTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IndependentExpressionReductionShift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IndependentExpressionShiftNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicRealizationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralBoundaryExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralCanonicalAmbientModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralCartesianCompactSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactSupportDefs | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactSupportPreservation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactSupportPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationOrdinaryComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationOrdinaryScalarAction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationRealizationData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralComparisonRecursionLaws | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralCompatibleComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransportComplete | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransportHom | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizingFiniteBounds | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizingMappingLimit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizingRoosModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalLimitConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionCoefficientSquares | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionRecursion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralFiniteHomEstimate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralKernelContractions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralKernelTateComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralKernelUnitCounit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralNormalizedComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralNormalizedFamily | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralOpenMateNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralProperTowerTransition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationAssemblyData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralReductionPullbackModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionFunctors | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralSupportRealizationComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralSupportTowerNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCompositorAssociativity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemDualityCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralTateLineConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorLeftShiftUnique | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorRightShiftExt | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorRightShiftUnique | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorShiftProperties | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.KunnethFirstOpenSubstitution | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.KunnethSecondOpenSubstitution | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ListedScalarCoefficientMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.NormalizedRingCompactScalarCocycle | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenBaseChangeReductionSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenBaseChangeSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenBaseChangeSquareData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateCoefficient | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateCompletion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateFinite | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateIntegral | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenDvrRingedIdentification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherenceData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenFactorExchangeRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenFactorOpenRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenFactorProjectionRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenInterchangeReductionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenInterchangeReductionSquares | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenNormalizedProductCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionCompletedSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionOrdinaryRoos | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRestrictionNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenReconstructionEffectivity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenReductionMateLocalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenScalarAdjunctionCounit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenStarShriekScalarMateSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenSupportStepBounds | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenTensorAugmentationLimitSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientCochains | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientGeometry | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OpenTensorReductionSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OrdinaryAmbientProperOpenLaws | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OrdinaryOpenReductionMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.OrdinaryProperOpenInvertibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.PrimitiveCompletionEffectivity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.PrimitiveQuotientAugmentations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralResidueCriterion | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProEtale.InternalFirstResidueOrdinaryComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProEtale.InternalFirstResidueReductionComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProEtale.InternalResidueStacksComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProductCompactificationIdentity | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProjectionRefinementDescent | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProjectionSystemCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProperOpenInterchangeReductionSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProperOpenLambdaReductionSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ProperSupportStepBounds | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.PublishedSystemTensorComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.PullQuotientAugmentationOnGood | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarPreparation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarSupportCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RationalDualizingIdentification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RationalExceptionalIdentifications | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RationalHomIdentifications | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RationalOperationsData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierDatum | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierUnit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.RefinementProjectionCounit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ScalarDenseRefinementSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ScalarSixAdmissibleThickness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCanonicalExtensionComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCtf | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCtfGenerators | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ScalarSixDirectImage | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ScalarSixFiniteGeneration | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ScalarSixNonfiniteGeneration | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ScalarSixPerfectExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisComparisonNormalForm | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SemilinearOpenExternalCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SemilinearOrdinaryCompactificationComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ShortWordCompletionIsomorphism | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ShortWordIntegralDomain | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.StructuralReductionWordSubstitution | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenLambdaExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SystemPullbackCompositorIdentification | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SystemPushCompositionLaws | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SystemPushIdentityPullUnit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SystemTensorLeftShiftUnique | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SystemTensorRightShiftUnique | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.SystemTotalEnrichedTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.TensorAdjunctionReductionSquares | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.TensorExchangeCoherentConclusions | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.TensorExchangeNormalizedModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.TensorExchangePresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.TensorHomTranspositionData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.TensorQuotientAugmentationOnGood | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.ThreeCellCompositor | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.TriangleProjectionCompositorContraction | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.TriangleProjectionNormalForm | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.TriangleProjectionSystemNormalForm | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.VerdierExchangeData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryBinaryProductTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryProductTransposeData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryTripleLeftComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryTripleProductTranspose | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryTripleRightComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.TraceFormula.CompactDirectPowerTransportNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.TraceFormula.CondensedStalkFrobeniusOrbitTrace | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.TraceFormula.FrobeniusCompactPowerExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.TraceFormula.FrobeniusProperPowerExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.TraceFormula.LocalNormalizationStrictRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.TraceFormula.PointConeLiftsChainNaturality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.TraceFormula.WeilUnit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.DerivedHomSingleResolution | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativeBasicComparisons | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativeCompactificationModelComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativeCompatibleTowerCalculation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativeDerivedHomComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalLeftModels | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativeHomPrecompositionQuasiIso | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativeImmersionHeartLocalization | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativeInjectiveAdjunctionModel | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativeOpenProperForgetting | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativeOpenProperInterchange | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativePullbackStarPreservation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.ProperSheafFiniteness | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | unclaimed in local claim records | Same exported API; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed in local claim records | Same exported API; no adaptation. |
| TargetsCheck | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ArtinSchreierDual | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Constituent | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DirectImageUnit | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.GeometricSMul | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LaurentPoints | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LinearCharacters | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Punctual | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RamifiedAtInfinity | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.AdicReconstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.UnitDualDatum | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryGenericRep | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodConstruction | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodExistence | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseSheafEquivalence | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseWeilSheafTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentationTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSections | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationFunctor | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.CoefficientReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.AdicFrobenius | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.AdicSystem | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundedConstructibleUpperShriek | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeOpenImmersion | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeOpenImmersionSheaf | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeStalk | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnit | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitDerived | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitLowerStar | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitRefinement | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.FieldStagePointers | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImageReduction | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralExceptionalAdjoint | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralVerdier | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.PointFiberAlgClosed | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.PointFiberIntegral | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.PointFiberRational | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.RestrictScalars | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalOperations | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.CtfStability | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.FiniteStage | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Reduction | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Remarks | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexVerdierDual | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.AdicAbIdentification | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.AdicConstantSheafLeg | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedLowerStar | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.DerivedForget | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.EtaleBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicHFinite | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ForgetLowerStar | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionSMulUpperStar | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafBasis | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafStageMap | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeApproximation | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeIdentification | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeIntegrality | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeKernel | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeScalarLinear | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeSemilinear | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeTensorBijective | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverEquivalence | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExists | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyLift | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerShriekFiniteness | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarConstantBounded | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarConstantFiniteness | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarConstantFinitenessStratum | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarDevissage | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarDevissageRegular | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarStratumLisse | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarStratumLisseComponents | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarScalar | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeAdic | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLisse | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperTwistedLattice | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.TwistedSection | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.UpperShriek | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.AdicBaseChangeTower | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.AdicSmoothBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstructibleTwoColimit | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstructibleTwoColimitTStructure | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalars | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalarsComp | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalarsConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtensionConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CoefficientSetup | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompletedExchange | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompletedExchangeComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.BaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.CompactFrobenius | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Constructible | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerShriek | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerShriekBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerStar | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.OpenImmersion | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Projection | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.ProjectionPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.RestrictScalarsMate | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.StrictWeilComplex | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.StrictWeilComplexFrobenius | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.StrictWeilComplexTrace | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Trace | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.UpperStarCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.WeilDatum | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChangeAlgClosed | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChangeComplete | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChangeRational | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionExtendScalars | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormulaBounded | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TraceScalarExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.PullbackSquareComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekLocalizing | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaAdic | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaField | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopologicalInvariance | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionConstructible | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionProjection | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionProjectionComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionProjectionIso | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.Statement | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.Additivity | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.CoefficientMorphism | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.CompactPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.CorrespondencePair | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.CurvePieces | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.FibreCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.FibreModel | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.FixedPointScheme | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.Frobenius | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.GenericQuotient | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.HomologyUnit | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.KunnethVerdier | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.LefschetzVerdier | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.LocalTermLocality | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.Main | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.ModelExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.OpenCover | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.OpenSquare | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.PointNormalization | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.Product | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.ProperCompatibility | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.ProperCurve | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforward | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.PullbackFamily | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobenius | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.Stalk | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.SupportedPairing | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.TraceClass | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.WeilBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Homology | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierFunctions | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierInertia | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierIsotypic | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierMul | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierMulGeometric | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierNeg | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPlane | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrivialization | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.BaseChangeField.Cohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.BaseChangeField.Comparison | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalkFrobenius | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalkGaloisInvariants | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalkSpecialization | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStrictHenselization | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ClosedLowerStar | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyAdicConstant | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyAdicConstantExt | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyAdicConstantLattice | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyGeometricConjugacy | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyGeometricEquivalence | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyNonneg | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyProEtale | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyResolution | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologySequence | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CompactSupportAdicConstant | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ConstantTwistWeight | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.Defs | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.DerivedHom | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FieldCoefficientCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FieldCoefficientExtendScalars | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FieldCoefficientForget | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FieldCoefficientFrobeniusTwist | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FieldCoefficientKaroubian | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FieldCoefficientTateTwist | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FieldCoefficientTransition | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FieldCoefficientTriangulated | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FieldCoefficientTwoColimit | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FiniteEtale | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FiniteLeray | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FiniteLowerStar | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FinitePointCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierBaseLinear | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierFirstFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.AffinePlaneAdd | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.ConvolutionKernel | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.KernelComposition | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Reflection | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisseComm | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalkFibre | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.FrobeniusTwist | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.GlobalSectionsUpperStar | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.HigherLowerStarZero | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.IhomCurry | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.IhomLisse.CompWeil | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.IhomLisse.SwapWeil | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.IhomLisse.UpperStar | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.IhomLisse.UpperStarDual | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.IntegralCoefficientCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.Isotypic | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.IsotypicPullback | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.Karoubian | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.KaroubianPointer | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.LSeries | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.LisseExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.Localization | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarTriangulated | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.Operations | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ProjectionFormulaLisse.ExtensionByZero | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerShriek | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerStar | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ProperBaseChange | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.ShiftedSheaf | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.SplitTorsor | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.StalkRationalPoint | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.StalkStrictlyHenselian | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.StalkTensorTrace | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.StrictWeilComplexNotFaithful | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.TensorHomAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.TorsorPairing | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.TraceCupAdicConstant | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunction | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarLowerStar | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunctionWeil | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.SixOperations | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed in local claim records | Same exported API; no adaptation. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | unclaimed in local claim records | Same exported API; no adaptation. |

## Status

landed 20261026T100410-L-14247 2026-10-26 (merge of deliver/T1/Sheaf.Paper.AdicConstructibleFiniteReductions)
