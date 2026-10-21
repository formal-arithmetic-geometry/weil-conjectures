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

/-- Finite reductions with the given Tor interval and the prescribed residue marking.
Source: Stacks Project, proetale.tex, Tag 09C2 (1)-(4), and Tag 09AL for full-faithfulness.
The quotient cocycle and alpha compatibility use the actual scalar-extension adjunction
comparisons; beta is stated for all quotient maps, including identity reductions.

Proof (for stage 3):

1. The finite affine cover makes $X$ quasi-compact: restrict an open cover to each affine,
choose finite subcovers, and take their finite union, using [lem-weil-pbc-affine-scheme-qcqs].
It is locally Noetherian by the stipulated affine-cover definition, hence quasi-separated by
[lem-weil-pbc-locally-noetherian-quasi-separated]. Every $P_n=A/J^n$ is Noetherian: inverse
images of its ideals are finitely generated ideals of $A$, and their generators descend. Thus
the comparison theorems below apply to $X$ and to each discrete coefficient ring $P_n$.
Uses: lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-locally-noetherian-quasi-separated.

2. Choose one K-flat resolution $P\to N$ with flat terms [lem-pc-kflat-resolution]. The
complexes $P\otimes_A P_n$ represent $N_n$ by [lem-pur-derived-change-of-rings] and are K-flat
with flat terms over $P_n$ by [lem-pur-kflat-change-of-rings]. Consequently, for every degree-
zero $P_n$-module sheaf $F$, $N_n\otimes^L_{P_n}F$ is represented by $(P\otimes_A
P_n)\otimes_{P_n}F=P\otimes_AF$. For $m\ge n$, balancing gives
$\rho_{m,n}:N_m\otimes^L_{P_m}P_n\simeq N_n$, represented by $(p\otimes u)\otimes v\mapsto
p\otimes q_{m,n}(u)v$, with inverse $p\otimes v\mapsto(p\otimes1)\otimes v$. For $r\ge m\ge n$
both iterated maps send $((p\otimes u)\otimes v)\otimes w$ to $p\otimes q_{r,n}(u)q_{m,n}(v)w$;
thus these normalizations satisfy the quotient cocycle and commute with maps of representatives.
Uses: lem-pc-kflat-resolution, lem-pur-derived-change-of-rings, lem-pur-kflat-change-of-rings.

3. The assumed Tor tests say exactly that $C$ has Tor amplitude in $[a,b]$ on the étale site.
The given constructible cohomology and boundedness put $C$ in $D^b_c(X_{\mathrm{ét}},P_1)$. By
[det-pe-finite-tor-comparison-noetherian], $N_1\simeq\nu_X^*C$ has the same Tor interval on the
pro-étale site. The constructible comparison [sk-thm-pe-constructible-comparison] also makes its
cohomology constructible. Exactness of comparison inverse image [sk-thm-pe-classical-sheaves]
identifies its cohomology with the pullbacks of those of $C$.
Uses: det-pe-finite-tor-comparison-noetherian, sk-thm-pe-constructible-comparison, sk-thm-pe-
classical-sheaves.

4. Fix $n$ and any degree-zero $P_n$-module sheaf $F$. Its finite filtration $F\supset
JF\supset\cdots\supset J^nF=0$ has quotients $G_i=J^iF/J^{i+1}F$ annihilated by $J$. By Step 2,
$N_n\otimes^L_{P_n}G_i=N_1\otimes^L_{P_1}G_i$, which has no cohomology outside $[a,b]$ by Step
3. Tensoring the short exact sequences of this filtration with $P$ remains termwise exact since
its terms are flat [def-pc-flat-sheaf-modules]. Their long exact cohomology sequences [lem-weil-
pbc-complex-ses-homology-long-exact], inducting up from $J^nF=0$, therefore give the same
vanishing for $N_n\otimes^L_{P_n}F$. This proves the required Tor amplitude for every $n$ by
[def-weil-proetale-tor-amplitude]; taking $F=P_n$ also proves that $N_n$ itself is supported in
$[a,b]$.
Uses: def-pc-flat-sheaf-modules, def-weil-proetale-tor-amplitude, lem-pur-kflat-change-of-rings,
lem-weil-pbc-complex-ses-homology-long-exact.

5. The given local derived $J\underline A$-completeness is precisely the complete-subcategory
condition in [lem-sp-completed-pullback-adjunction]. Its completion adjunction identifies the
unit on a complete object with an isomorphism, so $N\simeq R\varprojlim_nN_n$. To retain the
upper endpoint $b$, tensor $0\to J^n/J^{n+1}\to P_{n+1}\to P_n\to0$ with the flat-term complex
$P$. The first resulting complex is $N_1\otimes^L_{P_1}\underline{J^n/J^{n+1}}$ by Step 2 and
has Tor-test cohomology in $[a,b]$. The long exact sequence [lem-weil-pbc-complex-ses-homology-
long-exact] gives an epimorphism $H^b(N_{n+1})\to H^b(N_n)$. Work throughout over the common
sheaf $\underline A$, forgetting the quotient scalar actions. Write $\mathcal
M=\Mod(X_{\mathrm{proét}},\underline A)$. Its countable products are exact by [det-pe-products-
exact]; it is Grothendieck abelian by [lem-weil-pbc-ring-sheaves-grothendieck] and has enough
injectives by [lem-sp-grothendieck-enough-injectives]. Clause (3) of [lem-weil-derived-limit-
existence] therefore identifies the K-injective strict-tower limit in the completion formula
with a derived limit in the Roos-triangle sense. For the strict representatives $T_n=P\otimes_A
P_n$ from Step 2, [det-pe-products-derived] identifies their termwise product $V=\prod_nT_n$
with the product in $D(\mathcal M)$. The chain map $1-T:V\to V$ satisfies
$\mathrm{pr}_n(1-T)=\mathrm{pr}_n-t_n\mathrm{pr}_{n+1}$, where $t_n:T_{n+1}\to T_n$ is induced
by the quotient. Rotating the cone triangle in [def-weil-abstract-derived-category] by TR2 of
[def-weil-triangulated-category] makes $\operatorname{Cone}(1-T)[-1]$ another derived limit of
this same tower. Clause (1) of [lem-weil-derived-limit-existence] supplies an isomorphism
between these two limit objects; only the cohomology bounds, not a canonical comparison map, are
needed here. Now [det-pe-milnor-sequence] gives $0\to R^1\!\varprojlim H^{q-1}(N_n)\to
H^q(N)\to\varprojlim H^q(N_n)\to0$. Outside $[a,b]$ both end terms are zero, except potentially
the left term for $q=b+1$; that term is zero by [det-pe-milnor-epimorphic] and the epimorphisms
just proved. Hence $H^q(N)=0$ for $q\notin[a,b]$.
Uses: lem-sp-completed-pullback-adjunction, det-pe-milnor-sequence, det-pe-milnor-epimorphic,
def-pc-flat-sheaf-modules, det-pe-products-exact, lem-weil-pbc-ring-sheaves-grothendieck, lem-
sp-grothendieck-enough-injectives, lem-weil-derived-limit-existence, det-pe-products-derived,
def-weil-abstract-derived-category, def-weil-triangulated-category, lem-weil-pbc-complex-ses-
homology-long-exact.

6. Constructibility in [sk-thm-pe-constructible-comparison] is local on $X$, so Step 3 supplies,
for each of the finitely many degrees $a\le q\le b$, an open covering of $X$ on whose members
$H^q(N_1)$ has a finite stratification. Intersecting members of these finitely many coverings
gives one open covering of $X$ by opens $U$ on which every $H^q(N_1)$, $a\le q\le b$, has a
finite stratification. Restriction to $U$ along the open immersion is the exact pro-étale
restriction of [def-weil-pbc-proetale-operations] and commutes with the reductions by [lem-weil-
pbc-ringed-topoi-derived-tensor-pullback], and constructibility of $N_n$ is checked on such $U$;
so fix one $U$ and write $X$ for it in the rest of this step (only the scheme structure of $X$
and of its affine opens is used below). Refine the finitely many stratifications of $H^q(N_1)$,
$a\le q\le b$, as follows. For each tuple of input strata take their finite fibre product over
$X$ [def-pc-fibre-product], and omit the empty products. This is the scheme-theoretic
intersection with its actual projection morphisms to all input strata. Indeed write each input
immersion as closed in an open neighborhood [def-weil-closed-immersion]; on the intersection of
these open neighborhoods and on an affine $\operatorname{Spec}R$ therein, the product is $\opera
torname{Spec}(R/I_1\otimes_R\cdots\otimes_RR/I_s)=\operatorname{Spec}(R/(I_1+\cdots+I_s))$ by
[lem-weil-pbc-fibre-product-affine-spectra]. The ring equality follows from
$1\otimes\cdots\otimes1\mapsto1$ and the quotient maps as mutual inverses, so these products are
closed in that open intersection. Their images are the finite intersections of the input
subsets, hence pairwise disjoint and covering $X$. For a projection $h:T\to S$ to an input
stratum, pull its pro-étale trivializing covering $\{V_i\to S\}$ back by the covering-preserving
base-change functor of [def-weil-proetale-inverse-image]. The inverse image preserves finite
limits and all colimits by [lem-weil-pbc-left-exact-site-inverse-image-tensor]. It therefore
preserves constant sheaves: the constant set sheaf with value $M$ is the coproduct of $M$ copies
of the terminal sheaf (maps into any sheaf are $M$-indexed global sections); naturality in $M$
preserves the ring and module operations. Its constant-ring isomorphism agrees with $c^h_{P_1}$
because both are adjoint to the same constant sections. On $T\times_S V_i$, [lem-weil-pbc-
localize-ringed-site-morphism] identifies the restriction of $h^*$ with the inverse image of the
localized morphism; the same constant-sheaf argument applies there. Thus each pulled-back
covering trivializes the restriction by the same finite-type module. The adjoint-compatible
composition isomorphism [lem-weil-pbc-site-morphism-composition] identifies the iterated
restrictions with restriction along the actual composite immersion. Thus the resulting finite
stratification makes every cohomology sheaf of $N_1$ locally constant of finite type. Fix one
such stratum $i:S\to X$ and $n\ge1$. Exact pro-étale restriction [def-weil-pbc-proetale-
operations] and the derived tensor pullback comparison [lem-weil-pbc-ringed-topoi-derived-
tensor-pullback] identify $(N_n|_S)\otimes^L_{P_n}P_1$ with $N_1|_S$. Apply [lem-weil-pbc-
nilpotent-reduction-lissity] on $S_{\mathrm{proét}}$ with coefficient ring $B=P_n$, ideal
$I=J/J^n$, and complex $K=N_n|_S$. Here $K$ is bounded above by Step 4, $B$ is Noetherian by
Step 1, and $I^n=0$. Its final clause therefore makes every $H^q(N_n|_S)$ locally constant of
finite type over $P_n$. This proves constructibility of all the reductions on that finite
stratification. No finiteness of the underlying sets of $P_n$ is used.
Uses: def-weil-pbc-proetale-operations, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-
weil-pbc-nilpotent-reduction-lissity, def-pc-fibre-product, def-weil-closed-immersion, lem-weil-
pbc-fibre-product-affine-spectra, def-weil-proetale-inverse-image, lem-weil-pbc-left-exact-site-
inverse-image-tensor, lem-weil-pbc-localize-ringed-site-morphism, lem-weil-pbc-site-morphism-
composition, def-weil-pbc-constant-sheaf, sk-thm-pe-constructible-comparison.

7. For each $n\ge2$, Steps 4 and 6 put $N_n$ in the bounded constructible pro-étale category for
$P_n$. The equivalence [sk-thm-pe-constructible-comparison] gives $C_n\in
D^b_c(X_{\mathrm{ét}},P_n)$ and $\alpha_n:\nu_X^*C_n\simeq N_n$. Use $C_1=C$ and the prescribed
isomorphism for $\alpha_1$. The reverse implication of [det-pe-finite-tor-comparison-noetherian]
puts every $C_n$ in the same Tor interval $[a,b]$. This uses each ring $P_n$ separately, never a
finite-ring or perfect-$A$-module identification.
Uses: sk-thm-pe-constructible-comparison, det-pe-finite-tor-comparison-noetherian.

8. For $m\ge n$, put $Q_{m,n}=C_m\otimes^L_{P_m}P_n$ on the étale site. It has Tor amplitude
$[a,b]$: for every $P_n$-module sheaf $F$, a flat-term K-flat representative $R\to C_m$ gives
the chain isomorphism $(R\otimes_{P_m}P_n)\otimes_{P_n}F\to R\otimes_{P_m}F$, $(r\otimes
v)\otimes f\mapsto r\otimes vf$, with inverse $r\otimes f\mapsto(r\otimes1)\otimes f$,
identifying $Q_{m,n}\otimes^L_{P_n}F$ with $C_m\otimes^L_{P_m}F$, which has the required
vanishing by Step 7. In particular $Q_{m,n}$ is bounded. It also has constructible cohomology.
Indeed, as in Step 6, pass to an open covering of $X$ on whose members the finitely many nonzero
$H^q(C_m)$ all have finite stratifications (étale restriction to an open is exact by [prop-weil-
pbc-inverse-image-modules-exact] and commutes with the reduction by [lem-weil-pbc-ringed-topoi-
derived-tensor-pullback]), and on each member apply the explicit fibre-product refinement
construction of Step 6 to these finite stratifications, obtaining actual projection morphisms to
the input strata. The étale coverings pull back to coverings by [lem-weil-pbc-etale-covering-
base-change]; the localization and constant-sheaf argument of Step 6 applies to the étale
inverse image as well, using the inverse-image adjunction in [prop-weil-pbc-inverse-image-
modules-exact]. Exact étale restriction [prop-weil-pbc-inverse-image-modules-exact] and tensor
pullback [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] reduce to each stratum; there [lem-
weil-pbc-locally-constant-tensor] applies to $C_m$ and the constant finite-type $P_m$-module
$P_n$ in degree zero, both bounded above. It gives locally constant finite-type cohomology. The
resulting local trivializations, initially $P_m$-linear, are $P_n$-linear because the scalar
action factors through $P_m\twoheadrightarrow P_n$; their model modules are finitely generated
over $P_n$ by the same generators. Thus $Q_{m,n}\in D^b_c(X_{\mathrm{ét}},P_n)$.
Uses: lem-pc-kflat-resolution, lem-pur-kflat-change-of-rings, prop-weil-pbc-inverse-image-
modules-exact, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-locally-constant-
tensor, lem-weil-pbc-etale-covering-base-change, lem-weil-pbc-localize-ringed-site-morphism,
lem-weil-pbc-site-morphism-composition.

9. Derived tensor pullback [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] and the constant-
coefficient identification in [sk-thm-pe-classical-sheaves] identify $\nu_X^*Q_{m,n}$ with
$\nu_X^*C_m\otimes^L_{P_m}P_n$. Therefore $\alpha_n^{-1}\rho_{m,n}(\alpha_m\otimes^LP_n)$ is an
isomorphism $\nu_X^*Q_{m,n}\to\nu_X^*C_n$. Both its source and target are in the bounded
constructible comparison domain by Steps 7 and 8. Full faithfulness of [sk-thm-pe-constructible-
comparison] lifts it uniquely to $\beta_{m,n}:Q_{m,n}\to C_n$; lifting its inverse shows that
this is an isomorphism. Taking $m=n+1$ gives the required $\beta_n$ and, by their definition,
the stated compatibility equation with $\alpha_n$ and $\rho_n=\rho_{n+1,n}$.
Uses: lem-weil-pbc-ringed-topoi-derived-tensor-pullback, sk-thm-pe-classical-sheaves, sk-thm-pe-
constructible-comparison.

10. For $r\ge m\ge n$, compare $\beta_{r,n}$ with $\beta_{m,n}\circ(\beta_{r,m}\otimes^LP_n)$
under canonical tensor balancing. Apply $\nu_X^*$ and then $\alpha_n$. By Step 9 the latter
composite becomes $\rho_{m,n}\circ(\rho_{r,m}\otimes^LP_n)\circ(\alpha_r\otimes^LP_n)$: the
intervening $\alpha_m^{-1}$ and $\alpha_m$ cancel. Step 2 identifies this with
$\rho_{r,n}\circ(\alpha_r\otimes^LP_n)$, the image of the former map. Faithfulness of [sk-thm-
pe-constructible-comparison] gives equality. For $m=n$, Step 2 gives the unit normalization
$\rho_{n,n}$; hence the compared map is $\alpha_n^{-1}\rho_{n,n}(\alpha_n\otimes^LP_n)$, which
is the unit map $C_n\otimes^L_{P_n}P_n\to C_n$. Faithfulness gives this identity normalization
for $\beta_{n,n}$. This proves the quotient cocycle, retaining exactly the original $C_1$ and
residue marking chosen in Step 7.
Uses: sk-thm-pe-constructible-comparison, lem-pur-kflat-change-of-rings.

(blueprint: lem-sfb-adic-constructible-finite-reductions) -/
theorem adic_constructible_finite_reductions (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A) (hcomplete : adicFiniteComplete.{u, v} X A J N)
    (C : adicFiniteEtale.{u, v} X J 0)
    (hC : IsCoefficientBoundedConstructibleEtale.{u, v} X (adicFiniteCoeff J 0) C)
    (e : (adicFinitePullback.{u, v} X (adicFiniteCoeff J 0)).obj C ≅
      adicFiniteReduction.{u, v} X J N 0)
    (a b : ℤ) (hab : a ≤ b)
    (hTor : HasCoefficientModelTorAmplitude
      (constant (smallModelComparisonEtaleTopology.{u, v} X) (adicFiniteCoeff J 0)) C a b) :
    (∃ hp : HasProduct (adicFiniteUnderlying.{u, v} X J N),
      @IsDerivedLimit _ _ _ _ _ _ _ _ hp (adicFiniteTransition.{u, v} X J N) N) ∧
    (∀ q : ℤ, (q < a ∨ b < q) → IsZero ((coefficientModelCohomology
      (constant (coefficientProEtaleModelTopology.{u, v} X) A) q).obj N)) ∧
    (∀ n : ℕ, HasCoefficientProEtaleTorAmplitude.{u, v} X (adicFiniteCoeff J n)
      (adicFiniteReduction.{u, v} X J N n) a b) ∧
    ∃ (Cn : ∀ n : ℕ, adicFiniteEtale.{u, v} X J n)
      (alpha : ∀ n : ℕ, (adicFinitePullback.{u, v} X (adicFiniteCoeff J n)).obj (Cn n) ≅
        adicFiniteReduction.{u, v} X J N n)
      (beta : ∀ {m n : ℕ} (h : n ≤ m),
        (adicFiniteExtension (smallModelComparisonEtaleTopology.{u, v} X)
          (adicFiniteFactor J h)).obj (Cn m) ≅ Cn n),
      (∀ n : ℕ, IsCoefficientBoundedConstructibleEtale.{u, v} X (adicFiniteCoeff J n) (Cn n)) ∧
      (∀ n : ℕ, HasCoefficientModelTorAmplitude
        (constant (smallModelComparisonEtaleTopology.{u, v} X) (adicFiniteCoeff J n))
          (Cn n) a b) ∧
      (∃ hzero : Cn 0 = C,
        (adicFinitePullback.{u, v} X (adicFiniteCoeff J 0)).map (eqToIso hzero).hom ≫ e.hom =
          (alpha 0).hom) ∧
      (∀ (r m n : ℕ) (hnm : n ≤ m) (hmr : m ≤ r),
        (adicFiniteExtensionComp (smallModelComparisonEtaleTopology.{u, v} X)
          (adicFiniteFactor J hmr) (adicFiniteFactor J hnm)
          (adicFiniteFactor J (hnm.trans hmr)) (adicFiniteFactorComp J hnm hmr)).hom.app
            (Cn r) ≫ (beta (hnm.trans hmr)).hom =
        (adicFiniteExtension (smallModelComparisonEtaleTopology.{u, v} X)
          (adicFiniteFactor J hnm)).map (beta hmr).hom ≫ (beta hnm).hom) ∧
      (∀ (m n : ℕ) (h : n ≤ m),
        (adicFinitePullback.{u, v} X (adicFiniteCoeff J n)).map (beta h).hom ≫ (alpha n).hom =
        (adicFiniteComparison.{u, v} X (adicFiniteFactor J h)).inv.app (Cn m) ≫
          (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X)
            (adicFiniteFactor J h)).map (alpha m).hom ≫ (adicFiniteRho.{u, v} X J N h).hom) := by
  sorry

end AlgebraicGeometry.Scheme
