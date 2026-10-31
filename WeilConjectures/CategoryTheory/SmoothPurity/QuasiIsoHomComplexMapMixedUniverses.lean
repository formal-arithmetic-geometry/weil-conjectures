/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
import WeilConjectures.CategoryTheory.SiteModuleExtensionByZeroExact
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexProjections
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor

/-! # Quasi-isomorphism invariance of the Hom complex with smaller coefficient rings

Source: Stacks Project, Tags 03DI, 03DJ, 08FI, 0A8Y, 0A94 and 0A95.
(blueprint: lem-pur-rhom-well-defined-mixed-universes).
The sectionwise proof uses rings in r and module sections in max u v r throughout.
The private helpers generalize the existing independent-universe proofs without changing
any existing interface or replacing the ring sheaf.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
namespace MixedHom
attribute [local irreducible] homComplexFunctor

/-- Restriction of a quasi-isomorphism of module complexes to `C/U` is a quasi-isomorphism.
Source: Stacks Project, Section 18.19 (Tag 03DH), restriction exactness recalled in
Lemma 18.19.4 (Tag 03DK), as used in Tag 0A95.

Proof: restriction to the slice site preserves kernels: kernels of module sheaves are
computed sectionwise. It also preserves cokernels: the presheaf cokernel is computed
sectionwise and restriction commutes with sheafification. For the latter, a covering
sieve of an object `(V,f)` of `C/U` is precisely a covering sieve of `V` equipped with
its forced maps to `U`; the local representatives and local equalities used by
sheafification are therefore identical on both sites. Thus restriction is an exact
additive functor of abelian categories. Exact functors preserve homology, by preserving
the kernels and cokernels defining it. The restricted homology map is consequently
isomorphic to restriction of the original homology map, hence is invertible. This works
for arbitrary Grothendieck topologies, including the trivial and maximal ones, and
requires no boundedness of the complexes. -/
private theorem localizedModule_restriction_quasiIsoOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J RingCat.{r}) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (hzero : (SheafOfModules.overFunctor.{max u v r} R U).PreservesZeroMorphisms)
    {L' L : CochainComplex (SheafOfModules.{max u v r} R) ℤ}
    (t : L' ⟶ L) [QuasiIso t] :
    letI := hzero
    QuasiIso (((SheafOfModules.overFunctor.{max u v r} R U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map t) := by
  let := hzero
  let F := SheafOfModules.overFunctor.{max u v r} R U
  obtain ⟨hlim, hcolim⟩ := SheafOfModules.overFunctor_exact_ofUniverses.{u, v, r} R U
  let := hlim
  let := hcolim
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  exact HomologicalComplex.quasiIso_map_of_preservesHomology t F

private theorem fan_projection_bijective.{t} {ι : Type} {X : ι → Type t}
    {P : Type t} (π : ∀ i, P ⟶ X i) (h : Limits.IsLimit (Limits.Fan.mk P π)) :
    Function.Bijective (fun x i ↦ π i x) := by
  let e := h.conePointUniqueUpToIso (Limits.Types.productLimitCone X).isLimit
  have he (x : P) (i : ι) : e.hom x i = π i x :=
    ConcreteCategory.congr_hom (h.conePointUniqueUpToIso_hom_comp
      (Limits.Types.productLimitCone X).isLimit ⟨i⟩) x
  have hf : (fun x i ↦ π i x) = e.toEquiv := by
    funext x i
    exact (he x i).symm
  rw [hf]
  exact e.toEquiv.bijective

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionToLocalizedHom
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{r}) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (A B : SheafOfModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (φ : (SheafOfModules.homObj (R := R) A B).val.obj (op U)) :
    (SheafOfModules.overFunctor _ U).obj A ⟶
      (SheafOfModules.overFunctor _ U).obj B := ⟨φ⟩

private noncomputable def sectionToLocalizedHomAdd
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{r}) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (A B : SheafOfModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    (SheafOfModules.homObj (R := R) A B).val.obj (op U) →+
      ((SheafOfModules.overFunctor _ U).obj A ⟶
        (SheafOfModules.overFunctor _ U).obj B) :=
  AddMonoidHom.mk' (sectionToLocalizedHom.{u, v, r} R U A B) (fun _ _ ↦ rfl)

private noncomputable def familyCochainEquiv
    {A : Type*} [Category A] [Preadditive A]
    (L I : CochainComplex A ℤ) (n : ℤ) :
    (∀ p : ℤ, L.X p ⟶ I.X (p + n)) ≃
      CochainComplex.HomComplex.Cochain L I n where
  toFun f := CochainComplex.HomComplex.Cochain.mk (fun p q hpq ↦ by subst q; exact f p)
  invFun c p := c.v p (p + n) rfl
  left_inv f := rfl
  right_inv c := by
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    subst q
    rfl

private noncomputable def familyCochainAddEquiv
    {A : Type*} [Category A] [Preadditive A]
    (L I : CochainComplex A ℤ) (n : ℤ) :
    (∀ p : ℤ, L.X p ⟶ I.X (p + n)) ≃+
      CochainComplex.HomComplex.Cochain L I n :=
  { familyCochainEquiv L I n with
    map_add' := fun f g ↦ by
      apply CochainComplex.HomComplex.Cochain.ext
      intro p q hpq
      subst q
      rfl }

private lemma cocycle_prepost_v
    {A : Type*} [Category A] [Preadditive A]
    {L L' I I' : CochainComplex A ℤ} (t : L' ⟶ L) (s : I' ⟶ I)
    {n : ℤ} (z : CochainComplex.HomComplex.Cocycle L I' n)
    (p q : ℤ) (hpq : p + n = q) :
    (((z.precomp t).postcomp s).val.v p q hpq) =
      t.f p ≫ z.val.v p q hpq ≫ s.f q := by
  simp only [CochainComplex.HomComplex.Cocycle.postcomp_coe,
    CochainComplex.HomComplex.Cocycle.precomp_coe,
    CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v, Category.assoc]

private lemma cocycle_prepost_hom
    {A : Type*} [Category A] [Preadditive A]
    {L L' I I' : CochainComplex A ℤ} (t : L' ⟶ L) (s : I' ⟶ I)
    {n : ℤ} (z : CochainComplex.HomComplex.Cocycle L I' n) :
    CochainComplex.HomComplex.Cocycle.equivHomShift.symm ((z.precomp t).postcomp s) =
      t ≫ CochainComplex.HomComplex.Cocycle.equivHomShift.symm z ≫
        (shiftFunctor _ n).map s := by
  rw [CochainComplex.HomComplex.Cocycle.equivHomShift_symm_postcomp,
    CochainComplex.HomComplex.Cocycle.equivHomShift_symm_precomp, Category.assoc]

private theorem sectionToLocalizedHom_bijective
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{r}) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (A B : SheafOfModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    Function.Bijective (sectionToLocalizedHomAdd R U A B) := by
  exact ((SheafOfModules.fullyFaithfulForget _).homEquiv
    (X := (SheafOfModules.overFunctor _ U).obj A)
    (Y := (SheafOfModules.overFunctor _ U).obj B)).symm.bijective

set_option maxHeartbeats 100000 in
-- Chosen products and section evaluation require extra elaboration heartbeats.
set_option backward.isDefEq.respectTransparency false in
/-- Product projections identify degreewise sections with all localized cochains.
Source: Stacks Project, Tag 0A8Y, Equation (21.34.0.1).

Proof: the product cone specified by homComplex_exists remains a product after
forgetting module sheaves, evaluating at U, and forgetting to abelian groups.
Its factors are localized presheaf-module morphisms by the construction of
internal Hom. The fully faithful forgetful functor from localized module sheaves
to presheaf modules identifies each factor with localized sheaf-module morphisms.
A degree-n external cochain is exactly a family of these morphisms indexed by p,
with target degree p+n. The product universal property supplies the forward map
and inverse; the projection formulas prove both inverse laws. Each projection and
the inverse preserve addition, so this is an additive equivalence. Reindexing q
along p + n = q gives the displayed formula. No finite support or boundedness is
required. If either complex is zero every factor and the product are zero, and
for n=0 the same construction gives arbitrary degree-preserving families. -/
private theorem homComplex_sections_cochainsOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{r}) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (L I : CochainComplex
      (SheafOfModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
    let E := (SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v r} (R₀.obj.obj (op U)))
        AddCommGrpCat.{max u v r}).mapHomologicalComplex (ComplexShape.up ℤ)
    letI := module_overFunctor_preservesZero.{u, v, max u v r, r} R₀ U
    let res := (SheafOfModules.overFunctor.{max u v r} R₀ U).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let S := E.obj ((((homComplexFunctor (R := R)).obj (op L)).obj I))
    let π := Classical.choose
      (homComplex_projections_exists.{u, v, max u v r, r} (J := J) (R := R))
    ∃ e : ∀ n : ℤ, S.X n ≃+
        CochainComplex.HomComplex.Cochain (res.obj L) (res.obj I) n,
      ∀ (n : ℤ) (x : S.X n) (p q : ℤ) (hpq : p + n = q),
        (e n x).v p q hpq = sectionToLocalizedHom R U (L.X p) (I.X q)
          (((π L I n p q hpq).val.app (op U)) x) := by
  classical
  intro R₀ E res S π
  let E₀ := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
    forget₂ (ModuleCat.{max u v r} (R₀.obj.obj (op U))) AddCommGrpCat.{max u v r}
  let f (n : ℤ) : S.X n →+ CochainComplex.HomComplex.Cochain (res.obj L) (res.obj I) n :=
    (familyCochainAddEquiv (res.obj L) (res.obj I) n).toAddMonoidHom.comp
      (AddMonoidHom.pi (fun p : ℤ ↦
        (sectionToLocalizedHomAdd R U (L.X p) (I.X (p + n))).comp
          ((π L I n p (p + n) rfl).val.app (op U)).hom.toAddMonoidHom))
  have hf (n : ℤ) : Function.Bijective (f n) := by
    let H := fun p : ℤ ↦ SheafOfModules.homObj (L.X p) (I.X (p + n))
    have hlim := (Classical.choose_spec
      (homComplex_projections_exists.{u, v, max u v r, r}
        (J := J) (R := R))).1 L I n
    let h := Limits.isLimitFanMkObjOfIsLimit (E₀ ⋙ forget AddCommGrpCat.{max u v r}) H
      (fun p ↦ π L I n p (p + n) rfl) hlim.some
    let e₁ := Equiv.ofBijective _ (fan_projection_bijective.{max u v r} _ h)
    let e₂ := Equiv.piCongrRight (fun p : ℤ ↦
      Equiv.ofBijective _ (sectionToLocalizedHom_bijective R U (L.X p) (I.X (p + n))))
    let e₃ := familyCochainEquiv (res.obj L) (res.obj I) n
    have hh : (f n : _ → _) = (e₁.trans e₂ |>.trans e₃) := by
      funext x
      apply CochainComplex.HomComplex.Cochain.ext
      intro p q hpq
      subst q
      rfl
    rw [hh]
    exact (e₁.trans e₂ |>.trans e₃).bijective
  refine ⟨fun n ↦ AddEquiv.ofBijective (f n) (hf n), ?_⟩
  intro n x p q hpq
  subst q
  rfl


private lemma section_sub_units
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    {R₀ : Sheaf J RingCat.{r}} (U : C)
    {M N : SheafOfModules.{max u v r} R₀} (f g : M ⟶ N)
    (n : ℤˣ) (x : M.val.obj (op U)) :
    ((f - n • g).val.app (op U)) x =
      (f.val.app (op U)) x - n • (g.val.app (op U)) x := by
  let V := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U)
  change (V.map (f - n • g)).hom x = _
  rw [Functor.map_sub]
  simp only [Units.smul_def, Functor.map_zsmul, ModuleCat.hom_sub,
    ModuleCat.hom_zsmul, LinearMap.sub_apply, LinearMap.smul_apply]
  rfl

private lemma sheaf_units_smul_val
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    {R₀ : Sheaf K RingCat.{r}}
    {M N : SheafOfModules.{max u v r} R₀} (n : ℤˣ) (f : M ⟶ N) :
    (n • f).val = n • f.val := by
  change (SheafOfModules.forget R₀).map (n • f) = _
  simp only [Units.smul_def, Functor.map_zsmul]
  rfl

private lemma sheaf_add_units_app
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    {R₀ : Sheaf K RingCat.{r}}
    {M N : SheafOfModules.{max u v r} R₀} (f g : M ⟶ N) (n : ℤˣ) (W : Dᵒᵖ) :
    (f + n • g).val.app W = f.val.app W + n • g.val.app W := by
  rw [SheafOfModules.add_val, sheaf_units_smul_val.{u, v, r}, PresheafOfModules.add_app]
  simp only [Units.smul_def, PresheafOfModules.zsmul_app]

private lemma section_sub_units_component
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{r}) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    {A B M : SheafOfModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    (f g : M ⟶ SheafOfModules.homObj (R := R) A B) (n : ℤˣ)
    (x : M.val.obj (op U)) (W : (Over U)ᵒᵖ) :
    (((f - n • g).val.app (op U)) x).app W =
      ((f.val.app (op U)) x).app W - n • ((g.val.app (op U)) x).app W := by
  rw [section_sub_units.{u, v, r}]
  change (((f.val.app (op U)) x - (n : ℤ) • (g.val.app (op U)) x) :
    (PresheafOfModules.restrictOver R.obj U).obj A.val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj B.val).app W = _
  rw [PresheafOfModules.sub_app, PresheafOfModules.zsmul_app]
  rfl

set_option maxHeartbeats 100000 in
-- Evaluating chosen Hom-complex projections requires extra elaboration heartbeats.
/-- Any degreewise identification given by the section projections respects differentials.
Source: Stacks Project, Tag 0A8X, differential of the Hom complex; Tag 0A8Y.

Proof: compare the two external cochains on each component p,q with p+j=q.
For j=i+1, apply the differential projection identity of homComplex_exists at
q'=p+i and p'=p+1, then evaluate at U and at each localized object W.
Evaluation preserves subtraction and integer scalar multiplication. Internal Hom
postcomposition and precomposition evaluate to composition with the restricted
differentials. Substitute the given component formulas for e in degree i and j.
Mathlib's external differential is the first composite plus j.negOnePow times
the second composite; j=i+1 gives j.negOnePow=-i.negOnePow, exactly the internal
Hom differential. Extensionality of module-sheaf morphisms and cochains proves
the equality. No bijectivity or cycle condition is used, so this step is separate
from the product universal property and the homology quotient argument. At zero
complexes both sides vanish; at i=0 the formula is d_I f - f d_L; at i=-1 it is
 d_I f + f d_L. Products allow arbitrary unbounded families. -/
private theorem homComplex_sections_cochains_commOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{r}) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (L I : CochainComplex
      (SheafOfModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
    let E := (SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v r} (R₀.obj.obj (op U)))
        AddCommGrpCat.{max u v r}).mapHomologicalComplex (ComplexShape.up ℤ)
    letI := module_overFunctor_preservesZero.{u, v, max u v r, r} R₀ U
    let res := (SheafOfModules.overFunctor.{max u v r} R₀ U).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let S := E.obj ((((homComplexFunctor (R := R)).obj (op L)).obj I))
    let π := Classical.choose
      (homComplex_projections_exists.{u, v, max u v r, r} (J := J) (R := R))
    ∀ (e : ∀ n : ℤ, S.X n ≃+
        CochainComplex.HomComplex.Cochain (res.obj L) (res.obj I) n),
      (∀ (n : ℤ) (x : S.X n) (p q : ℤ) (hpq : p + n = q),
        (e n x).v p q hpq = sectionToLocalizedHom R U (L.X p) (I.X q)
          (((π L I n p q hpq).val.app (op U)) x)) →
      ∀ (i j : ℤ), i + 1 = j → ∀ x : S.X i,
        e j (S.d i j x) = CochainComplex.HomComplex.δ i j (e i x) := by
  classical
  intro R₀ E res S π e he₀ i j hij x
  have he (n : ℤ) (x : S.X n) (p q : ℤ) (hpq : p + n = q) (W : (Over U)ᵒᵖ) :=
    congrArg (fun f ↦ f.val.app W) (he₀ n x p q hpq)
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  apply SheafOfModules.hom_ext
  ext W y
  rw [he]
  have hd := (Classical.choose_spec
    (homComplex_projections_exists.{u, v, max u v r, r} (J := J) (R := R))).2.1
    L I i j p q (p + i) (p + 1) hij hpq rfl (by omega)
  change ((((homComplexFunctor (R := R)).obj (op L)).obj I)).d i j ≫ π L I j p q hpq = _ at hd
  have hx := congrArg (fun f ↦ ((f.val.app (op U)) x).app W) hd
  have hx' := section_sub_units_component.{u, v, r} R U
    (π L I i p (p + i) rfl ≫ SheafOfModules.homObjMap (𝟙 (L.X p)) (I.d (p + i) q))
    (π L I i (p + 1) q (by omega) ≫
      SheafOfModules.homObjMap (L.d p (p + 1)) (𝟙 (I.X q))) i.negOnePow x W
  have hx := hx.trans hx'
  conv_rhs =>
    rw [CochainComplex.HomComplex.δ_v i j hij (e i x) p q hpq
      (p + i) (p + 1) (by omega) rfl]
  simp only [sheaf_add_units_app.{max u v, v, r}, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, he]
  have hs : j.negOnePow = -i.negOnePow := by rw [← hij, Int.negOnePow_succ]
  simp only [hs, Units.neg_smul, ← sub_eq_add_neg]
  exact congrArg (fun f ↦ f.hom y) hx

set_option maxHeartbeats 100000 in
-- Elaborating chosen products through section evaluation requires extra heartbeats.
set_option backward.isDefEq.respectTransparency false in
/-- The canonical shifted section comparison, specified on cocycle representatives.
Source: Stacks Project, Tag 0A8Y, Equation (21.34.0.1).

Proof: sections preserve the product cone specifying the sheaf Hom complex.
Its projections therefore identify degree-n sections with all degree-n cochains
between the restricted complexes. The differential projection formula identifies
the kernel with Mathlib's cocycles, giving e with the component formula below.
The same formula in degree n-1 identifies images of differentials with coboundaries.
Thus e descends to a bijection of the quotients. Compose that bijection with
Mathlib's equivalence from cohomology classes to shifted homotopy-category maps
to obtain a. On cocycles this composite is the quotient of equivHomShift.symm,
which proves the asserted representative formula. This construction works for
unbounded complexes since it uses products. Zero complexes give singleton
quotients; n=0 is the usual unshifted comparison. -/
private theorem homComplex_sections_canonical_comparisonOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{r}) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (L I : CochainComplex
      (SheafOfModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (n : ℤ) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
    let E := (SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v r} (R₀.obj.obj (op U)))
        AddCommGrpCat.{max u v r}).mapHomologicalComplex (ComplexShape.up ℤ)
    letI := module_overFunctor_preservesZero.{u, v, max u v r, r} R₀ U
    let res := (SheafOfModules.overFunctor.{max u v r} R₀ U).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Q := HomotopyCategory.quotient (SheafOfModules.{max u v r} (R₀.over U))
      (ComplexShape.up ℤ)
    let S := E.obj ((((homComplexFunctor (R := R)).obj (op L)).obj I))
    let π := Classical.choose
      (homComplex_projections_exists.{u, v, max u v r, r} (J := J) (R := R))
    ∃ e : S.cycles n ≃ CochainComplex.HomComplex.Cocycle (res.obj L) (res.obj I) n,
      (∀ (z : S.cycles n) (p q : ℤ) (hpq : p + n = q),
        (e z).val.v p q hpq = sectionToLocalizedHom R U (L.X p) (I.X q)
          (((π L I n p q hpq).val.app (op U)) (S.iCycles n z))) ∧
      ∃ a : S.homology n ≃ (Q.obj (res.obj L) ⟶ Q.obj ((res.obj I)⟦n⟧)),
        ∀ z : S.cycles n, a (S.homologyπ n z) =
          Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (e z)) := by
  classical
  let R₀ := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
  let := module_overFunctor_preservesZero.{u, v, max u v r, r} R₀ U
  let res : CochainComplex (SheafOfModules.{max u v r} R₀) ℤ ⥤
      CochainComplex (SheafOfModules.{max u v r} (R₀.over U)) ℤ :=
    (SheafOfModules.overFunctor.{max u v r} R₀ U).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let E := (SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
    forget₂ (ModuleCat.{max u v r} (R₀.obj.obj (op U)))
      AddCommGrpCat.{max u v r}).mapHomologicalComplex (ComplexShape.up ℤ)
  let S : CochainComplex AddCommGrpCat.{max u v r} ℤ :=
    E.obj ((((homComplexFunctor (R := R)).obj (op L)).obj I))
  let T : CochainComplex AddCommGrpCat.{max u v r} ℤ :=
    CochainComplex.HomComplex (res.obj L) (res.obj I)
  let π := Classical.choose
    (homComplex_projections_exists.{u, v, max u v r, r} (J := J) (R := R))
  have hco := homComplex_sections_cochainsOfUniverses.{u, v, r} (C := C) (J := J) R U L I
  dsimp only at hco
  obtain ⟨e, he⟩ := hco
  have hcomm := homComplex_sections_cochains_commOfUniverses.{u, v, r}
    (C := C) (J := J) R U L I
  dsimp only at hcomm
  have hd := hcomm e he
  let f : S ⟶ T :=
    { f := fun i ↦ AddCommGrpCat.ofHom (e i).toAddMonoidHom
      comm' := by
        intro i j hij
        ext x
        exact (hd i j hij x).symm }
  have hf (i : ℤ) : IsIso (f.f i) := by
    exact (AddEquiv.toAddCommGrpIso (X := S.X i) (Y := T.X i) (e i)).isIso_hom
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  let F := asIso f
  let h := CochainComplex.HomComplex.leftHomologyData (res.obj L) (res.obj I) n
  let ec := (HomologicalComplex.cyclesMapIso F n) ≪≫ h.cyclesIso
  let ac := (HomologicalComplex.homologyMapIso F n) ≪≫ h.homologyIso
  let a := ac.addCommGroupIsoToAddEquiv.trans
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv
  refine ⟨ec.addCommGroupIsoToAddEquiv.toEquiv, ?_, a.toEquiv, ?_⟩
  · intro z p q hpq
    have hc : (ec.hom z).val = e n (S.iCycles n z) := by
      have hh := ConcreteCategory.congr_hom
        (h.cyclesIso_hom_comp_i) (HomologicalComplex.cyclesMap f n z)
      have hh' := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f n) z
      exact hh.trans hh'
    exact (congrArg (fun c ↦ c.v p q hpq) hc).trans
      (he n (S.iCycles n z) p q hpq)
  · intro z
    have ha : ac.hom (S.homologyπ n z) =
        CochainComplex.HomComplex.CohomologyClass.mk (ec.hom z) := by
      have hh := ConcreteCategory.congr_hom
        (h.homologyπ_comp_homologyIso_hom) (HomologicalComplex.cyclesMap f n z)
      have hh' := ConcreteCategory.congr_hom
        (HomologicalComplex.homologyπ_naturality f n) z
      exact (congrArg h.homologyIso.hom hh').trans hh
    change CochainComplex.HomComplex.CohomologyClass.homAddEquiv
      (ac.hom (S.homologyπ n z)) = _
    exact (congrArg CochainComplex.HomComplex.CohomologyClass.homAddEquiv ha).trans
      (CochainComplex.HomComplex.CohomologyClass.toHom_mk (ec.hom z))

private lemma homObjMap_section_component
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{r}) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    {A A' B B' : SheafOfModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    (t : A' ⟶ A) (s : B ⟶ B')
    (φ : (SheafOfModules.homObj (R := R) A B).val.obj (op U))
    (W : (Over U)ᵒᵖ) :
    (((SheafOfModules.homObjMap t s).val.app (op U)) φ).app W =
      ((SheafOfModules.overFunctor _ U).map t).val.app W ≫ φ.app W ≫
        ((SheafOfModules.overFunctor _ U).map s).val.app W := by
  rfl

set_option maxHeartbeats 100000 in
-- Projection comparisons involve several composed functors and chosen product objects.
/-- The shifted section Hom-complex comparison in the homotopy category is natural.
Source: Stacks Project, Tag 0A8Y, Equation (21.34.0.1).

Proof: evaluate the product projections of the sheaf Hom complex at U. Sections
in degree n are families of maps L^p|U to I^(p + n)|U. The differential formula
identifies cycles with chain maps into the shifted target, whose differential
is (-1)^n times the original differential. Multiply a family in degree n-1
by (-1)^n to identify its differential with a null-homotopy into that target.
Quotienting gives a bijection between homology classes
and homotopy classes, since both quotient projections are surjective. Apply
this construction to (L,I') and (L',I), obtaining a and b. Componentwise
composition sends a family f to s f t; the homotopy sign correction depends
only on n and hence commutes with both maps. This proves the displayed equality
on cycles and then on all homology classes. No K-injectivity or localization
at quasi-isomorphisms is used. Degree zero recovers the unshifted comparison;
zero complexes give singleton Hom sets; unbounded complexes use products. -/
private theorem homComplex_sections_homotopy_naturalityOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{r}) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    {I' I L' L : CochainComplex
      (SheafOfModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ}
    (s : I' ⟶ I) (t : L' ⟶ L) (n : ℤ) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
    let E := (SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v r} (R₀.obj.obj (op U)))
        AddCommGrpCat.{max u v r}).mapHomologicalComplex (ComplexShape.up ℤ)
    letI := module_overFunctor_preservesZero.{u, v, max u v r, r} R₀ U
    let res := (SheafOfModules.overFunctor.{max u v r} R₀ U).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Q := HomotopyCategory.quotient (SheafOfModules.{max u v r} (R₀.over U))
      (ComplexShape.up ℤ)
    let f : E.obj (((homComplexFunctor (R := R)).obj (op L)).obj I') ⟶
        E.obj (((homComplexFunctor (R := R)).obj (op L')).obj I) :=
      E.map (((homComplexFunctor (R := R)).map t.op).app I' ≫
        ((homComplexFunctor (R := R)).obj (op L')).map s)
    ∃ a : (E.obj ((((homComplexFunctor (R := R)).obj (op L)).obj I'))).homology n ≃
        (Q.obj (res.obj L) ⟶ Q.obj ((res.obj I')⟦n⟧)),
      ∃ b : (E.obj ((((homComplexFunctor (R := R)).obj (op L')).obj I))).homology n ≃
          (Q.obj (res.obj L') ⟶ Q.obj ((res.obj I)⟦n⟧)),
        b ∘ HomologicalComplex.homologyMap f n =
          (fun k ↦ Q.map (res.map t) ≫ k ≫
            Q.map ((shiftFunctor _ n).map (res.map s))) ∘ a := by
  classical
  intro R₀ E res Q f
  let S := E.obj (((homComplexFunctor (R := R)).obj (op L)).obj I')
  let T := E.obj (((homComplexFunctor (R := R)).obj (op L')).obj I)
  let π := Classical.choose
    (homComplex_projections_exists.{u, v, max u v r, r} (J := J) (R := R))
  have hmap := (Classical.choose_spec
    (homComplex_projections_exists.{u, v, max u v r, r} (J := J) (R := R))).2.2
  obtain ⟨e, he, a, ha⟩ := homComplex_sections_canonical_comparisonOfUniverses.{u, v, r} R U L I' n
  obtain ⟨e', he', b, hb⟩ :=
    homComplex_sections_canonical_comparisonOfUniverses.{u, v, r} R U L' I n
  change S.cycles n ≃ CochainComplex.HomComplex.Cocycle (res.obj L) (res.obj I') n at e
  change T.cycles n ≃ CochainComplex.HomComplex.Cocycle (res.obj L') (res.obj I) n at e'
  change S.homology n ≃ (Q.obj (res.obj L) ⟶ Q.obj ((res.obj I')⟦n⟧)) at a
  change T.homology n ≃ (Q.obj (res.obj L') ⟶ Q.obj ((res.obj I)⟦n⟧)) at b
  change ∀ (z : S.cycles n) (p q : ℤ) (hpq : p + n = q),
    (e z).val.v p q hpq = sectionToLocalizedHom R U (L.X p) (I'.X q)
      (((π L I' n p q hpq).val.app (op U)) (S.iCycles n z)) at he
  change ∀ (z : T.cycles n) (p q : ℤ) (hpq : p + n = q),
    (e' z).val.v p q hpq = sectionToLocalizedHom R U (L'.X p) (I.X q)
      (((π L' I n p q hpq).val.app (op U)) (T.iCycles n z)) at he'
  change ∀ z : S.cycles n, a (S.homologyπ n z) =
    Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (e z)) at ha
  change ∀ z : T.cycles n, b (T.homologyπ n z) =
    Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (e' z)) at hb
  change ∃ a : S.homology n ≃ (Q.obj (res.obj L) ⟶ Q.obj ((res.obj I')⟦n⟧)),
    ∃ b : T.homology n ≃ (Q.obj (res.obj L') ⟶ Q.obj ((res.obj I)⟦n⟧)),
      b ∘ HomologicalComplex.homologyMap f n =
        (fun k ↦ Q.map (res.map t) ≫ k ≫
          Q.map ((shiftFunctor _ n).map (res.map s))) ∘ a
  refine ⟨a, b, ?_⟩
  funext x
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (S.homologyπ n)).mp inferInstance x
  have hz : e' (HomologicalComplex.cyclesMap f n z) =
      ((e z).precomp (res.map t)).postcomp (res.map s) := by
    apply CochainComplex.HomComplex.Cocycle.ext
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    apply SheafOfModules.hom_ext
    ext W y
    have hh := congrArg (fun k ↦ (k.val.app W).hom y)
      (he' (HomologicalComplex.cyclesMap f n z) p q hpq)
    refine hh.trans ?_
    have hci := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f n) z
    change T.iCycles n (HomologicalComplex.cyclesMap f n z) =
      f.f n (S.iCycles n z) at hci
    change ((((π L' I n p q hpq).val.app (op U))
      (T.iCycles n (HomologicalComplex.cyclesMap f n z))).app W).hom y = _
    rw [hci]
    have hm0 : (((homComplexFunctor (R := R)).map t.op).app I' ≫
        ((homComplexFunctor (R := R)).obj (op L')).map s).f n ≫ π L' I n p q hpq =
        π L I' n p q hpq ≫ SheafOfModules.homObjMap (R := R) (t.f p) (s.f q) :=
      hmap L L' I' I t s n p q hpq
    have hm := congrArg
      (fun k : ((((homComplexFunctor (R := R)).obj (op L)).obj I')).X n ⟶
          SheafOfModules.homObj (R := R) (L'.X p) (I.X q) ↦
        (k.val.app (op U)) (S.iCycles n z))
      hm0
    change ((π L' I n p q hpq).val.app (op U)) (f.f n (S.iCycles n z)) =
      (SheafOfModules.homObjMap (R := R) (t.f p) (s.f q)).val.app (op U)
        (((π L I' n p q hpq).val.app (op U)) (S.iCycles n z)) at hm
    rw [hm]
    have hpost := cocycle_prepost_v (res.map t) (res.map s) (e z) p q hpq
    have hpost := congrArg (fun k ↦ (k.val.app W).hom y) hpost
    refine Eq.trans ?_ hpost.symm
    have hev := congrArg (fun k ↦ k.val.app W) (he z p q hpq)
    have hc := congrArg (fun k ↦ k.hom (((res.map t).f p).val.app W y)) hev
    have hc' := congrArg (((res.map s).f q).val.app W) hc
    have hmapp := homObjMap_section_component.{u, v, r} R U
      (t.f p) (s.f q) (((π L I' n p q hpq).val.app (op U)) (S.iCycles n z)) W
    exact (congrArg (fun k ↦ k.hom y) hmapp).trans hc'.symm
  change b (HomologicalComplex.homologyMap f n (S.homologyπ n z)) =
    Q.map (res.map t) ≫ a (S.homologyπ n z) ≫
      Q.map ((shiftFunctor _ n).map (res.map s))
  have hn := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f n) z
  change HomologicalComplex.homologyMap f n (S.homologyπ n z) =
    T.homologyπ n (HomologicalComplex.cyclesMap f n z) at hn
  calc
    b (HomologicalComplex.homologyMap f n (S.homologyπ n z)) =
        b (T.homologyπ n (HomologicalComplex.cyclesMap f n z)) := congrArg b hn
    _ = Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (e' (HomologicalComplex.cyclesMap f n z))) := hb _
    _ = Q.map (res.map t) ≫
        Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (e z)) ≫
          Q.map ((shiftFunctor _ n).map (res.map s)) := by
      exact (congrArg (fun c ↦ Q.map
        (CochainComplex.HomComplex.Cocycle.equivHomShift.symm c)) hz).trans
          ((congrArg Q.map (cocycle_prepost_hom (res.map t) (res.map s) (e z))).trans
            (by simp only [Functor.map_comp]))
    _ = _ := congrArg (fun k ↦ Q.map (res.map t) ≫ k ≫
      Q.map ((shiftFunctor _ n).map (res.map s))) (ha z).symm

private theorem hom_comp_bijective_of_functor
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X X' Y Y' : A} (t : X' ⟶ X) (s : Y' ⟶ Y)
    [IsIso (F.map t)] [IsIso (F.map s)]
    (hA : Function.Bijective (F.map : (X ⟶ Y') → _))
    (hB : Function.Bijective (F.map : (X' ⟶ Y) → _)) :
    Function.Bijective (fun k : X ⟶ Y' ↦ t ≫ k ≫ s) := by
  have h : Function.Bijective (fun k : F.obj X ⟶ F.obj Y' ↦ F.map t ≫ k ≫ F.map s) := by
    refine ⟨?_, ?_⟩
    · intro k l he
      have he' := congrArg (fun z ↦ inv (F.map t) ≫ z ≫ inv (F.map s)) he
      simpa [Category.assoc] using he'
    · intro k
      exact ⟨inv (F.map t) ≫ k ≫ inv (F.map s), by simp [Category.assoc]⟩
  apply (Function.Bijective.of_comp_iff' hB _).mp
  simpa only [Function.comp_def, F.map_comp] using h.comp hA

/-- The map of Hom complexes induces a quasi-isomorphism on sections over every site object.
Source: Stacks Project, sites-cohomology.tex, Lemma 0A95, using Lemma 0A94.

Proof: the product projections identify degree-n sections with external cochains on C/U.
The differential comparison identifies homology with shifted homotopy classes, naturally
in both arguments. Exact slice restriction preserves quasi-isomorphisms. Its exact
extension-by-zero left adjoint makes the restricted targets K-injective. Mathlib's
Qh_map_bijective identifies the relevant homotopy-category Hom sets with derived Hom
sets. The derived images of the restricted quasi-isomorphisms are invertible, hence
pre- and postcomposition are bijective there. Transfer this bijectivity along the two
Qh bijections and the natural homology comparisons. Abelian-group homology maps are
isomorphisms exactly when they are bijective, giving the asserted quasi-isomorphism.
This step uses no exactness of sheafification or comparison with cohomology sheaves. -/
private theorem homComplex_sections_quasiIsoOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    {R : Sheaf J CommRingCat.{r}}
    {I' I L' L : CochainComplex
      (SheafOfModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ}
    (s : I' ⟶ I) (t : L' ⟶ L) [I'.IsKInjective] [I.IsKInjective]
    [QuasiIso s] [QuasiIso t] (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}] :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
    QuasiIso (((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v r} (R₀.obj.obj (op U)))
        AddCommGrpCat.{max u v r}).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((homComplexFunctor (R := R)).map t.op).app I' ≫
      ((homComplexFunctor (R := R)).obj (op L')).map s)) := by
  classical
  let R₀ := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
  let := module_overFunctor_preservesZero.{u, v, max u v r, r} R₀ U
  let res := (SheafOfModules.overFunctor.{max u v r} R₀ U).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let := HasDerivedCategory.standard (SheafOfModules.{max u v r} (R₀.over U))
  let q := HomotopyCategory.quotient (SheafOfModules.{max u v r} (R₀.over U))
    (ComplexShape.up ℤ)
  let F := DerivedCategory.Qh (C := SheafOfModules.{max u v r} (R₀.over U))
  obtain ⟨hadd, hlim, hcolim, ⟨adj⟩⟩ :=
    SheafOfModules.siteModuleExtensionByZero_exact R₀ U
  let := hadd
  let := hlim
  let := hcolim
  have : (SheafOfModules.overFunctor.{max u v r} R₀ U).PreservesKInjectiveComplexes :=
    adj.preservesKInjectiveComplexes
  have : CochainComplex.IsKInjective (res.obj I') :=
    Functor.PreservesKInjectiveComplexes.isKInjective_map I'
  have : CochainComplex.IsKInjective (res.obj I) :=
    Functor.PreservesKInjectiveComplexes.isKInjective_map I
  have : QuasiIso (res.map t) :=
    localizedModule_restriction_quasiIsoOfUniverses.{u, v, r} R₀ U inferInstance t
  have : QuasiIso (res.map s) :=
    localizedModule_restriction_quasiIsoOfUniverses.{u, v, r} R₀ U inferInstance s
  refine ⟨fun n ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := homComplex_sections_homotopy_naturalityOfUniverses.{u, v, r} R U s t n
  let f := q.map (res.map t)
  let g := q.map ((shiftFunctor _ n).map (res.map s))
  have : IsIso (F.map f) := by
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
      (show QuasiIso _ from inferInstance)
  have : IsIso (F.map g) := by
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
      (show QuasiIso _ from inferInstance)
  have hc : Function.Bijective (fun h : q.obj (res.obj L) ⟶ q.obj ((res.obj I')⟦n⟧) ↦
      f ≫ h ≫ g) := hom_comp_bijective_of_functor F f g
    (CochainComplex.IsKInjective.Qh_map_bijective _ _)
    (CochainComplex.IsKInjective.Qh_map_bijective _ _)
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  apply (Function.Bijective.of_comp_iff' b.bijective _).mp
  exact hab.symm ▸ hc.comp a.bijective

/-- Sectionwise quasi-isomorphisms induce quasi-isomorphisms of module sheaves.
Source: Stacks Project, sites-cohomology.tex, proof of Lemma 0A95

Proof: forget the module structure and view the complexes as complexes of presheaves of
abelian groups. Evaluation at each site object is exact and jointly detects their cohomology
isomorphisms. Sheafification is exact, so the presheaf quasi-isomorphism remains one after
sheafification. The counit of sheafification identifies the resulting complexes naturally
with the original abelian-sheaf complexes. Finally the exact forgetful functor from module
sheaves to abelian sheaves reflects isomorphisms, hence reflects quasi-isomorphisms. -/
private theorem quasiIso_of_sectionsOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    {R : Sheaf J RingCat.{r}}
    {K L : CochainComplex (SheafOfModules.{max u v r} R) ℤ} (f : K ⟶ L)
    (h : ∀ U : C, QuasiIso (((SheafOfModules.forget R ⋙
      PresheafOfModules.evaluation R.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v r} (R.obj.obj (op U)))
        AddCommGrpCat.{max u v r}).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)) : QuasiIso f := by
  let T := SheafOfModules.toSheaf R
  let V := sheafToPresheaf J AddCommGrpCat.{max u v r}
  let A := presheafToSheaf J AddCommGrpCat.{max u v r}
  let g := ((T ⋙ V).mapHomologicalComplex (ComplexShape.up ℤ)).map f
  have hg : QuasiIso g := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro U
    let ec := Functor.mapHomologicalComplexCompIso
      (F := T ⋙ V) (G := (evaluation Cᵒᵖ AddCommGrpCat.{max u v r}).obj U)
      (H := SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj U ⋙
        forget₂ (ModuleCat.{max u v r} (R.obj.obj U)) AddCommGrpCat.{max u v r})
      (Iso.refl _) (ComplexShape.up ℤ)
    have hh := h U.unop
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoOfNatIso ec.symm (Arrow.mk f))).mp hh
  have hg' : QuasiIso ((A.mapHomologicalComplex (ComplexShape.up ℤ)).map g) := by
    infer_instance
  let e : (T ⋙ V) ⋙ A ≅ T :=
    Functor.associator T V A ≪≫
    Functor.isoWhiskerLeft T (asIso (sheafificationAdjunction J
      AddCommGrpCat.{max u v r}).counit) ≪≫ T.rightUnitor
  let ec := Functor.mapHomologicalComplexCompIso
    (F := T ⋙ V) (G := A) (Iso.refl ((T ⋙ V) ⋙ A)) (ComplexShape.up ℤ) ≪≫
      NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)
  have ht : QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoOfNatIso ec (Arrow.mk f))).mp hg'
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f T).mp ht

end MixedHom

open MixedHom in
/-- The map of sheaf Hom complexes obtained by precomposing with `t` and postcomposing
with `s` is a quasi-isomorphism when `s` and `t` are quasi-isomorphisms and both targets
of the Hom complexes are K-injective.
Source: Stacks Project, sites-cohomology.tex, Lemma 0A95, using Lemma 0A94
(blueprint: lem-pur-rhom-well-defined-mixed-universes).

Proof:
1. On each slice C/U, restriction is exact by
   `SheafOfModules.overFunctor_exact_ofUniverses`. Its exact additive left adjoint
   `SheafOfModules.siteModuleExtensionByZero_exact` shows that it preserves K-injectives.
2. The Hom-complex product projections identify its sections with the external Hom
   complex of the restricted complexes. The differential formula makes this an
   isomorphism of complexes. Its homology identifies with shifted homotopy classes,
   naturally under precomposition by t and postcomposition by s.
3. K-injectivity identifies these homotopy classes with derived morphisms. Exact
   restriction preserves the two quasi-isomorphisms, whose derived images are
   invertible. Composition with their inverses proves sectionwise homology bijective.
4. Evaluation detects quasi-isomorphisms of abelian presheaf complexes. Exact
   sheafification preserves them, and its counit identifies the resulting complexes
   with the underlying abelian sheaf complexes. The exact conservative functor from
   module sheaves to abelian sheaves reflects quasi-isomorphisms. -/
theorem quasiIso_homComplex_mapMixedUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    {R : Sheaf J CommRingCat.{r}}
    {I' I L' L : CochainComplex
      (SheafOfModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ}
    (s : I' ⟶ I) (t : L' ⟶ L) [I'.IsKInjective] [I.IsKInjective]
    [QuasiIso s] [QuasiIso t] :
    QuasiIso (((homComplexFunctor (R := R)).map t.op).app I' ≫
      ((homComplexFunctor (R := R)).obj (op L')).map s) := by
  apply quasiIso_of_sectionsOfUniverses.{u, v, r}
  intro U
  let : HasSheafify (J.over U) AddCommGrpCat.{max u v r} :=
    siteAbelianHasSheafify.{max u v, v, max u v r} (J.over U)
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r} :=
    siteAbelianWEqualsLocallyBijective.{max u v, v, max u v r} (J.over U)
  exact homComplex_sections_quasiIsoOfUniverses.{u, v, r} s t U

end CategoryTheory
