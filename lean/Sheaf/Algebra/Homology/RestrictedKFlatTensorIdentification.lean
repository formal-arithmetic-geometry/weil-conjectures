/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Restricted scalar-first K-flat tensor identifications

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 06YT, and
sites-modules.tex, Tags 03EK and 03CY.
(blueprint: lem-pe-restricted-kflat-tensor-identification)

The scalar-last complex is specified by its underlying B-linear tensor complex and
its S-linear swap from the existing scalar-first extension. The pure-tensor equation
fixes the swap, including its inverse, and hence fixes the S-action on the last factor.
No existence choice of an unspecified object or map is used in a definition.
-/

@[expose] public section
set_option autoImplicit false
universe u v r wB wA wS wT
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- Ordinary scalar restriction on the given site.
Source: Stacks 03DA (blueprint: lem-pe-restricted-kflat-tensor-identification). -/
noncomputable abbrev restrictedTensorScalars {A S : Sheaf J CommRingCat.{r}} (v : A ⟶ S) :=
  restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map v)

/-- Scalar restriction preserves finite limits.
Source: Stacks 03DA (blueprint: lem-pe-restricted-kflat-tensor-identification).
Proof: restriction keeps the underlying abelian sheaves; kernels and finite products
are sectionwise. Apply lem-pur-sheaf-ring-coefficient-ordinary-adjunction. -/
@[instance] theorem restrictedTensorScalars_preservesFiniteLimits
    {A S : Sheaf J CommRingCat.{r}} (v : A ⟶ S) :
    PreservesFiniteLimits (restrictedTensorScalars v) := by
  sorry

/-- Scalar restriction preserves finite colimits.
Source: Stacks 03DA (blueprint: lem-pe-restricted-kflat-tensor-identification).
Proof: cokernels are sheafifications of sectionwise cokernels. Restriction leaves
both underlying abelian presheaves and their sheafifications unchanged. Apply
lem-pur-sheaf-ring-coefficient-ordinary-adjunction. -/
@[instance] theorem restrictedTensorScalars_preservesFiniteColimits
    {A S : Sheaf J CommRingCat.{r}} (v : A ⟶ S) :
    PreservesFiniteColimits (restrictedTensorScalars v) := by
  sorry

/-- The coefficient sheaf as a module over the source ring.
Source: Stacks 03EK (blueprint: lem-pe-restricted-kflat-tensor-identification). -/
noncomputable abbrev restrictedTensorCoefficient
    {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S) :=
  (restrictedTensorScalars φ).obj (unit (derivedChangeRingIndependentCoefficients J S))

/-- The underlying B-linear scalar-last tensor complex, with differential d tensor 1.
Source: Stacks 03EK (blueprint: lem-pe-restricted-kflat-tensor-identification). -/
noncomputable abbrev restrictedTensorLastComplex
    {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ) :=
  ((siteSheafTensorRight (restrictedTensorCoefficient φ)).mapHomologicalComplex (.up ℤ)).obj P

variable {B A S T : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wA} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J A))]
  [HasDerivedCategory.{wS} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J S))]

/-- A pure scalar-first section in the prescribed ordinary extension functor.
Source: Stacks 03EK (blueprint: lem-pe-restricted-kflat-tensor-identification). -/
noncomputable def restrictedTensorFirstSection {φ : B ⟶ S}
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} φ)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (n : ℤ) (U : Cᵒᵖ) (s : S.obj.obj U) (p : (P.X n).val.obj U) :
    (D.E.obj (P.X n)).val.obj U :=
  (eqToHom (D.obj_eq (P.X n)).symm).val.app U
    ((CategoryTheory.toSheafify J (changeOfRingsPresheaf φ (P.X n)).presheaf).app U
      (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] p))

/-- The canonical localization comparison for restriction (oriented as lambda in the node).
Source: Stacks 05RU (blueprint: lem-pe-restricted-kflat-tensor-identification). -/
noncomputable abbrev restrictedTensorLocalization (v : A ⟶ S) :=
  (restrictedTensorScalars v).mapDerivedCategoryFactors.symm

/-- Termwise restriction preserves quasi-isomorphisms, without a flatness hypothesis.
Source: Stacks 03DA, 05RU (blueprint: lem-pe-restricted-kflat-tensor-identification).
Proof: exact restriction identifies the cohomology of the restricted complex with
restriction of its cohomology. Thus an isomorphism on each cohomology stays one. -/
theorem restrictedTensorScalars_quasiIso (v : A ⟶ S)
    {H H' : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S)) ℤ}
    (a : H ⟶ H') [QuasiIso a] :
    QuasiIso (((restrictedTensorScalars v).mapHomologicalComplex (.up ℤ)).map a) := by
  sorry

/-- The natural localization comparison is compatible with shifts.
Source: Stacks 05RU (blueprint: lem-pe-restricted-kflat-tensor-identification).
Proof: restriction leaves differentials and additive maps unchanged, hence commutes
with degree-one shift and negation of the differential. Localization transports
this identity. The two comparisons agree after Q, so uniqueness gives compatibility. -/
theorem restrictedTensorLocalization_commShift (v : A ⟶ S) :
    NatTrans.CommShift (restrictedTensorLocalization v).hom ℤ := by
  sorry

/-- The scalar-last S-linear model and its normalized K-flat and derived comparisons.
Source: Stacks 03EK, 06YT, 06YY (blueprint: lem-pe-restricted-kflat-tensor-identification).
The underlying B-linear model is the actual sheafified tensor P tensor S. The swap
normalization specifies s tensor p mapping to p tensor s, so S acts on the last factor.
The counit normalization specifies the canonical computation comparison for f.
Eta and delta are included with equations fixing exactly the composites in the node. -/
structure RestrictedKFlatTensorIdentification (u : B ⟶ A) (v : A ⟶ S)
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} (u ≫ v))
    (K : DerivedCategory (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)))
    (P G : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (e : DerivedCategory.Q.obj G ≅ K) (f : P ⟶ G) [QuasiIso f] where
  /-- The S-linear scalar-last complex. -/
  H : CochainComplex (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J S)) ℤ
  /-- The S-linear cochain swap, including its inverse. -/
  τ : (D.E.mapHomologicalComplex (.up ℤ)).obj P ≅ H
  /-- Identification with the existing B-linear scalar-last tensor complex. -/
  last : ((restrictedTensorScalars (u ≫ v)).mapHomologicalComplex (.up ℤ)).obj H ≅
    restrictedTensorLastComplex (u ≫ v) P
  /-- The swap is the specified pure-tensor exchange. -/
  swap : ∀ (n : ℤ) (U : Cᵒᵖ) (s : S.obj.obj U) (p : (P.X n).val.obj U),
    (last.hom.f n).val.app U ((τ.hom.f n).val.app U
      (restrictedTensorFirstSection D P n U s p)) =
      siteSheafTensorTmul (P.X n) (restrictedTensorCoefficient (u ≫ v)) U p s
  /-- The K-flat computation comparison. -/
  c : D.T.obj (DerivedCategory.Q.obj G) ≅ DerivedCategory.Q.obj H
  /-- The computation is the inverse resolution map followed by the K-flat counit. -/
  computation : c.hom ≫ DerivedCategory.Q.map τ.inv =
    inv (D.T.map (DerivedCategory.Q.map f)) ≫ D.ε.app P
  /-- The comparison for the represented derived object K. -/
  η : D.T.obj K ≅ DerivedCategory.Q.obj H
  /-- Eta is exactly c composed with F(e inverse). -/
  eta_eq : η = D.T.mapIso e.symm ≪≫ c
  /-- The restricted scalar-first derived identification. -/
  δ : DerivedCategory.Q.obj
      (((restrictedTensorScalars v).mapHomologicalComplex (.up ℤ)).obj
        ((D.E.mapHomologicalComplex (.up ℤ)).obj P)) ≅
    (restrictedTensorScalars v).mapDerivedCategory.obj (D.T.obj K)
  /-- Delta is the composite displayed in the node, in its stated order. -/
  delta_eq : δ = DerivedCategory.Q.mapIso
      (((restrictedTensorScalars v).mapHomologicalComplex (.up ℤ)).mapIso τ) ≪≫
    (restrictedTensorLocalization v).app H ≪≫
    (restrictedTensorScalars v).mapDerivedCategory.mapIso η.symm

/-- Restricted scalar-first K-flat models identify derived scalar extensions.
Source: Stacks 06YY, 06YT, 03EK, 03CY.
(blueprint: lem-pe-restricted-kflat-tensor-identification)

Proof: exact scalar restriction preserves cohomology, hence quasi-isomorphisms
(lem-pur-sheaf-ring-coefficient-ordinary-adjunction). Its localization comparison
is natural and shift compatible by the universal property of Q. Construct the
scalar-last model by sheafifying the sectionwise tensor with S in the second
factor, with S acting there. The mutually inverse pure-tensor swaps are balanced,
commute with restrictions and differentials, and are S-linear. Sheafification
extends them uniquely (def-pur-sheaf-tensor-product and
 def-weil-presheaf-modules-sheafification). Thus no degree sign occurs. The canonical
K-flat counit of lem-pur-derived-change-of-rings and the inverse of F(Q f) give c.
Compose with F(e inverse) to obtain eta. Localize and restrict the swap, follow it
by lambda, and then by restriction of eta inverse to obtain delta. Each factor is
an isomorphism, so the reverse composite of their inverses is its inverse.
Neither flatness of the ring maps nor boundedness or completeness is used. -/
theorem nonempty_restrictedKFlatTensorIdentification (u : B ⟶ A) (v : A ⟶ S)
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} (u ≫ v))
    (K : DerivedCategory (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)))
    (P G : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (e : DerivedCategory.Q.obj G ≅ K) (f : P ⟶ G) [QuasiIso f]
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := B) P)
    (hflat : ∀ n : ℤ, IsFlatOnSite (R := B) (P.X n)) :
    Nonempty (RestrictedKFlatTensorIdentification u v D K P G e f) := by
  sorry

variable [HasDerivedCategory.{wT} (ringedSiteModules.{r}
  (derivedChangeRingIndependentCoefficients J T))]

/-- An arbitrary A-linear coefficient map commutes with the scalar swap, and the
localized map is exactly the map on scalar-last representatives under delta.
Source: Stacks 03EK, 03CY, 06YY.
(blueprint: lem-pe-restricted-kflat-tensor-identification)

Proof: A-linearity of h implies B-linearity through u. The formulas h tensor 1
and 1 tensor h therefore respect B-balancing. They respect the A-actions since h
is A-linear, commute with restrictions by naturality of h, and commute with the
differentials because h is in degree zero. Sheafification extends them uniquely.
Both routes around the swap square send s tensor p to p tensor h(s); equality on
pure tensors, followed by uniqueness of sheafification, gives the cochain square.
Localize that square and substitute delta's three factors. The adjacent swap and
inverse swap cancel. The remaining factors are exactly the displayed conjugation
through lambda and eta. This does not apply naturality of lambda to a map between
different coefficient categories and needs neither multiplicativity nor unitality
of h. This is steps 6 and 7 of the node's proof, using the tensor and sheafification
nodes together with def-pc-sheaf-restrict-scalars. -/
theorem restrictedKFlatTensorIdentification_coefficientMap
    (u : B ⟶ A) (v : A ⟶ S) (w : A ⟶ T)
    (DS : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} (u ≫ v))
    (DT : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wT} (u ≫ w))
    (K : DerivedCategory (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)))
    (P G : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (e : DerivedCategory.Q.obj G ≅ K) (f : P ⟶ G) [QuasiIso f]
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := B) P)
    (hflat : ∀ n : ℤ, IsFlatOnSite (R := B) (P.X n))
    (dS : RestrictedKFlatTensorIdentification u v DS K P G e f)
    (dT : RestrictedKFlatTensorIdentification u w DT K P G e f)
    (h : (restrictedTensorScalars v).obj (unit (derivedChangeRingIndependentCoefficients J S)) ⟶
      (restrictedTensorScalars w).obj (unit (derivedChangeRingIndependentCoefficients J T))) :
    ∃ (a : ((restrictedTensorScalars v).mapHomologicalComplex (.up ℤ)).obj
          ((DS.E.mapHomologicalComplex (.up ℤ)).obj P) ⟶
        ((restrictedTensorScalars w).mapHomologicalComplex (.up ℤ)).obj
          ((DT.E.mapHomologicalComplex (.up ℤ)).obj P))
      (b : ((restrictedTensorScalars v).mapHomologicalComplex (.up ℤ)).obj dS.H ⟶
        ((restrictedTensorScalars w).mapHomologicalComplex (.up ℤ)).obj dT.H),
      (∀ (n : ℤ) (U : Cᵒᵖ) (s : S.obj.obj U) (p : (P.X n).val.obj U),
        (a.f n).val.app U (restrictedTensorFirstSection DS P n U s p) =
          restrictedTensorFirstSection DT P n U (h.val.app U s) p) ∧
      (∀ (n : ℤ) (U : Cᵒᵖ) (s : S.obj.obj U) (p : (P.X n).val.obj U),
        (dT.last.hom.f n).val.app U ((b.f n).val.app U ((dS.τ.hom.f n).val.app U
          (restrictedTensorFirstSection DS P n U s p))) =
          siteSheafTensorTmul (P.X n) (restrictedTensorCoefficient (u ≫ w)) U p
            (h.val.app U s)) ∧
      a ≫ ((restrictedTensorScalars w).mapHomologicalComplex (.up ℤ)).map dT.τ.hom =
        ((restrictedTensorScalars v).mapHomologicalComplex (.up ℤ)).map dS.τ.hom ≫ b ∧
      dS.δ.inv ≫ DerivedCategory.Q.map a ≫ dT.δ.hom =
        (restrictedTensorScalars v).mapDerivedCategory.map dS.η.hom ≫
          (restrictedTensorLocalization v).inv.app dS.H ≫ DerivedCategory.Q.map b ≫
          (restrictedTensorLocalization w).hom.app dT.H ≫
          (restrictedTensorScalars w).mapDerivedCategory.map dT.η.inv := by
  sorry

end SheafOfModules
