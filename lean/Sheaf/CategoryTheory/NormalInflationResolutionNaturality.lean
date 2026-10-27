module

public import Sheaf.CategoryTheory.OpenNormalActionInjectiveModels
public import Sheaf.CategoryTheory.CondensedNormalInvariantData
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.CategoryTheory.CondensedRestrictionMateNormalization
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Sheaf.CategoryTheory.CondensedDerivedInvariants
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-! # Normalized inflation on resolutions and auxiliary-group restriction

Source: blueprint direct-image stability, paragraph (3), extracted normal-subgroup
comparison proof steps 5–9; the nine proof steps of the node
(blueprint: lem-sfb-normal-inflation-resolution-naturality).

The comparisons and units are the existing canonical constructions. Auxiliary-group
restriction is exact; none of the statements assumes that it preserves K-injectives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar (Ring)
namespace Profinite.CondensedAction

variable [C : NormalComparisonCategories.{u}] [V : NormalInvariantFamily.{u}]
  [W : NormalSystem.{u}]

/-- The derived full-invariant comparison is the conjugate of the descended identity
of left inflations. Source: direct-images paragraph (3), node proof steps 1–2
(blueprint: lem-sfb-normal-inflation-resolution-naturality).
Proof: use openNormalActionInjectiveModels to compute the normalized adjunctions on
K-injectives. The ordinary transpose restricts successively to kernel-fixed and fully
fixed sections, hence is the inclusion-normalized ordinary comparison. Apply
lem-sfb-derived-composition-adjunction-normalization, using Adjunction.comp and
conjugateIsoEquiv. This also fixes exactly the composite unit and counit. -/
theorem normalComparison_conjugate (A : Ring.{u}) (G L : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) :
    normalComparison A G L K (W.comparisons A G L K) =
      conjugateIsoEquiv
        (V.invariants A (normalProduct G L)).adjunction.mapDerivedCategoryRightDerivedAdjunction
        ((V.invariants A (normalProduct (normalQuotient G K) L)).adjunction
          |>.mapDerivedCategoryRightDerivedAdjunction |>.comp
            (W.quotient A G L K).adjunction.mapDerivedCategoryRightDerivedAdjunction)
        (normalDerivedInflationIso A G L K (W.comparisons A G L K)) := by
  sorry

/-- On a K-injective complex c is the ordinary identity of invariant submodules,
including the composition identification of complexes.
Source: direct-images paragraph (3), node proof step 2
(blueprint: lem-sfb-normal-inflation-resolution-naturality).
Proof: apply the model formula in derivedCompositionAdjunctionNormalization to the
specified normalized adjunctions. Its ordinary conjugate is the invariant-inclusion
identity. Quotient invariants preserve K-injectives by the models lemma, so both
right-derived computation units are the indicated resolution identifications. -/
theorem normalComparison_onKInjective (A : Ring.{u}) (G L : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G)
    (I : CochainComplex (ActionModule A.toMon (G × L)) ℤ) [I.IsKInjective] :
    (normalComparison A G L K (W.comparisons A G L K)).hom.app (DerivedCategory.Q.obj I) ≫
      (V.invariants A (normalProduct (normalQuotient G K) L)).functor.rightDerivedFunctor.map
        (((W.quotient A G L K).functor.rightDerivedFunctorObjQIso I).hom) ≫
      ((V.invariants A (normalProduct (normalQuotient G K) L)).functor.rightDerivedFunctorObjQIso
          (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj I)).hom =
    ((V.invariants A (normalProduct G L)).functor.rightDerivedFunctorObjQIso I).hom ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (W.comparisons A G L K).ordinary.hom (.up ℤ)).app I) ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (Iso.refl ((W.quotient A G L K).functor ⋙
          (V.invariants A (normalProduct (normalQuotient G K) L)).functor)) (.up ℤ)).inv.app I)
    := by
  sorry

/-- The canonical unit is represented by T(i), with no boundedness assumption.
Specializing X to N[0] is the module assertion.
Source: direct-images paragraph (3), node proof step 3
(blueprint: lem-sfb-normal-inflation-resolution-naturality).
Proof: naturality of the computation unit gives RT(Qi) alpha_X = alpha_I Q(Ti).
The computation unit at the K-injective I is inverse to the displayed ObjQIso;
compose with this inverse to obtain the stated representative. -/
theorem normalResolutionUnit_onResolution (A : Ring.{u}) (G L : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G)
    (X I : CochainComplex (ActionModule A.toMon (G × L)) ℤ) [I.IsKInjective]
    (i : X ⟶ I) [QuasiIso i] :
    normalResolutionUnit (W.quotient A G L K).functor X ≫
      (W.quotient A G L K).functor.rightDerivedFunctor.map (DerivedCategory.Q.map i) ≫
      ((W.quotient A G L K).functor.rightDerivedFunctorObjQIso I).hom =
    DerivedCategory.Q.map (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).map i)
    := by
  sorry

/-- There is exactly one homotopy class of lifts b through the quotient resolution a.
Source: direct-images paragraph (3), node proof step 4
(blueprint: lem-sfb-normal-inflation-resolution-naturality).
Proof: TI is K-injective by lem-sfb-open-normal-action-injective-models.
Use lem-weil-pbc-kinjective-hom-derived to identify homotopy classes into TI with
derived maps. Since Qa is invertible, the only possible class is Q(Ti)(Qa)^{-1};
the same bijection supplies its existence. -/
theorem normalInflation_uniqueLift (A : Ring.{u}) (G L : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G)
    (X I : CochainComplex (ActionModule A.toMon (G × L)) ℤ) [I.IsKInjective]
    (i : X ⟶ I) [QuasiIso i]
    (J : CochainComplex (ActionModule A.toMon ((G ⧸ K.toSubgroup) × L)) ℤ)
    [J.IsKInjective]
    (a : ((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj X ⟶ J)
    [QuasiIso a] :
    ∃! b : (HomotopyCategory.quotient _ (.up ℤ)).obj J ⟶
        (HomotopyCategory.quotient _ (.up ℤ)).obj
          (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj I),
      (HomotopyCategory.quotient _ (.up ℤ)).map a ≫ b =
        (HomotopyCategory.quotient _ (.up ℤ)).map
          (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).map i) := by
  sorry

/-- Inverse transpose of b is its inflation followed by the invariant inclusion,
expressed degreewise using the actual inclusion in NormalQuotient.
Source: direct-images paragraph (3), node proof step 4
(blueprint: lem-sfb-normal-inflation-resolution-naturality).
Proof: apply the normalized untranspose formula in each degree. The induced adjunction
on complexes has those termwise transposes, hence the stated underlying section maps. -/
theorem normalInflation_transpose (A : Ring.{u}) (G L : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G)
    (I : CochainComplex (ActionModule A.toMon (G × L)) ℤ)
    (J : CochainComplex (ActionModule A.toMon ((G ⧸ K.toSubgroup) × L)) ℤ)
    (b : J ⟶ ((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj I)
    (n : ℤ) :
    ((((W.quotient A G L K).adjunction.mapHomologicalComplex (.up ℤ)).homEquiv J I).symm b
      |>.f n).val = (b.f n).val ≫ (W.quotient A G L K).inclusion.app (I.X n) := by
  sorry

/-- The existing fixed-section inclusion, with its unused smaller localization instances
supplied internally. Its result is entirely underived, so no category is transported.
Source: direct-images paragraph (3), node proof step 7
(blueprint: lem-sfb-normal-inflation-resolution-naturality). -/
def normalInvariantRestriction (A : Ring.{u}) (P H : ProfiniteGrp.{u}) (h : H →ₜ* P) :
    (V.invariants A P).functor ⟶ inflate (R := A.toMon) h ⋙ (V.invariants A H).functor :=
  letI : HasDerivedCategory.{u + 1} (CategoryTheory.CondensedBar.Modules A) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{u + 1} (CategoryTheory.CondensedBar.Equivariant A P) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{u + 1} (CategoryTheory.CondensedBar.Equivariant A H) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  CategoryTheory.CondensedDerivedRestriction.invariantRestriction
    (V.invariants A P) (V.invariants A H) h

/-- The canonical b_u in the larger localization universe, using the existing
fixed-section inclusion and the same universal rightDerivedPullback construction.
Source: direct-images paragraph (3), derived restriction calculus
(blueprint: lem-sfb-normal-inflation-resolution-naturality). -/
def normalDerivedRestriction (A : Ring.{u}) (P H : ProfiniteGrp.{u}) (h : H →ₜ* P) :
    (V.invariants A P).functor.rightDerivedFunctor ⟶
      (inflate (R := A.toMon) h).mapDerivedCategory ⋙
        (V.invariants A H).functor.rightDerivedFunctor :=
  Functor.rightDerivedPullback (inflate (R := A.toMon) h) (normalInvariantRestriction A P H h)

/-- Derived inflation attached independently to the original invariant inclusion:
first restrict full invariants along the quotient, then apply its counit inclusion.
Source: direct-images paragraph (3), node proof steps 4–5
(blueprint: lem-sfb-normal-inflation-resolution-naturality). -/
def normalInclusionInflation (A : Ring.{u}) (G L : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G)
    (X : CochainComplex (ActionModule A.toMon (G × L)) ℤ) :=
  (normalDerivedRestriction A (normalProduct (normalQuotient G K) L) (normalProduct G L)
    (normalProjection G K L)).app
      (DerivedCategory.Q.obj (((W.quotient A G L K).functor.mapHomologicalComplex
        (.up ℤ)).obj X)) ≫
    (V.invariants A (normalProduct G L)).functor.rightDerivedFunctor.map
      ((inflate (R := A.toMon) (normalProjection G K L)).mapDerivedCategoryFactors.hom.app
          (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj X) ≫
        DerivedCategory.Q.map
          (((W.quotient A G L K).adjunction.mapHomologicalComplex (.up ℤ)).counit.app X))

/-- The normalized unit and inflation equations, with the invariant-complex resolution
formula for every lift; thus the representative is independent of resolutions and lifts.
Source: direct-images paragraph (3), node proof steps 3–6
(blueprint: lem-sfb-normal-inflation-resolution-naturality).
Proof: step 3 computes the unit and beta by T(i) and (ri)^K. Step 4 gives the unique
homotopy lift and its inclusion transpose. Full invariants take this transpose to
Gamma_Q(b), which represents the inclusion-induced inflation by
lem-sfb-condensed-restriction-mate-normalization. The c comparison is the identity on
this target model (step 2). This proves c inf = RGamma_Q(eta), the beta unit formula,
and NormalInflationResolution. For different resolutions, the unique comparison
homotopy classes from lem-weil-pbc-kinjective-hom-derived identify the same derived
arrow, proving independence. -/
theorem normalInflation_resolution (A : Ring.{u}) (G L : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) :
    NormalInflationEquation A G L K ∧ NormalBetaUnit A G L K ∧
      NormalInflationResolution A G L K ∧
      ∀ X : CochainComplex (ActionModule A.toMon (G × L)) ℤ,
        normalInflation A G L K (W.comparisons A G L K) X = normalInclusionInflation A G L K X
    := by
  sorry

/-- Ordinary restriction of the auxiliary group, on the actual internal action category.
Source: direct-images paragraph (3), node proof step 7
(blueprint: lem-sfb-normal-inflation-resolution-naturality). -/
abbrev normalAuxiliaryRestriction (A : Ring.{u}) (P L L' : ProfiniteGrp.{u}) (h : L' →ₜ* L) :=
  inflate (R := A.toMon) (ContinuousMonoidHom.prodMap (ContinuousMonoidHom.id P) h)

/-- Restricting the auxiliary action leaves the underlying module unchanged.
Source: direct-images paragraph (3), node proof step 8
(blueprint: lem-sfb-normal-inflation-resolution-naturality). -/
def normalAuxiliaryForget (A : Ring.{u}) (P L L' : ProfiniteGrp.{u}) (h : L' →ₜ* L) :
    normalAuxiliaryRestriction A P L L' h ⋙ forgetAction ≅
      forgetAction (R := A.toMon) (P := P × L) := Iso.refl _

/-- The quotient-invariant identity under auxiliary restriction is uniquely normalized
by its inclusion, even for independently chosen invariant objects.
Source: direct-images paragraph (3), node proof step 7
(blueprint: lem-sfb-normal-inflation-resolution-naturality).
Proof: both functors have exactly the same kernel-fixed sections, with the same
residual restricted action. Restrict the two inclusions to these sections in both
directions. The inclusions are sectionwise injective, so the maps are inverse,
equivariant, natural, and uniquely determined. -/
theorem normalAuxiliaryQuotient_existsUnique (A : Ring.{u}) (G L L' : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) (h : L' →ₜ* L) :
    ∃! e : (W.quotient A G L K).functor ⋙
        normalAuxiliaryRestriction A (normalQuotient G K) L L' h ≅
      normalAuxiliaryRestriction A G L L' h ⋙ (W.quotient A G L' K).functor,
      ∀ N : ActionModule A.toMon (G × L),
        (e.hom.app N).val ≫ (W.quotient A G L' K).inclusion.app
          ((normalAuxiliaryRestriction A G L L' h).obj N) =
        (W.quotient A G L K).inclusion.app N := by
  sorry

/-- The inclusion-normalized identity T' r_h = r_h T, in the direction used for tau.
Source: direct-images paragraph (3), node proof step 7
(blueprint: lem-sfb-normal-inflation-resolution-naturality). -/
def normalAuxiliaryQuotient (A : Ring.{u}) (G L L' : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) (h : L' →ₜ* L) :=
  Classical.choose (normalAuxiliaryQuotient_existsUnique A G L L' K h)

/-- Exact restriction to the kernel is unchanged, with the identity underlying map.
Source: direct-images paragraph (3), node proof step 8
(blueprint: lem-sfb-normal-inflation-resolution-naturality).
Proof: (1_G times h)(k,1)=(k,1), because h(1)=1. Thus the two restricted actions
agree on all generalized sections. The identity underlying maps give a natural
isomorphism; faithfulness of forgetting gives uniqueness. -/
theorem normalAuxiliaryKernel_existsUnique (A : Ring.{u}) (G L L' : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) (h : L' →ₜ* L) :
    ∃! e : normalAuxiliaryRestriction A G L L' h ⋙
        inflate (R := A.toMon) (normalKernelInclusion G K L') ≅
      inflate (R := A.toMon) (normalKernelInclusion G K L),
      ∀ N : ActionModule A.toMon (G × L), (e.hom.app N).val = 𝟙 N.module := by
  sorry

/-- The actual identity on restriction to K.
Source: direct-images paragraph (3), node proof step 8
(blueprint: lem-sfb-normal-inflation-resolution-naturality). -/
def normalAuxiliaryKernel (A : Ring.{u}) (G L L' : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) (h : L' →ₜ* L) :=
  Classical.choose (normalAuxiliaryKernel_existsUnique A G L L' K h)

/-- Tau is the canonical derived square of the ordinary quotient-invariant identity.
Source: direct-images paragraph (3), node proof step 7
(blueprint: lem-sfb-normal-inflation-resolution-naturality). -/
def normalAuxiliaryTau (A : Ring.{u}) (G L L' : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) (h : L' →ₜ* L) :=
  normalSquare (W.quotient A G L K).functor (W.quotient A G L' K).functor
    (normalAuxiliaryRestriction A G L L' h)
    (normalAuxiliaryRestriction A (normalQuotient G K) L L' h)
    (normalAuxiliaryQuotient A G L L' K h).hom

/-- The ordinary quotient identity applied to complexes, with both composition maps.
Source: direct-images paragraph (3), node proof steps 7 and 9
(blueprint: lem-sfb-normal-inflation-resolution-naturality). -/
def normalAuxiliaryQuotientComplex (A : Ring.{u}) (G L L' : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) (h : L' →ₜ* L)
    (X : CochainComplex (ActionModule A.toMon (G × L)) ℤ) :=
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl ((W.quotient A G L K).functor ⋙
      normalAuxiliaryRestriction A (normalQuotient G K) L L' h)) (.up ℤ)).hom.app X ≫
    (NatTrans.mapHomologicalComplex (normalAuxiliaryQuotient A G L L' K h).hom
      (.up ℤ)).app X ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (normalAuxiliaryRestriction A G L L' h ⋙
        (W.quotient A G L' K).functor)) (.up ℤ)).inv.app X

/-- The canonical derived identification that auxiliary restriction forgets to the identity.
Source: direct-images paragraph (3), node proof step 8
(blueprint: lem-sfb-normal-inflation-resolution-naturality). -/
def normalAuxiliaryForgetDerived (A : Ring.{u}) (P L L' : ProfiniteGrp.{u}) (h : L' →ₜ* L) :=
  (Functor.mapDerivedCategoryCompIso (normalAuxiliaryRestriction A P L L' h)
    (forgetAction (R := A.toMon) (P := P × L'))).symm ≪≫
      Functor.mapDerivedCategoryNatIso (normalAuxiliaryForget A P L L' h)

/-- The descended identity r' r_h = r on restriction to the kernel.
Source: direct-images paragraph (3), node proof step 8
(blueprint: lem-sfb-normal-inflation-resolution-naturality). -/
def normalAuxiliaryKernelDerived (A : Ring.{u}) (G L L' : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) (h : L' →ₜ* L) :=
  (Functor.mapDerivedCategoryCompIso (normalAuxiliaryRestriction A G L L' h)
    (inflate (R := A.toMon) (normalKernelInclusion G K L'))).symm ≪≫
      Functor.mapDerivedCategoryNatIso (normalAuxiliaryKernel A G L L' K h)

/-- The transposed lift represents the original inclusion of kernel invariants.
Source: direct-images paragraph (3), node proof step 4
(blueprint: lem-sfb-normal-inflation-resolution-naturality).
Proof: transpose ba homotopic to T(i) under the additive termwise adjunction, which
preserves homotopies. The adjunction's counit is the given invariant inclusion;
its naturality identifies the other composite with the inclusion followed by i.
Exact quotient inflation preserves the resolution quasi-isomorphism a. -/
theorem normalInflation_transposeLift (A : Ring.{u}) (G L : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G)
    (X I : CochainComplex (ActionModule A.toMon (G × L)) ℤ) [I.IsKInjective]
    (i : X ⟶ I) [QuasiIso i]
    (J : CochainComplex (ActionModule A.toMon ((G ⧸ K.toSubgroup) × L)) ℤ)
    [J.IsKInjective]
    (a : ((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj X ⟶ J)
    [QuasiIso a]
    (b : J ⟶ ((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj I)
    (hb : Nonempty (Homotopy (a ≫ b)
      (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).map i))) :
    Nonempty (Homotopy
      (((inflate (R := A.toMon) (normalProjection G K L)).mapHomologicalComplex (.up ℤ)).map a ≫
        (((W.quotient A G L K).adjunction.mapHomologicalComplex (.up ℤ)).homEquiv J I).symm b)
      (((W.quotient A G L K).adjunction.mapHomologicalComplex (.up ℤ)).counit.app X ≫ i))
    := by
  sorry

/-- The invariant inclusion definition of b_u is represented on any fresh K-injective
resolution by inclusion followed by the invariant map of that resolution.
Source: direct-images paragraph (3), node proof step 7
(blueprint: lem-sfb-normal-inflation-resolution-naturality).
Proof: use the computation-unit normalization of
lem-sfb-condensed-derived-restriction-calculus and
lem-sfb-condensed-restriction-mate-normalization, or equivalently the defining
rightDerivedPullback_fac_app. Naturality along a and invertibility of the units on
I,J give this formula. There is no K-injectivity hypothesis on h^*I. -/
theorem normalDerivedRestriction_onResolution (A : Ring.{u}) (P H : ProfiniteGrp.{u})
    (h : H →ₜ* P) (I : CochainComplex (ActionModule A.toMon P) ℤ) [I.IsKInjective]
    (J : CochainComplex (ActionModule A.toMon H) ℤ) [J.IsKInjective]
    (a : ((inflate (R := A.toMon) h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso a] :
    (normalDerivedRestriction A P H h).app (DerivedCategory.Q.obj I) ≫
      (V.invariants A H).functor.rightDerivedFunctor.map
        ((inflate (R := A.toMon) h).mapDerivedCategoryFactors.hom.app I ≫
          DerivedCategory.Q.map a) ≫
      ((V.invariants A H).functor.rightDerivedFunctorObjQIso J).hom =
    ((V.invariants A P).functor.rightDerivedFunctorObjQIso I).hom ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (normalInvariantRestriction A P H h) (.up ℤ)).app I ≫
          ((V.invariants A H).functor.mapHomologicalComplex (.up ℤ)).map a) := by
  sorry

/-- The tau comparison on I is induced by T'(a) for every fresh primed resolution a.
Source: direct-images paragraph (3), node proof step 7
(blueprint: lem-sfb-normal-inflation-resolution-naturality).
Proof: derive the ordinary quotient square with its computation unit. At I the
unprimed computation unit is invertible. Postcompose the primed unit with the
resolution a and use its naturality. The resulting map is exactly the ordinary
quotient identity followed by T'(a). This construction does not suppose r_hI
K-injective; only the chosen J is required to be K-injective. -/
theorem normalAuxiliaryTau_onResolution (A : Ring.{u}) (G L L' : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) (h : L' →ₜ* L)
    (I : CochainComplex (ActionModule A.toMon (G × L)) ℤ) [I.IsKInjective]
    (J : CochainComplex (ActionModule A.toMon (G × L')) ℤ) [J.IsKInjective]
    (a : ((normalAuxiliaryRestriction A G L L' h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso a] :
    (normalAuxiliaryTau A G L L' K h).app (DerivedCategory.Q.obj I) ≫
      (W.quotient A G L' K).functor.rightDerivedFunctor.map
        ((normalAuxiliaryRestriction A G L L' h).mapDerivedCategoryFactors.hom.app I ≫
          DerivedCategory.Q.map a) ≫
      ((W.quotient A G L' K).functor.rightDerivedFunctorObjQIso J).hom =
    (normalAuxiliaryRestriction A (normalQuotient G K) L L' h).mapDerivedCategory.map
        (((W.quotient A G L K).functor.rightDerivedFunctorObjQIso I).hom) ≫
      (normalAuxiliaryRestriction A (normalQuotient G K) L L' h).mapDerivedCategoryFactors.hom.app
        (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map (normalAuxiliaryQuotientComplex A G L L' K h I ≫
        (((W.quotient A G L' K).functor.mapHomologicalComplex (.up ℤ)).map a)) := by
  sorry

/-- The c square for every unbounded derived object and every continuous h.
Source: direct-images paragraph (3), node proof steps 7–8
(blueprint: lem-sfb-normal-inflation-resolution-naturality).
Proof: represent N by a K-injective I and resolve r_hI by a:r_hI→J. The two c
comparisons are the ordinary invariant identities. The b^G side is the full-invariant
inclusion followed by the invariant map of a. Factor T'(a) through a fresh resolution
of r_hTI; uniqueness of maps into the K-injective T'J shows that the b^Q,tau side
has the same representative. The K-injective Hom bijection proves independence and
naturality on all derived morphisms (lem-weil-pbc-kinjective-hom-derived). -/
theorem normalAuxiliaryComparison_square (A : Ring.{u}) (G L L' : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) (h : L' →ₜ* L)
    (N : DerivedCategory.{u + 2} (ActionModule A.toMon (G × L))) :
    (normalDerivedRestriction A (normalProduct G L) (normalProduct G L')
      (ContinuousMonoidHom.prodMap (ContinuousMonoidHom.id G) h)).app N ≫
      (normalComparison A G L' K (W.comparisons A G L' K)).hom.app
        ((normalAuxiliaryRestriction A G L L' h).mapDerivedCategory.obj N) =
    (normalComparison A G L K (W.comparisons A G L K)).hom.app N ≫
      (normalDerivedRestriction A (normalProduct (normalQuotient G K) L)
        (normalProduct (normalQuotient G K) L')
        (ContinuousMonoidHom.prodMap (ContinuousMonoidHom.id (normalQuotient G K)) h)).app
          ((W.quotient A G L K).functor.rightDerivedFunctor.obj N) ≫
      (V.invariants A (normalProduct (normalQuotient G K) L')).functor.rightDerivedFunctor.map
        ((normalAuxiliaryTau A G L L' K h).app N) := by
  sorry

/-- Forgetting the residual action makes tau the identity on derived K-invariants,
with the exact-composition identifications displayed.
Source: direct-images paragraph (3), node proof step 8
(blueprint: lem-sfb-normal-inflation-resolution-naturality).
Proof: on I and a:r_hI→J the beta normalizations identify the comparison with the
map on K-invariants of r'(a), and r'r_hI=rI. Both kernel-restricted complexes are
K-injective by the models lemma. Their quasi-isomorphic comparison is a homotopy
equivalence by lem-weil-pbc-kinjective-hom-derived. Under resolution identifications
it is the identity on RGamma_K D(r); its chain representative need not be an identity. -/
theorem normalAuxiliaryBeta_square (A : Ring.{u}) (G L L' : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) (h : L' →ₜ* L)
    (N : DerivedCategory.{u + 2} (ActionModule A.toMon (G × L))) :
    (normalAuxiliaryForgetDerived A (normalQuotient G K) L L' h).inv.app
        ((W.quotient A G L K).functor.rightDerivedFunctor.obj N) ≫
      (forgetAction (R := A.toMon) (P := (G ⧸ K.toSubgroup) × L')).mapDerivedCategory.map
        ((normalAuxiliaryTau A G L L' K h).app N) ≫
      (normalBeta A G L' K (W.comparisons A G L' K)).hom.app
        ((normalAuxiliaryRestriction A G L L' h).mapDerivedCategory.obj N) ≫
      (V.invariants A (normalKernel G K)).functor.rightDerivedFunctor.map
        ((normalAuxiliaryKernelDerived A G L L' K h).hom.app N) =
    (normalBeta A G L K (W.comparisons A G L K)).hom.app N := by
  sorry

/-- The resolution unit commutes with auxiliary restriction.
Source: direct-images paragraph (3), node proof step 9
(blueprint: lem-sfb-normal-inflation-resolution-naturality).
Proof: for i:X→I and a:r_hI→J use a r_h(i) as the primed resolution. Both unit
composites are T'(a)r_h(T(i))=T'(a r_h(i)). Naturality of the computation units
and the normalized ordinary quotient identity give the displayed derived equality.
The same calculation under beta is the unchanged kernel-invariant unit square. -/
theorem normalAuxiliaryUnit_square (A : Ring.{u}) (G L L' : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) (h : L' →ₜ* L)
    (X : CochainComplex (ActionModule A.toMon (G × L)) ℤ) :
    (normalAuxiliaryRestriction A (normalQuotient G K) L L' h).mapDerivedCategory.map
        (normalResolutionUnit (W.quotient A G L K).functor X) ≫
      (normalAuxiliaryTau A G L L' K h).app (DerivedCategory.Q.obj X) ≫
      (W.quotient A G L' K).functor.rightDerivedFunctor.map
        ((normalAuxiliaryRestriction A G L L' h).mapDerivedCategoryFactors.hom.app X) =
    (normalAuxiliaryRestriction A (normalQuotient G K) L L' h).mapDerivedCategoryFactors.hom.app
        (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj X) ≫
      DerivedCategory.Q.map (normalAuxiliaryQuotientComplex A G L L' K h X) ≫
      normalResolutionUnit (W.quotient A G L' K).functor
        (((normalAuxiliaryRestriction A G L L' h).mapHomologicalComplex (.up ℤ)).obj X) := by
  sorry

/-- The inflation equation commutes with auxiliary restriction.
Source: direct-images paragraph (3), node proof step 9
(blueprint: lem-sfb-normal-inflation-resolution-naturality).
Proof: combine the c square, both equations c inf = RGamma_Q(eta), the unit square,
and naturality of b^Q in derived maps. Cancel the primed isomorphism c'. The
representative calculation sends each fully fixed generalized section x to a(x),
so it also respects the invariant inclusions on every profinite base change. -/
theorem normalAuxiliaryInflation_square (A : Ring.{u}) (G L L' : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) (h : L' →ₜ* L)
    (X : CochainComplex (ActionModule A.toMon (G × L)) ℤ) :
    (normalDerivedRestriction A (normalProduct (normalQuotient G K) L)
      (normalProduct (normalQuotient G K) L')
      (ContinuousMonoidHom.prodMap (ContinuousMonoidHom.id (normalQuotient G K)) h)).app
        (DerivedCategory.Q.obj
          (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj X)) ≫
      (V.invariants A (normalProduct (normalQuotient G K) L')).functor.rightDerivedFunctor.map
        (
          (normalAuxiliaryRestriction A
            (normalQuotient G K) L L' h).mapDerivedCategoryFactors.hom.app
            (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj X) ≫
          DerivedCategory.Q.map (normalAuxiliaryQuotientComplex A G L L' K h X)) ≫
      normalInflation A G L' K (W.comparisons A G L' K)
        (((normalAuxiliaryRestriction A G L L' h).mapHomologicalComplex (.up ℤ)).obj X) =
    normalInflation A G L K (W.comparisons A G L K) X ≫
      (normalDerivedRestriction A (normalProduct G L) (normalProduct G L')
        (ContinuousMonoidHom.prodMap (ContinuousMonoidHom.id G) h)).app
          (DerivedCategory.Q.obj X) ≫
      (V.invariants A (normalProduct G L')).functor.rightDerivedFunctor.map
        ((normalAuxiliaryRestriction A G L L' h).mapDerivedCategoryFactors.hom.app X) := by
  sorry

/-- The descriptions are natural in equivariant maps (in particular maps of modules
in degree zero). Beta and c are already natural isomorphisms on the entire derived
category, rather than only natural cohomology identifications.
Source: direct-images paragraph (3), node proof step 6
(blueprint: lem-sfb-normal-inflation-resolution-naturality).
Proof: lift a chain map to maps of the two chosen resolutions, using the K-injective
Hom bijection. The composites with the quotient lifts agree after precomposition
with a, hence are homotopic. Invariant functors preserve that homotopy. This proves
naturality of both the resolution formula and inflation. For identity coefficient
maps the same argument compares arbitrary choices of resolutions and lifts. -/
theorem normalInflation_natural (A : Ring.{u}) (G L : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G)
    (X Y : CochainComplex (ActionModule A.toMon (G × L)) ℤ) (f : X ⟶ Y) :
    (V.invariants A (normalProduct (normalQuotient G K) L)).functor.rightDerivedFunctor.map
        (DerivedCategory.Q.map
          (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).map f)) ≫
      normalInflation A G L K (W.comparisons A G L K) Y =
    normalInflation A G L K (W.comparisons A G L K) X ≫
      (V.invariants A (normalProduct G L)).functor.rightDerivedFunctor.map
        (DerivedCategory.Q.map f) := by
  sorry

end Profinite.CondensedAction
