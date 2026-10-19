/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedSupport
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-! # Ambient pro-etale adjunction for the actual constant coefficient sheaf

Source: Weil blueprint, smooth purity, order 1859; Stacks Project, Tags 09BM and 09AH
(blueprint: lem-exc-proetale-closed-support).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private noncomputable def coefficientEquivalence (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R := by
  let : (CategoryTheory.Equivalence.refl (C := X.ProEt)).functor.IsContinuous
      (ProEt.topology X) (ProEt.topology X) := by
    change (𝟭 X.ProEt).IsContinuous _ _
    infer_instance
  let : (CategoryTheory.Equivalence.refl (C := X.ProEt)).inverse.IsContinuous
      (ProEt.topology X) (ProEt.topology X) := by
    change (𝟭 X.ProEt).IsContinuous _ _
    infer_instance
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (J := ProEt.topology X) (K := ProEt.topology X) (S := R) (R := S)
    (CategoryTheory.Equivalence.refl (C := X.ProEt)) c.hom c.inv
    (by
      apply NatTrans.ext
      funext U
      dsimp [CategoryTheory.Equivalence.refl]
      erw [S.obj.map_id]
      exact congrArg (fun q ↦ q.hom.app U) c.inv_hom_id.symm)
    (by
      apply NatTrans.ext
      funext U
      dsimp [CategoryTheory.Equivalence.refl]
      erw [R.obj.map_id, Category.comp_id]
      exact congrArg (fun q ↦ q.hom.app U) c.hom_inv_id)

private noncomputable def coefficientTransport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModules X S ≌
      proEtaleRingModules X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) :=
  coefficientEquivalence X
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def directImageComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModuleDirectImage f R S c ≅
      (coefficientTransport f R S c).functor ⋙ proEtaleRingedDirectImage f R := by
  let φ : proEtaleModuleCoefficients R ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          (proEtaleModuleCoefficients
            ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)) :=
    ⟨Functor.whiskerRight ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let ψ : proEtaleModuleCoefficients
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) ⟶
        proEtaleModuleCoefficients S := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom
  exact (SheafOfModules.pushforwardComp (F := proEtaleBaseChange f)
    (G := 𝟭 X.ProEt) (K' := ProEt.topology X)
    (R' := proEtaleModuleCoefficients S) φ ψ).symm

private noncomputable def pullbackComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (a : proEtaleModuleInverseImage f R ⊣ proEtaleRingedDirectImage f R) :
    proEtaleRingModulePullback f R S c ≅
      proEtaleModuleInverseImage f R ⋙ (coefficientTransport f R S c).inverse :=
  (proEtaleRingModuleAdjunction f R S c).leftAdjointUniq
    ((a.comp (coefficientTransport f R S c).symm.toAdjunction).ofNatIsoRight
      (directImageComparison f R S c).symm)

private noncomputable def unitKernelCompEquivalenceIso
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (e : D ≌ E) :
    kernel a.unit ≅ kernel (a.comp e.toAdjunction).unit := by
  let q : L ⋙ R ≅ (L ⋙ e.functor) ⋙ (e.inverse ⋙ R) :=
    Functor.isoWhiskerLeft L
      ((Functor.leftUnitor R).symm ≪≫ Functor.isoWhiskerRight e.unitIso R ≪≫
        Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm
  refine kernel.mapIso _ _ (Iso.refl _) q ?_
  ext X
  simp [q, Adjunction.comp_unit_app]

private noncomputable def unitKernelIsoOfLeftIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R') (e : L ≅ L') :
    kernel a.unit ≅ kernel b.unit := by
  let b' := b.ofNatIsoLeft e.symm
  let r := a.rightAdjointUniq b'
  let q : L ⋙ R ≅ L' ⋙ R' :=
    Functor.isoWhiskerLeft L r ≪≫ Functor.isoWhiskerRight e R'
  refine kernel.mapIso _ _ (Iso.refl _) q ?_
  ext X
  change a.unit.app X ≫ (r.hom.app (L.obj X) ≫ R'.map (e.hom.app X)) =
    𝟙 X ≫ b.unit.app X
  rw [← Category.assoc, Adjunction.unit_rightAdjointUniq_hom_app]
  simp [b', Adjunction.ofNatIsoLeft_unit, ← R'.map_comp]

attribute [local irreducible] proEtaleRingModuleAdjunction

set_option maxHeartbeats 1000000 in
-- The pointwise kernel functor's identity proof needs more unfolding heartbeats.
private noncomputable def pointwiseKernel
    {C D : Type*} [Category* C] [Category* D] [Abelian D]
    {F G : C ⥤ D} (η : F ⟶ G) : C ⥤ D where
  obj X := kernel (η.app X)
  map f := kernel.map _ _ (F.map f) (G.map f) (η.naturality f).symm
  map_id X := equalizer.hom_ext (by simp)
  map_comp f g := equalizer.hom_ext (by simp)

private noncomputable def pointwiseKernelIso
    {C D : Type*} [Category* C] [Category* D] [Abelian D]
    {F G : C ⥤ D} (η : F ⟶ G) : kernel η ≅ pointwiseKernel η := by
  let ev := CategoryTheory.evaluation C D
  refine NatIso.ofComponents
    (fun X ↦ asIso (kernelComparison η (ev.obj X))) ?_
  intro X Y f
  apply (cancel_mono (kernel.ι (η.app Y))).mp
  simp only [Category.assoc]
  change (kernel η).map f ≫ kernelComparison η (ev.obj Y) ≫ kernel.ι (η.app Y) =
    kernelComparison η (ev.obj X) ≫
      kernel.map (η.app X) (η.app Y) (F.map f) (G.map f)
        (η.naturality f).symm ≫ kernel.ι (η.app Y)
  have hc (X : C) : kernelComparison η (ev.obj X) ≫ kernel.ι (η.app X) =
      (kernel.ι η).app X := kernelComparison_comp_ι η (ev.obj X)
  rw [hc, kernel.lift_ι, ← Category.assoc, hc]
  exact (kernel.ι η).naturality f

private noncomputable def supportKernelIso {T U : Scheme.{u}} (j : U ⟶ T)
    (A : Type u) [CommRing A] [Finite A] :
    kernel (C := proEtaleRingModules T (proEtaleConstantRing T A) ⥤
      proEtaleRingModules T (proEtaleConstantRing T A))
        (sfConstantModuleAdjunction j A).unit ≅ sfIntrinsicSectionsWithSupport j A :=
  pointwiseKernelIso (sfConstantModuleAdjunction j A).unit

/-- Closed direct image is exact and its unbounded derived functor is left adjoint to
R i!_0, where i!_0 is the closed inverse image of the kernel of the open adjunction unit.
Exactness makes the displayed derived direct image the direct image applied termwise.
Source: Weil blueprint, order 1859; Stacks Project, Tags 09BM, 09AH and 07A5
(blueprint: lem-exc-proetale-closed-support).

Proof:
1. A Noetherian target makes the complementary open quasi-compact. Apply ringed open-closed
localization to the actual constant coefficient sheaf, identifying its inverse images with
constant coefficients through the canonical constant-section maps. Closed direct image is
exact, fully faithful, and identifies modules on Z with modules vanishing on U.
2. For a map i* M → N the composite with the open adjunction unit is zero by restriction
to U. The kernel universal property factors it uniquely through sections with support.
The supported-category equivalence has inverse i*, giving the sheaf adjunction to i!_0.
3. Choose K-injective resolutions with injective terms among all constant-ring modules.
The sheaf right adjoint preserves K-injectives because closed direct image is exact:
the termwise homotopy adjunction makes maps from acyclic complexes null-homotopic.
4. Compute derived Hom into those resolutions. The termwise adjunction, followed by the
K-injective Hom identification, gives the derived adjunction naturally in both variables.
The total right derived construction is everywhere defined by those same resolutions.
There is no restriction on boundedness, constructibility, or the values of R i!_0.

Complete DAG proof plan:
1. By [lem-weil-pbc-noetherian-open-subscheme-noetherian], $U\cap V$ is quasi-compact for each
affine open $V\subset T$, so $j$ is quasi-compact. The canonical structure maps $i^{-1}A_T\to A_Z$
and $j^{-1}A_T\to A_U$ are isomorphisms by [prop-weil-pbc-proetale-constant-exact], whose
coefficient convention explicitly supplies these maps; hence the ringed coefficient hypotheses of
the essential-image theorem hold. Thus [lem-exc-proetale-closed-exact], [lem-exc-proetale-closed-
fully-faithful], and [lem-exc-proetale-closed-essential-image] give exactness and full
faithfulness of $i_*$, and identify its essential image with the sheaves killed by $j^*$. We make
explicit the open-restriction calculation used below. Under the localized-site identification of
[lem-weil-proetale-weakly-etale-localization], $j^*$ is restriction: in the inverse-image formula
of [def-weil-proetale-inverse-image], for $W\to U$ the indexing category has initial object $W\to
T$ with the identity $W\cong W\times_TU$, so its opposite has a terminal object and the presheaf
inverse image is $N(W)$; this is already a sheaf, with the restricted constant-ring action. By
[def-weil-proetale-module-direct-image], $(j^*j_*G)(W)=G(W\times_TU)=G(W)$, and the counit is this
identity. Consequently $j^*$ of the unit $N\to j_*j^*N$ is an isomorphism, inverse to that counit
by the adjunction triangle identity. Since $j^*$ preserves kernels by [prop-weil-pbc-proetale-
constant-exact], the sheaf $\Gamma_ZN=\ker(N\to j_*j^*N)$ has $j^*\Gamma_ZN=0$.
Dependencies: lem-weil-pbc-noetherian-open-subscheme-noetherian, lem-exc-proetale-closed-exact,
lem-exc-proetale-closed-fully-faithful, lem-exc-proetale-closed-essential-image, lem-weil-
proetale-weakly-etale-localization, def-weil-proetale-inverse-image, def-weil-proetale-module-
direct-image, prop-weil-pbc-proetale-constant-exact.

2. For a sheaf $M$ on $Z$, [lem-exc-proetale-closed-essential-image] gives $j^*i_*M=0$; for
$\Gamma_ZN$ of Step 1 it gives the natural isomorphism $\Gamma_ZN\to i_*i^*\Gamma_ZN$. If
$f:i_*M\to N$, naturality of the open unit $\eta$ gives $\eta_N f=j_*j^*(f)\eta_{i_*M}=0$, because
$j^*i_*M=0$. The kernel property therefore gives a unique factorization through $\Gamma_ZN$.
Composing with its displayed isomorphism and using [lem-exc-proetale-closed-fully-faithful] gives
the natural bijection $\operatorname{Hom}_T(i_*M,N)\cong\operatorname{Hom}_T(i_*M,\Gamma_ZN)\cong
\operatorname{Hom}_Z(M,i^*\Gamma_ZN)=\operatorname{Hom}_Z(M,i^!_0N)$, with the last equality from
[def-exc-proetale-sections-with-support]. Thus $i_*\dashv i^!_0$ on the whole sheaf categories.
These functors are additive: $i_*$ is additive by its sectionwise definition [def-weil-proetale-
module-direct-image], and its right adjoint preserves zero and finite products, hence biproducts
and their diagonal/codiagonal formula for addition.
Dependencies: lem-exc-proetale-closed-essential-image, lem-exc-proetale-closed-fully-faithful,
def-exc-proetale-sections-with-support, def-weil-proetale-module-direct-image.

3. Use the small skeletons in [def-weil-pbc-proetale-site]. The constant coefficient sheaf is a
sheaf of commutative rings, so [prop-pur-kinjective-resolutions-exist] supplies K-injective
resolutions on $T$ and $Z$ for arbitrary unbounded complexes. In [lem-weil-pbc-right-adjoint-
preserves-kinjective] take $\mathcal A=\operatorname{Sh}(T_{\mathrm{proet}},A)$, $\mathcal
B=\operatorname{Sh}(Z_{\mathrm{proet}},A)$, $v=i_*$ and $u=i^!_0$. Step 2 gives $v\dashv u$ and
Step 1 gives exactness of $v$, so $i^!_0$ sends K-injective complexes on $T$ to K-injective
complexes on $Z$. To apply [lem-weil-pbc-kinjective-total-derived], take $F=Q_Z\circ
(i^!_0)^K:K(T)\to D(Z)$, where $Q_Z$ is localization and the superscript $K$ means termwise
application on the homotopy category. This is an exact functor of triangulated categories:
additivity preserves the chain-homotopy equation, shifts and the biproduct differential matrix
defining each cone in [def-weil-abstract-derived-category]. The cited total-derived theorem
constructs $Ri^!_0$ and identifies $Ri^!_0N$ with $Q_Z(i^!_0I)$ whenever $N\to I$ is a K-injective
resolution on $T$.
Dependencies: def-weil-pbc-proetale-site, prop-pur-kinjective-resolutions-exist, lem-weil-pbc-
right-adjoint-preserves-kinjective, lem-weil-pbc-kinjective-total-derived, def-weil-abstract-
derived-category.

4. Exactness of $i_*$ and [lem-sf-exact-functor-derived-triangulated] give its functor on $D(Z)\to
D(T)$ by termwise application (also computing $Ri_*$). Let $K$ be any complex on $Z$, let $N$ be
any complex on $T$, and choose a K-injective resolution $N\to I$. Step 3 makes $i^!_0I$
K-injective and identifies it with $Ri^!_0N$ in $D(Z)$. The homotopy adjunction [lem-weil-pbc-
termwise-adjunction-homotopy] and the two K-injective Hom comparisons [lem-weil-pbc-kinjective-
hom-derived] give $$\operatorname{Hom}_{D(T)}(i_*K,N)\cong\operatorname{Hom}_{K(T)}(i_*K,I)\cong
\operatorname{Hom}_{K(Z)}(K,i^!_0I)\cong\operatorname{Hom}_{D(Z)}(K,Ri^!_0N).$$ The resolution can
be chosen functorially by [prop-pur-kinjective-resolutions-exist]; every displayed comparison is
natural in $K$ and $N$. These bijections therefore exhibit $i_*\dashv Ri^!_0$ on the whole
unbounded derived categories. No bound or constructibility assumption was used.
Dependencies: lem-sf-exact-functor-derived-triangulated, lem-weil-pbc-termwise-adjunction-
homotopy, lem-weil-pbc-kinjective-hom-derived, prop-pur-kinjective-resolutions-exist.
-/
theorem sfIntrinsicClosedAmbientAdjunction
    (A : Type u) [CommRing A] [Finite A]
    {Z U T : Scheme.{u}} [IsNoetherian T]
    (i : Z ⟶ T) [IsClosedImmersion i] (j : U ⟶ T) [IsOpenImmersion j]
    (_hij : IsCompl (Set.range i) (Set.range j)) :
    PreservesFiniteColimits (sfConstantModuleDirectImage i A) ∧
      Nonempty ((sfConstantModuleDirectImage i A).rightDerivedFunctor ⊣
        (sfIntrinsicClosedUpperShriek i j A).rightDerivedFunctor) := by
  let B := proEtaleConstantRing T A
  let Bi := proEtaleConstantRing Z A
  let Bj := proEtaleConstantRing U A
  let ci := sfConstantCoefficientIso i A
  let cj := sfConstantCoefficientIso j A
  let V : T.ProEt := ProEt.mk j
  let : IsOpenImmersion V.hom := ‹IsOpenImmersion j›
  let : QuasiCompact V.hom := inferInstanceAs (QuasiCompact j)
  obtain ⟨ai, aj, haddi, haddj, haddRi, haddRj, hlimLi, hcolLi, hlimLj, hcolLj,
    hlimRi, hcolRi, haddH, a0, eH, hrest⟩ :=
    proEtale_ringed_closed_kernel_adjoint i V _hij.compl_eq.symm B
  let ei := coefficientTransport i B Bi ci
  let ej := coefficientTransport j B Bj cj
  let li := pullbackComparison i B Bi ci ai
  let lj := pullbackComparison j B Bj cj aj
  let lj' : sfConstantModulePullback j A ⋙ ej.functor ≅
      proEtaleModuleInverseImage j B :=
    Functor.isoWhiskerRight lj ej.functor ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ej.counitIso ≪≫ Functor.rightUnitor _
  let eK : sfIntrinsicSectionsWithSupport j A ≅ ringedSupportKernel j B aj :=
    (supportKernelIso j A).symm ≪≫
      unitKernelCompEquivalenceIso (sfConstantModuleAdjunction j A) ej ≪≫
      unitKernelIsoOfLeftIso ((sfConstantModuleAdjunction j A).comp ej.toAdjunction) aj lj'
  let eS : sfIntrinsicClosedUpperShriek i j A ≅
      ringedClosedKernelShriek i j B aj ⋙ ei.inverse :=
    Functor.isoWhiskerRight eK (sfConstantModulePullback i A) ≪≫
      Functor.isoWhiskerLeft _ li ≪≫ (Functor.associator _ _ _).symm
  let a : sfConstantModuleDirectImage i A ⊣ sfIntrinsicClosedUpperShriek i j A :=
    ((ei.toAdjunction.comp a0).ofNatIsoLeft
      (directImageComparison i B Bi ci).symm).ofNatIsoRight eS.symm
  have : PreservesFiniteColimits (sfConstantModuleDirectImage i A) :=
    preservesFiniteColimits_of_natIso (directImageComparison i B Bi ci).symm
  have : PreservesLimitsOfSize.{0, 0} (sfConstantModuleDirectImage i A) :=
    (sfConstantModuleAdjunction i A).rightAdjoint_preservesLimits
  refine ⟨inferInstance, ⟨?_⟩⟩
  exact a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
    (sfConstantModuleDirectImage i A).rightDerivedFunctorIsoMapDerivedCategory.symm

end AlgebraicGeometry.Scheme
