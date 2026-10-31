/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfLocalizationData

import WeilConjectures.AlgebraicGeometry.SfIntegralLocalizationConstruction
import WeilConjectures.AlgebraicGeometry.SfRationalLocalizationConstruction
import WeilConjectures.AlgebraicGeometry.SfCommonStageLocalizationConstruction
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
import WeilConjectures.AlgebraicGeometry.CommonStageRationalCompositionNaturality
import WeilConjectures.AlgebraicGeometry.PodCommonStageCompositorNaturality
import WeilConjectures.AlgebraicGeometry.FrobeniusDetailed
import WeilConjectures.AlgebraicGeometry.IsomorphismFieldTransport
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Supported localization at every coefficient stage

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-localization,
proposition prop-sf-localization-all-stages
(blueprint: prop-sf-localization-all-stages).

The records below only package the clauses of the proposition. They do not assume
existence of any of its adjoints or connecting arrows.

## Main statements

- `sfLocalizationAllStages`: the four coefficient stages and their finite-Tor bounds.
- `sfLocalizationExceptionalLimit`: the integral exceptional inverse-limit formula.
- `sfLocalizationAllStages_weil`: equivariance for a pair descending to the finite field.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v c h

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

private theorem sfWeilLift
    {C Z U : Type c} [Category.{h} C] [Category.{h} Z] [Category.{h} U]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroMorphisms Z]
    (S : SfSupportedLocalization (𝟭 C) (𝟭 Z) (𝟭 U))
    (P : C ⥤ C) (Q : Z ⥤ Z) (H : U ⥤ U)
    [P.IsEquivalence] [Q.IsEquivalence] [H.IsEquivalence]
    [P.CommShift ℤ] [P.IsTriangulated]
    (d : S.iPull ⋙ Q ≅ P ⋙ S.iPull)
    (dj : S.jPull ⋙ H ≅ P ⋙ S.jPull) :
    Nonempty (SfWeilLocalization S P Q H) := by
  let a := Endofunctor.IsoAlgebra.mateIso S.closedAdjunction d
  let b := Endofunctor.IsoAlgebra.mateIso S.exceptionalAdjunction a
  let r := Endofunctor.IsoAlgebra.mateIso S.openAdjunction dj
  let A := Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction
    S.exceptionalAdjunction a b rfl
  let B := Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction S.openAdjunction dj r rfl
  let LF := Endofunctor.IsoAlgebra.mapOfNatIso b
  let LI := Endofunctor.IsoAlgebra.mapOfNatIso a
  let LJ := Endofunctor.IsoAlgebra.mapOfNatIso dj
  let LR := Endofunctor.IsoAlgebra.mapOfNatIso r
  let LT := Endofunctor.IsoAlgebra.mapOfNatIso (P.commShiftIso (1 : ℤ))
  have boundary_square (K : Endofunctor.IsoAlgebra P) :
      P.map (S.boundary.app K.carrier) ≫ ((LT.obj (LI.obj (LF.obj K))).str).hom =
        ((LR.obj (LJ.obj K)).str).hom ≫ S.boundary.app K.carrier := by
    let e₁ := (LI.obj (LF.obj K)).str
    let e₂ := K.str
    let e₃ := (LR.obj (LJ.obj K)).str
    let δ := e₃.inv ≫ P.map (S.boundary.app K.carrier) ≫
      (P.commShiftIso (1 : ℤ)).hom.app (S.iPush.obj (S.exceptional.obj K.carrier)) ≫
      (shiftFunctor C (1 : ℤ)).map e₁.hom
    have h₁ : P.map (S.exceptionalAdjunction.counit.app K.carrier) ≫ e₂.hom =
        e₁.hom ≫ S.exceptionalAdjunction.counit.app K.carrier :=
      Endofunctor.IsoAlgebra.map_counit_app_comp_str
        S.exceptionalAdjunction a b rfl K
    have h₂ : P.map (S.openAdjunction.unit.app K.carrier) ≫ e₃.hom =
        e₂.hom ≫ S.openAdjunction.unit.app K.carrier :=
      Endofunctor.IsoAlgebra.map_unit_app_comp_str S.openAdjunction dj r rfl K
    let e : P.mapTriangle.obj
        (Triangle.mk (S.exceptionalAdjunction.counit.app K.carrier)
          (S.openAdjunction.unit.app K.carrier) (S.boundary.app K.carrier)) ≅
        Triangle.mk (S.exceptionalAdjunction.counit.app K.carrier)
          (S.openAdjunction.unit.app K.carrier) δ :=
      Triangle.isoMk _ _ e₁ e₂ e₃ h₁ h₂ (by
        dsimp only [Functor.mapTriangle, Triangle.mk]
        simp only [δ, Category.assoc, Iso.hom_inv_id_assoc, Functor.comp_obj])
    have hδ := S.unique_boundary K.carrier δ
      (isomorphic_distinguished _ (P.map_distinguished _ (S.distinguished K.carrier)) _ e.symm)
    have hs : ((LT.obj (LI.obj (LF.obj K))).str).hom =
        (P.commShiftIso (1 : ℤ)).hom.app _ ≫
          (shiftFunctor C (1 : ℤ)).map e₁.hom := by
      rfl
    rw [hs]
    simpa only [δ, e₃, LI, LF, Endofunctor.IsoAlgebra.mapOfNatIso_obj_carrier,
      Iso.hom_inv_id_assoc, Category.assoc] using congrArg (fun f ↦ e₃.hom ≫ f) hδ
  let β : LJ ⋙ LR ⟶ LF ⋙ LI ⋙ LT :=
    { app K := ObjectProperty.homMk ⟨S.boundary.app K.carrier, boundary_square K⟩
      naturality K L f := by
        apply ObjectProperty.hom_ext
        apply Endofunctor.Algebra.Hom.ext
        exact S.boundary.naturality f.hom.f }
  exact ⟨{
    exceptionalLift := LF
    closedLift := LI
    openPullLift := LJ
    openPushLift := LR
    shiftLift := LT
    exceptional_underlying := rfl
    closed_underlying := rfl
    open_pull_underlying := rfl
    open_push_underlying := rfl
    shift_underlying := rfl
    closedAdjunction := A
    openAdjunction := B
    counit_underlying := fun K ↦ HEq.rfl
    open_unit_underlying := fun K ↦ HEq.rfl
    closed_unit_underlying := fun K ↦ HEq.rfl
    boundaryLift := β
    boundary_underlying := fun K ↦ HEq.rfl }⟩

private theorem sfWeilTransports
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    (sfWeilFrobeniusPullback D l hl T₀ E).IsEquivalence ∧
    (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω).IsEquivalence ∧
    (∃ s : (sfWeilFrobeniusPullback D l hl T₀ E).CommShift ℤ,
      letI := s; (sfWeilFrobeniusPullback D l hl T₀ E).IsTriangulated) ∧
    (∃ s : (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω).CommShift ℤ,
      letI := s; (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω).IsTriangulated) := by
  let i := fun x ↦ sfWeilPrimeInvertible D l hl T₀ x
  let : ∀ x : (D.geometricFiber T₀).left,
      Invertible (l : (D.geometricFiber T₀).left.residueField x) := i
  let : (D.geometricFiber T₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber T₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber T₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType
      (pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber T₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact
      (pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  obtain ⟨iX, iY, H⟩ := isomorphismFieldTransport D l hl Ω
    (D.geometricFrobenius T₀).hom
  have hiX : iX = i := Subsingleton.elim _ _
  have hiY : iY = i := Subsingleton.elim _ _
  cases hiX
  cases hiY
  obtain ⟨_, _, hE, _, _, _, _, ⟨A⟩, _⟩ := H
  obtain ⟨R⟩ := (hE E).1
  exact ⟨R.rationalEquivalence, A.equivalence,
    ⟨R.rationalShift, R.rationalExact⟩, ⟨A.shift, A.exact⟩⟩

/-- The Frobenius pullback squares follow from naturality of the prescribed
pullback compositors and commutativity of the geometric Frobenius square. -/
private theorem sfWeilPullbackSquares
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (Y₀ X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (f₀ : Y₀ ⟶ X₀) :
    letI := fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
    letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
    Nonempty (rationalDerivedPullback l E (sfLocalizationFiberMap D f₀) ⋙
        sfWeilFrobeniusPullback D l hl Y₀ E ≅
      sfWeilFrobeniusPullback D l hl X₀ E ⋙
        rationalDerivedPullback l E (sfLocalizationFiberMap D f₀)) ∧
    Nonempty (commonStageDerivedPullback l Ω (sfLocalizationFiberMap D f₀) ⋙
        sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ≅
      sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ⋙
        commonStageDerivedPullback l Ω (sfLocalizationFiberMap D f₀)) := by
  let := fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  let := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  dsimp only [sfWeilFrobeniusPullback, sfCommonStageWeilFrobeniusPullback]
  let f := sfLocalizationFiberMap D f₀
  have w : (D.geometricFrobenius Y₀).hom ≫ f =
      f ≫ (D.geometricFrobenius X₀).hom := by
    let σ := @FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
      (Fintype.ofFinite D.k₀) _ _ _
    change D.galoisMap Y₀.hom σ ≫ f = f ≫ D.galoisMap X₀.hom σ
    apply pullback.hom_ext
    · simp only [Category.assoc, f, sfLocalizationFiberMap, Over.pullback_map_left,
        pullback.lift_fst]
      rw [← Category.assoc, (D.galoisMap_projections Y₀.hom σ).1,
        (D.galoisMap_projections X₀.hom σ).1]
      simp only [pullback.lift_fst]
    · simp only [Category.assoc, f, sfLocalizationFiberMap, Over.pullback_map_left,
        pullback.lift_snd]
      rw [(D.galoisMap_projections Y₀.hom σ).2,
        (D.galoisMap_projections X₀.hom σ).2]
      simp
  let cr (V W Z : Scheme.{u}) (g : V ⟶ W) (h : Z ⟶ V)
      [∀ x : V, Invertible (l : V.residueField x)]
      [∀ y : W, Invertible (l : W.residueField y)]
      [∀ z : Z, Invertible (l : Z.residueField z)] :
      rationalDerivedPullback l E (h ≫ g) ≅
        rationalDerivedPullback l E g ⋙ rationalDerivedPullback l E h :=
    NatIso.ofComponents (pullbackTensorRationalComposition l E g h)
      (fun a ↦ commonStageRationalComposition_naturality l E g h a)
  let cc (V W Z : Scheme.{u}) (g : V ⟶ W) (h : Z ⟶ V)
      [∀ x : V, Invertible (l : V.residueField x)]
      [∀ y : W, Invertible (l : W.residueField y)]
      [∀ z : Z, Invertible (l : Z.residueField z)] :
      commonStageDerivedPullback l Ω (h ≫ g) ≅
        commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω h :=
    NatIso.ofComponents (pullbackTensorCommonComposition l Ω g h)
      (fun a ↦ PodCoefficientDescent.commonStagePullbackComposition_naturality l Ω g h a)
  exact ⟨⟨(cr _ _ _ f (D.geometricFrobenius Y₀).hom).symm ≪≫
    eqToIso (congrArg (fun m : _ ⟶ _ ↦ rationalDerivedPullback l E m) w) ≪≫
      cr _ _ _ (D.geometricFrobenius X₀).hom f⟩,
    ⟨(cc _ _ _ f (D.geometricFrobenius Y₀).hom).symm ≪≫
      eqToIso (congrArg (fun m : _ ⟶ _ ↦ commonStageDerivedPullback l Ω m) w) ≪≫
        cc _ _ _ (D.geometricFrobenius X₀).hom f⟩⟩

private theorem sfWeilFiberRange (D : FiniteFieldDatum.{u})
    {Y₀ X₀ : Over (Spec (.of D.k₀))} (f : Y₀ ⟶ X₀) :
    Set.range (sfLocalizationFiberMap D f) =
      (pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ⁻¹'
        Set.range f.left := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have h : IsPullback (pullback.fst Y₀.hom g) (sfLocalizationFiberMap D f)
      f.left (pullback.fst X₀.hom g) := by
    refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback X₀.hom g)
    · convert IsPullback.of_hasPullback Y₀.hom g using 1 <;>
        simp [sfLocalizationFiberMap, Over.pullback, g]
    · simp [sfLocalizationFiberMap, Over.pullback, g]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨pullback.fst Y₀.hom g y, ?_⟩
    calc
      f.left (pullback.fst Y₀.hom g y) =
          (pullback.fst Y₀.hom g ≫ f.left) y :=
        (Scheme.Hom.comp_apply _ _ y).symm
      _ = (sfLocalizationFiberMap D f ≫ pullback.fst X₀.hom g) y :=
        congrArg (fun e : pullback Y₀.hom g ⟶ X₀.left ↦ e y) h.w
      _ = _ := Scheme.Hom.comp_apply _ _ y
  · rintro ⟨y, hy⟩
    obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback h y x hy
    exact ⟨z, hz⟩

/-- Supported localization at every coefficient stage, without imposing a finite
cohomological dimension on the base for clauses (1)--(4). The finite-Tor assertions
carry the separate finite-cd hypothesis in their tor fields.
Source: Weil blueprint, proposition prop-sf-localization-all-stages
(blueprint: prop-sf-localization-all-stages).

Proof plan (the node's steps):

1. Finite-level setting and open direct image. Interfaces phrased with a global finite-field datum
but an arbitrary scheme $T$ are used with an auxiliary finite-field datum of characteristic
different from $\ell$; they impose no map from $T$ to that auxiliary field. In the Weil clause
alone the datum is the actual base-field datum of the statement. The adic-coefficient interfaces
are instantiated with $(A,I)=(\mathcal O_E,(\varpi_E))$: the valuation-ring theorem gives a
Noetherian DVR, the quotient theorem gives finite quotients, and
[lem-weil-pbc-standard-quotients-perfect], with $n\ge1$, gives the augmented resolution $[\mathcal
O_E\xrightarrow{\varpi_E^n}\mathcal O_E]\to A_{E,n}[0]$ in degrees $-1,0$. This verifies
perfectness of the ordinary $\mathcal O_E$-module $A_{E,n}$ in the adic datum; it does not
identify constant and completed coefficient sheaf categories. All schemes in the assertion are
Noetherian: finite type over a field implies Noetherianity, so $j$ is quasi-compact (every open of
a Noetherian space is quasi-compact), and is separated. Write $G\cong\nu_U^*G'$ with $G'$ bounded
constructible, using the constructible-origin equivalence. The comparison for qcqs direct images
gives $Rj_*G\cong\nu_X^*Rj_{\mathrm{et},*}G'$. For each of the finitely many nonzero $\mathcal
H^q(G')$, the open-immersion finiteness theorem makes all $R^pj_*\mathcal H^q(G')$ constructible,
with only finitely many nonzero. The truncation spectral sequence and the Serre property then show
that $Rj_{\mathrm{et},*}G'$ is bounded constructible. Pulling back by the exact $\nu_X^*$ proves
(1) at $A_{E,n}$.

2. Ambient adjoints before localization. Work with $B_X=(A_{E,n})_X$ or $B_X=\widehat{\mathcal
O}_{E,X}$. The coefficient inverse-image theorem identifies the pulled-back rings with $B_Z,B_U$,
respecting quotient projections. Since $j$ is quasi-compact by Step 1,
[lem-sf-ringed-closed-kernel-adjoint] applies. It constructs $i^!_0N=i^*\ker(N\to j_*j^*N)$, its
ambient derived right adjoint $Ri^!_0$, and all four adjunctions needed for the unit's Hom
argument. In particular $i^*i_*\cong1$, $j^*Rj_*\cong1$ and $j^*i_*=0$ on all complexes. Exact
immersion pullback and exact closed pushforward are termwise; the exact-functor factorization
gives their triangulated structures. The K-injective total-derived theorem gives the exact
structure of $Ri^!_0$. None of these inputs uses the supported triangle.

3. The prescribed Hom(-,K) comparison. The ordinary ringed short exact sequence, termwise on $M$,
gives the distinguished triangle $j_!j^*M\to M\to i_*i^*M\to(j_!j^*M)[1]$. Apply Hom(-,K) and
shifts. The four adjunctions of Step 2 identify its outer groups as
$$\operatorname{Hom}(i_*i^*M,K)=\operatorname{Hom}(i^*M,Ri^!_0K)=\operatorname{Hom}(M,i_*Ri^!_0K),$$
$$\operatorname{Hom}(j_!j^*M,K)=\operatorname{Hom}(j^*M,j^*K)=\operatorname{Hom}(M,Rj_*j^*K).$$
The maps are induced by the actual exceptional counit $e$ and open unit $u$: substitute the
adjunction bijections and cancel the adjacent unit/counit pairs. Complete $e$ to a distinguished
triangle. Apply [lem-sf-ordinary-triangle-counit-cone], whose four adjunctions, invertible closed
and open counits, vanishing $j^*i_*$, and ordinary triangle have all just been supplied. Its
specified comparison from the counit cone to $Rj_*j^*K$ is invertible and preserves $u$. Transport
the connecting arrow through that comparison. This proves the ambient supported triangle at both
finite and completed coefficients, with the prescribed first two maps. The same lemma gives
closed-to-open orthogonality for every input and shift.

4. Finite constructible restriction and the determination interface. Step 3 is an ambient
argument, so it does not presuppose boundedness of $Ri^!_0K$. For finite coefficients and
constructible $K$, its third term is bounded constructible by Step 1 and pullback preservation.
The finite bounded constructible subcategory is triangulated; hence $A=i_*Ri^!_0K$ is bounded
constructible. The termwise closed counit of Step 2 gives $Ri^!_0K\cong i^*A$, which is bounded
constructible by the pullback theorem. The ambient adjunction restricts to these full
subcategories. This proves finite-level (2) and the existence in (3). Closed pushforward
preservation and full faithfulness are also supplied by the all-stage closed-unit theorem. The
natural-transformation determination theorem can be applied to the counit $i^*i_*\to1$: both
functors are exact, and the degreewise counit commutes with the usual signed shifts. It is an
isomorphism on sheaves. The truncation triangle of a bounded-cohomology complex has a shift of its
highest cohomology sheaf as last vertex; the first vertex has fewer nonzero cohomology sheaves.
Starting with zero, two-out-of-three propagates invertibility to every bounded complex. This
spells out the unit's determination tool with the shift hypothesis it actually requires; the cone
comparison itself has already been proved for every $M$ in Step 3, without assuming that a
transformation is determined by its values on generators.

5. Integral operations. Put $R=\mathcal O_E$. The DVR and finite-quotient theorems and the
ordinary augmented resolution $[R\xrightarrow{\varpi_E^n}R]\to A_{E,n}[0]$ from the
perfect-quotient theorem verify the Noetherian adic datum, for $n\ge1$. Apply
[prop-weil-pbc-direct-image-limits] to $i,j$: its canonical strict-tower comparison identifies
ordinary completed-ring direct image with $R\varprojlim_n\operatorname{Res}_nRf_{*,n}K_n$,
including finite projection maps and their quotient compatibility. Thus it is precisely the
integral direct image in [def-weil-derived-direct-image]. The constant/completion equivalence
identifies the two completeness conventions, without identifying their ambient module categories.
The integral direct-image constructibility theorem and integral pullback theorem give
constructibility and the required uniform bounds. For reduction detection, a complete $C$ whose
reductions vanish has defining Roos triangle $C\to0\to0\to C[1]$, hence $C=0$. Apply this to the
cone of a morphism: the integral subcategory is triangulated and reduction is exact derived
tensor, so isomorphisms are detected by all reductions.

6. Ordinary and completed immersion pullbacks. Apply
[lem-sf-immersion-completed-pullback-comparison] to $i,j$. Its actual coefficient-ring map is the
canonical inverse-image isomorphism, not a general scalar extension. It identifies ordinary
inverse image with the specified completed pullback on derived-complete objects, including its
completion unit, finite projections and quotient transitions. In particular both inverse images
preserve the precise integral constructible category, with the same uniform cohomological
intervals. The ambient adjunctions of Step 2 therefore restrict, using the direct-image
identifications of Step 5, to the integral operations in the statement. Their unit/counit formulas
are the restrictions of the ambient formulas. Consequently $j^*Rj_*\cong1$, $j^*i_*=0$, and the
orthogonality of Step 3 holds in the integral subcategories.

7. Integral restriction and reduction of the exceptional counit. In the ambient supported triangle
of Step 3, $K$ and $Rj_*j^*K$ are integral constructible by Steps 5-6. Triangulated closure gives
$A=i_*Ri^!_0K$ integral constructible; the invertible closed counit identifies $Ri^!_0K=i^*A$, so
Step 6 restricts the ambient adjunction. Let $T_n$ be derived reduction. Under the canonical
pullback and direct-image projection comparisons, the transpose of $T_n\eta_j$ is
$T_n(\varepsilon_jj^*\circ j^*\eta_j)=1$. Thus the reduced open map is the finite open unit. The
reduced triangle and the finite triangle have identical middle and open vertices and maps. Their
first vertices are closed-supported, by the closed direct-image reduction comparison.
Closed-to-open orthogonality and [lem-weil-pbc-triangle-morphism-extension] (1)-(2) give the
unique triangle morphism with identity middle and open components; [lem-sf-triangle-morphism-iso]
makes the closed component invertible. Applying $i_n^*$ gives $(Ri^!K)_n\cong Ri_n^!K_n$,
preserving the exceptional counit. For $m\ge n$, restrict the $n$-triangle to
$A_{E,m}$-coefficients. The direct-image/restriction-of-scalars comparison identifies its open
vertex with $Rj_{m,*}\operatorname{Res}_{m,n}j_n^*K_n$. Orthogonality therefore holds in this
single category. Both candidate transition comparisons have the same natural middle and open
components, so the uniqueness clause of the triangle-morphism-extension lemma makes them equal.
This proves quotient-transition coherence, not just objectwise reduction isomorphisms.

8. Identification with the specified exceptional inverse image. At finite level
[lem-exc-closed-ambient] supplies the ambient etale closed adjoint. The ordinary etale open-closed
sequence gives a triangle on all complexes. Exact inverse image, exact closed direct image (a
closed immersion is finite), and open full faithfulness supply the four adjunctions and invertible
counits, and the shift-compatible right-adjoint theorem gives the closed adjoint its exact
structure, so [lem-sf-ordinary-triangle-counit-cone] applies. Open finiteness and the truncation
spectral sequence make its open vertex bounded constructible. The cohomology long exact sequence
expresses each cohomology sheaf of its first vertex as an extension of a kernel by a cokernel of
constructible sheaves; the Serre property gives constructibility, and boundedness follows from the
same sequence. Exact $i^*$ and constructible pullback restrict the closed adjoint. The
compactification $Z\xrightarrow1Z\xrightarrow iX$ gives compact-support direct image $i_*$, hence
the adjoint in the exceptional-inverse-image definition. For a finite pro-etale constructible $K$,
choose its bounded constructible etale origin. Exact comparison pullback and the canonical
direct-image mate identify the middle and open maps of that etale supported triangle with Step 3.
Orthogonality and [lem-weil-pbc-triangle-morphism-extension] (1)-(2) give the unique comparison;
[lem-sf-triangle-morphism-iso] makes it invertible. Applying $i^*$ identifies the exceptional
functors and counits, hence the adjunction units. Step 7 identifies the integral reductions with
these finite objects respecting quotient transitions. Completeness gives $Ri^!K\cong
R\varprojlim_n\operatorname{Res}_nRi_n^!K_n$, the stated integral definition. The Hom bijections
remain those of Step 2.

9. At both the finite and integral stages, $Ri^!$ is an exact functor, linear over the
corresponding coefficient ring. At finite level its $A_{E,n}$-linearity can also be seen directly:
under the adjunction a map $P\to Ri^!K$ is sent to its closed pushforward followed by the counit;
both operations are linear, so the inverse bijection, and the representing action on maps, are
linear. Give it the unique shift structure compatible with the adjunction $i_*\dashv Ri^!$, using
the adjunction shift theorem. The closed functor $i_*$ is exact: on the ambient categories it is a
derived direct image, and the full finite and integral constructible subcategories are
triangulated, and its preservation at each stage was proved above. The
shift-compatible-right-adjoint theorem now makes $Ri^!$ exact. Thus all the functors, units,
counits and triangle maps constructed so far have compatible exact structures; this supplies the
exactness required before scalar localization.

10. Uniqueness of the connecting arrow and of maps of supported triangles, at the finite and
integral stages. Write a supported triangle as
$A\xrightarrow{e}K\xrightarrow{u}B\xrightarrow{\delta}A[1]$, where $A$ is in the closed image and
$B$ in the open direct image. Given $f:K\to K'$, the right-adjoint bijection determines a unique
$a:A\to A'$ with $e'a=fe$. TR3 supplies a map $b:B\to B'$ completing $(a,f)$ to a triangle
morphism. Its first square on $K$ gives $bu=u'f$. The natural map $Rj_*j^*f$ satisfies the same
equation. The difference of the two maps factors through $\delta$ by Hom-out exactness and so is
zero, since $\operatorname{Hom}(A[1],B')=0$. Therefore $b=Rj_*j^*f$, proving functoriality. For
two choices of $\delta$ with fixed $e,u$, TR3 with the two identity maps gives such a $b$; the
same vanishing forces $b=1$, and the last square forces the two connecting arrows to coincide. The
closed map is also unique when only $f$ is specified: its difference factors through $B'[-1]$ by
Hom-into exactness, and $\operatorname{Hom}(A,B'[-1])=0$. This proves exactly the uniqueness
promised by the unit and by (3).

11. Coefficient-category identification before rationalization. On each of X, Z and U, finite type
over the field gives Noetherianity and finite dimension, and ell is invertible. By
[lem-weil-pbc-integral-stratified-perfect-characterization], the full completed-coefficient
category of [def-weil-derived-complete-integral-detailed] is exactly the category of
[def-weil-pbc-bounded-constructible-complete], including the existence of compatible etale-origin
witnesses, with the same completed ring sheaf and reduction functors. Their raw rationalizations
therefore agree, with the same objects and Hom modules tensored with E. Use this identification
also for the finite-stage categories in Step 12. Rational stage. Apply rational transport to the
exact $R$-linear functors and to their units and counits. The identities remain identities, and
the Hom adjunction bijections tensor with $E$, so $i_{*,E}\dashv Ri_E^!$ and $j_E^*\dashv
Rj_{*,E}$. Distinguished integral triangles remain distinguished under raw scalar localization.
Hom orthogonality remains zero after tensoring. For a middle map $f$, the rational adjunction
determines the closed map $a$, and TR3 gives an open map $b$. Subtracting the natural open map
gives a map factoring through the closed vertex shifted by $1$; rational orthogonality makes that
factor zero. Applying this to identity middle and closed maps forces two connecting arrows to
agree, and the underlying objects still have the specified integral representatives. This proves
(1)–(3) at $E$, without an idempotent completion.

12. Coefficient-extension coherence and the algebraically closed stage. For $E\subset L$, scalar
extension commutes with $i_*,Rj_*,i^*,j^*$ by the scalar-extension theorem. It carries the open
unit to the open unit as follows. Write $S$ for coefficient extension and $\pi:S
Rf_{*,E}\xrightarrow{\sim}Rf_{*,L}S$. Under the pullback comparison, the transpose of $\pi
S\eta_{f,K}$ is $S(\varepsilon_f f^*\circ f^*\eta_f)=1$, since $\pi$ is the canonical projection
mate adjoint to $S\varepsilon_f$. Thus $\pi S\eta_f$ is the $L$-unit; its counit equation is
$\varepsilon_{f,L}\circ f_L^*\pi=S\varepsilon_{f,E}$ under that same comparison. This uses the
canonical derived tensor/pullback identification, not an arbitrarily chosen isomorphism of the two
functors. Thus scalar extension of the supported triangle is a triangle with the prescribed middle
and open vertices and maps at $L$. Step 10 gives a unique isomorphism of these supported
triangles; applying $i^*$ gives $Ri_E^!K\otimes_EL\cong Ri_L^!(K\otimes_EL)$, preserving the
counit. Comparing successive extensions with direct extension, both composites preserve this
counit and the middle object, so Step 10 makes them equal. For the unit equation set $L=E$ and use
the identity scalar comparison; both supported comparisons preserve the counit and hence are
identities by Step 10. For the shift equation compare the scalar-extension comparison at $K[1]$
with its shifted comparison at $K$ under the supplied exact shifts. Both have the same middle and
open components, so Step 10 makes their closed components agree too. Exact functors and compatible
transformations now descend by the common-stage descent theorem; the Verdier-axioms theorem keeps
the triangles distinguished. The finite-stage adjunction bijections commute with extension, and
hence induce adjunction bijections on the filtered-colimit Hom groups. Orthogonality passes to
these same colimits. This proves (1)–(3) at $\overline{\mathbf Q}_\ell$ for the specified pair
category.

13. At each stage take $H=Ri^!Rj_*G$. The adjunction and orthogonality give
$\operatorname{Hom}(N,H)=\operatorname{Hom}(i_*N,Rj_*G)=0$ for every $N$; taking $N=H$ makes
$1_H=0$, so $H=0$. Full faithfulness of the closed pushforward gives the isomorphism $Q\to
Ri^!i_*Q$ by the closed-unit theorem. This proves (4).

14. Finite Tor preparation. For $A=A_{E,n}$ and $\kappa=A/(\varpi_E)$, the residue criteria detect
Tor amplitude by the cohomological interval of $-\otimes_A^L\kappa$ on the etale and pro-etale
constructible categories. Every application below is to a bounded constructible object, already
established in Steps 1–4 and 8. Derived pullback is monoidal; the coefficient-ring maps identify
pullback of $\kappa$ with $\kappa$. Exact inverse image therefore preserves the interval of the
residue tensor, so $i^*$ and $j^*$ preserve Tor intervals. They preserve constructibility by the
pullback theorem. The comparison-pullback Tor theorem ensures that an etale origin $G'$ of a
pro-etale finite-Tor $G$ has the same Tor interval, and conversely. In particular these assertions
do not assume that every bounded constructible $A$-complex is perfect.

15. The closed pushforward preserves the same Tor interval. Let $P$ on $Z$ have interval $[a,b]$,
and put $C=i_*P\otimes_A^L\kappa$. Exactness and monoidality of $j^*$ give $j^*C=0$. For each $r$,
the sheaf $\mathcal H^r(C)$ is therefore in the closed image by the essential-image theorem, and
its closed unit identifies it with $i_*i^*\mathcal H^r(C)$. Exactness of $i^*$, its monoidality
and $i^*i_*P\cong P$ give $i^*\mathcal H^r(C)=\mathcal H^r(P\otimes_A^L\kappa)$, which is zero
outside $[a,b]$. Hence $\mathcal H^r(C)=0$ there. Apply the pro-etale residue criterion to the
bounded constructible $i_*P$ (closed constructible preservation is included in the all-stage
closed-unit theorem). This proves finite-level (3′).

16. Uniform etale direct-image bound. Set $N=2d+c$. When $k$ is algebraically closed, $c=0$, so
the etale direct-image vanishing theorem applied to $j$ gives $R^qj_*M=0$ for $q>N$, for every
$A$-module sheaf, with a bound independent of $n$. For a general field with
$\operatorname{cd}_{\mathrm{tor}}(k)\le c$, the same inference has the following explicit
argument: on the basis of affine etale $V\to X$, the scheme $V\times_XU$ is finite type over $k$
and has dimension at most $d$ by etale local-dimension invariance: the local ring at each point
has the dimension of the corresponding local ring on $U$, and the stalk-dimension chain theorem
identifies these local dimensions with the lengths of generalization chains. Taking their supremum
gives the topological dimension bound. The finite-type torsion-cd theorem makes its cohomology
vanish in degrees $>2d+c$. The higher-direct-image sheafification formula then makes $R^qj_*M$
zero on $X$. The forgetful derived-direct-image comparison justifies using the underlying torsion
abelian sheaf in this formula. When $U$ is empty the direct image is zero and $N=c\ge0$ works
directly, with no use of $\dim\varnothing=-\infty$.

17. Open Tor bound. Let $G$ have Tor interval $[a,b]$, and choose its bounded constructible etale
origin $G'$; by Step 14, $G'\otimes_A^L\kappa$ has cohomology only in $[a,b]$. The truncation
spectral sequence, with Step 16's vanishing bound, puts $Rj_*(G'\otimes_A^L\kappa)$ in $[a,b+N]$.
The projection-formula lemma for a finitely presented constant module applies to $f=j$, $K=G'\in
D^-$ and $M=\kappa$: $A$ is Noetherian (indeed Artinian), $\kappa=A/(\varpi_E)$ is finitely
presented by a single relation, and the required uniform bound is Step 16. It gives
$Rj_*G'\otimes_A^L\kappa\cong Rj_*(G'\otimes_A^L\kappa)$. Exact monoidal comparison pullback and
the qcqs direct-image comparison give the same residue interval for $Rj_*G$. This object is
already bounded constructible by Step 1; the residue criterion now gives Tor interval
$[a,b+2d+c]$. This is (1′); the residue field was not treated as a perfect $A$-module.

18. Closed exceptional Tor bound. Let $K$ have Tor interval $[a,b]$. By Steps 14 and 17, $j^*K$
has interval $[a,b]$ and $B=Rj_*j^*K$ interval $[a,b+N]$. Tensor the finite supported triangle
with $\kappa$; exactness of derived tensor leaves it distinguished. The exact cohomology segment
$\mathcal H^{r-1}(B\otimes_A^L\kappa)\to\mathcal H^r(i_*Ri^!K\otimes_A^L\kappa)\to\mathcal
H^r(K\otimes_A^L\kappa)$ is zero on the two outside terms whenever $r<a$ or $r>b+N+1$. Apply the
exact monoidal $i^*$ and $i^*i_*\cong1$ to identify the residue tensor of $Ri^!K$, giving the same
vanishing. Since $Ri^!K$ is bounded constructible by Step 4, the residue criterion gives interval
$[a,b+2d+c+1]$. This proves finite-level (2′).

19. At the integral stage use the definition by a single uniform Tor interval for all reductions.
Steps 5–6 identify reductions of $Rj_*,i_*,i^*,j^*$ with the finite operations; Step 7 identifies
reductions of $Ri^!$. Applying Steps 14–18 at every $n$ gives the same intervals $[a,b]$,
$[a,b+2d+c]$, $[a,b+2d+c+1]$, independent of $n$. Thus (1′)–(3′) hold integrally. The finite-Tor
categories are full triangulated subcategories by their defining finite/integral
triangulated-subcategory theorems, so the supported triangles lie in them, and the adjunction
bijections and (4) restrict to them. At $E$ and $\overline{\mathbf Q}_\ell$ the finite-Tor
categories equal the constructible categories by definition. This proves (4′) and all the
remaining assertions about finite Tor.

20. Weil equivariance. Use the stated descent of the whole closed/open pair over $k_0$. The
Weil-operation theorem supplies Frobenius comparisons for $i_*,i^*,j^*,Rj_*$ and equivariance of
the open unit; all their constructible domains have now been proved. Write $F_K=i_*Ri^!K$. For a
Weil complex $(K,\theta_K)$, pull the supported triangle back by the Frobenius automorphism and
compare it with the supported triangle of $K$. TR3 and Step 10 give the unique map
$\theta_F:g_X^*F_K\to F_K$ extending the given $\theta_K$ and its open counterpart. It is
invertible by two-out-of-three. The induced $i^*\theta_F$, combined with the pullback composition
comparison, gives $\theta_{Ri^!K}:g_Z^*Ri^!K\xrightarrow{\sim}Ri^!K$. The counit is equivariant by
construction. Under the adjunction Hom bijections constructed in Step 2 and identified with the
specified functor in Step 8 this action on the right adjoint is the mate of the action on $i_*$,
so the adjunction bijections commute with Frobenius; in particular the unit, which corresponds to
an identity, is equivariant. Finally Step 10 says the connecting arrow is the unique one
completing the first two arrows, so its Frobenius conjugate is itself. This proves equivariance of
all three arrows and of the exceptional unit.
-/
theorem sfLocalizationAllStages
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k))
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X : Scheme.{u}) (t : X ⟶ Spec (.of k))
    [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]
    {Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : Set.range j = (Set.range i)ᶜ) :
    (∀ n : ℕ, Nonempty (SfFiniteLocalization l E n k i j)) ∧
    Nonempty (SfIntegralLocalization l E k hl t i j) ∧
    Nonempty (SfRationalLocalization l E k hl t i j) ∧
    Nonempty (SfAlgebraicallyClosedLocalization l Ω k hl t i j) := by
  have integral (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] : Nonempty (SfIntegralLocalization l F k hl t i j) :=
    sfIntegralLocalizationConstruction k l hl F X t i j hij
  obtain ⟨I⟩ := integral E
  obtain ⟨R⟩ := sfRationalLocalizationConstruction k l hl E X t i j hij I
  have rational (L : AlgebraicallyClosedCoefficients.Index l Ω) :
      Nonempty (SfRationalLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) k hl t i j) := by
    obtain ⟨IL⟩ := integral (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
    exact sfRationalLocalizationConstruction k l hl _ X t i j hij IL
  obtain ⟨A⟩ := sfCommonStageLocalizationConstruction k l hl Ω X t i j hij rational
  exact ⟨fun n ↦ ⟨I.finiteStages n⟩, ⟨I⟩, ⟨R⟩, ⟨A⟩⟩

/-- Weil-equivariant supported localization, with the closed/open pair itself
obtained by base change from the finite field, and with the current fixed-pair
Weil categories. The lifts carry exactly the actual underlying adjunction maps.
Source: Weil blueprint, supported localization, final paragraph
(blueprint: prop-sf-localization-all-stages).
Proof: the immersion pair commutes with geometric Frobenius. Apply the canonical
pullback/direct-image comparisons to the four adjunctions. Their mates identify
the Frobenius pullback of the closed right adjoint with the right adjoint of the
Frobenius pullback. Uniqueness of adjoints gives the coefficient-compatible
exceptional comparison. The mate equations make the exceptional counit, open
unit, and exceptional unit equivariant. Pull back the distinguished triangle;
its first two arrows are those same equivariant maps. Closed-to-open orthogonality
and uniqueness of the connecting arrow identify the pulled-back boundary with
the original boundary. Thus all three arrows and the unit are morphisms of the
fixed pairs. Repeat after rationalization and common-stage descent; the specified
scalar comparisons respect units, counits and the boundary. No triangulated
structure on fixed pairs is asserted. -/
theorem sfLocalizationAllStages_weil
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X₀ Z₀ U₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    (i₀ : Z₀ ⟶ X₀) (j₀ : U₀ ⟶ X₀)
    [IsClosedImmersion i₀.left] [IsOpenImmersion j₀.left]
    (hij : Set.range j₀.left = (Set.range i₀.left)ᶜ) :
    (∃ S : SfSupportedLocalization
        (𝟭 (sfRationalConstructibleCategory l E (D.geometricFiber X₀).left))
        (𝟭 (sfRationalConstructibleCategory l E (D.geometricFiber Z₀).left))
        (𝟭 (sfRationalConstructibleCategory l E (D.geometricFiber U₀).left)),
      S.iPull = @rationalDerivedPullback l _ E _ _ _ _ _ (sfLocalizationFiberMap D i₀)
        (sfWeilPrimeInvertible D l hl Z₀) (sfWeilPrimeInvertible D l hl X₀) ∧
      S.jPull = @rationalDerivedPullback l _ E _ _ _ _ _ (sfLocalizationFiberMap D j₀)
        (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl X₀) ∧
      Nonempty (SfWeilLocalization S
        (sfWeilFrobeniusPullback D l hl X₀ E) (sfWeilFrobeniusPullback D l hl Z₀ E)
        (sfWeilFrobeniusPullback D l hl U₀ E))) ∧
    (∃ S : SfSupportedLocalization
        (𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left))
        (𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Z₀).left))
        (𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber U₀).left)),
      S.iPull = @commonStageDerivedPullback l _ Ω _ _ _ _ _ (sfLocalizationFiberMap D i₀)
        (sfWeilPrimeInvertible D l hl Z₀) (sfWeilPrimeInvertible D l hl X₀) ∧
      S.jPull = @commonStageDerivedPullback l _ Ω _ _ _ _ _ (sfLocalizationFiberMap D j₀)
        (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl X₀) ∧
      Nonempty (SfWeilLocalization S
        (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
        (sfCommonStageWeilFrobeniusPullback D l hl Z₀ Ω)
        (sfCommonStageWeilFrobeniusPullback D l hl U₀ Ω))) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have hi : IsClosedImmersion (sfLocalizationFiberMap D i₀) :=
    MorphismProperty.overPullbackMap
      (P := fun {A B : Scheme.{u}} (f : A ⟶ B) ↦ IsClosedImmersion f) g i₀ inferInstance
  have hj : IsOpenImmersion (sfLocalizationFiberMap D j₀) :=
    MorphismProperty.overPullbackMap
      (P := fun {A B : Scheme.{u}} (f : A ⟶ B) ↦ IsOpenImmersion f) g j₀ inferInstance
  have hX : IsSeparated (D.geometricFiber X₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd X₀.hom g))
  have hXft : LocallyOfFiniteType (D.geometricFiber X₀).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom g))
  have hXqc : QuasiCompact (D.geometricFiber X₀).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom g))
  have hpair : Set.range (sfLocalizationFiberMap D j₀) =
      (Set.range (sfLocalizationFiberMap D i₀))ᶜ := by
    rw [sfWeilFiberRange, sfWeilFiberRange, hij, Set.preimage_compl]
  have hk : IsUnit (l : D.k) := by
    let := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
    have hunit : IsUnit (l : D.k₀) :=
      (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) hl.symm).isUnit
    simpa only [map_natCast] using hunit.map (algebraMap D.k₀ D.k)
  obtain ⟨_, _, ⟨R⟩, ⟨A⟩⟩ := sfLocalizationAllStages D.k l
    hk E Ω (D.geometricFiber X₀).left
    (D.geometricFiber X₀).hom (sfLocalizationFiberMap D i₀)
    (sfLocalizationFiberMap D j₀) hpair
  obtain ⟨⟨di⟩, ⟨dai⟩⟩ := sfWeilPullbackSquares D l hl E Ω Z₀ X₀ i₀
  obtain ⟨⟨dj⟩, ⟨daj⟩⟩ := sfWeilPullbackSquares D l hl E Ω U₀ X₀ j₀
  obtain ⟨pR, pA, ⟨sR, eR⟩, ⟨sA, eA⟩⟩ := sfWeilTransports D l hl E Ω X₀
  obtain ⟨qR, qA, _, _⟩ := sfWeilTransports D l hl E Ω Z₀
  obtain ⟨hR, hA, _, _⟩ := sfWeilTransports D l hl E Ω U₀
  constructor
  · refine ⟨R.supported, ?_, ?_, ?_⟩
    · exact R.closed_pull
    · exact R.open_pull
    · let := sR
      let := eR
      apply sfWeilLift R.supported
      · exact Functor.isoWhiskerRight (eqToIso R.closed_pull) _ ≪≫
          di ≪≫
          Functor.isoWhiskerLeft _ (eqToIso R.closed_pull).symm
      · exact Functor.isoWhiskerRight (eqToIso R.open_pull) _ ≪≫ dj ≪≫
          Functor.isoWhiskerLeft _ (eqToIso R.open_pull).symm
  · refine ⟨A.supported, ?_, ?_, ?_⟩
    · exact A.closed_pull
    · exact A.open_pull
    · let := sA
      let := eA
      apply sfWeilLift A.supported
      · exact Functor.isoWhiskerRight (eqToIso A.closed_pull) _ ≪≫ dai ≪≫
          Functor.isoWhiskerLeft _ (eqToIso A.closed_pull).symm
      · exact Functor.isoWhiskerRight (eqToIso A.open_pull) _ ≪≫ daj ≪≫
          Functor.isoWhiskerLeft _ (eqToIso A.open_pull).symm


end WeilConjectures
