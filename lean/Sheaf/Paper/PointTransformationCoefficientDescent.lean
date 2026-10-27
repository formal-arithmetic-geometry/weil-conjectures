/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q120
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.PointFdQbarCategory
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.PointSectionsScalarExtension
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.PointFibreDerivedTensorBasic
public import Sheaf.Paper.PointTransformationRationalNormalization
public import Sheaf.Paper.PointRationalFamilyCommonStageNaturality
import Sheaf.Paper.PointCompositeComparisonTower

/-! # Descent of arbitrary integral point-section transformations

Source: Deligne, Weil II, (1.1.3), p. 150 and (1.1.7), pp. 150--151;
normalized completed-coefficient argument extracted in the DAG by Q97 and Q93
(blueprint: lem-weil-point-transformation-coefficient-descent).

The comparison maps below are composites of the recorded canonical maps. They
introduce no alternative scalar extensions or choices of comparison isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

namespace WeilConjectures.PointTransformationDescent

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (g : Spec (.of D.k) ⟶ Spec (.of D.k))

/-- Integral sections, included in the ambient derived module category.
Source: Weil II (1.1.3) and the recorded point sections construction
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev integralSections (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  PointRationalNormalization.sections D l E

/-- The recorded completed pullback with its implied residue-field invertibility supplied.
Source: Weil II (1.1.7), the global finite-field convention
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev integralPullback (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  PointRationalNormalization.pullback D l hl g E

/-- The same recorded pullback on raw rational Hom tensors.
Source: Weil II (1.1.3) and the normalized derived operations
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev rationalPullback (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  PointRationalFamily.rationalPullback D l hl g E

/-- The recorded pullback on the literal common-stage pair category.
Source: Weil II (1.1.3), (1.1.7)
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev commonPullback :=
  PointRationalFamily.commonPullback D l hl Ω g

/-- Its literal object formula, used to specify representative endpoints.
Source: Weil II (1.1.3), (1.1.7)
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev pullbackObject (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :=
  PointRationalFamily.pullbackObject D l hl Ω g A

variable (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

/-- Alpha is the specified completed integral comparison, restricted to constructibles.
Source: normalized scalar comparison in the DAG, integral hypothesis
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev integralAlpha (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :=
  PointRationalNormalization.alpha D l hl g E L ι K

/-- Phi is precisely the recorded normalized sections comparison.
Source: normalized scalar comparison in the DAG, integral hypothesis
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev integralPhi (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :=
  PointRationalNormalization.phi D l hl E L ι K

/-- The rational comparison b = phi at P(K) after F(alpha inverse).
Source: normalized scalar comparison in the DAG, rational paragraph
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev rationalB (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :=
  PointRationalFamily.rationalB D l hl g E L ι K

/-- All supplied integral transformations; no components or invertibility are prescribed.
Source: the integral transformation hypothesis of the DAG
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev IntegralFamily :=
  PointRationalNormalization.IntegralFamily D l hl Ω g

/-- Compatibility uses the specified alpha and phi, in exactly their given directions.
Source: the displayed integral hypothesis of the DAG
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev IntegralCompatible (η : IntegralFamily D l hl Ω g) : Prop :=
  PointRationalNormalization.IntegralCompatible D l hl Ω g η

/-- A rational family is natural for every arrow in the raw scalar localization.
Source: the arbitrary tensor-sum assertion of the DAG
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev RationalFamily :=
  PointRationalFamily.RationalFamily D l hl Ω g

/-- The rational components are precisely eta tensored with the fraction field.
The canonical size-lift normalization makes the equality an equality of actual sections.
Source: the rational-component formula of the DAG
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev RationalNormalized (η : IntegralFamily D l hl Ω g)
    (t : RationalFamily D l hl Ω g) : Prop :=
  PointRationalNormalization.Components D l hl Ω g η t

/-- Rational scalar compatibility, using exactly the rationalizations of alpha and phi.
Source: equation (*) in proof step 3 of the DAG
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev RationalCompatible (t : RationalFamily D l hl Ω g) : Prop :=
  PointRationalFamily.RationalCompatible D l hl Ω g t

/-- The normalized pullback comparison at an arbitrary common stage, including its
specified transition identifications. Source: DAG proof steps 4--5
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev pullbackComparison
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  PointRationalFamily.pullbackComparison D l hl Ω g A N h

/-- The comparison b on the actual coefficient-field stage models.
Source: DAG proof steps 4--5; it is F(alpha inverse) followed by phi at P(K)
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev stageB
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  PointRationalFamily.stageB D l hl Ω g A N h

/-- The component at the coefficient field of a literal pair, transported by the
recorded Shrink algebra equivalence. Source: DAG proof step 6
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev stageComponent (t : RationalFamily D l hl Ω g)
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :=
  PointRationalFamily.stageComponent D l hl Ω g t A

/-- Extend that component to the very same field as a supplied representative.
Source: DAG proof step 6, t^L at (E,K)
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev componentAt (t : RationalFamily D l hl Ω g)
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  PointRationalFamily.componentAt D l hl Ω g t A N h

variable
  (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
  (N : Index l Ω) (hA : A.stage ≤ N) (hB : B.stage ≤ N)
  (f : A.toStage hA ⟶ B.toStage hB)

/-- A_L(u) = phi_target F_L(u) phi_source inverse.
Source: the first common-stage action formula in the DAG
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev fibreArrow :=
  PointRationalFamily.fibreArrow D l hl Ω A B N hA hB f

/-- B_L(u) = b_target H_L(u) b_source inverse.
Source: the second common-stage action formula in the DAG
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev pullbackArrow :=
  PointRationalFamily.pullbackArrow D l hl Ω g A B N hA hB f

/-- The usual finite-stage class in the recorded point-category cocone.
Source: common-stage realization in the DAG and def-weil-point-fd-qlbar-category
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev pointClass (X Y : DerivedCategory.PointFdQbar l Ω)
    (M : Index l Ω) (hX : X.1 ≤ M) (hY : Y.1 ≤ M)
    (v : (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hX).toRingHom).obj X.2 ⟶
      (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hY).toRingHom).obj Y.2) : X ⟶ Y :=
  PointRationalFamily.pointClass l Ω X Y M hX hY v

/-- The finite-stage class of the prescribed first action formula.
Source: DAG proof step 5
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev fibreClass :=
  PointRationalFamily.fibreClass D l hl Ω A B N hA hB f

/-- The finite-stage class of the prescribed composite action formula.
Source: DAG proof step 5
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev pullbackClass :=
  PointRationalFamily.pullbackClass D l hl Ω g A B N hA hB f

/-- Extend a point-category representative using exactly its specified tensor towers.
Source: def-weil-point-fd-qlbar-category, transition formula in the DAG proof step 7
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev pointTransport (X Y : DerivedCategory.PointFdQbar l Ω)
    (N M : Index l Ω) (hX : X.1 ≤ N) (hY : Y.1 ≤ N) (h : N ≤ M)
    (v : (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hX).toRingHom).obj X.2 ⟶
      (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hY).toRingHom).obj Y.2) :=
  PointRationalFamily.pointTransport l Ω X Y N M hX hY h v

/-- Same-field naturality, its preservation under every further finite extension,
and the two actual common-stage functor actions.
Source: the last two paragraphs of the DAG statement, proof steps 5--7
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
def RepresentativeAssertions (t : RationalFamily D l hl Ω g) : Prop :=
  ∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (hA : A.stage ≤ N) (hB : B.stage ≤ N)
    (f : A.toStage hA ⟶ B.toStage hB),
    (fibreArrow D l hl Ω A B N hA hB f ≫ componentAt D l hl Ω g t B N hB =
      componentAt D l hl Ω g t A N hA ≫ pullbackArrow D l hl Ω g A B N hA hB f) ∧
    (∀ (M : Index l Ω) (h : N ≤ M),
      HEq (pointTransport l Ω (pointQbarFibreObj D l hl Ω A)
        (pointQbarFibreObj D l hl Ω B) N M hA hB h
        (fibreArrow D l hl Ω A B N hA hB f))
        (fibreArrow D l hl Ω A B M (hA.trans h) (hB.trans h)
          ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).tr h f)) ∧
      HEq (pointTransport l Ω
        (pointQbarFibreObj D l hl Ω (pullbackObject D l hl Ω g A))
        (pointQbarFibreObj D l hl Ω (pullbackObject D l hl Ω g B)) N M hA hB h
        (pullbackArrow D l hl Ω g A B N hA hB f))
        (pullbackArrow D l hl Ω g A B M (hA.trans h) (hB.trans h)
          ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).tr h f))) ∧
    HEq ((pointQbarFibre D l hl Ω).map
      (StageSystem.PairCategory.mkHom N hA hB f))
      (fibreClass D l hl Ω A B N hA hB f) ∧
    HEq ((commonPullback D l hl Ω g ⋙ pointQbarFibre D l hl Ω).map
      (StageSystem.PairCategory.mkHom N hA hB f))
      (pullbackClass D l hl Ω g A B N hA hB f)

/-- Both action formulas are independent of every equivalent common-stage representative.
Source: the final sentence of the DAG statement and its equality criterion, step 7
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
def RepresentativeIndependent : Prop :=
  ∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N M : Index l Ω) (hA : A.stage ≤ N) (hB : B.stage ≤ N)
    (hA' : A.stage ≤ M) (hB' : B.stage ≤ M)
    (f : A.toStage hA ⟶ B.toStage hB) (f' : A.toStage hA' ⟶ B.toStage hB'),
    StageSystem.PairCategory.mkHom N hA hB f =
      StageSystem.PairCategory.mkHom M hA' hB' f' →
    fibreClass D l hl Ω A B N hA hB f = fibreClass D l hl Ω A B M hA' hB' f' ∧
      pullbackClass D l hl Ω g A B N hA hB f =
        pullbackClass D l hl Ω g A B M hA' hB' f'

/-- The common-stage components are exactly the classes of the rational components.
HEq inserts only the object equalities in the defining specifications of the two
recorded functors. Source: DAG final paragraph and proof step 7
(blueprint: lem-weil-point-transformation-coefficient-descent). -/
abbrev CommonNormalized (t : RationalFamily D l hl Ω g)
    (τ : pointQbarFibre D l hl Ω ⟶ commonPullback D l hl Ω g ⋙ pointQbarFibre D l hl Ω) :
    Prop :=
  PointRationalFamily.CommonNormalized D l hl Ω g t τ

private theorem comparison_hom
    (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (PointCompositeComparison.comparison D l hl g E L ι).hom.app K =
      (rationalB D l hl g E L ι K).hom := by
  simp only [PointCompositeComparison.comparison, rationalB, PointRationalFamily.rationalB,
    Iso.trans_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    PointCompositeComparison.sectionsPullback, PointCompositeComparison.pullback,
    PointRationalFamily.rationalPullback, Functor.comp_obj,
    Category.id_comp, Category.comp_id]

/-- Arbitrary scalar-compatible integral point-section transformations descend to the
raw rational categories and to the specified common-stage point category.

Source: Deligne, Weil II, (1.1.3), p. 150 and (1.1.7), pp. 150--151;
the normalized completed-coefficient descent is the agent-written argument in the DAG
(blueprint: lem-weil-point-transformation-coefficient-descent).

Proof:
1. Use [lem-weil-isomorphism-derived-pullback] with the automorphism $g$ of $s$; $\ell$ is
invertible since $\ell\ne p$. Thus $P_E$ preserves the integral category. By
[def-weil-rationalization-karoubi] the rational category has exactly the integral objects and
Hom groups tensored with $E$. The formulas in [def-weil-finite-coefficient-point] and
[def-weil-derived-pullback-tensor-hom] give, for an integral $v:K\to K'$ and $a\in E$,
$F_E(v\otimes a)=a(F_E^{\mathrm{int}}(v)\otimes E)$ and $H_E(v\otimes
a)=a(F_E^{\mathrm{int}}(P_Ev)\otimes E)$. In particular the proposed component
$t_{E,K}:=\eta^E_K\otimes E$ has source $F_EK$ and target $H_EK$, both in
$D^b_{\mathrm{fd}}(E)$. Uses: lem-weil-isomorphism-derived-pullback,
def-weil-rationalization-karoubi, def-weil-finite-coefficient-point,
def-weil-derived-pullback-tensor-hom.

2. For integral $v:K\to K'$, the assumed naturality is
$F_E^{\mathrm{int}}(P_Ev)\eta^E_K=\eta^E_{K'}F_E^{\mathrm{int}}(v)$. Apply the module-complex
scalar-extension functor $-\otimes_{\mathcal O_E}E$ and multiply the resulting equality by $a\in
E$. The formulas of [def-weil-finite-coefficient-point] and
[def-weil-derived-pullback-tensor-hom] give $H_E(v\otimes a)t_{E,K}=t_{E,K'}F_E(v\otimes a)$.
Every tensor is a finite sum of pure tensors by [def-weil-rationalization-karoubi]. Bilinearity
of composition therefore gives, for $u=\sum_jv_j\otimes a_j$, $H_E(u)t_{E,K}=\sum_j
a_j(H_E(v_j\otimes1)t_{E,K})=\sum_j a_j(t_{E,K'}F_E(v_j\otimes1))=t_{E,K'}F_E(u)$. This includes
zero, sums and every balanced tensor representative, since both functor maps already factor
through the tensor product. Uses: def-weil-finite-coefficient-point,
def-weil-derived-pullback-tensor-hom, def-weil-rationalization-karoubi.

3. For $E\subset L$, tensor the assumed integral compatibility equation with $L$ over $\mathcal
O_L$. The last display of [lem-weil-point-sections-scalar-extension] identifies its sections
comparisons with precisely $\bar\varphi_{E,L}$, and rationalizing the pullback comparison of
[lem-pur-integral-operations-scalar-extension] gives precisely $\bar\alpha_{E,L}$. Consequently
the equation becomes $$b_{E,L,K}\,t_{L,K\otimes_E L}=(t_{E,K}\otimes_E L)\,\bar\varphi_{E,L,K}.
\tag{*}$$ No comparison is replaced by an arbitrary isomorphism: tensoring is a functor, so it
preserves the composite and the inverse occurring in the supplied equation. Tensoring the unit
and tower equations in the two cited statements preserves those equations too. This proves the
specified rational scalar compatibility, including equality of fields. Uses:
lem-weil-point-sections-scalar-extension, lem-pur-integral-operations-scalar-extension.

4. Write $S_{L/E}K=K\otimes_E L$, $T_{L/E}A=A\otimes_E L$, and write
$a^C:S_{N/L}S_{L/E}\xrightarrow{\sim}S_{N/E}$ and $a^D:T_{N/L}T_{L/E}\xrightarrow{\sim}T_{N/E}$
for the specified associators. For $E\subset L\subset N$, suppress these associators
momentarily. The two cited tower equations read
$$\bar\alpha_{E,N}=\bar\alpha_{L,N,S_{L/E}K}\,S_{N/L}(\bar\alpha_{E,L}),\qquad
\bar\varphi_{E,N}=(\bar\varphi_{E,L}\otimes_LN)\bar\varphi_{L,N,S_{L/E}K}.$$ Insert these
expressions into $b_{E,N}=\bar\varphi_{E,N,P_EK}F_N(\bar\alpha_{E,N})^{-1}$ and use naturality
of $\bar\varphi_{L,N}$ for $\bar\alpha_{E,L}^{-1}$. The result, with associators restored, is
$$b_{E,N,K}H_N(a^C_K)=a^D_{H_EK}(b_{E,L,K}\otimes_LN)b_{L,N,S_{L/E}K}. \tag{**}$$ Explicitly the
middle interchange is
$\bar\varphi_{L,N,S_{L/E}P_EK}F_N(S_{N/L}\bar\alpha_{E,L}^{-1})=(F_L(\bar\alpha_{E,L}^{-1})\otim
es_LN)\bar\varphi_{L,N,P_LS_{L/E}K}$.
This gives (**), and the unit equations give $b_{E,E}=1$ under unit identifications. Naturality
follows by composing the two natural isomorphisms defining $b$. All the inputs here are the
naturality, identity and tower assertions of [lem-weil-point-sections-scalar-extension] and
[lem-pur-integral-operations-scalar-extension]. Uses: lem-weil-point-sections-scalar-extension,
lem-pur-integral-operations-scalar-extension.

5. Let $u:S_{L/E}K\to S_{L/E'}K'$ represent a common-stage arrow as in
[def-weil-algebraically-closed-coefficients]. The point-fiber action in
[def-weil-finite-coefficient-point] is
$A_L(u)=\bar\varphi_{E',L,K'}F_L(u)\bar\varphi_{E,L,K}^{-1}$. The pullback action of
[def-weil-derived-pullback-tensor-hom] first gives
$\bar\alpha_{E',L,K'}^{-1}P_L(u)\bar\alpha_{E,L,K}$. Apply the point-fiber action to this arrow,
now between $P_EK$ and $P_{E'}K'$. Expanding $F_L$ of the composite gives exactly
$B_L(u)=b_{E',L,K'}H_L(u)b_{E,L,K}^{-1}$. Thus these are the two specified functors, rather than
alternative realizations. At a common stage they preserve identities and composition: the
intermediate $\bar\varphi^{-1}\bar\varphi$ or $b^{-1}b$ cancels, and $F_L,H_L$ are functors. The
two tower equations (the sections equation and (**)) show that scalar extension of
$A_L(u),B_L(u)$ is respectively $A_N(u_N),B_N(u_N)$ after the source and target associators.
Hence their classes are unchanged by further extension, and by changing to any equivalent
representative, using the equality criterion of [def-weil-point-fd-qlbar-category]. Uses:
def-weil-algebraically-closed-coefficients, def-weil-finite-coefficient-point,
def-weil-derived-pullback-tensor-hom, def-weil-point-fd-qlbar-category.

6. The proposed component at $(E,K)$ is the finite-stage class of $t_{E,K}$. Put
$t^L_{E,K}=t_{E,K}\otimes_E L$ with the target-category unit identifications of
[def-weil-point-fd-qlbar-category]. Equation (*) says
$b_{E,L,K}^{-1}t^L_{E,K}=t_{L,S_{L/E}K}\bar\varphi_{E,L,K}^{-1}$. Apply Step 2 at field $L$ to
the arbitrary rational morphism $u:S_{L/E}K\to S_{L/E'}K'$ and calculate in $D(L)$:
$$\begin{aligned} B_L(u)t^L_{E,K}&=b_{E',L,K'}H_L(u)t_{L,S_{L/E}K}\bar\varphi_{E,L,K}^{-1}\\
&=b_{E',L,K'}t_{L,S_{L/E'}K'}F_L(u)\bar\varphi_{E,L,K}^{-1}\\
&=t^L_{E',K'}\bar\varphi_{E',L,K'}F_L(u)\bar\varphi_{E,L,K}^{-1}=t^L_{E',K'}A_L(u).\end{aligned}$$
This is naturality over the very same field $L$, before passing to any colimit. Uses:
def-weil-point-fd-qlbar-category.

7. For a further finite field $N\supset L$, apply $-\otimes_LN$ to the equality of Step 6 and
conjugate by the source and target tower associators. Functoriality preserves the equality and
the expansions of Step 5 identify it with the equation for $u_N$. If $[L,u]=[L',v]$,
[def-weil-algebraically-closed-coefficients] gives $N\supset L,L'$ with $u_N=v_N$. The two
equations then have identical sides in $D(N)$; by [def-weil-point-fd-qlbar-category] they yield
the same equality of morphism classes. Therefore all supplied integral components give the
claimed natural transformation on the common-stage category. This proves independence of
representative without assuming injectivity of transition maps, invertibility of $\eta$, or any
special formula for its components. Uses: def-weil-algebraically-closed-coefficients,
def-weil-point-fd-qlbar-category. -/
theorem coefficient_descent [IsIso g]
    (η : IntegralFamily D l hl Ω g) (hη : IntegralCompatible D l hl Ω g η) :
    ∃ t : RationalFamily D l hl Ω g,
      RationalNormalized D l hl Ω g η t ∧ RationalCompatible D l hl Ω g t ∧
      RepresentativeAssertions D l hl Ω g t ∧ RepresentativeIndependent D l hl Ω g ∧
      ∃ τ : pointQbarFibre D l hl Ω ⟶
          commonPullback D l hl Ω g ⋙ pointQbarFibre D l hl Ω,
        CommonNormalized D l hl Ω g t τ := by
  obtain ⟨t, hnorm, _, hscalar, _⟩ :=
    PointRationalNormalization.rational_normalization D l hl Ω g η hη
  obtain ⟨hunit, htower, hactions, _, hext, hind⟩ :=
    PointCompositeComparison.tower_and_actions D l hl g Ω
  have hcommon := PointRationalFamily.rational_family_common_stage_naturality
    D l hl Ω g t hscalar
    (fun E K ↦ heq_of_eq (by
      have h := hunit.2 E K
      rw [comparison_hom] at h
      exact h))
    (fun E L N h k K ↦ heq_of_eq (by
      have ht := htower E L N h k K
      simp only [comparison_hom] at ht
      exact ht))
    (fun A B N hA hB f ↦
      ⟨(hactions A B N hA hB f).1, (hactions A B N hA hB f).2.1,
        fun M h ↦ hext A B N M hA hB h f⟩)
  refine ⟨t, hnorm, hscalar, ?_, hind, hcommon.2.2⟩
  intro A B N hA hB f
  exact ⟨(hcommon.1 A B N hA hB f).1,
    fun M h ↦ hext A B N M hA hB h f,
    (hactions A B N hA hB f).1, (hactions A B N hA hB f).2.1⟩

end WeilConjectures.PointTransformationDescent
