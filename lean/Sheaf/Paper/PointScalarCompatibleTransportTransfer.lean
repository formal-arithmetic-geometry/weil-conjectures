/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module
public import Sheaf.Paper.PointSectionsScalarExtension
public import Sheaf.Paper.IsomorphismComparisonScalarExtension
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.CoefficientComplexRationalization
public import Sheaf.Paper.SfIntegralConstructibleLinear
public import Sheaf.Paper.PointProEtaleSectionsExactOfUniverses
import Sheaf.CategoryTheory.SemilinearScalarLocalization
public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.IsomorphismDerivedPullback
public import Sheaf.Paper.PointAutomorphismRestrictionNatural
import Mathlib.Algebra.CharP.CharAndCard

/-! # Transfer of scalar-compatible point transports

Source: blueprint main-20261015, `def-weil-global-geometric-frobenius`,
first arrows of the ordinary and compact-support composites
(blueprint: lem-weil-point-scalar-compatible-transport-transfer).

All coefficient and geometric functors below are the recorded constructions.
The target functors J are linear, while u and v are only object-indexed families.
The final clause realizes the raw Hom tensors, including fractional arrows.
-/

@[expose] public noncomputable section
attribute [-instance] WeilConjectures.coefficientComplexModuleDerived
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- The coefficient prime is a unit at every point of `Spec K`, for every field `K` over the
finite base field `k₀`; at `K = k` this is the input of the coefficient-transported
inverse-image interface used by this item. The case `K = k` is also stated by
`pointTransportPrimeUnits` of `lem-weil-point-automorphism-transport-scalar-extension`, but that
node lists this item as a proof dependency, so its module is downstream and is not imported.
Source: blueprint main-20261015, first transport arrow of
`def-weil-global-geometric-frobenius` (blueprint:
`lem-weil-point-scalar-compatible-transport-transfer`), finite-field context.
Proof: cardinality `q = p^a` with positive `a` gives characteristic `p` on `k₀`.
Since `l` is prime and differs from `p`, its cast is nonzero and hence a unit in
`k₀`; map this unit to `K` along the algebra map, then through the inverse
`Γ(Spec K) = K` comparison and each germ. Ring homomorphisms preserve units and
natural-number casts. -/
theorem pointRestrictionPrimeUnits (K : Type u) [Field K] [Algebra D.k₀ K] (_hl : l ≠ D.p) :
    ∀ x : Spec (.of K), IsUnit (l : (Spec (.of K)).presheaf.stalk x) := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  have hunit : IsUnit (l : D.k₀) :=
    (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) _hl.symm).isUnit
  intro x
  simpa only [map_natCast] using (hunit.map (algebraMap D.k₀ K)).map
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (Spec (.of K)).presheaf.germ ⊤ x (by trivial)).hom

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]

/-- Restriction followed by the distinguished inverse-image coprojection. The
module transformation is fixed on every section by the recorded restriction theorem;
restriction of scalars removes only the auxiliary `ULift` on `O_E`.
Source: blueprint main-20261015, first transport arrow of
`def-weil-global-geometric-frobenius` (blueprint:
`lem-weil-point-scalar-compatible-transport-transfer`), using the recorded
`lem-weil-point-automorphism-restriction-natural` section formula. -/
def pointRestrictionIntegralModules :
    pointCompletedSections D.k l E ⟶
      inverseImageIntegralModules l E g ⋙ pointCompletedSections D.k l E :=
  Functor.whiskerRight
    (point_automorphism_restriction_natural l E D hl g none).2.2.choose
    (ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l E) ≃+* _).symm.toRingHom)

/-- Termwise restriction localized at quasi-isomorphisms, followed by the canonical
exact-functor composition comparison. This fixes the point transport on all derived
objects and arrows, including unbounded complexes, using exactly the sectionwise
restriction above.
Source: blueprint main-20261015, first transport arrow of
`def-weil-global-geometric-frobenius` (blueprint:
`lem-weil-point-scalar-compatible-transport-transfer`), derived localization clause. -/
def pointRestrictionIntegralDerived :
    pointCompletedDerivedSections D.k l E ⟶
      inverseImageIntegralDerived l E g ⋙ pointCompletedDerivedSections D.k l E :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
    ((pointCompletedSections D.k l E).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    ((Functor.mapHomologicalComplex
      (inverseImageIntegralModules l E g ⋙ pointCompletedSections D.k l E) (.up ℤ)) ⋙
        DerivedCategory.Q)
    (pointCompletedDerivedSections D.k l E)
    (inverseImageIntegralModules l E g ⋙ pointCompletedSections D.k l E).mapDerivedCategory
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (pointRestrictionIntegralModules D l hl E g) (.up ℤ))
      DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso (inverseImageIntegralModules l E g)
      (pointCompletedSections D.k l E)).hom

end WeilConjectures
namespace WeilConjectures.PointScalarTransfer
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Q : Type u) [Field Q] [Algebra ℚ_[l] Q] [hQ : IsAlgClosure ℚ_[l] Q]
/-- The recorded bounded constructible derived-complete full subcategory.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
abbrev Integral (F : Padic.FiniteCoefficientFields l Q) :=
  sfIntegralConstructibleCategory l F.val (Spec (.of D.k))
/-- The coefficient-module derived category in the section universe.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
abbrev Modules (F : Padic.FiniteCoefficientFields l Q) :=
  DerivedCategory (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l F.val))
/-- The coefficient-field derived category in the same section universe.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
abbrev Fields (F : Padic.FiniteCoefficientFields l Q) :=
  DerivedCategory (ModuleCat.{u + 1} F.val)
/-- The recorded completed scalar extension restricted to constructible objects.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
def extension (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) :
    Integral D l Q E ⥤ Integral D l Q L :=
  sfConstructibleIntegralScalarExtension D.p l hl E.val L.val
    (IntermediateField.inclusion h) (Spec (.of D.k))
/-- Termwise exact sections restricted to the recorded integral category.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
def sections (F : Padic.FiniteCoefficientFields l Q) : Integral D l Q F ⥤ Modules l Q F :=
  (sfIntegralConstructible l F.val (Spec (.of D.k))).ι ⋙
    pointCompletedDerivedSections D.k l F.val
/-- The specified sections comparison, with the equivalent constructibility predicate.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
def phi (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) (H : Integral D l Q E) :
    (sections D l Q L).obj ((extension D l hl Q E L h).obj H) ≅
      (pointIntegralModuleDerivedTensor l E.val L.val (IntermediateField.inclusion h)).obj
        ((sections D l Q E).obj H) :=
  pointSectionsScalarExtensionIso l E.val L.val (IntermediateField.inclusion h) D hl
    H.obj ((pointIntegralConstructible_iff l E.val D hl H.obj).mpr H.property)
/-- The specified completed identity-extension comparison in the full subcategory.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
def unit (E : Padic.FiniteCoefficientFields l Q) (H : Integral D l Q E) :
    (extension D l hl Q E E le_rfl).obj H ≅ H :=
  (sfIntegralConstructible l E.val (Spec (.of D.k))).isoMk
    (pointIntegralScalarUnit l E.val D hl H.obj
      ((pointIntegralConstructible_iff l E.val D hl H.obj).mpr H.property))
/-- The specified integral tower associator in the full subcategory.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
def assoc (E L M : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) (j : L ≤ M)
    (H : Integral D l Q E) :
    (extension D l hl Q L M j).obj ((extension D l hl Q E L h).obj H) ≅
      (extension D l hl Q E M (h.trans j)).obj H :=
  (sfIntegralConstructible l M.val (Spec (.of D.k))).isoMk
    (pointIntegralScalarAssoc l E.val L.val (IntermediateField.inclusion h)
      M.val (IntermediateField.inclusion j) D hl H.obj
      ((pointIntegralConstructible_iff l E.val D hl H.obj).mpr H.property))
variable (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]
/-- The recorded coefficient-transported inverse image, restricted by preservation.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
def inverseImage (F : Padic.FiniteCoefficientFields l Q) : Integral D l Q F ⥤ Integral D l Q F :=
  (sfIntegralConstructible l F.val (Spec (.of D.k))).lift
    ((sfIntegralConstructible l F.val (Spec (.of D.k))).ι ⋙
      inverseImageIntegralDerived l F.val g)
    (fun H ↦ (isomorphismComparisonInputs_constructible l F.val g
      (pointRestrictionPrimeUnits D l D.k hl) (pointRestrictionPrimeUnits D l D.k hl)
      H.obj H.property).1)
/-- The restriction/coprojection transport descended termwise to the derived category.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
def sigma (F : Padic.FiniteCoefficientFields l Q) (H : Integral D l Q F) :=
  (pointRestrictionIntegralDerived D l hl F.val g).app H.obj
/-- The specified chi-conjugated scalar/inverse-image comparison, packaged as an iso.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
def beta (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) (H : Integral D l Q E) :
    (extension D l hl Q E L h).obj ((inverseImage D l hl Q g E).obj H) ≅
      (inverseImage D l hl Q g L).obj ((extension D l hl Q E L h).obj H) :=
  (sfIntegralConstructible l L.val (Spec (.of D.k))).isoMk
    ((scalarCompletionIso l E.val L.val (IntermediateField.inclusion h) (Spec (.of D.k)) _
      ((isomorphismComparisonInputs_constructible l E.val g
        (pointRestrictionPrimeUnits D l D.k hl) (pointRestrictionPrimeUnits D l D.k hl)
        H.obj H.property).1).1).symm ≪≫
      (isomorphismScalarTensorDerived l E.val L.val (IntermediateField.inclusion h) g).app
        H.obj ≪≫
      (inverseImageIntegralDerived l L.val g).mapIso
        (scalarCompletionIso l E.val L.val (IntermediateField.inclusion h) (Spec (.of D.k))
          H.obj H.property.1))
/-- The recorded ordinary integral module tensor descended termwise.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
abbrev tensor (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) :=
  pointIntegralModuleDerivedTensor l E.val L.val (IntermediateField.inclusion h)
/-- The coefficient-complex rationalization functor, at the section universe.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
abbrev rationalize (E : Padic.FiniteCoefficientFields l Q) :=
  (coefficientComplexRationalize.{u, u + 1} l E.val).mapDerivedCategory
/-- The recorded exact field-extension functor on coefficient complexes.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
abbrev fieldTensor (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) :=
  (coefficientComplexFieldTensor.{u, u + 1} l E.val L.val
    (IntermediateField.inclusion h)).mapDerivedCategory
/-- Exactly the specified coefficient-complex rationalization comparison.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
def rho (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) :=
  coefficientComplexDerivedBeta.{u, u + 1} l E.val L.val (IntermediateField.inclusion h)
variable (J : ∀ F : Padic.FiniteCoefficientFields l Q, Integral D l Q F ⥤ Integral D l Q F)
  [hJ : ∀ F, (J F).Linear (Padic.coefficientExtensionIntegers l F.val)]
variable (δ : ∀ (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L),
  J E ⋙ extension D l hl Q E L h ≅ extension D l hl Q E L h ⋙ J L)
variable (u : ∀ (F : Padic.FiniteCoefficientFields l Q) (H : Integral D l Q F),
  (inverseImage D l hl Q g F).obj H ⟶ (J F).obj H)
/-- The objectwise transport Gamma(u) after sigma; no naturality of u is assumed.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
def v (F : Padic.FiniteCoefficientFields l Q) (H : Integral D l Q F) :=
  sigma D l hl Q g F H ≫ (sections D l Q F).map (u F H)
/-- The target comparison Gamma(delta inverse) followed by the specified phi.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
def zeta (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) (H : Integral D l Q E) :=
  (sections D l Q L).map ((δ E L h).inv.app H) ≫
    (phi D l hl Q E L h ((J E).obj H)).hom
/-- Rationalization of phi followed by the specified rho.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
def rationalPhi (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L)
    (H : Integral D l Q E) :=
  (rationalize l Q L).map (phi D l hl Q E L h H).hom ≫
    (rho l Q E L h).hom.app ((sections D l Q E).obj H)
/-- Rationalization of zeta followed by exactly the same specified rho.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
def rationalZeta (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L)
    (H : Integral D l Q E) :=
  (rationalize l Q L).map (zeta D l hl Q J δ E L h H) ≫
    (rho l Q E L h).hom.app ((sections D l Q E).obj ((J E).obj H))

/-- The recorded integral module identity comparison by multiplication.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
def moduleUnit (E : Padic.FiniteCoefficientFields l Q) :=
  pointIntegralModuleDerivedUnit l E.val
/-- The recorded integral module tower associator by coefficient multiplication.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
def moduleAssoc (E L M : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) (j : L ≤ M) :=
  pointIntegralModuleDerivedAssoc l E.val L.val (IntermediateField.inclusion h)
    M.val (IntermediateField.inclusion j)
/-- The recorded coefficient-field identity comparison.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
def fieldUnit (E : Padic.FiniteCoefficientFields l Q) :=
  coefficientComplexDerivedFieldUnit.{u, u + 1} l E.val
/-- The recorded coefficient-field tower associator.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
def fieldAssoc (E L M : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) (j : L ≤ M) :=
  coefficientComplexDerivedFieldAssoc.{u, u + 1} l E.val L.val (IntermediateField.inclusion h)
    M.val (IntermediateField.inclusion j)
/-- The recorded raw scalar localization, with the same integral objects.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
abbrev Raw (E : Padic.FiniteCoefficientFields l Q) :=
  sfRationalConstructibleCategory l E.val (Spec (.of D.k))
/-- The recorded scalar transition of the raw rationalized categories.
Source: blueprint first transport arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-point-scalar-compatible-transport-transfer). -/
abbrev rawExtension (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) :=
  sfRationalScalarExtension l E.val (Spec (.of D.k)) D.p hl L.val (IntermediateField.inclusion h)

include hJ hQ in
/-- The integral transport square, target unit and tower, their specified rationalizations,
and the raw rationalized natural comparisons, without naturality assumptions on u or v.
Source: blueprint main-20261015, `def-weil-global-geometric-frobenius`, first transport arrows
(blueprint: lem-weil-point-scalar-compatible-transport-transfer).

Proof, following the seven reviewed DAG steps:
1. Write $S_F=\Gamma(s,-)$ and write composites right to left. By
[lem-weil-point-proetale-sections-exact], $S_F$ is a functor on derived categories. Its action
is $\mathcal O_F$-linear, since termwise sections sends multiplication by a constant scalar to
that same multiplication. The hypotheses give $J_FH\in\mathcal D_F$, and
[lem-weil-isomorphism-derived-pullback] gives $G_FH\in\mathcal D_F$. Thus all applications of
the natural isomorphism $\varphi$ and its specified tower equation in
[lem-weil-point-sections-scalar-extension] are legitimate, including at the derived arrow
$u^E_H:G_EH\to J_EH$. No representative of this arrow as a chain map is required.

2. Fix $E\subset L$ and $H$. The assumed equality $\delta T(u^E_H)=u^L_{TH}\beta$ gives
$S_L(\delta^{-1})S_L(u^L_{TH})=S_L(Tu^E_H)S_L(\beta^{-1})$. Naturality of $\varphi$ in
[lem-weil-point-sections-scalar-extension] and the assumed inverse-image sections square
therefore give
$$\begin{aligned}
\zeta_{L/E,H}v^L_{TH}
&=\varphi_{L/E,J_EH}S_L(Tu^E_H)S_L(\beta^{-1})\sigma^{g,L}_{TH}\\
&=(S_E(u^E_H)\otimes1)\varphi_{L/E,G_EH}S_L(\beta^{-1})\sigma^{g,L}_{TH}\\
&=(S_E(u^E_H)\otimes1)(\sigma^{g,E}_H\otimes1)\varphi_{L/E,H}
=(v^E_H\otimes1)\varphi_{L/E,H}.
\end{aligned}$$
This uses naturality of $\varphi$ at the single arrow $u^E_H$, not naturality of the family $u$.

3. For $E\subset L\subset M$ abbreviate $T=T_{L/E}$, $U=T_{M/L}$, $e=\delta_{L/E,H}$,
$d=\delta_{M/L,TH}$ and $D=\delta_{M/E,H}$. Inverting and rearranging the assumed $\delta$ tower
gives
$$D^{-1}J_M(A_H)=A_{J_EH}U(e^{-1})d^{-1}.$$
Use the $\varphi$ tower of [lem-weil-point-sections-scalar-extension] at $J_EH$, and then its
naturality for $e^{-1}:J_LTH\to TJ_EH$:
$$\begin{aligned}
\zeta_{M/E,H}S_M(J_M A_H)
&=\varphi_{M/E,J_EH}S_M(A_{J_EH})S_M(Ue^{-1})S_M(d^{-1})\\
&=a^{\mathrm{mod}}(\varphi_{L/E,J_EH}\otimes1)\varphi_{M/L,TJ_EH}S_M(Ue^{-1})S_M(d^{-1})\\
&=a^{\mathrm{mod}}((\varphi_{L/E,J_EH}S_L(e^{-1}))\otimes1)
  \varphi_{M/L,J_LTH}S_M(d^{-1})\\
&=a^{\mathrm{mod}}(\zeta_{L/E,H}\otimes1)\zeta_{M/L,TH}.
\end{aligned}$$
The unit statements for $\delta$ and $\varphi$ give $\zeta_{E/E,H}=\mathrm{id}$ under the
stipulated unit identifications.

4. The successive-extension compatibility of the transport squares follows by pasting their
actual equations. Apply Step 2 for $M/L$ at $TH$ and tensor its $L/E$ equation with $\mathcal
O_M$. Step 3 and the $\varphi$ tower of [lem-weil-point-sections-scalar-extension] give
$$\begin{aligned}
\zeta_{M/E,H}S_M(J_M A_H)v^M_{UTH}
&=a^{\mathrm{mod}}(\zeta_{L/E,H}\otimes1)(v^L_{TH}\otimes1)\varphi_{M/L,TH}\\
&=(v^E_H\otimes1_M)\varphi_{M/E,H}S_M(A_H).
\end{aligned}$$
Here the second equality uses naturality of the module associator at the single module-derived
arrow $v^E_H$. The direct $M/E$ square, precomposed by $S_M(A_H)$, has exactly the same right
side. Since $\zeta_{M/E,H}$ is invertible, this also proves
$$S_M(J_M A_H)v^M_{UTH}=v^M_{T_{M/E}H}S_M(A_H).$$
Thus no unstated naturality of $v$ at $A_H$ is used. For an identity extension the two sides of
Step 2 are the same arrow under the given units; this proves identity compatibility as well.

5. By [lem-weil-coefficient-complex-rationalization], $q_F$ and field scalar extension are
functors on derived categories, and the specified $\rho$ is natural for every derived arrow.
Apply $q_L$ to Step 2 and postcompose with $\rho_{L/E,S_EJ_EH}$. Its naturality at
$v^E_H:S_EH\to S_EJ_EH$ says
$$\rho_{L/E,S_EJ_EH}q_L(v^E_H\otimes1)
=(q_E(v^E_H)\otimes_E1_L)\rho_{L/E,S_EH}.$$
Substitution gives precisely
$$\zeta^{\mathrm{rat}}_{L/E,H}q_L(v^L_{TH})
=(v^{E,\mathrm{rat}}_H\otimes_E1_L)\varphi^{\mathrm{rat}}_{L/E,H}.$$
The definitions here use the specified $\rho((n\otimes a)\otimes b)=(n\otimes1)\otimes ab$; none
of the comparisons has been replaced by an arbitrary isomorphism.

6. For a tower, apply $q_M$ to Step 3 and to the pasted equation of Step 4. Use the mixed
integral/field tower equality of [lem-weil-coefficient-complex-rationalization], first at $S_EH$
and then at $S_EJ_EH$. It replaces the direct comparison $\rho_{M/E}q_M(a^{\mathrm{mod}})$ by
the successive $\rho_{M/L}$, $\rho_{L/E}\otimes_L M$, and field associator, in that order.
Naturality of $\rho$ at the arrows in those equations then gives
$$\zeta^{\mathrm{rat}}_{M/E,H}q_M S_M(J_M A_H)
=a^{\mathrm{fld}}(\zeta^{\mathrm{rat}}_{L/E,H}\otimes_L1_M)\zeta^{\mathrm{rat}}_{M/L,TH},$$
and the identical pasting equation for the rational transport squares. The analogous equation
for $\varphi^{\mathrm{rat}}$ follows from the cited $\varphi$ tower. The unit equation of $\rho$
gives the rational units. This checks the specified associators, including their order, rather
than merely asserting coherence.

7. Use the raw Hom tensors of [def-weil-rationalization-karoubi]. The functors $J_F$ extend
because they are linear; integral coefficient extension is semilinear. Their natural comparisons
extend by [lem-pur-semilinear-scalar-localization], with the coefficient inclusions sending each
uniformizer to an invertible field element. The sections realization on raw Hom tensors is
explicitly
$$\sum_i f_i\otimes a_i\longmapsto\sum_i a_i\,q_F(S_F(f_i)),$$
and similarly with $S_FJ_F$ in place of $S_F$. These maps are balanced because $S_F,J_F$ are
linear; they preserve identities and composition by expansion and bilinearity. They are
independent of fraction presentations, without needing injectivity on integral Hom groups.
Naturality of the comparisons for an arrow $f/\varpi_F^n$ is its integral naturality equation
multiplied by $\varpi_F^{-n}$, and for a finite sum it is the sum of these equations. Thus all
comparison equations used above remain valid for fraction-valued morphisms. The components
$u^F_H,v^F_H$ are simply sent to their $q_F$ images: no extension as a natural transformation is
asserted for either family. Objects in the raw localization are the same integral objects, so
Steps 5--6 apply to all of them; no idempotent splitting is involved.
-/
theorem scalar_compatible_transport_transfer
    (hδunit : ∀ (E : Padic.FiniteCoefficientFields l Q) (H : Integral D l Q E),
      (δ E E le_rfl).hom.app H ≫ (J E).map (unit D l hl Q E H).hom =
        (unit D l hl Q E ((J E).obj H)).hom)
    (hδtower : ∀ (E L M : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) (j : L ≤ M)
      (H : Integral D l Q E),
      (extension D l hl Q L M j).map ((δ E L h).hom.app H) ≫
          (δ L M j).hom.app ((extension D l hl Q E L h).obj H) ≫
          (J M).map (assoc D l hl Q E L M h j H).hom =
        (assoc D l hl Q E L M h j ((J E).obj H)).hom ≫
          (δ E M (h.trans j)).hom.app H)
    (hu : ∀ (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) (H : Integral D l Q E),
      (extension D l hl Q E L h).map (u E H) ≫ (δ E L h).hom.app H =
        (beta D l hl Q g E L h H).hom ≫ u L ((extension D l hl Q E L h).obj H))
    (hσ : ∀ (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) (H : Integral D l Q E),
      sigma D l hl Q g L ((extension D l hl Q E L h).obj H) ≫
          (sections D l Q L).map (beta D l hl Q g E L h H).inv ≫
          (phi D l hl Q E L h ((inverseImage D l hl Q g E).obj H)).hom =
        (phi D l hl Q E L h H).hom ≫
          (tensor l Q E L h).map (sigma D l hl Q g E H)) :
    (∀ (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) (H : Integral D l Q E),
      v D l hl Q g J u L ((extension D l hl Q E L h).obj H) ≫
          zeta D l hl Q J δ E L h H =
        (phi D l hl Q E L h H).hom ≫ (tensor l Q E L h).map (v D l hl Q g J u E H)) ∧
    (∀ (E : Padic.FiniteCoefficientFields l Q) (H : Integral D l Q E),
      zeta D l hl Q J δ E E le_rfl H ≫
          (moduleUnit l Q E).hom.app ((sections D l Q E).obj ((J E).obj H)) =
        (sections D l Q E).map ((J E).map (unit D l hl Q E H).hom)) ∧
    (∀ (E L M : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) (j : L ≤ M)
      (H : Integral D l Q E),
      (sections D l Q M).map ((J M).map (assoc D l hl Q E L M h j H).hom) ≫
          zeta D l hl Q J δ E M (h.trans j) H =
        zeta D l hl Q J δ L M j ((extension D l hl Q E L h).obj H) ≫
          (tensor l Q L M j).map (zeta D l hl Q J δ E L h H) ≫
          (moduleAssoc l Q E L M h j).hom.app ((sections D l Q E).obj ((J E).obj H))) ∧
    (∀ (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) (H : Integral D l Q E),
      (rationalize l Q L).map (v D l hl Q g J u L ((extension D l hl Q E L h).obj H)) ≫
          rationalZeta D l hl Q J δ E L h H =
        rationalPhi D l hl Q E L h H ≫
          (fieldTensor l Q E L h).map ((rationalize l Q E).map (v D l hl Q g J u E H))) ∧
    (∀ (E : Padic.FiniteCoefficientFields l Q) (H : Integral D l Q E),
      v D l hl Q g J u E ((extension D l hl Q E E le_rfl).obj H) ≫
          (sections D l Q E).map ((J E).map (unit D l hl Q E H).hom) =
        (sections D l Q E).map (unit D l hl Q E H).hom ≫ v D l hl Q g J u E H) ∧
    (∀ (E L M : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) (j : L ≤ M)
      (H : Integral D l Q E),
      v D l hl Q g J u M
          ((extension D l hl Q L M j).obj ((extension D l hl Q E L h).obj H)) ≫
          (sections D l Q M).map ((J M).map (assoc D l hl Q E L M h j H).hom) =
        (sections D l Q M).map (assoc D l hl Q E L M h j H).hom ≫
          v D l hl Q g J u M ((extension D l hl Q E M (h.trans j)).obj H)) ∧
    (∀ (E L M : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) (j : L ≤ M)
      (H : Integral D l Q E),
      v D l hl Q g J u M
          ((extension D l hl Q L M j).obj ((extension D l hl Q E L h).obj H)) ≫
          (sections D l Q M).map ((J M).map (assoc D l hl Q E L M h j H).hom) ≫
          zeta D l hl Q J δ E M (h.trans j) H =
        (sections D l Q M).map (assoc D l hl Q E L M h j H).hom ≫
          (phi D l hl Q E M (h.trans j) H).hom ≫
          (tensor l Q E M (h.trans j)).map (v D l hl Q g J u E H)) ∧
    (∀ (E : Padic.FiniteCoefficientFields l Q) (H : Integral D l Q E),
      rationalZeta D l hl Q J δ E E le_rfl H ≫
          (fieldUnit l Q E).hom.app
            ((rationalize l Q E).obj ((sections D l Q E).obj ((J E).obj H))) =
        (rationalize l Q E).map
          ((sections D l Q E).map ((J E).map (unit D l hl Q E H).hom))) ∧
    (∀ (E L M : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) (j : L ≤ M)
      (H : Integral D l Q E),
      (rationalize l Q M).map
          ((sections D l Q M).map ((J M).map (assoc D l hl Q E L M h j H).hom)) ≫
          rationalZeta D l hl Q J δ E M (h.trans j) H =
        rationalZeta D l hl Q J δ L M j ((extension D l hl Q E L h).obj H) ≫
          (fieldTensor l Q L M j).map (rationalZeta D l hl Q J δ E L h H) ≫
          (fieldAssoc l Q E L M h j).hom.app
            ((rationalize l Q E).obj ((sections D l Q E).obj ((J E).obj H)))) ∧
    (∀ (E L M : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) (j : L ≤ M)
      (H : Integral D l Q E),
      (rationalize l Q M).map
          (v D l hl Q g J u M
            ((extension D l hl Q L M j).obj ((extension D l hl Q E L h).obj H)) ≫
            (sections D l Q M).map ((J M).map (assoc D l hl Q E L M h j H).hom)) ≫
          rationalZeta D l hl Q J δ E M (h.trans j) H =
        (rationalize l Q M).map ((sections D l Q M).map
          (assoc D l hl Q E L M h j H).hom) ≫
          rationalPhi D l hl Q E M (h.trans j) H ≫
          (fieldTensor l Q E M (h.trans j)).map
            ((rationalize l Q E).map (v D l hl Q g J u E H))) ∧
    (∃ (S SJ : ∀ E : Padic.FiniteCoefficientFields l Q, Raw D l Q E ⥤ Fields l Q E),
      (∀ E : Padic.FiniteCoefficientFields l Q, (S E).Additive ∧ (SJ E).Additive) ∧
      (∀ (E : Padic.FiniteCoefficientFields l Q) (H : Raw D l Q E),
        (S E).obj H = (rationalize l Q E).obj ((sections D l Q E).obj H.obj)) ∧
      (∀ (E : Padic.FiniteCoefficientFields l Q) (H : Raw D l Q E),
        (SJ E).obj H = (rationalize l Q E).obj ((sections D l Q E).obj ((J E).obj H.obj))) ∧
      (∀ (E : Padic.FiniteCoefficientFields l Q) (H K : Integral D l Q E)
        (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)) (f : H ⟶ K),
        HEq ((S E).map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
          (⟨H⟩ : Raw D l Q E) ⟶ ⟨K⟩))
          (sfRationalCoefficientEquiv l E.val a •
            (rationalize l Q E).map ((sections D l Q E).map f)) ∧
        HEq ((SJ E).map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
          (⟨H⟩ : Raw D l Q E) ⟶ ⟨K⟩))
          (sfRationalCoefficientEquiv l E.val a •
            (rationalize l Q E).map ((sections D l Q E).map ((J E).map f)))) ∧
      (∀ (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L),
        ∃ (Φ : rawExtension D l hl Q E L h ⋙ S L ≅ S E ⋙ fieldTensor l Q E L h)
          (Ζ : rawExtension D l hl Q E L h ⋙ SJ L ≅ SJ E ⋙ fieldTensor l Q E L h),
          ∀ H : Integral D l Q E,
            HEq (Φ.hom.app ⟨H⟩) (rationalPhi D l hl Q E L h H) ∧
            HEq (Ζ.hom.app ⟨H⟩) (rationalZeta D l hl Q J δ E L h H))) := by
  sorry

end WeilConjectures.PointScalarTransfer
