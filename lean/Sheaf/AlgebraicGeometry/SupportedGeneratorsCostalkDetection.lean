/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSupportedSections
public import Sheaf.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.RingTheory.StrictHenselizationNoetherian
import Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import Sheaf.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal
import Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.EtaleCohomology.EtaleSectionZeroOpen
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-! # Detection of supported bounds by geometric costalks

Source: ILO, Travaux de Gabber, XVII, Definition 1.1.1 and section 5.2;
Stacks Project, Etale Cohomology, Tags 09XP and 09XQ.
(blueprint: lem-per-supported-generators-costalk-detection).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Closed-point supported cohomology after exact inverse image to the strict localization.
Source: ILO XVII, Definition 1.1.1; Stacks 09XP.
(blueprint: lem-per-supported-generators-costalk-detection). -/
def geometricCostalk (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (ModuleCat.{u + 1} Λ) :=
  letI : IsLocalRing (Scheme.strictHenselizationRing x) :=
    Classical.choose (AlgebraicGeometry.strictHenselizationLocalStructure x)
  (upperStar (ModuleCat.{u + 1} Λ)
      (Scheme.strictHenselizationStructuralMap x)).mapDerivedCategoryPlus ⋙
    derivedSupportedEtaleSections Λ (Scheme.strictHenselizationScheme x)
      ⟨{IsLocalRing.closedPoint (Scheme.strictHenselizationRing x)}ᶜ,
        (IsLocalRing.isClosed_singleton_closedPoint _).isOpen_compl⟩

/-- Supported cohomology after inverse image to an etale object, in any integer degree.
Source: Stacks 09XP and 09XQ.
(blueprint: lem-per-supported-generators-costalk-detection). -/
def etaleSupportedCohomology (Λ : Type (u + 1)) [CommRing Λ]
    {X V Z : Scheme.{u}} (v : V ⟶ X) (i : Z ⟶ V) [IsClosedImmersion i] (m : ℤ) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      ModuleCat.{u + 1} Λ :=
  (upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategoryPlus ⋙
    derivedSupportedEtaleSections Λ V i.openComplement ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) m

/-- The sheaf `v_! i_* Λ_Z`, put in degree zero and shifted by `-m`.
Here `v_!` is the existing sheafified sum over lifts, not a compactification construction.
Source: Stacks 03DI and 09XQ.
(blueprint: lem-per-supported-generators-costalk-detection). -/
def etaleSupportedGenerator (Λ : Type (u + 1)) [CommRing Λ]
    {X V Z : Scheme.{u}} (v : V ⟶ X) (hv : Etale v) (i : Z ⟶ V) (m : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ((DerivedCategory.singleFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
    ((etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj
      ((lowerStar (ModuleCat.{u + 1} Λ) i).obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ Λ)))))⟦-m⟧

/-- Geometric costalk bounds are equivalent to bounds on all affine etale closed supports.
No excellence or constructibility is assumed.
Source: ILO XVII, Definition 1.1.1 and section 5.2; Stacks 09XP, 09XQ and 0A45.
(blueprint: lem-per-supported-generators-costalk-detection).

Proof plan (the dependency ids are those recorded in the DAG):
1. For a closed immersion $i:Z\hookrightarrow T$ with complement $j$, write $P_ZF=\ker(F\to
j_*j^*F)$ and $i^!_0F=i^*P_ZF$. The supported-kernel adjunction gives $P_ZF=i_*i^!_0F$,
exactness of $i_*$, and $i_*\dashv i^!_0$ on abelian sheaves. These assertions extend to
constant $\Lambda$-module sheaves: all maps are natural in $F$, so commute with multiplication
by each scalar; the Hom bijection restricts to linear maps because a map commutes with each
scalar exactly when its transpose does. Exact coefficient forgetting detects exactness. Thus
these are the same supported kernels in the module category, not a different coefficient theory.
2. The inverse image $i^*$ is exact and left adjoint to $i_*$. Therefore $i_*$ preserves
injectives. Since $i_*$ is exact and left adjoint to $i^!_0$, the latter also preserves
injectives. Consequently $P_Z=i_*i^!_0$ preserves injectives. On a bounded-below injective
representative $I$ of $L$ put $P_Z^RL=P_ZI=i_*Ri^!L$. This specifies the derived sheaf of
supported sections on $T$. All its cohomology sheaves are supported on $|Z|$, since the terms
vanish on the complementary open.
3. The same representative gives $R\Gamma_Z(T,L)=R\Gamma(T,P_Z^RL)$: both are represented by
$\Gamma(T,P_ZI)$, since $P_ZI$ is a bounded-below complex of injectives. If $W\subseteq |Z|$ is
closed, it also gives $R\Gamma_W(T,P_Z^RL)=R\Gamma_W(T,L)$, since a section supported on $W$
already lies in $P_ZI$, so $\Gamma_W(T,P_ZI)=\Gamma_W(T,I)$ in every degree. These identities
depend only on the closed subsets, not on nilpotents in their scheme structures, because the
defining restriction kernel uses only the complementary open.
4. We will use the following elementary calculation from the injective representative, for
either global sections or sections with a fixed closed support, or the sheaf functor $P_Z$. If
$L\in D^{\geq q}$, take $J^r=0$ for $r<q$ in such a representative. For a left exact functor
$F$, $FJ$ vanishes below $q$ and $H^q(FJ)=\ker(FJ^q\to FJ^{q+1})=F(\ker(J^q\to
J^{q+1}))=F(\mathcal H^qL)$. Thus $RF(L)$ has the same lower bound and its bottom cohomology is
the underived functor of the bottom cohomology. No spectral sequence, convergence, or dimension
bound is needed.
5. For an etale map $v:T'\to T$, restriction sends injective module sheaves to injectives.
Sectionwise the kernels satisfy $(P_ZF)|_{T'}=P_{Z\times_TT'}(F|_{T'})$: on an etale object
$B\to T'$ both are the kernel of $F(B)\to F(B\setminus (Z\times_T B))$. Applying this to an
injective representative gives $v^*P_Z^RL=P_{Z\times_TT'}^R(v^*L)$ and the corresponding
formulas for supported sections on etale objects. Exactness of inverse image identifies its
cohomology sheaves with the inverse images of the cohomology sheaves.
6. All affine etale schemes used below are Noetherian. Indeed, etale maps are locally of finite
presentation; their affine source has a finite cover by affine charts with finitely presented,
hence finite-type, coordinate algebras over Noetherian affine charts of the base. Those algebras
are Noetherian. For an affine Noetherian $T=\operatorname{Spec}B$ and a geometric point $\bar t$
over the prime $\mathfrak p$, the affine strict-local comparison identifies the ring of
$T_{(\bar t)}$, as a $B$-algebra, with a strict henselization of $B_{\mathfrak p}$;
$B_{\mathfrak p}$ is Noetherian by localization, and its strict henselization by the
strict-henselization theorem. For an affine scheme $T$, its strict-localization map $T_{(\bar
t)}\to T$ is affine and ind-etale by the affine-chart strict-henselization lemma. These verify
the hypotheses of the ind-etale supported base-change theorem whenever we use it.
7. Here is the geometry at a generic point of a closed support. Let $T=\operatorname{Spec}B$,
$E=V(J)$, and let $t=\mathfrak p$ be a generic point of an irreducible component of $E$, so
$\mathfrak p$ is minimal among primes containing $J$. Let $C$ be the ring of $T_{(\bar t)}$. The
affine strict-local comparison gives a $B$-algebra isomorphism of $C$ with a strict
henselization of $B_{\mathfrak p}$, so every element of $B$ outside $\mathfrak p$, already a
unit in $B_{\mathfrak p}$, is a unit in $C$; the chart maximal-ideal lemma (with the identity
chart of $T$, whose ring map is the structural one) gives that the maximal ideal of $C$ is
$\mathfrak p C$. A prime of $C$ lying over $E$ therefore contracts to a prime containing $J$ and
contained in $\mathfrak p$; by minimality its contraction is $\mathfrak p$, so it contains
$\mathfrak p C$ and is the maximal ideal. Hence the inverse image of $E$ in $T_{(\bar t)}$ is
exactly its closed point. This argument applies also to $E=\overline{\{t\}}$ for any $t$.
8. For the strict-localization map $g:T'\to T$ of an affine Noetherian scheme and a closed
immersion $i:Z\hookrightarrow T$, ind-etale supported base change gives $h^*Ri^!L\cong
Ri'^!g^*L$. The same theorem specifies the closed direct-image base-change isomorphism
$g^*i_*\cong i'_*h^*$. Combining them gives $g^*P_Z^RL\cong P_{Z\times_TT'}^R(g^*L)$. For an
etale $v:T\to X$, the strict-local invariance theorem identifies $T_{(\bar t)}$ with $X_{(v\bar
t)}$ over $X$. Thus the closed-point supported cohomology after either strict localization is
the costalk in the statement.
9. Assume (1) and fix affine etale $u:V\to X$ and $Z$ as in (2). Put $L=u^*K$, $M=P_Z^RL$. Fix
$b$ with $K\in D^{\geq b}$; Steps 4 and 5 give $M\in D^{\geq b}$. If some $\mathcal H^qM\ne0$
with $q\leq a$, choose the least such $q$ (among the integers at least $b$), so $M\in D^{\geq
q}$. A nonzero sheaf has a nonzero section $s$ on some affine etale $W\to V$ (restrict any
nonzero section to an affine cover). The zero-open lemma shows that its support $E\subset W$ is
nonempty and closed and that its germ is nonzero at every point of $E$. Since $\mathcal H^qM$ is
supported on $Z$, $E\subseteq Z\times_VW$. Choose an irreducible component of $E$ and its
generic point $w$, using finite decomposition of closed subsets and sobriety. Then $u(w)\in S$.
10. Choose a geometric $\bar w$ over $w$ and pull $M|_W$ and $s$ back to $T=W_{(\bar w)}$. Its
pullback $N$ is in $D^{\geq q}$ by exactness. The pulled-back section of $\mathcal H^qN$ is
supported at the closed point by Step 7: it is zero off the inverse image of $E$, since $s$ was
already zero on $W\setminus E$. Its closed-point germ is nonzero by inverse-image compatibility
with germs. Thus $\Gamma_{\{w_0\}}(T,\mathcal H^qN)\ne0$. Step 4 identifies this with
$H^qR\Gamma_{\{w_0\}}(T,N)$. Steps 5 and 8 identify $N$ with $P_{Z_T}^R(K|_T)$, and $w_0\in
Z_T$. Step 3 then identifies this nonzero group with $H^qR\Gamma_{\{w_0\}}(T,K|_T)=H^q(C_{u\bar
w}K)$. This contradicts (1). Hence $M\in D^{\geq a+1}$.
11. By Step 3, $R\Gamma_Z(V,u^*K)=R\Gamma(V,M)$. Global sections is left exact, so the injective
calculation in Step 4 applied to $M\in D^{\geq a+1}$ makes this complex concentrated in degrees
at least $a+1$. This is precisely (2).
12. Conversely assume (2). Let $V\to X$ be affine etale and let $Z\subseteq V$ be closed with
image in $S$. Then $M=P_Z^R(K|_V)$ is in $D^{\geq a+1}$. To see this, otherwise choose its first
nonzero $\mathcal H^qM$, $q\leq a$, as in Step 9, and a nonzero section on an affine etale $W\to
V$. Steps 4 and 5 identify this section group with
$H^qR\Gamma(W,M|_W)=H^qR\Gamma_{Z_W}(W,K|_W)$, the latter by Step 3. Replace $Z_W$ by the
reduced induced closed subscheme: Step 3 shows that the complex is unchanged. The composite
$W\to X$ is affine etale as an object of the small site (its source is affine), and the image of
this reduced support is in $S$. Hypothesis (2) makes the displayed group zero, a contradiction.
This proves the claimed sheaf bound for every such $Z$.
13. Fix $x\in S$ and any geometric $\bar x$ over $x$. Choose an affine open $V\subseteq X$
containing $x$ and give $Z=\overline{\{x\}}\cap V$ its reduced induced structure. Specialization
stability ensures $Z\subseteq S$. Step 12 gives $P_Z^R(K|_V)\in D^{\geq a+1}$. Pull this to
$T=V_{(\bar x)}$, which the strict-local invariance theorem for the open (hence etale) immersion
$V\hookrightarrow X$ identifies with $X_{(\bar x)}$ over $X$, closed point to closed point. By
Step 7, the inverse image of $Z$ is the closed point; Step 8 identifies the pullback with
$P_{\{x_0\}}^R(K|_T)$. Its lower bound is preserved by exact pullback. Taking derived global
sections preserves that bound by Step 4. Step 3 identifies the result with $C_{\bar x}K$. Thus
$H^mC_{\bar x}K=0$ for $m\leq a$, proving (1). The choice of $\bar x$ was arbitrary. -/
theorem supported_bounds_iff_geometricCostalk
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) [IsNoetherian X]
    (S : Set X) (hS : ∀ (x y : X), x ⤳ y → x ∈ S → y ∈ S) (a : ℤ)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      x (IsLocalRing.closedPoint Ω) ∈ S → ∀ (m : ℤ), m ≤ a →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) m).obj
          ((geometricCostalk Λ x).obj K))) ↔
    (∀ (V : Scheme.{u}) (v : V ⟶ X) [Etale v] [IsAffine V]
      (Z : Scheme.{u}) (i : Z ⟶ V) [IsClosedImmersion i] [IsReduced Z],
      Set.range (i ≫ v) ⊆ S → ∀ (m : ℤ), m ≤ a →
        IsZero ((etaleSupportedCohomology Λ v i m).obj K)) := by
  sorry

/-- The supported-generator Hom groups are naturally the supported cohomology groups.
The natural isomorphism is in `K` on the bounded below derived category.
Source: Stacks 03DI, 03DJ and 09XQ; ILO XVII, section 5.2.
(blueprint: lem-per-supported-generators-costalk-detection).

Proof: choose a bounded below injective representative I of K
(lem-weil-pbc-dplus-injective-representative). The exact etale sum extension is left
adjoint to restriction, so restriction preserves injectives
(lem-weil-pbc-etale-restriction-injectives). Compute derived Hom into I
(lem-weil-pbc-kinjective-hom-derived). Adjunction identifies its complex with
Hom(i_* Λ_Z, v^* I). The scalar-linear supported-kernel adjunction
(lem-pur-etale-supported-kernel-adjunction), followed by evaluation at 1 of Λ,
identifies this with Γ_Z(V,v^* I). Taking degree m cohomology gives the group
isomorphism; the shift -m puts the source in degree m. All these identifications
are functorial in K and additive. This proves naturality as an isomorphism of
AddCommGrpCat-valued functors. -/
theorem supportedGenerator_hom_naturally_iso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) [IsNoetherian X]
    (V : Scheme.{u}) (v : V ⟶ X) [Etale v] [IsAffine V]
    (Z : Scheme.{u}) (i : Z ⟶ V) [IsClosedImmersion i] [IsReduced Z] (m : ℤ) :
    Nonempty
      (DerivedCategory.Plus.ι ⋙
          preadditiveCoyoneda.obj (op (etaleSupportedGenerator Λ v inferInstance i m)) ≅
        etaleSupportedCohomology Λ v i m ⋙
          forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := by
  sorry

end AlgebraicGeometry.Etale
