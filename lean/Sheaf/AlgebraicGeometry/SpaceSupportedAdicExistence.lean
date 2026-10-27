/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.SpaceCoherentAdicSystem
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import WeilConjectures.RingTheory.FiniteModuleComplete
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ChowAlgebraizationCore
import WeilConjectures.AlgebraicGeometry.ModuleSupportProperOverBase

/-! # Proper-support Grothendieck existence for algebraic spaces

Source: Stacks Project, spaces-more-morphisms.tex, Tags 08BE and 08BF
(blueprint: lem-sfb-space-supported-adic-existence).

The index n denotes the positive level n+1. Systems are algebras for the endofunctor
(F_n) ↦ (j_n^* F_{n+1}) with invertible structure arrows. Thus their morphisms are
exactly families of module maps commuting with the adjacent restriction isomorphisms.
The completion functor uses the existing tensor-normalized composition comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {A : Type u} [CommRing A]
variable (a : Spec (.of A) ⟶ S) (I : Ideal A)

/-- Proper support is the closed-carrier condition, with no flatness requirement.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
def SupportedAdicProperSupport {X T : AlgebraicSpace S} (p : X ⟶ T)
    (M : X.Modules) : Prop :=
  ∃ (Z : AlgebraicSpace S) (i : Z ⟶ X),
    IsRepresentableWith (fun _ _ q ↦ IsClosedImmersion q.left) i.hom.hom ∧
    MapIsProper (i ≫ p) ∧ ∃ G : Z.Modules,
      G.IsQuasicoherent ∧ G.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj G ≅ M)

/-- The category D: finitely presented quasi-coherent modules with proper support.
All module homomorphisms are retained by the full-subcategory construction.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
abbrev SupportedAdicModules {X T : AlgebraicSpace S} (p : X ⟶ T) :=
  ObjectProperty.FullSubcategory (C := X.Modules)
    (fun M ↦ M.IsQuasicoherent ∧ M.IsFinitePresentation ∧ SupportedAdicProperSupport p M)

/-- The scheme Spec(A/I^(n+1)), with its specified map to S.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
def supportedAdicBase (n : ℕ) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ a)

/-- The quotient-base map to Spec A, as a morphism over S.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
def supportedAdicBaseMap (n : ℕ) : supportedAdicBase a I n ⟶ Over.mk a :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) rfl

/-- The quotient-base test object over the algebraic space Spec A.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
def supportedAdicTest (n : ℕ) : ProperQuotTest (schemeSpace (Over.mk a)) :=
  CostructuredArrow.mk (yoneda.map (supportedAdicBaseMap a I n))

/-- The actual adjacent ring quotient A/I^(n+2) → A/I^(n+1).
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
def supportedAdicQuotientStep (n : ℕ) : A ⧸ I ^ (n + 2) →+* A ⧸ I ^ (n + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

/-- The quotient triangle over S.
Proof: both composites are Spec of the quotient A → A/I^(n+1), followed by a;
use Spec.map_comp and Ideal.Quotient.factor_mk.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
theorem supportedAdicBaseStep_w (n : ℕ) :
    Spec.map (CommRingCat.ofHom (supportedAdicQuotientStep I n)) ≫
        (supportedAdicBase a I (n + 1)).hom = (supportedAdicBase a I n).hom := by
  sorry

/-- The canonical adjacent closed-base map over S.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
def supportedAdicBaseStep (n : ℕ) : supportedAdicBase a I n ⟶
    supportedAdicBase a I (n + 1) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (supportedAdicQuotientStep I n)))
    (supportedAdicBaseStep_w a I n)

/-- The adjacent map commutes with the test maps to Spec A.
Proof: factor_mk identifies the composite ring map with the quotient map.
Apply contravariant Spec and Yoneda functoriality.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
theorem supportedAdicTestStep_w (n : ℕ) :
    yoneda.map (supportedAdicBaseStep a I n) ≫ (supportedAdicTest a I (n + 1)).hom =
      (supportedAdicTest a I n).hom := by
  sorry

/-- The adjacent morphism in the category of scheme tests of Spec A.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
def supportedAdicTestStep (n : ℕ) : supportedAdicTest a I n ⟶
    supportedAdicTest a I (n + 1) :=
  CostructuredArrow.homMk (supportedAdicBaseStep a I n) (supportedAdicTestStep_w a I n)

variable {Y : AlgebraicSpace S} (p : Y ⟶ schemeSpace (Over.mk a))

/-- The actual sheaf fibre product Y_(n+1) = Y ×_A Spec(A/I^(n+1)).
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
abbrev supportedAdicThickening (n : ℕ) : AlgebraicSpace S :=
  properQuotFibre p (supportedAdicTest a I n)

/-- The canonical projection Y_(n+1) → Y.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
abbrev supportedAdicProjection (n : ℕ) : supportedAdicThickening a I p n ⟶ Y :=
  properQuotFst p (supportedAdicTest a I n)

/-- The canonical adjacent closed immersion j_(n+1).
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
abbrev supportedAdicStep (n : ℕ) : supportedAdicThickening a I p n ⟶
    supportedAdicThickening a I p (n + 1) :=
  properQuotFibreMap p (supportedAdicTestStep a I n)

/-- The product of all level module categories, including level one at index zero.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
abbrev SupportedAdicFamilies := ∀ n : ℕ, (supportedAdicThickening a I p n).Modules

/-- The endofunctor whose algebra structure is the family of adjacent tensor restrictions.
Its maps are actual tensor pullbacks of the next component maps.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
def supportedAdicShift : SupportedAdicFamilies a I p ⥤ SupportedAdicFamilies a I p :=
  Pi.comap (fun n : ℕ ↦ (supportedAdicThickening a I p n).Modules) Nat.succ ⋙
    Functor.pi (fun n : ℕ ↦ moduleTensorPullback (supportedAdicStep a I p n))

/-- The object condition for D-hat: finite presentation and quasi-coherence at every
positive level, invertible adjacent restrictions, and proper support of level one over A/I.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
def IsSupportedAdicSystem : ObjectProperty (Endofunctor.Algebra (supportedAdicShift a I p)) :=
  fun F ↦ (∀ n : ℕ, (F.a n).IsQuasicoherent ∧ (F.a n).IsFinitePresentation) ∧
    (∀ n : ℕ, IsIso (F.str n)) ∧
    SupportedAdicProperSupport (properQuotSnd p (supportedAdicTest a I 0)) (F.a 0)

/-- The category D-hat; its arrows are precisely the compatible families of module maps.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
abbrev SupportedAdicSystems := (IsSupportedAdicSystem a I p).FullSubcategory

/-- The family of actual tensor restriction functors to all positive thickenings.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
def supportedAdicRestrictionFamily : Y.Modules ⥤ SupportedAdicFamilies a I p :=
  Functor.pi' (fun n : ℕ ↦ moduleTensorPullback (supportedAdicProjection a I p n))

/-- The normalized adjacent restriction isomorphism, induced by tensor associativity
and the equality j_n ≫ (Y_(n+1) → Y) = (Y_n → Y).
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
def supportedAdicRestrictionIso (n : ℕ) :
    moduleTensorPullback (supportedAdicProjection a I p (n + 1)) ⋙
        moduleTensorPullback (supportedAdicStep a I p n) ≅
      moduleTensorPullback (supportedAdicProjection a I p n) :=
  moduleTensorComposition (supportedAdicStep a I p n)
      (supportedAdicProjection a I p (n + 1)) ≪≫
    eqToIso (congrArg moduleTensorPullback
      (properQuotFibreMap_fst p (supportedAdicTestStep a I n)))

/-- The unrestricted tensor restriction system of a module on Y.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
def supportedAdicRestrictionObject (M : Y.Modules) :
    Endofunctor.Algebra (supportedAdicShift a I p) where
  a := (supportedAdicRestrictionFamily a I p).obj M
  str n := (supportedAdicRestrictionIso a I p n).hom.app M

/-- Compatibility of component restriction maps with adjacent restrictions.
Proof: this is naturality of the tensor-normalized composition isomorphism,
followed by naturality of transport along the projection triangle.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
theorem supportedAdicRestrictionMap_w {M N : Y.Modules} (f : M ⟶ N) :
    (supportedAdicShift a I p).map ((supportedAdicRestrictionFamily a I p).map f) ≫
        (supportedAdicRestrictionObject a I p N).str =
      (supportedAdicRestrictionObject a I p M).str ≫
        (supportedAdicRestrictionFamily a I p).map f := by
  sorry

/-- The restriction of a module homomorphism, with its canonical compatibility square.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
def supportedAdicRestrictionMap {M N : Y.Modules} (f : M ⟶ N) :
    supportedAdicRestrictionObject a I p M ⟶ supportedAdicRestrictionObject a I p N :=
  ⟨(supportedAdicRestrictionFamily a I p).map f, supportedAdicRestrictionMap_w a I p f⟩

/-- Identity and composition laws for the specified restriction arrows.
Proof: algebra morphisms are determined by their underlying component maps.
Functoriality of each tensor pullback gives both laws componentwise.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
theorem supportedAdicRestrictionLaws :
    (∀ M : Y.Modules, supportedAdicRestrictionMap a I p (𝟙 M) =
      𝟙 (supportedAdicRestrictionObject a I p M)) ∧
    (∀ (M N P : Y.Modules) (f : M ⟶ N) (g : N ⟶ P),
      supportedAdicRestrictionMap a I p (f ≫ g) =
        supportedAdicRestrictionMap a I p f ≫ supportedAdicRestrictionMap a I p g) := by
  sorry

/-- The actual tensor restriction functor before imposing finiteness or support.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
def supportedAdicRestrictionAmbient : Y.Modules ⥤
    Endofunctor.Algebra (supportedAdicShift a I p) where
  obj := supportedAdicRestrictionObject a I p
  map := supportedAdicRestrictionMap a I p
  map_id := (supportedAdicRestrictionLaws a I p).1
  map_comp := (supportedAdicRestrictionLaws a I p).2 _ _ _

/-- Tensor restriction lands in D-hat on D.
Proof: tensor pullback preserves a local finite free presentation and hence
quasi-coherence and finite presentation. Each structure map is the component of
supportedAdicRestrictionIso, hence invertible. Base change of a proper closed carrier
to Spec(A/I) is again a proper closed carrier; tensor pull back its finite type module.
The closed-immersion tensor/direct-image identification realizes the restricted module
on this carrier. This is the landing argument in step 1 of the node proof.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
theorem supportedAdicRestriction_admissible (M : SupportedAdicModules p) :
    IsSupportedAdicSystem a I p ((supportedAdicRestrictionAmbient a I p).obj M.obj) := by
  sorry

/-- The tensor restriction functor D → D-hat, with its actual maps and normalized transitions.
Source: Stacks Project, Tag 08BF
(blueprint: lem-sfb-space-supported-adic-existence). -/
def supportedAdicRestriction : SupportedAdicModules p ⥤ SupportedAdicSystems a I p :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ supportedAdicRestrictionAmbient a I p)
    (supportedAdicRestriction_admissible a I p)

/-- Proper-support Grothendieck existence, without any flatness hypothesis.
Source: Stacks Project, Tags 08BE and 08BF
(blueprint: lem-sfb-space-supported-adic-existence).

Proof plan (the dependencies are recorded in the DAG):
1. Write $J=I\mathcal O_Y$. The Noetherian-coherent finiteness theorem makes $Y$ and its closed
subspaces Noetherian and identifies finite presentation with coherence. The proper-carrier
theorem identifies the support condition with properness of the scheme-theoretic support. Apply
the closed-adic dictionary termwise: $F_n$ is sent to its pushforward to $Y$, killed by $J^n$,
and the adjacent restriction isomorphisms become quotient transition isomorphisms. This
identifies the target category with the proper-support subcategory of $\mathrm{Coh}(Y,J)$, on
arrows as well as objects, and identifies tensor restriction with completion. Completion lands
in this subcategory: if $w:W\hookrightarrow Y$ is a proper closed carrier of $F$, the ideal of
$W$ kills $F$ (it acts through $\mathcal O_Y\to w_*\mathcal O_W$), so the closed-adic dictionary
writes $F=w_*G$ with $G$ coherent and $F/J^nF\simeq w_*(G/(J\mathcal O_W)^nG)$, which has the
same proper carrier $W$. Properness over $A/I$ and over $A$ agrees for a closed subspace
factoring through $\operatorname{Spec}(A/I)$: one direction is proper composition, and the other
is the proper cancellation theorem with the separated closed base immersion.

2. For coherent $F,G$ with proper support, put $\mathcal H=\mathcal Hom(F,G)$. The
completion-Hom lemma makes $\mathcal H$ coherent. By the carrier theorem choose a closed
immersion $i:Z\hookrightarrow Y$ with $Z\to\operatorname{Spec}A$ proper and $F\simeq i_*F'$; the
ideal $K_Z$ of $Z$ acts on $i_*F'$ through $\mathcal O_Y\to i_*\mathcal O_Z$, so $K_ZF=0$. For
local sections $a$ of $K_Z$ and $\varphi$ of $\mathcal H$, $(a\varphi)(s)=\varphi(as)=0$, so
$K_Z\mathcal H=0$. The closed-adic dictionary ($Z$ is Noetherian) gives a coherent $Q$ on $Z$
with $\mathcal H\simeq i_*Q$ and $i_*(Q/I^nQ)\simeq\mathcal H/J^n\mathcal H$ compatibly with the
transitions, and its thickening clause identifies $Q/I^nQ$ with the tensor restriction of $Q$ to
$Z\times_A\operatorname{Spec}(A/I^n)$. Sections of a direct image over $Y$ are sections over the
whole source, so quotient global sections on $Y$ equal those on $Z$. Proper coherent higher
images and affine-chart calculus make $\Gamma(Z,Q)$ a finite $A$-module: it is the sections of
the coherent zeroth direct image on $\operatorname{Spec}A$. It is complete by finite-module
completeness over a complete Noetherian ring. Formal functions at degree zero therefore
identifies $\Gamma(Y,\mathcal H)$ with $\varprojlim_n\Gamma(Y,\mathcal H/J^n\mathcal H)$.
Composing with completion-Hom gives a bijection
$\operatorname{Hom}_Y(F,G)\to\operatorname{Hom}(\widehat F_J,\widehat G_J)$; the compatibility
clause says this is the actual completion map. This proves full faithfulness for every separated
finite-type $Y$ over $A$, before any existence argument.

3. It remains to prove essential surjectivity. For a quasi-coherent ideal $L\subseteq\mathcal
O_Y$, let $P(L)$ say every proper-support $J$-system annihilated termwise by $L$ is
algebraizable with proper support. The empty space and the zero system are immediate. If $P(0)$
fails, the ascending chain condition gives a maximal ideal $L$ for which $P(L)$ fails. By the
closed-adic dictionary replace $Y$ by $V(L)$; its coherent modules and systems are precisely
those killed by $L$ on the old space, and proper support is preserved. Every nonzero
quasi-coherent ideal of this quotient corresponds to an ideal $L'\supsetneq L$, so $P(L')$ holds
by maximality. The algebraization it gives lies on $V(L')$: let $M'$ be killed by $L'$ and $F$
coherent with proper support with $\widehat F_J\simeq M'$. Then $L'(F/J^nF)=0$, so $L'F\subseteq
J^nF$ for all $n$. The quotient $\pi:F\to F'=F/L'F$ is killed by the ideal of a proper carrier
of $F$, so it has that carrier by the closed-adic dictionary, and
$F'/J^nF'=F/(L'F+J^nF)=F/J^nF$; thus $\widehat\pi$ is the identity on each level. Step 2 gives
$\sigma:F'\to F$ with $\widehat\sigma=\widehat\pi^{-1}$, and injectivity of the step-2 bijection
gives $\sigma\pi=1$ and $\pi\sigma=1$. Hence $L'F=0$, and the closed-adic dictionary puts $F$
and the isomorphism on $V(L')$. Full faithfulness on this quotient and on all its closed
subspaces is already step 2. Fix a proper-support system $M$ on this quotient; algebraizing it
will contradict the choice of $L$.

4. For this nonempty quotient $Y$, the dense-open Chow modification supplies $q:V\to Y$, with
$V$ a Noetherian scheme immersed over $A$ into finite projective space, and $q$ an isomorphism
over a dense open $U$. The tensor pullback system $q^*M$ is a coherent $I\mathcal O_V$-system
because tensor pullback of a finite presentation remains a finite presentation: it preserves the
finite free terms and their cokernel; quotient transitions are preserved by associativity of
tensor product. Its first term has support proper over $A$. Let $c:C\hookrightarrow Y$ be a
proper closed carrier of $M_1$ with ideal $K_C$, so $K_CM_1=0$. Let
$V_C=V\times_YC\hookrightarrow V$ be the base-changed closed immersion. Its ideal is
$K_C\mathcal O_V$: on etale charts, the base change of
$\operatorname{Spec}(R/K)\to\operatorname{Spec}R$ along $R\to B$ is $\operatorname{Spec}(B/KB)$.
Sections of $q^{-1}K_C$ act by zero on $q^{-1}M_1$, so $K_C\mathcal O_V$ kills $q^*M_1$. Base
change makes $V_C\to C$ proper, and proper composition makes $V_C\to\operatorname{Spec}A$
proper. After the Zariski--etale passage below, the scheme proper-support criterion (a closed
subscheme proper over $A$ whose ideal kills the module) shows that $\operatorname{Supp}(q^*M_1)$
is proper over $A$. By the support-pullback formula this support is
$|q|^{-1}(\operatorname{Supp}M_1)$. Use the scheme Zariski--etale equivalence termwise,
including its natural tensor-pullback comparison, to regard $q^*M$ as a Zariski coherent formal
system on the actual scheme $V$. Apply new-chow-algebraization-core with its scheme $Z=V$, its
proper map the identity of $V$, and the immersion just obtained. It gives a coherent $E$ on $V$
with proper support over $A$ and a compatible isomorphism $\beta:q^*M\simeq\widehat E$. Bring
$E$ and $\beta$ back through the same scheme-site equivalence. No assertion that $Y$ is a scheme
is used.

5. Let $K$ cut out the reduced closed complement $Y\setminus U$; existence of this closed
subspace and its quasi-coherent ideal is the closed-support convention. Its restriction to $U$
is the unit ideal. Since $U$ is dense in nonempty $Y$, it is nonempty, so $K^e\ne0$ for every
$e\geq1$ (its stalk on $U$ is the unit ideal). Step 3 therefore algebraizes every proper-support
system killed by $K^e$ by a coherent module killed by $K^e$. The closed-adic dictionary and step
2 upgrade this to an equivalence for completion on every $V(K^e)$: essential surjectivity is
step 3 and full faithfulness is step 2.

6. Set $H=q_*E$. Proper coherent higher images makes $H$ coherent. To check its proper support
rather than assume it: through the scheme-site equivalence, $E$ is a coherent Zariski module on
the scheme $V$ with support proper over $A$. The scheme proper-support criterion gives a closed
subscheme $c_E:C_E\hookrightarrow V$, proper over $A$, whose ideal $K_E$ kills $E$. Apply the
proper schematic-image theorem to $q\circ c_E:C_E\to Y$ over $\operatorname{Spec}A$. The target
morphism is separated and locally of finite type, so $qc_E$ factors through a closed subspace
$z:Z\hookrightarrow Y$ proper over $A$. Let $K_Z$ be the ideal of $Z$. The factorization means
$q^\sharp(K_Z)\subseteq K_E$. By the defining chart-limit description of $q_*$, a local section
$a$ of $K_Z$ acts on each chart value $E(T)$ through $q^\sharp(a)$, hence by zero: $K_ZH=0$. The
closed-adic dictionary writes $H\simeq z_*Q$ with $Q$ coherent on $Z$. Thus $Z$ is a proper
closed carrier of $H$, and $H$ has proper support over $A$.

7. The modification comparison applied to $q$, $J$, $K$, $M$, $E$ and $\beta$ gives
$a:M\to\widehat H_J$ with uniformly $K$-power-annihilated component kernels and cokernels. Its
hypotheses hold: $q$ is representable proper, both spaces are Noetherian, and $q$ is an
isomorphism over $Y\setminus V(K)=U$. Step 6 gives proper support of $H$; step 5 gives the
completion equivalence on every $V(K^e)$. These are exactly the hypotheses of
bounded-exceptional-torsion devissage. It yields a coherent $F$ with proper support and
$\widehat F_J\simeq M$, contradicting the chosen maximal failure. Consequently there is no bad
ideal and every proper-support system on the original $Y$ is algebraizable.

8. Full faithfulness from step 2 and essential surjectivity from step 7 give the required
equivalence: choose an algebraization and a compatible isomorphism for each system; lift each
morphism uniquely by the Hom bijection. Injectivity of that bijection proves the identity and
composition laws and the naturality of the chosen isomorphisms. The closed-adic dictionary of
step 1 identifies these isomorphisms with all the specified adjacent tensor restrictions. No
step assumed flatness of the spaces or modules. -/
theorem supportedAdicRestriction_isEquivalence [IsNoetherianRing A] [IsAdicComplete I A]
    (hsep : MapIsSeparated p) (hft : MapIsFiniteType p) :
    (supportedAdicRestriction a I p).IsEquivalence := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
