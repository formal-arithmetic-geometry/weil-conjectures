module

public import Sheaf.Paper.PodMixedSupportCupProduct
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Paper.AdmissibleCupCoefficientPassages
public import Sheaf.Paper.MixedCupTensorNormalization
public import Sheaf.Paper.BasicOperationsCoefficientReduction

import Sheaf.Paper.MixedCupOperationComparisons
import Sheaf.Paper.MixedCupTensorComparisons
import Sheaf.Paper.MixedCupCoefficientSquare

/-! # Coefficient comparisons for the mixed-support cup

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
def-pod-mixed-support-cup-product, final coefficient compatibility sentence
(blueprint: prop-sf-mixed-cup-coefficient-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings
namespace WeilConjectures.MixedCupCoefficientChange
open scoped WeilConjectures.MixedCupCoefficientChange

variable {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)

/-- All coefficient squares, with natural comparisons on the actual functors.
The point tensorator and the unit/composition comparisons have fixed K-flat
normalizations. Both support choices occur in one family; the final field only
states a square, rather than postulating any new cup product.
Source: final two paragraphs of def-pod-mixed-support-cup-product
(blueprint: prop-sf-mixed-cup-coefficient-change). -/
structure Comparisons (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left) where
  pointUnit : ∀ a : Stage C, pointChange C (.identity a) ≅ 𝟭 _
  pointUnit_normalized : ∀ a, PointUnitNormalized C a (pointUnit a)
  pointComp : ∀ {a b d : Stage C} (f : Passage C a b) (g : Passage C b d),
    pointChange C (.comp f g) ≅ pointChange C f ⋙ pointChange C g
  pointComp_normalized : ∀ {a b d : Stage C} (f : Passage C a b) (g : Passage C b d),
    PointCompNormalized C f g (pointComp f g)
  cohomologyIso : ∀ {a b : Stage C} (f : Passage C a b) (compact : Bool),
    cohomology C S X c compact a ⋙ pointChange C f ≅
      change C X f ⋙ cohomology C S X c compact b
  ringed_cohomology_normalized : RingedCohomologyNormalized C S X c cohomologyIso
  localization_cohomology_normalized : LocalizationCohomologyNormalized C S X c cohomologyIso
  field_cohomology_normalized : FieldCohomologyNormalized C S X c cohomologyIso
  tensorIso : ∀ {a b : Stage C} (f : Passage C a b), TensorComparison C S X f
  finite_tensor_normalized : FiniteTensorNormalized C S X tensorIso
  integral_tensor_normalized : IntegralTensorNormalized C S X tensorIso
  rational_tensor_normalized : RationalTensorNormalized C S X tensorIso
  reduction_tensor_normalized : ReductionTensorNormalized C S X tensorIso
  localization_tensor_normalized : LocalizationTensorNormalized C S X tensorIso
  closure_tensor_normalized : ClosureTensorNormalized C S X tensorIso
  tensor_natural : ∀ {a b : Stage C} (f : Passage C a b)
    {K K' L L' : (domain C X.obj.left a).FullSubcategory} (k : K ⟶ K') (l : L ⟶ L'),
    (change C X f).map (tensorMap C S X a k l) ≫ (tensorIso f K' L').hom =
      (tensorIso f K L).hom ≫
      tensorMap C S X b ((change C X f).map k) ((change C X f).map l)
  identity : ∀ (a : Stage C) (compact : Bool)
    (K : (domain C X.obj.left a).FullSubcategory),
    (cohomologyIso (.identity a) compact).hom.app K =
      (pointUnit a).hom.app ((cohomology C S X c compact a).obj K)
  composition : ∀ {a b d : Stage C} (f : Passage C a b) (g : Passage C b d)
    (compact : Bool) (K : (domain C X.obj.left a).FullSubcategory),
    (cohomologyIso (.comp f g) compact).hom.app K =
      (pointComp f g).hom.app ((cohomology C S X c compact a).obj K) ≫
      (pointChange C g).map ((cohomologyIso f compact).hom.app K) ≫
      (cohomologyIso g compact).hom.app ((change C X f).obj K)
  tensor_identity : ∀ (a : Stage C) (K L : (domain C X.obj.left a).FullSubcategory),
    (tensorIso (.identity a) K L).hom = 𝟙 _
  tensor_composition : ∀ {a b d : Stage C} (f : Passage C a b) (g : Passage C b d)
    (K L : (domain C X.obj.left a).FullSubcategory),
    (tensorIso (.comp f g) K L).hom =
      (change C X g).map ((tensorIso f K L).hom) ≫
      (tensorIso g ((change C X f).obj K) ((change C X f).obj L)).hom
  square : ∀ {a b : Stage C} (f : Passage C a b)
    (K L : (domain C X.obj.left a).FullSubcategory),
    (pointChange C f).map (normalizedCup C S X c a K L) ≫
      (cohomologyIso f true).hom.app (tensorInput C S X a K L) ≫
      (cohomology C S X c true b).map ((tensorIso f K L).hom) =
      (pointTensor C f ((cohomology C S X c true a).obj K)
        ((cohomology C S X c false a).obj L)).hom ≫
      ((cohomologyIso f true).hom.app K ⊗ₘ (cohomologyIso f false).hom.app L) ≫
      normalizedCup C S X c b ((change C X f).obj K) ((change C X f).obj L)

/-- Separation of the specified geometric fibre is inherited by base change.
Source: sk-def-set, geometric fibre in the mixed-support cup setting
(blueprint: prop-sf-mixed-cup-coefficient-change). -/
instance geometricSpaceSeparated (d : ℕ) (G : PoincareDualitySetting D.k₀ d) :
    IsSeparated (pairingGeometricSpace D d G).obj.hom := by
  dsimp [pairingGeometricSpace, PoincareDualitySetting.structureMorphism]
  infer_instance

/-- Coefficient compatibility of the recorded mixed-support cups, for every
finite-ring homomorphism, integral reduction, finite integral/field extension,
rationalization, common-stage inclusion, and every successive passage.
The geometry is precisely the geometric fibre of the fixed smooth pure-dimensional,
separated finite-type geometrically connected model. The operations argument is the
existing normalized construction datum, not an additional coefficient comparison.

Source: current blueprint, def-pod-mixed-support-cup-product, final two paragraphs
(blueprint: prop-sf-mixed-cup-coefficient-change).

Proof:
1. Write $f=a_X$, $F_\Lambda=Rf_{!,\Lambda}$, $G_\Lambda=Rf_{*,\Lambda}$ and
$P_\Lambda=Lf_\Lambda^*$. The definition gives the sheaf-level cup map
$F_\Lambda(1_K\otimes\varepsilon_L)\circ\operatorname{PF}_{\Lambda;K,G_\Lambda L}$. Its second
projection-formula input is $G_\Lambda L$, an object on $s$, rather than $L$ on $X$. All these
expressions lie in the finite-Tor constructible domains recorded in that definition. For a
coefficient passage, denote the canonical comparisons by $c:S_sF_\Lambda\cong F_BS_X$,
$o:S_sG_\Lambda\cong G_BS_X$, $h:P_BS_s\cong S_XP_\Lambda$, and $t:S(M\otimes N)\cong SM\otimes
SN$. We establish these actual comparisons, then paste two squares.

2. For $A_{E,n}\to A_{F,m}$, both rings are finite and the target is a finite module over the
source. The finite-direct-image theorem gives $o$, including its pro-etale form and its
counit-transpose normalization. At etale level the compact-support scalar theorem gives $c$ by
$S Rp_*j_!\to Rp_*S j_!\cong Rp_*j_!S$ for a compactification $f=pj$, and gives its projection
compatibility. Finite constructible complexes have etale origin; the compact-support site
comparison identifies this composite with the pro-etale one. The scalar/pullback cube identifies
the pullback comparisons in this transport. The canonical ringed derived tensor comparisons give
$h,t$. No flatness or finite projective dimension of $A_{F,m}$ over $A_{E,n}$ is used. This
includes $m=n$ and nonflat quotient reductions. The $B$-stage inputs lie in the domain of
$\mu^B$: let $G,G'$ be bounded constructible finite-Tor etale origins of $K,L$. The domain
theorem for finite coefficient change [lem-sp-finite-compact-support-domains], applied to the
identity compactification $X=X=X$, shows that $G_B,G'_B$ are bounded constructible of finite Tor
amplitude and that their site pullbacks are intrinsically constructible of finite Tor amplitude
on $X_{\mathrm{proet}}$. The comparison $\delta_X$ of the scalar/pullback cube identifies these
pullbacks with $K_B,L_B$. Hence $K_B,L_B\in D^b_{ctf}(X,A_{F,m})$, and $\mu^B_{K_B,L_B}$ is
defined.

3. For integral reduction, use the operation-reduction comparisons for $c,o,h,t$; these preserve
the units and counits, not only the objects. For $\mathcal O_E\to\mathcal O_F$, the finite-free
completed-scalar theorem identifies the prescribed completed extension with ordinary tensor
along $R_W=\widehat{\mathcal O}_{E,W}\to\widehat{\mathcal O}_{F,W}=T_W$. Its completed pullback
and tensor comparisons are those of the integral-operations scalar theorem. The compact-support
integral-coefficient theorem gives $c$ with exactly the specified finite-free reductions. To see
$o$ is invertible, restrict completed coefficients to constant $\mathcal O_E$ coefficients via
the completed-pushforward comparison. Choose an $\mathcal O_E$-basis of $\mathcal O_F$: the
canonical tensor/direct-image map becomes the comparison $\bigoplus_{i=1}^{[F:E]}Rf_*M\to
Rf_*(\bigoplus_iM)$, an isomorphism since an additive functor preserves finite biproducts. This
is a verification of the canonical map, so its definition is independent of the basis. Domains:
$K\otimes_{\mathcal O_E}\mathcal O_F$ lies in $D^b_c(X,\mathcal O_F)$
[lem-weil-integral-scalar-extension-constructible], which equals $D^b_{ctf}(X,\mathcal O_F)$ by
[thm-sf-ctf-stability] (vii); integral reductions $K_n$ lie in $D^b_{ctf}(X,A_{E,n})$ by the
uniform Tor interval of the definition. In the basis argument the $\mathcal O_F$-direct image is
compared with the $\mathcal O_E$-direct image of the restricted module. Restriction along
$R_W\to T_W$ is the exact direct image of the identity-site ringed morphism, so the composite
comparison $\kappa$ of [lem-sfb-ringed-derived-monoidal-comparisons] commutes it with $Rf_*$.
Restriction is conservative, so invertibility may be checked on underlying $R$-modules.

4. Rationalization sends the integral comparisons to $c,o,h,t$ for $\mathcal O_E\to E$. For
$E\to F$, rationalize the integral extension comparisons. The operation-reduction theorem
supplies compatibility with the ordinary units and counits in both passages, and projection
coherence supplies compatibility with the specified projection transformation. At
$\overline{\mathbf Q}_\ell$, choose a common finite coefficient field for the finitely many
objects and arrows involved and use their representatives there. The common-stage definition
identifies representatives after further extension, so the finite-field comparisons define the
claimed natural isomorphisms independently of that choice. This uses the rationalized and
common-stage categories of the item, without identifying them with ambient condensed module
categories. At $E$ and $\overline{\mathbf Q}_\ell$ the finite-Tor categories are the
rationalized and common-stage categories themselves [def-weil-finite-tor-amplitude], so the
integral domain statements of step 3 give the domains.

5. For every passage the ordinary comparison is the counit-normalized mate. Thus, with
right-to-left composition, its defining equation is $\varepsilon^B_{S_XL}\circ
P_B(o_L)=S_X(\varepsilon^\Lambda_L)\circ h_{G_\Lambda L}$. At finite coefficients this is
precisely the transpose specification in the finite-direct-image theorem. At completed and
rational stages it is the unit/counit compatibility in operation reduction. For finite-free
integral extension it is the same ringed derived adjunction calculation: both maps, on
restriction and in a finite basis, are the direct sum of the original counit. Tensoring this
equality with $S_XK$ and using $t$ gives the square comparing $S_X(1_K\otimes\varepsilon_L)$
with $1_{S_XK}\otimes\varepsilon^B_{S_XL}$, with $1\otimes P_B(o_L)$ on its source. This
equation is the required compatibility of the second factor of the cup composite.

6. Projection coherence identifies $S_s(\operatorname{PF}_{\Lambda;K,G_\Lambda L})$, through
$c,t,h$, with $\operatorname{PF}_{B;S_XK,S_sG_\Lambda L}$. Its naturality in the second
variable, applied to $o_L:S_sG_\Lambda L\to G_BS_XL$, then gives
$\operatorname{PF}_{B;S_XK,G_BS_XL}\circ(1\otimes o_L)$ on the upper source, and $F_B(1\otimes
P_B(o_L))$ on the lower target. Paste this square with the counit square from the preceding
step, and use naturality of $c$ on the morphism $1_K\otimes\varepsilon_L$. The middle arrow
$P_B(o_L)$ is absorbed by the counit equation. The resulting equality is $$c_{K\otimes
L}\,S_s\bigl(F_\Lambda(1\otimes\varepsilon_L)\operatorname{PF}_{\Lambda;K,G_\Lambda
L}\bigr)=F_B(1\otimes\varepsilon^B)\operatorname{PF}_{B;S_XK,G_BS_XL}(c_K\otimes o_L),$$ with
the canonical scalar tensor identifications understood. This is the desired square before taking
the point fibre.

7. Apply $\operatorname{Fib}_s$ to that equality. Its tensor comparison is coefficient
compatible, so the bottom and top composites become exactly $\mu^B$ and $S_s\mu^\Lambda$. For
integral reduction the sections/scalar identification is the natural point-sections
derived-reduction isomorphism; for integral extension it is the inverse of the point-sections
scalar-extension comparison; for rationalization it is the defining rationalization of sections.
For an arbitrary map of the finite rings, compute on the etale point: the constant/stalk
equivalence is symmetric monoidal and its tensor map sends $x\otimes b$ to $x\otimes b$.
Transport through the finite etale/pro-etale equivalence yields the same sections/scalar map.
Hence the induced vertical maps are precisely $u_c,u_o,u_{c,\otimes}$ specified in the item,
rather than unspecified isomorphisms of cohomology objects.

8. Identity coefficient maps have identity tensor comparisons and identity mates. For successive
coefficient maps, balanced reassociation sends $((x\otimes b)\otimes c)$ to $x\otimes bc$. The
ringed derived monoidal comparisons identify the direct scalar/pullback comparison with the
composite one. Taking its adjunction transpose gives the same equality for $o$ (explicitly
included in the finite-direct-image theorem). The compact-support map is the proper comparison
followed by the open balancing map; the latter has the same formula on the open and is zero off
it, so these two factors give the same coefficient cocycle for $c$. The integral extension
cocycle is the specified completed scalar associator and the integral compact-support cocycle;
the point-sections comparison obeys the same associator. Operation reduction preserves the
structural maps for mixed reductions, and rationalization preserves these equalities. Finally,
equality after a further common finite field is equality in the common-stage category. Pasting
the two coefficient squares therefore gives the square for the successive passage.

9. Under integral reduction, the integral projection transformation is the finite one by the
adic projection theorem, and the ordinary counit reduces to the finite counit by operation
reduction. Reducing their composite therefore gives the finite cup map, for every $n$. This
proves the last assertion as an equality of the specified derived morphisms. At a field stage
choose the stipulated integral representative and apply this statement to it; no map from a
field to its finite residue quotient or representative-independent field reduction is
introduced.
-/
theorem mixedCupCoefficientChange (S : Operations C) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d)
    (c : Compactification (sixFunctorStructure (pairingGeometricSpace D d G)).hom.left) :
    Nonempty (Comparisons C S (pairingGeometricSpace D d G) c) := by
  let X := pairingGeometricSpace D d G
  obtain ⟨pointUnit, pointComp, cohomologyIso, h_pointUnit_normalized, h_pointComp_normalized,
    h_ringed_cohomology_normalized, h_localization_cohomology_normalized,
    h_field_cohomology_normalized, h_identity, h_composition⟩ :=
    operationComparisons_exists C S X c
  obtain ⟨tensorIso, h_finite_tensor_normalized, h_integral_tensor_normalized,
    h_rational_tensor_normalized, h_reduction_tensor_normalized,
    h_localization_tensor_normalized, h_closure_tensor_normalized, h_tensor_natural,
    h_tensor_identity, h_tensor_composition⟩ :=
    tensorComparisons_exists C S X
  refine ⟨{ pointUnit := pointUnit
            pointUnit_normalized := h_pointUnit_normalized
            pointComp := pointComp
            pointComp_normalized := h_pointComp_normalized
            cohomologyIso := cohomologyIso
            ringed_cohomology_normalized := h_ringed_cohomology_normalized
            localization_cohomology_normalized := h_localization_cohomology_normalized
            field_cohomology_normalized := h_field_cohomology_normalized
            tensorIso := tensorIso
            finite_tensor_normalized := h_finite_tensor_normalized
            integral_tensor_normalized := h_integral_tensor_normalized
            rational_tensor_normalized := h_rational_tensor_normalized
            reduction_tensor_normalized := h_reduction_tensor_normalized
            localization_tensor_normalized := h_localization_tensor_normalized
            closure_tensor_normalized := h_closure_tensor_normalized
            tensor_natural := h_tensor_natural
            identity := h_identity
            composition := h_composition
            tensor_identity := h_tensor_identity
            tensor_composition := h_tensor_composition
            square := ?_ }⟩
  exact normalizedCup_coefficient_square C S X c pointUnit pointComp cohomologyIso tensorIso
    h_pointUnit_normalized h_pointComp_normalized h_ringed_cohomology_normalized
    h_localization_cohomology_normalized h_field_cohomology_normalized h_identity h_composition
    h_finite_tensor_normalized h_integral_tensor_normalized h_rational_tensor_normalized
    h_reduction_tensor_normalized h_localization_tensor_normalized h_closure_tensor_normalized
    h_tensor_natural h_tensor_identity h_tensor_composition

end WeilConjectures.MixedCupCoefficientChange
