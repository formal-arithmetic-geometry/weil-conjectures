/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection

/-! # Smooth tensor duality for ordinary etale coefficients

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/thm-asd-smooth-tensor.md
(blueprint: thm-asd-smooth-tensor).

The tensor morphism is the specified adjunction mate, with no chosen orientation.
-/

@[expose] public section

universe u u' w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The canonical derived braiding, obtained from the Koszul braiding of the homotopy
category by the derived tensor universal property. Source: blueprint
sec-smooth-purity/sk-prop-sf-cbc/thm-asd-smooth-tensor.md, the tensor mate;
(blueprint: thm-asd-smooth-tensor). This uses the actual derived braiding construction,
not a choice of an unspecified isomorphism. -/
@[instance_reducible]
noncomputable def smoothTensorCanonicalDerivedBraiding
    (C : Type u') [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{u + 1} C] :
    BraidedCategory (_root_.DerivedCategory C) :=
  DerivedMonoidal.braidedCategory' (_root_.DerivedCategory.Qh (C := C))
    (HomotopyCategory.quasiIso C (.up ℤ))

/-- The canonical tensor morphism for the ordinary exceptional adjoint. Source: blueprint
sec-smooth-purity/sk-prop-sf-cbc/thm-asd-smooth-tensor.md, first displayed composite in
its proof (blueprint: thm-asd-smooth-tensor).

Transpose the inverse compact-support projection formula followed by tensoring the
counit at the coefficient unit and the right unit constraint. The upstream projection
map uses the opposite order of tensor factors; the two canonical Koszul symmetries
put it in the displayed order. Its inverse is determined by that map. -/
noncomputable def smoothTensorDualityMap
    (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
    {FC : A → A → Type w} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [(rightDerivedLowerShriek A f).IsLeftAdjoint]
    (hPF : IsIso (projectionMap A f))
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    ((derivedTensor A X).obj ((upperStar A f).leftDerivedFunctor.obj K)).obj
      (dualizingComplex A f) ⟶ (rightDerivedUpperShriek A f).obj K := by
  letI := smoothTensorCanonicalDerivedBraiding (Sheaf X.smallEtaleTopology A)
  letI := smoothTensorCanonicalDerivedBraiding (Sheaf S.smallEtaleTopology A)
  let F := rightDerivedLowerShriek A f
  let w := dualizingComplex A f
  let P := (upperStar A f).leftDerivedFunctor
  letI := hPF
  exact (rightDerivedUpperShriekAdjunction A f).homEquiv _ K
    (F.map (β_ (P.obj K) w).hom ≫
      inv (((projectionMap A f).app w).app K) ≫
      (β_ (F.obj w) K).hom ≫
      ((derivedTensor A S).obj K).map
        ((rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) ≫
      (derivedTensorRightUnitor A S K).hom)


private lemma braided_tensor_mate
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (P W : C) (K : D) (Q : D)
    (π : F.obj (W ⊗ P) ⟶ Q ⊗ K) (ε : Q ⟶ 𝟙_ D) :
    adj.homEquiv _ _ (F.map (β_ P W).hom ≫ π ≫
        (β_ Q K).hom ≫ (K ◁ ε) ≫ (ρ_ K).hom) =
      (β_ P W).hom ≫ (adj.homEquiv _ _ (π ≫ (ε ▷ K)) ≫ G.map (λ_ K).hom) := by
  rw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_left]
  apply congrArg (adj.homEquiv _ _)
  simp only [Category.assoc]
  rw [← BraidedCategory.braiding_naturality_left_assoc, braiding_rightUnitor]

private lemma smoothTensorDualityMap_eq
    (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
    {FC : A → A → Type w} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [(rightDerivedLowerShriek A f).IsLeftAdjoint]
    [hPF : IsIso (projectionMap A f)]
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    let := derivedBraidedCategory A X
    smoothTensorDualityMap A f hPF K =
      (β_ ((upperStar A f).leftDerivedFunctor.obj K) (dualizingComplex A f)).hom ≫
        dualizingComplexTensorMapOfIsIso f K := by
  let := derivedBraidedCategory A X
  let := derivedBraidedCategory A S
  exact braided_tensor_mate (rightDerivedUpperShriekAdjunction A f)
    _ _ K _ (inv (((projectionMap A f).app _).app K))
    ((rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _))


/-- Smooth tensor duality without a chosen orientation, for finite ordinary etale
coefficients and the whole unbounded derived category. Source: blueprint
sec-smooth-purity/sk-prop-sf-cbc/thm-asd-smooth-tensor.md
(blueprint: thm-asd-smooth-tensor).

The local trivializations are module-sheaf isomorphisms to the coefficient ring itself,
so they assert free rank one as well as local constancy. The shifted dualizing object
is isomorphic to this sheaf placed in degree zero. The second clause concerns the
specified canonical tensor mate, not merely existence of an isomorphism.

Proof (the seven steps of the DAG node):
1. Choose a compactification $f=rj$. For an open immersion, the extension-by-zero stalk is the
original stalk in the open and zero outside. Consequently $j_!(j^*P\otimes Q)\cong P\otimes j_!Q$:
at a point in the open it is the identity tensor comparison and outside both sides vanish. This
holds for total complexes as well. Compute the derived tensor with a K-flat resolution with flat
terms of $K$; its inverse image stays K-flat by the ringed-topos tensor-pullback lemma. Since
$j_!$ is exact, the termwise comparison computes the derived one. Apply the proper projection
formula for $r$ to $j_!M$ to obtain $Rf_!(f^*K\otimes^L M)\cong K\otimes^LRf_!M$, for all
unbounded $K,M$. In particular set $M=\omega_f$, compose with the adjunction counit at $A_S$ and
the tensor unit constraint, and transpose. This constructs the claimed global map $\alpha_{f,K}$.
All schemes in the compactification are Noetherian, since $S$ is Noetherian and the morphisms are
finite type. Uses: def-asd-compactifiable, def-amb-etale-compact-support,
lem-weil-pbc-extension-by-zero-stalks, lem-weil-pbc-extension-by-zero-exact,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-amb-proper-coproducts-projection,
thm-amb-etale-exceptional-adjoint, lem-kun-tensor-unit, def-pur-sheaf-tensor-product,
def-weil-pbc-geometric-stalks, prop-weil-pbc-geometric-stalks-exact,
lemma-weil-pbc-geometric-stalk-conservative.

2. The comparison in [lem-amb-etale-compact-comparisons] is used only with the following unbounded
justification, not with its bounded-below source proof. Apply
[lem-kun-proper-base-change-torsion-ring] to every proper rectangle, with coefficient ring $A$ (it
is torsion because $NA=0$). For an open $v:Y\hookrightarrow\overline Y$ and proper $p:\overline
X\to\overline Y$, write $V=p^{-1}Y$, $b:V\hookrightarrow\overline X$. Form the map $v_!Rp_{Y*}M\to
Rp_*b_!M$ as the adjunct for $v_!\dashv v^*$ of the inverse open proper exchange $Rp_{Y*}M\cong
v^*Rp_*b_!M$. Over $Y$ this is that exchange; at a geometric point outside $Y$, unbounded proper
exchange identifies the right side with the cohomology of the fibre of $b_!M$, which is zero
because the fibre misses $V$. The left side is zero by extension-by-zero stalks. Exact restriction
and the stalk criterion applied to each cohomology sheaf prove it is an isomorphism for every
$M\in D(V_{\mathrm{et}},A)$. For a proper refinement $a:\overline X_1\to\overline X_2$ extending
the identity of $X$, over $X$ the open $X\hookrightarrow a^{-1}X$ is a section of the separated
map $a^{-1}X\to X$, hence clopen by [lem-weil-pbc-open-section-clopen]. Extension by zero is $M$
on that component and zero on its complement, so the same argument gives $j_{2!}M\cong
Ra_*j_{1!}M$, with identity on $X$ and zero fibres outside $X$. For coherence, use the canonical
derived pushforward composition of [lem-weil-pbc-ringed-topoi-derived-pushforward-composition].
Every exchange is the mate of the equality of inverse images: its transpose is the inverse-image
comparison followed by the pulled-back counit. For two rectangles substitute the composite counit
$\epsilon_{ba}=\epsilon_b\circ Rb_*(\epsilon_a)$; naturality moves the intervening pullback
comparison past $\epsilon_a$, giving precisely the transpose for the outer rectangle. Thus the two
exchanges agree by the adjunction bijection, for arbitrary unbounded arguments. The same
calculation with three counits proves associativity, and the identity counit proves the identity
law. For the open-extension maps, transpose instead under $v_!\dashv v^*$: restrictions of the two
proposed composites are the just-equal pasted exchanges, so the composites agree. This proves
refinement coherence without claiming that equality of derived morphisms can be tested on stalks.
The Noetherian bases are quasi-compact and quasi-separated, and the source opens in the Noetherian
compactifications are quasi-compact. Thus [prop-nagata-compactification-category], clauses (i) and
(ii), supplies common proper refinements and equalizing refinements. Comparing through a common
refinement gives independence of compactification; equalizing parallel refinements and the
composition law just proved gives independence of the chosen maps into it. Compactify $g$ as
$Y\xrightarrow{v}\overline Y\xrightarrow{r}S$ and $vf$ as $X\xrightarrow{a}\overline
X\xrightarrow{p}\overline Y$; existence is Nagata. Then $X\hookrightarrow V\to Y$ compactifies
$f$. Apply the proved map to $M$ equal to extension by zero from $X$ into $V$, and apply $Rr_*$.
This gives the canonical $Rg_!Rf_!\cong R(gf)_!$; the pasted-exchange identity just proved gives
its associativity and refinement independence. Finally
[lem-weil-pbc-ringed-exchange-tensor-coherence] makes each proper rectangle commute with its
tensor projection map. The open rectangle commutes termwise with tensor by the two
extension-by-zero stalk cases of step 1. Consequently the resulting composition identifies
$P_{gf}$ with $P_g\circ Rg_!(P_f)$, with the usual pullback and tensor associators. These
comparisons supply exactly the unbounded composition used below. Uses:
lem-amb-etale-compact-comparisons, lem-kun-proper-base-change-torsion-ring,
lem-weil-pbc-open-section-clopen, lem-weil-pbc-ringed-topoi-derived-pushforward-composition,
lem-weil-pbc-ringed-exchange-tensor-coherence, lem-weil-pbc-extension-by-zero-stalks,
prop-weil-pbc-inverse-image-modules-exact, lemma-weil-pbc-geometric-stalk-conservative,
thm-nagata-compactification, def-asd-compactifiable, def-amb-etale-compact-support,
prop-nagata-compactification-category.

3. At each point of $X$, the smooth local normal form supplies affine opens $U\subset X$,
$V\subset S$ and an etale map $U\to\mathbf A^d_V$. The dimension in this form is the given $d$:
the etale map has zero-dimensional relative fibres, and [sbc-lem-affine-space-smooth] says that
projection from affine space has relative dimension equal to its number of coordinates; apply
[lem-sbc-smooth-relative-dimension-permanence] to the etale map and that projection. At the chosen
point the resulting dimension equals $d$, so the chart integer is $d$. Compose the etale map with
the open immersion $\mathbf A^d_V\subset\mathbf A^d_S$ to obtain a separated finite-type etale
$e:U\to\mathbf A^d_S$ with $fu=p_de$, where $u:U\hookrightarrow X$. Thus the original base $S$ is
retained. The maps $u,e,p_d,fu$ are compactifiable by Nagata, applied to their separated
finite-type maps and qcqs Noetherian bases. Use the ordinary-etale projective-line adjunction
[lem-asd-ordinary-finite-p1-adjunction], restrict by the exact open extension adjunction to affine
lines, and iterate using step 2. This supplies $Rp_{d!}\dashv p_d^*(d)[2d]$ with its twist
explicitly $A(1)=\mu_N\otimes_{\mathbf Z/N}A$ on the ordinary etale site. In particular it makes
no identification with def-coefficient-twists-detailed. Etale adjoint locality for $u$ and $e$
then identifies $$u^*f^\times K\cong (fu)^\times K\cong e^*p_d^*K(d)[2d],\qquad u^*\omega_f\cong
A_U(d)[2d].$$ Here the finite etale twist is defined by the new ordinary projective-line input,
with the same annihilator $N$ as the twist-line lemma. The affine iteration uses pullback of roots
of unity and the tensor identity $A(1)^{\otimes d}=A(d)$, not an adic comparison. Step 4 below
fixes the counit of that iterated adjunction. The identification is the unique comparison of right
adjoints through their Hom bijections. Uses: sbc-thm-etale-local-normal-form,
lem-sbc-smooth-relative-dimension-permanence, thm-nagata-compactification,
lem-amb-etale-adjoint-locality, lem-asd-finite-etale-twist-line,
lem-asd-ordinary-finite-p1-adjunction, sbc-lem-affine-space-smooth.

4. Fix the normalization of the affine-space adjunction, rather than merely an abstract
isomorphism of its right adjoint. On $\mathbf P^1_S$, the adjunction counit is, by
[lem-asd-ordinary-finite-p1-adjunction] for our arbitrary finite $A$, $$Rq_*q^*K(1)[2]\cong
K\otimes^LRq_*A(1)[2]\xrightarrow{1\otimes t_q}K.$$ For $j:\mathbf A^1_S\hookrightarrow\mathbf
P^1_S$, the right adjoint of $Rq_*j_!$ is $j^*q^*(1)[2]$. Its counit is $Rq_*$ of the counit
$j_!j^*\to\mathrm{id}$ followed by the displayed counit. The open-immersion tensor comparison from
step 1 sends this composite to $1_K$ tensored with its value at $A_S$. Use the unbounded
composition comparison proved in step 2. Iterating the affine-line factorization of $p_d$ gives
the same assertion for $p_d$: the composite counit is obtained by successively applying the $d$
line counits. For $d=0$ it is the identity. Tensor reassociation sends $x\otimes
m_1\otimes\cdots\otimes m_d$ to the same tensor at each stage, so its transpose is exactly the
canonical isomorphism $p_d^*K\otimes^LA(d)[2d]\cong p_d^*K(d)[2d]$. Uses:
lem-amb-etale-adjoint-locality, lem-amb-etale-compact-comparisons, lem-kun-tensor-unit,
lem-asd-ordinary-finite-p1-adjunction.

5. For a separated finite-type etale map $v$, its sum-extension definition gives, at each
geometric point, one summand for each lift to the source. Indeed, a germ in the defining sum
presheaf has finite support; each map to the etale source determines a lift of the geometric
point, and equal germs of these maps agree on a common pointed etale neighbourhood. Conversely a
lift is represented on such a neighbourhood. Taking the filtered colimit therefore gives exactly
the sum over lifts, and exactness of geometric stalks lets this computation pass through
cohomology. The sheaf tensor definition gives its stalk as the tensor of stalks: both sides are
the filtered colimit of the section tensors, since every finite tensor expression and every
relation occurs on a common neighbourhood. Tensoring by an inverse-image complex distributes over
these sums; the comparison sends $x\otimes m$ in the summand of a lift to the same tensor in that
summand. The counit $v_!v^*B\to B$ is the fold map, so this tensor comparison commutes with the
counit. This can be checked on K-flat models: inverse image preserves K-flatness, $v_!$ is exact,
and its total sums preserve the termwise tensor identification. Thus it also holds on the
unbounded derived categories. Apply the comparison and fold-counit identity separately to the
factorizations $h=fu$ and $h=p_de$. Write $F=Rf_!$, $G=f^\times$, and $P_g$ for the projection
isomorphism $Rg_!(g^*K\otimes M)\to K\otimes Rg_!M$ of step 1. For $h=fu$, the canonical
right-adjoint comparison gives $h^\times=u^*G$, and its counit at $B$ is
$$\epsilon_{h,B}=\epsilon_{f,B}\circ F(\epsilon_{u,GB}).$$ The transpose under $Ru_!\dashv u^*$ of
$u^*\alpha_{f,K}$ is the composite $$Ru_!(h^*K\otimes u^*\omega_f)\xrightarrow{P_u} f^*K\otimes
Ru_!u^*\omega_f\xrightarrow{1\otimes\epsilon_{u,\omega_f}}
f^*K\otimes\omega_f\xrightarrow{\alpha_{f,K}}GK.$$
Indeed naturality of the fold counit moves $Ru_!u^*\alpha_{f,K}$ past that counit, and the
fold/tensor identity above gives the first two arrows. Applying $F$ and then $\epsilon_{f,K}$
transposes once more. The defining transpose of $\alpha_{f,K}$, naturality of $P_f$ in its second
variable, and the formula for $\epsilon_h$ identify the result with $P_h$ followed by
$1_K\otimes\epsilon_{h,A}$. Here the composition comparison identifies $P_h$ with first applying
$F(P_u)$ and then $P_f$: both projection maps are obtained from the pullback tensor comparison and
adjunction evaluation; substituting the composite evaluation applies these two evaluations in that
order. Thus $u^*\alpha_{f,K}$ is the canonical tensor mate for $h$. For $h=p_de$, put $H=Rp_{d!}$
and $J=p_d^\times$. Under $Re_!\dashv e^*$ the transpose of $e^*\alpha_{p_d,K}$ is explicitly
$$Re_!(h^*K\otimes e^*A(d)[2d])\xrightarrow{P_e}p_d^*K\otimes
Re_!e^*A(d)[2d]\xrightarrow{1\otimes\epsilon_{e,A(d)[2d]}}p_d^*K\otimes
A(d)[2d]\xrightarrow{\alpha_{p_d,K}}JK.$$ Applying $H$ and then $\epsilon_{p_d,K}$ replaces the
last arrow by $P_{p_d}$ followed by $1_K\otimes\epsilon_{p_d,A}$. Naturality of $P_{p_d}$ moves
$\epsilon_e$ into its second factor. Step 2 identifies the first two projection arrows with $P_h$,
and the remaining arrows with $1_K\otimes\epsilon_{h,A}$. Thus this transpose is the canonical
tensor mate for $h$, with counit $\epsilon_{p_d,B}\circ Rp_{d!}(\epsilon_{e,p_d^\times B})$; this
is an alternative expression for the counit of $h$, not an additional counit after the $u$-counit.
The unbounded compact-support composition and tensor compatibilities proved in step 2, and
uniqueness of the right-adjoint Hom bijections identify the two expressions. Step 4 makes
$\alpha_{p_d,K}$ the tensor reassociation isomorphism, and exact inverse image and the derived
tensor-pullback comparison preserve it. Hence $u^*\alpha_{f,K}$ is an isomorphism for every chart
$U$. Uses: def-weil-pbc-etale-sum-extension, lem-weil-pbc-etale-restriction-injectives,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-amb-etale-adjoint-locality,
lem-amb-etale-compact-comparisons, thm-amb-etale-exceptional-adjoint,
def-pur-sheaf-tensor-product, def-weil-pbc-geometric-stalks, prop-weil-pbc-geometric-stalks-exact,
lemma-weil-pbc-geometric-stalk-conservative.

6. Inverse image on etale module sheaves is exact, so it commutes with cohomology. The charts of
step 3 cover $X$, and step 5 therefore makes every geometric stalk of every cohomology map
$\mathcal H^i(\alpha_{f,K})$ an isomorphism. Apply the geometric-stalk criterion to each
underlying abelian cohomology sheaf. Every $\mathcal H^i(\alpha_{f,K})$ is an isomorphism;
equivalently its cone is acyclic, so $\alpha_{f,K}$ is an isomorphism in the ordinary derived
category. This uses no bounded-below hypothesis and applies the sheaf-level criterion only to
sheaves. Uses: prop-weil-pbc-inverse-image-modules-exact,
lemma-weil-pbc-geometric-stalk-conservative, def-weil-pbc-derived-categories,
def-weil-derived-cohomology-sheaves.

7. The local model $u^*\omega_f\cong A_U(d)[2d]$ and the twist-line lemma give $\mathcal
H^i(\omega_f)=0$ for $i\ne-2d$: exact inverse image and the sheaf-stalk criterion detect this
vanishing. Put $L=\mathcal H^{-2d}(\omega_f)$. It is locally isomorphic to $A_U(d)$, and refining
the chart by a twist trivialization makes it isomorphic to $A$, which is precisely the stated
local rank-one condition. To identify the complex globally, take a representative $C$ of
$\omega_f$ and let $q=-2d$. The good truncation $\tau_{\le q}C\to C$ is a quasi-isomorphism
because cohomology above $q$ vanishes. The projection $\tau_{\le q}C\to L[-q]$ is a
quasi-isomorphism because its kernel is acyclic (cohomology below $q$ vanishes and its degree-$q$
cycles equal its boundaries). These two quasi-isomorphisms give $\omega_f\cong L[2d]$. No local
choices of a primitive root or of a basis of $L$ are glued into an orientation. Uses:
lem-asd-finite-etale-twist-line, prop-weil-pbc-inverse-image-modules-exact,
lemma-weil-pbc-geometric-stalk-conservative, def-kun-truncations,
def-weil-derived-cohomology-sheaves, def-constructible-locally-constant.
-/
theorem smooth_tensor_duality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X S : Scheme.{u}} [IsNoetherian S]
    (hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s))
    (f : X ⟶ S) [IsSeparated f] [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    (∃ L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty ((dualizingComplex (ModuleCat.{u + 1} A) f)
        ⟦-(2 * (d : ℤ))⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj L) ∧
      ∃ cover : Scheme.Cover.{u} Scheme.etalePrecoverage X,
        ∀ i : cover.I₀,
          Nonempty (L.over (cover.etalePrecoverageToEtale i) ≅
            (constantSheaf (X.smallEtaleTopology.over (cover.etalePrecoverageToEtale i))
              (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))) ∧
    ∀ K : DerivedCategoryModule A S, IsIso (smoothTensorDualityMap (ModuleCat.{u + 1} A) f
      (isIso_projectionMap_of_finite A f) K) := by
  classical
  have hNS : IsUnit (N : Γ(S, ⊤)) := by
    apply S.toRingedSpace.isUnit_of_isUnit_germ
    intro s hs
    simpa only [map_natCast] using hInvertible s
  have : HasInvertibleExponent A S := ⟨N, hN, hA, hNS⟩
  have : HasInvertibleExponent A X := HasInvertibleExponent.of_hom f
  obtain ⟨L, hLC, hStalk, ⟨e⟩, hTensor⟩ := exists_dualizingComplex_iso_and_tensor A f d
  constructor
  · refine ⟨L, ?_, ?_⟩
    · exact ⟨(shiftFunctor _ (-(2 * (d : ℤ)))).mapIso e ≪≫
        shiftShiftNeg _ (2 * (d : ℤ))⟩
    · have : Scheme.IsLocallyConstantSheaf L := hLC
      obtain ⟨datum⟩ := hLC.nonempty_locallyConstantDatum
      let cover : Scheme.Cover.{u} Scheme.etalePrecoverage X :=
        Scheme.Cover.mkOfCovers (Σ i : datum.cover.I₀, datum.cover.X i)
          (fun i ↦ datum.cover.X i.1) (fun i ↦ datum.cover.f i.1)
          (by
            intro x
            obtain ⟨i, y, hy⟩ := datum.cover.exists_eq x
            exact ⟨⟨i, y⟩, y, hy⟩)
          (fun i ↦ datum.cover.map_prop i.1)
      refine ⟨cover, ?_⟩
      intro i
      let U := datum.cover.etalePrecoverageToEtale i.1
      have hC := datum.isConstant i.1
      have := hC
      obtain ⟨M, ⟨eM⟩⟩ := (L.over U).mem_essImage_of_isConstant
      let t := (datum.cover.X i.1).algClosurePoint i.2
      let P := upperStar (ModuleCat.{u + 1} A) U.hom
      let eP : (constantSheaf U.left.smallEtaleTopology (ModuleCat A)).obj M ≅ P.obj L :=
        ((Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
          (X.smallEtaleTopology.over U) U.left.smallEtaleTopology (ModuleCat A)
          Over.mkIdTerminal).symm.app M ≪≫
        (Scheme.Etale.overSheafEquiv U (ModuleCat A)).functor.mapIso eM ≪≫
        Scheme.overSheafEquivFunctorObjOverIso (ModuleCat A) U L
      have : PreservesFilteredColimitsOfSize.{u, u}
          (CategoryTheory.forget (ModuleCat.{u + 1} A)) :=
        preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
      let eFree : M ≅ ModuleCat.of A A :=
        ((Scheme.pointSmallEtale t).sheafFiberConstantSheafIso M).symm ≪≫
        (Scheme.pointSmallEtale t).sheafFiber.mapIso eP ≪≫
        (upperStarCompSheafFiberIso (ModuleCat A) U.hom t).app L ≪≫
        (hStalk _ (t ≫ U.hom)).some
      exact ⟨eM.symm ≪≫
        (constantSheaf (X.smallEtaleTopology.over U) (ModuleCat A)).mapIso eFree⟩
  · intro K
    let := derivedBraidedCategory (ModuleCat A) X
    rw [smoothTensorDualityMap_eq]
    have : IsIso (dualizingComplexTensorMapOfIsIso f K) := hTensor K
    infer_instance

end AlgebraicGeometry.Etale
