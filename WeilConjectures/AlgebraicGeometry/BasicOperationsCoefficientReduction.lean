/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OperationCoefficientActionData
import WeilConjectures.AlgebraicGeometry.BasicOperationReductionAndEvaluation
import WeilConjectures.AlgebraicGeometry.BasicOperationCoefficientCoherence
import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
import WeilConjectures.AlgebraicGeometry.IntegralOperationsPreserveConstructible

/-! # A component of the operation coefficient reduction argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe d t u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

/-- For the derived-complete coefficient categories, reduction commutes with
pullback, tensor, ordinary direct image, and compact-support direct image on
exactly the bounded domains of the definitions. The finite pullback/tensor
maps are the normalized `canonicalFinitePullbackTensor` maps and their quotient
mates; Hom maps are the evaluation-defined reduction maps. Scalar extension,
rationalization, common stages, exceptional-adjoint mates, and all stated
associativity, evaluation, unit, and counit equations use these same maps.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-sf-pf-reduction/lem-fix-operation-reduction.md
(blueprint: lem-fix-operation-reduction).
Proof (the ten steps of the DAG node):
1. Use the small pro-etale coefficient sites and operations of
[def-weil-derived-pullback-tensor-hom], and write $F_{A,B}=-\otimes_A^LB$ for coefficient
extension. For finite $A\to B$, [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] applied to the
identity topos gives $F_{A,B}(M\otimes_A^LN)\cong F_{A,B}M\otimes_B^LF_{A,B}N$. For pullback apply
the same K-flat construction to the commuting square of coefficient ring maps on $X$ and $Y$: both
$Lf_B^*F_{A,B}K$ and $F_{A,B}Lf_A^*K$ are represented by $B_X\otimes_{f^{-1}A_Y}f^{-1}P$ for a
flat-term K-flat replacement $P$ of $K$. The derived tensor-pullback lemma ensures these pullbacks
are K-flat, so these are comparisons of derived functors, not merely underived tensor expressions.
The two routes through a threefold coefficient extension send $((x\otimes a)\otimes b)$ to
$x\otimes ab$; the tensor comparison sends $(x\otimes a)\otimes(y\otimes b)$ to $(x\otimes
y)\otimes ab$. These formulas prove the associativity and unit identities and descend through
quasi-isomorphisms. At integral level the operations are completed pullback and completed tensor,
so one cannot simply omit completion: clauses (1) and (2) of
[lem-pur-integral-operations-preserve-constructible] supply their canonical reduction
isomorphisms. Their quotient-level maps are the same tensor formulas just written, so their
associativity and units have those formulas after reduction as well.
2. For finite $A=A_{E,n}\to B=A_{E,m}$ let $K$ be site-perfect [def-weil-site-perfect-complex].
The ringed-site duality theorem [lem-sfb-ringed-site-perfect-duality] gives $R\mathcal
Hom_A(K,L)=K^\vee\otimes_A^L L$ for arbitrary $L$, with its evaluation-defined map, and makes
$K^\vee$ perfect. Locally represent $K$ by a bounded complex $P$ of finite-projective sheaves. The
canonical map $P^\vee\otimes_A B\to(P\otimes_A B)^\vee$ is a chain isomorphism: for $P^i=A^r$ it
is the identity on $B^r$, and for a summand it is the restriction of that identity along the
tensor of its splitting. Only finitely many degrees occur, and precomposition with the
differential gives the same dual differential on both sides. Apply the tensor comparison of
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback] and the duality theorem over $A$ and $B$ to
obtain
$$F R\mathcal Hom_A(K,L)\cong F(K^\vee)\otimes_B^L FL\cong(FK)^\vee\otimes_B^L FL\cong R\mathcal
Hom_B(FK,FL).$$
The local map is the transpose of reduced evaluation: on each term it sends $h\otimes b,p\otimes
c$ to $h(p)\otimes bc$, with the same total-complex signs. By
[lem-weil-pbc-ringed-internal-hom-exact-restriction] this is the restriction of the global
comparison; the local-isomorphism criterion of [lem-weil-pbc-ringed-projection-restriction], for
the identity morphism, proves it invertible globally. No finite-Tor hypothesis on $L$ is used. The
perfectness of the coefficient dual of a perfect point complex is also the duality theorem's first
conclusion.
3. For integral coefficients the first variable need not be perfect. The finite free resolution
$[\mathcal O_E\xrightarrow{\varpi_E^n}\mathcal O_E]$ is supplied by
[lem-weil-pbc-standard-quotients-perfect]. By [lem-weil-l-adic-extension-integers-dvr], $\mathcal
O_E$ is a principal ideal domain, hence Noetherian since every ideal is finitely generated. Apply
[lem-weil-pbc-completed-constant-sheaf-reduction] to obtain the actual resolution
$[R\xrightarrow{\varpi_E^n}R]$ of $B=(A_{E,n})_W$ over $R=\widehat{\mathcal O}_{E,W}$; ring-module
perfectness alone would not identify these sheaves. The ambient comparison theorem
[lem-coef-integral-hom-reduction] now gives $R\mathcal
Hom_R(K,L)\otimes_R^LB\xrightarrow{\sim}R\mathcal Hom_B(K_n,L_n)$ for arbitrary $K,L$, and says
that this very map is the transpose of reduced evaluation. It also gives completeness of the
integral Hom when $L$ is complete. Restrict this ambient assertion to exactly those integral pairs
for which the Hom belongs to the stated constructible category. In the two-term description,
commuting Hom in the second variable with this finite cone accounts for the first isomorphism of
the blueprint, and extension-restriction adjunction accounts for the second. The cited ambient
theorem provides both assertions together with their specified evaluation normalization; no
general finite-level Hom comparison is being inferred without the site-perfect hypothesis of step
2.
4. For ordinary direct image apply [lemma-weil-pbc-perfect-projection-formula] to
$P_n=(A_{E,n})_Y$, which is site-perfect over the completed coefficient sheaf by the two-term
resolution in step 3. Its specified projection map is an isomorphism $(Rf_*K)\otimes^L P_n\to
Rf_*K_n$, and the theorem gives its compatibility with quotient maps.
[prop-weil-pbc-direct-image-limits] identifies ordinary direct image of a complete object with the
derived limit of its finite-level images, including the completion map and the Roos transition
operator $1-s$. Thus it identifies this object with the integral direct image actually defined in
[def-weil-derived-direct-image]. On the stated finite-type bounded constructible domains,
[lem-sf-integral-direct-image-constructible] explicitly says that the comparison from that
definition is an isomorphism and that the images are bounded constructible, with a uniform
cohomological bound independent of $n$. These are complementary assertions: the projection formula
fixes the map, the limit theorem fixes the completed realization, and the constructibility theorem
fixes its bounded domain.
5. Choose the single compactification $f=pj$ used in
[def-weil-integral-rational-qbar-compact-support], with $j:X\hookrightarrow\overline X$
quasi-compact open and $p$ proper. The compactification schemes are finite type over the base
field: p is proper, hence finite type, and finite-type morphisms compose by adjoining the two
finite sets of algebra generators. A field is Noetherian because its only ideals are zero and the
unit ideal. Thus [lem-weil-pbc-finite-type-over-noetherian] makes the compactification schemes
Noetherian, and [lem-weil-pbc-noetherian-open-subscheme-noetherian] makes all their opens and
intersections quasi-compact. This verifies the quasi-compactness of j and the constructibility of
the strata used in step 6. Work over the completed coefficient sheaf on $\overline X$ and its
restriction to $X$. Extension by zero $J=j_!$ is exact and left adjoint to restriction by
[lem-weil-pbc-proetale-ringed-open-closed]; the coefficient restrictions are canonical by
[lem-weil-pbc-profinite-coefficient-inverse-image]. The tensor identity
[lem-weil-pbc-ringed-slice-extension-tensor], using the open-slice identification
[lem-weil-proetale-weakly-etale-localization], gives $J(Q\otimes j^{-1}C)\cong JQ\otimes C$. The
same formula holds for total tensor complexes because J preserves their direct sums by
[lem-weil-pbc-left-adjoint-preserves-colimits]. For a K-flat representative $Q$ of $K$ supplied by
[lem-pc-kflat-resolution], $JQ$ is K-flat: for acyclic $C$, exact restriction makes $j^{-1}C$
acyclic by [lem-weil-pbc-proetale-immersion-limit-preservation], then $Q\otimes j^{-1}C$ is
acyclic and exact $J$ preserves that. Applying the tensor identity to each finite coefficient
quotient therefore gives $(JK)_n\cong j_!K_n$. It respects the quotient maps because on these
representatives the transition is $1\otimes(A_{E,n+1}\to A_{E,n})$ on both sides. It respects the
maps from $JK$ because both send a local section to its tensor with $1$.
6. The completeness assertion of [lem-cbc-completed-extension-zero-comparison], applied to the
identity cartesian square for this quasi-compact $j$, says that $JK$ is derived complete. Moreover
$JK$ is integral constructible: by step 5 its reductions are $j_!K_n$; exactness of $j_!$
identifies their cohomology with extension by zero of the cohomology of $K_n$. Add the closed
complement to any finite stratification witnessing finite-torsion constructibility
[def-weil-finite-torsion-constructibility]. On the old strata the sheaf is unchanged and on the
new stratum it is zero; all these strata are constructible in the Noetherian compactification. The
same uniform cohomological interval works since $j_!$ is exact. This verifies all the conditions
in [def-weil-derived-complete-integral-detailed]. Step 4 applied to $p$ and $JK$ now identifies
the reductions of $Rp_*JK$ with $Rp_{*,n}j_!K_n=Rf_{!,n}K_n$. The integral compact-support
definition is the derived limit of precisely this tower. The transition identifications in step 5
and the tower naturality in [prop-weil-pbc-direct-image-limits] identify its comparison with the
reduction of $Rp_*JK$, not just with an abstract isomorphism between these objects. This proves
$(Rf_!K)_n\cong Rf_{!,n}K_n$.
7. For $1\leq m\leq n$, the finite-level compact-support comparison is exactly
[lem-fix-compact-support-coefficient-change]: its hypotheses require the separated finite-type
morphism in the finite-field datum and a bounded constructible finite-Tor input. Its statement
includes successive reduction, pullback and the counits defining the projection map, so this
citation proves those clauses for the specified comparison. For exceptional right adjoints the
item makes a conditional assertion only: in [def-weil-exceptional-adjoint-admissibility],
admissibility at $\mathcal O_E,E,\overline{\mathbf Q}_\ell$ explicitly requires the
finite-reduction and scalar-extension maps of the right adjoints to be isomorphisms. Invoke
precisely that requirement whenever such an adjoint is used. Finite-stage admissibility alone has
no coefficient-isomorphism clause and is not being used to deduce one. The units and counits
mentioned below are those of the chosen adjunctions; no ambient right adjoint is asserted for a
morphism for which the admissibility conditions fail.
8. For finite $E\subset L$, use the completed pullback/tensor/Hom comparisons and tower laws of
[lem-pur-integral-operations-scalar-extension]. By
[lem-weil-finite-free-completed-scalar-comparison], scalar extension is ordinary tensor by
$S_W=\widehat{\mathcal O}_{L,W}$, finite free over $R_W=\widehat{\mathcal O}_{E,W}$. Step 5's
coefficient inverse-image identifications give compatible ringed squares. Apply
[lem-weil-pbc-flat-ringed-diagram-restriction] with terminal index category: finite freeness
implies flatness, and its restriction/direct-image comparison identifies the coefficient target,
including adjuncts. Apply [lemma-weil-pbc-perfect-projection-formula] with the site-perfect object
$S_Y$ to get the direct-image scalar isomorphism. Naturality for multiplication by sections makes
it $S_Y$-linear. The evaluation-defined scalar-Hom isomorphism for arbitrary variables is
[lem-sf-ringed-finite-free-hom-base-change]; its finite-free hypothesis was just verified, and its
transpose is exactly scalar extension of evaluation. For compact support combine the proper-factor
comparison with step 5's open tensor comparison. In the strict-tower triangle of
[lem-weil-pbc-ringed-strict-tower-homotopy-limit], finite-free tensor commutes with derived
products and cones: in a basis it is a finite sum of identity functors. The scalar-comparison
lemma identifies this realization with the defined integral scalar extension. For $R\to S\to T$,
the tensor and Hom maps send $x\otimes s\otimes t$ to $x\otimes st$ and $h\otimes s\otimes t$ to
$(p\otimes u\mapsto h(p)\otimes stu)$. Direct-image composites are mates of the same pullback map,
hence equal by [def-weil-pbc-adjunction-mate]; the product-cone construction gives compact-support
equality. With $S=R$ all formulas are identities.
9. Rationalization [def-weil-rationalization-karoubi] leaves objects unchanged and replaces each
integral Hom group by its tensor product with $E$. The operations
[def-weil-derived-pullback-tensor-hom] are defined there by linear extension of the integral
operations, and direct image and compact support are likewise rationalized in
[def-weil-derived-direct-image, def-weil-integral-rational-qbar-compact-support]. A commuting
integral comparison square remains commuting after this linear extension: expand a morphism as a
finite sum of $u_i\otimes a_i$, apply linearity to each summand, and use the integral square for
$u_i$. Inverses remain inverses. At the algebraic-closure stage
[def-weil-algebraically-closed-coefficients], represent the finitely many objects and maps of a
comparison diagram over one common finite extension. The integral scalar comparisons of step 8 and
the exact transition functors [lem-weil-scalar-extension-exact-triangulated] give the diagrams at
that stage. After enlarging the field their diagrams agree by the identity and tower laws of step
8. Thus they give well-defined comparison maps on the common-stage category, and any equality
follows from the equality at that common stage. This is transport in the prescribed localized and
common-stage categories, not an identification with discrete constant-field sheaf categories.
10. Write $F_X,F_Y$ for coefficient extension, $L_A\dashv R_A$, $L_B\dashv R_B$ for
pullback/direct image, and $a:L_BF_Y\xrightarrow{\sim}F_XL_A$ for step 1. Define $b:F_YR_A\to
R_BF_X$ by [def-weil-pbc-adjunction-mate]. Its transpose gives the counit equation
$$\varepsilon_B F_X\circ L_B b=F_X\varepsilon_A\circ aR_A.$$
The inverse-mate formula, naturality and the two triangle identities give
$$R_Ba\circ\eta_B F_Y=bL_A\circ F_Y\eta_A.$$
The projection comparison is this transpose [lem-weil-pbc-ringed-projection-mate-exact], with step
1's tensor constraint. The finite compact-support counit equation is included in
[lem-fix-compact-support-coefficient-change]. For Hom the equation is
$$\operatorname{ev}_B\circ(c\otimes1)=F(\operatorname{ev}_A)\circ\mu^{-1},$$
with $\mu$ the tensor comparison. Step 2's dual evaluation calculation,
[lem-coef-integral-hom-reduction], and [lem-sf-ringed-finite-free-hom-base-change] give this
equation for finite site-perfect, integral and scalar comparisons respectively. Applying the
adjunction bijection shows compatibility with tensor-Hom transposes. Thus transposing either route
in a projection or exchange square gives the same composite of evaluation, reassociation and
counit. The displayed unit equation handles units. For successive coefficient changes both
transposes have the same tensor formula, so injectivity of the adjunction bijection gives
equality. Exceptional comparisons use their mates and the explicit admissibility isomorphism
assumption of step 7; invertibility is not inferred merely by taking a mate. Step 9 carries these
equations to rational and common-stage coefficients. These are equalities of the specified maps. -/
theorem basicOperationsCoefficientReduction
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω]
    (X Y : Scheme.{u}) (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    ((∀ K : DerivedCategory (integralTowerModules l E Y),
        sfIntegralConstructible l E Y K →
          sfIntegralConstructible l E X ((integralDerivedPullback l E f).obj K) ∧
            ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
              (e : DerivedCategory.Q.obj P.obj ≅ K) (n : ℕ),
              IsIso (integralPullbackFiniteComparison l E f K P e n)) ∧
      ∀ (W : Scheme), W = X ∨ W = Y →
        ∀ M N : DerivedCategory (integralTowerModules l E W),
          sfIntegralConstructible l E W M → sfIntegralConstructible l E W N →
            sfIntegralConstructible l E W ((integralCompletedTensor l E W).obj (M, N)) ∧
              ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
                (e : DerivedCategory.Q.obj P.obj ≅ M)
                (d : DerivedCategory.Q.obj Q.obj ≅ N) (n : ℕ),
                IsIso (integralTensorFiniteComparison l E W M N P Q e d n)) ∧
    (∀ (n : ℕ)
      (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))),
      IsIso ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M N).hom) ∧
    (∀ (m n : ℕ) (h : n ≤ m)
      (M : proEtaleDerivedCategory Y (finiteCoefficientRing l E (m + 1))),
      IsIso ((pullbackTensorQuotient l E f h).hom.app M)) ∧
    (∀ (m n : ℕ) (h : n ≤ m)
      (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (m + 1))),
      canonicalFinitePullbackTensor_quotient_condition l E f
        (hX := hX) (hY := hY) h M N) ∧
    (∀ (K₀ : Type u) [Field K₀] (hl₀ : IsUnit (l : K₀))
      [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
      [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
      [QuasiCompact (X ↘ Spec (.of K₀))]
      [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
      [QuasiCompact (Y ↘ Spec (.of K₀))]
      [f.IsOver (Spec (.of K₀))]
      (K : DerivedCategory (scalarReductionSource l E X))
      (hK : sfIntegralConstructible l E X K),
      (∃ hprod : HasProduct (sfDirectImageTerm l E f K),
          @Nonempty (@SfIntegralDirectImage l _ E _ _ _ X Y f K hprod)) ∧
        ∀ [hprod : HasProduct (sfDirectImageTerm l E f K)]
          (L : SfIntegralDirectImage l E f K),
          sfIntegralConstructible l E Y L.obj ∧
            IsSfDerivedComplete l E Y L.obj ∧
              (∀ n : ℕ, IsIso (sfDirectImageReductionComparison l E f L n)) ∧
              ∀ n : ℕ,
                intrinsicFiniteTorsionConstructible l E (n + 1)
                  (Nat.succ_le_succ (Nat.zero_le n)) Y
                  (sfFiniteDerivedDirectImage l E f K n)) ∧
    (∀ (K₀ : Type u) [Field K₀] (hl₀ : IsUnit (l : K₀))
      [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
      [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
      [QuasiCompact (X ↘ Spec (.of K₀))]
      [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
      [QuasiCompact (Y ↘ Spec (.of K₀))]
      [f.IsOver (Spec (.of K₀))] [IsSeparated f]
      [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f)
      (K : DerivedCategory (scalarReductionSource l E X))
      (hK : sfIntegralConstructible l E X K)
      (M : DerivedCategory (scalarReductionSource l E Y))
      (p : M ⟶ ∏ᶜ fun n : ℕ ↦ sfCompactSupportTerm l E c K n)
      (δ : (∏ᶜ fun n : ℕ ↦ sfCompactSupportTerm l E c K n) ⟶ M⟦(1 : ℤ)⟧)
      (hδ : IsDerivedLimitTriangle (sfCompactSupportTransition l E c K) M p δ),
      sfIntegralConstructible l E Y M ∧
        (∀ n : ℕ, IsIso (coefIntegralCompactSupportComparison l E c K M p n)) ∧
        ∀ n : ℕ,
          coefIntegralCompactSupportComparison l E c K M p (n + 1) ≫
              coefCompactSupportFiniteTransition l E c K n =
            sfCompactSupportReductionTransition l E Y M n ≫
              (sfCompactSupportFiniteRestriction l E Y n).mapDerivedCategory.map
                (coefIntegralCompactSupportComparison l E c K M p n)) ∧
    (∀ (K₀ : Type u) [Field K₀] (hl₀ : IsUnit (l : K₀))
      (n : ℕ) (hn : 1 ≤ n) {X' Y' : Scheme.{u}}
      [X'.Over (Spec (.of K₀))] [Y'.Over (Spec (.of K₀))]
      [LocallyOfFiniteType (X' ↘ Spec (.of K₀))]
      [QuasiCompact (X' ↘ Spec (.of K₀))]
      [LocallyOfFiniteType (Y' ↘ Spec (.of K₀))]
      [QuasiCompact (Y' ↘ Spec (.of K₀))]
      (g : X' ⟶ Y') [g.IsOver (Spec (.of K₀))]
      [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
      (c : Compactification g) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
      (K : proEtaleDerivedCategory X' (Padic.coefficientExtensionRing l E n))
      (hK : finiteTorConstructible l E n hn X' K)
      (hKm : finiteTorConstructible l E m hm X'
        ((finiteLevelDerivedReduction l E m n hmn X').obj K)),
      IsIso (finiteLevelCompactSupportReductionComparison l E m n hm hmn c K)) ∧
    (∀ (W : Scheme.{u}) (m n : ℕ) (h : m ≤ n),
      CoefficientEvaluationCompatible (finiteIntrinsicClosed l E W n)
        (finiteIntrinsicClosed l E W m) (coefficientFiniteQuotientDerived l E W h)
        ((coefficientDerivedSystemEvaluationCalculus l E W).choose.quotientCalculus.tensor h) ∧
      FiniteHomEvaluation (finiteIntrinsicClosed l E W n) (finiteIntrinsicClosed l E W m)
        (coefficientFiniteQuotientDerived l E W h)
        ((coefficientDerivedSystemEvaluationCalculus l E W).choose.quotientCalculus.tensor h)) ∧
    (∀ (W : Scheme.{u}) (m n : ℕ) (h : m ≤ n)
      (P Q : normalizedDVRDerived l E W n),
      IsProEtaleSitePerfect W (integralCoefficientCommRingSheaf l E W n) P →
      IsIso (finiteIntrinsicReductionHom l E W h P Q)) ∧
    (∀ (D : FiniteFieldDatum.{d}) (_hl : l ≠ D.p) (W : Scheme.{t}),
      ∃ a : IntegralHom.TensorPresentation.{t, u} W
          (completedIntegralCommRingSheaf l E W D _hl),
        (∀ K L : completedIntegralDerivedCategory l E W D _hl,
          IsDerivedComplete l E W D _hl L →
            IsDerivedComplete l E W D _hl
              ((IntegralHom.hom.{t, u} W
                (completedIntegralCommRingSheaf l E W D _hl)).obj (op K, L))) ∧
          ∀ n : ℕ, ∃ m : IntegralHom.ReductionPresentation l E W D _hl a n,
            ∀ K L : completedIntegralDerivedCategory l E W D _hl,
              IsIso (IntegralHom.comparison l E W D _hl m K L) ∧
          (m.target.tensor.map (Prod.mkHom
              (𝟙 ((integralDerivedReduction l E W D _hl n).obj K))
              (IntegralHom.comparison l E W D _hl m K L)) ≫
            (m.target.adjunction ((integralDerivedReduction l E W D _hl n).obj K)).counit.app
              ((integralDerivedReduction l E W D _hl n).obj L) =
            m.mu.inv.app (K,
              (IntegralHom.hom.{t, u} W
                (completedIntegralCommRingSheaf l E W D _hl)).obj (op K, L)) ≫
            (integralDerivedReduction l E W D _hl n).map ((a.adjunction K).counit.app L)) ∧
          ∀ (T : completedIntegralDerivedCategory l E W D _hl)
            (f : T ⟶
              (IntegralHom.hom.{t, u} W
                (completedIntegralCommRingSheaf l E W D _hl)).obj (op K, L)),
            (m.target.adjunction ((integralDerivedReduction l E W D _hl n).obj K)).homEquiv
                ((integralDerivedReduction l E W D _hl n).obj T)
                ((integralDerivedReduction l E W D _hl n).obj L)
                (m.mu.inv.app (K, T) ≫ (integralDerivedReduction l E W D _hl n).map
                  (((a.adjunction K).homEquiv T L).symm f)) =
              (integralDerivedReduction l E W D _hl n).map f ≫
                IntegralHom.comparison l E W D _hl m K L) ∧
    (IntegralScalarOperations.Comparisons l Ω X Y f) ∧
    (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L) (W : Scheme.{u}),
      CoefficientEvaluationCompatible (scalarIntegralClosed l E W) (scalarIntegralClosed l L W)
        (integralOrdinaryDerivedScalar l E L ι W) (scalarClosedTensor l E L ι W) ∧
      FiniteHomEvaluation (scalarIntegralClosed l E W) (scalarIntegralClosed l L W)
        (integralOrdinaryDerivedScalar l E L ι W) (scalarClosedTensor l E L ι W)) ∧
    (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
      (K : sfRationalConstructibleCategory l E Y),
      HEq ((rationalPullbackScalarComparison l E L ι f).hom.app K)
        ((sfRationalConstructibleLocalization l L X).map
          (integralPullbackScalarComparison l E L ι f K.obj).hom)) ∧
    (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
      (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
      (M N : sfRationalConstructibleCategory l E W),
      HEq ((rationalTensorScalarComparison l E L ι W).hom.app (M, N))
        ((sfRationalConstructibleLocalization l L W).map
          (integralTensorScalarComparison l E L ι W M.obj N.obj).hom)) ∧
    (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
      (W : Scheme.{u}) (P : (constructibleRationalHomPairs l E W).FullSubcategory),
      HEq (rationalHomScalarComparison l E L ι W P).hom
        ((sfRationalConstructibleLocalization l L W).map
          (integralHomScalarComparison l E L ι W
            (integralPairOfRationalHomPair l E W P)).hom)) ∧
    commonStagePullbackRepresentativeLaws l Ω f ∧
    (∀ W : Scheme.{u}, ∀ [∀ w : W, Invertible (l : W.residueField w)],
      commonStageTensorRepresentativeLaws l Ω W) ∧
    (∀ W : Scheme.{u}, commonStageInternalHomRepresentativeLaws l Ω W) ∧
    coefficientOperationMateEquations ∧
    (canonicalIntegralPullbackTensor_associative l E f) ∧
    (canonicalIntegralPullbackTensor_unit l E f) ∧
    (canonicalRationalPullbackTensor_associative l E f) ∧
    (canonicalRationalPullbackTensor_unit l E f) ∧
    (canonicalCommonStagePullbackTensor_associative l Ω f) ∧
    (canonicalCommonStagePullbackTensor_unit l Ω f) ∧
    (∀ M N : sfRationalConstructibleCategory l E Y,
      HEq ((canonicalRationalPullbackTensor l E f) M N).hom
        ((sfRationalConstructibleLocalization l E X).map
          ((canonicalIntegralPullbackTensor l E f) M.obj N.obj).hom)) ∧
    (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
      (M N : sfIntegralConstructibleCategory l E Y),
      canonicalIntegralPullbackTensor_scalar_condition l E L ι f M N) ∧
    (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
      (M N : sfRationalConstructibleCategory l E Y),
      canonicalRationalPullbackTensor_scalar_condition l E L ι f M N) ∧
    (∀ (K₀ : Type u) [Field K₀] (hl₀ : IsUnit (l : K₀))
      [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
      [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
      [QuasiCompact (X ↘ Spec (.of K₀))]
      [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
      [QuasiCompact (Y ↘ Spec (.of K₀))]
      [f.IsOver (Spec (.of K₀))] [IsSeparated f]
      [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f),
      ∃ S : SfCompactSupportCoefficientAction l K₀ hl₀ Ω c,
        operationIntegralCoefficientCoherent l Ω X Y
          (fun E₀ ↦ sfCompactSupportFiniteIntegralFunctor l K₀ hl₀ c
            (Coefficient.{u} l Ω E₀)) (fun h ↦ S.integralBeta h)) ∧
    (∀ (K₀ : Type u) [Field K₀] (hl₀ : IsUnit (l : K₀))
      [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
      [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
      [QuasiCompact (X ↘ Spec (.of K₀))]
      [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
      [QuasiCompact (Y ↘ Spec (.of K₀))]
      [f.IsOver (Spec (.of K₀))],
      OperationDirectImageCoefficientAction l Ω X Y f) ∧
    (directImageScalarExtensionLaws l) ∧
    (compactSupportScalarIsomorphisms l) ∧
    (compactSupportScalarExtensionLaws) ∧
    directImageScalarTowerLaws ∧
    coefficientOperationIdentityLaws ∧
    (∀ (n : ℕ),
      canonicalFinitePullbackTensor_associativity_condition l E f n ∧
      canonicalFinitePullbackTensor_unit_condition l E f n ∧
      canonicalFinitePullbackTensor_braiding_condition l E f n) ∧
    (∀ (S : Scheme.{u}) (_hS : ∀ s : S, IsUnit (l : S.presheaf.stalk s))
      [X.Over S] [Y.Over S]
      [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
      [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
      [f.IsOver S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f),
      IsExceptionalAdjointAdmissibleAtIntegral l E S X Y _hS f c →
      ∃ DE : ExceptionalFiniteFieldFamily l E f c,
        HasUniformFiniteExceptionalAdjoints l (fun _ : PUnit.{1} ↦ E) f c DE ∧
          ExceptionalFiniteReductionsCompatible l E f c DE ∧
          ∀ (L : Type u) [Field L] [Algebra (Padic l) L]
            [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L),
            ∃ DL : ExceptionalFiniteFieldFamily l L f c,
              HasUniformFiniteExceptionalAdjoints l (fun _ : PUnit.{1} ↦ L) f c DL ∧
                ExceptionalFiniteReductionsCompatible l L f c DL ∧
                ExceptionalFiniteScalarsCompatible l E L ι f c DE DL) := by
  classical
  have A := basicOperationReductionAndEvaluation l E X Y f
  have B := basicOperationCoefficientCoherence l E Ω X Y f
  have hXu : ∀ x : X, IsUnit (l : X.presheaf.stalk x) := fun x ↦
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by
      rw [map_natCast]; exact (isUnit_of_invertible (l : X.residueField x)).ne_zero)
  have hYu : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y) := fun y ↦
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by
      rw [map_natCast]; exact (isUnit_of_invertible (l : Y.residueField y)).ne_zero)
  refine And.intro ?_ ?_
  · exact integralOperations_preserve_constructible l E f
  refine And.intro ?_ ?_
  · intro n M N
    infer_instance
  refine And.intro ?_ ?_
  · intro m n h M
    infer_instance
  refine And.intro ?_ ?_
  · intro m n h M N
    exact (derivedPullbackTensorIso l E f 0 Ω).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h M N
  refine And.intro ?_ ?_
  · intro K₀ _ hl₀ _ _ _ _ _ _ _ K hK
    exact ⟨(sfIntegralDirectImage_constructible K₀ l hl₀ E f K hK).1,
      (sfIntegralDirectImage_constructible K₀ l hl₀ E f K hK).2.1⟩
  refine And.intro ?_ ?_
  · exact A.1
  refine And.intro ?_ ?_
  · intro K₀ _ hl₀ n hn X' Y' _ _ _ _ _ _ g _ _ _ _ c m hm hmn K hK hKm
    exact ((Scheme.finiteCompactSupportConstructibility l E K₀ hl₀ n hn g).2.2
      m hm hmn c K hK.1 hKm.1).1
  refine And.intro ?_ ?_
  · exact A.2.1
  refine And.intro ?_ ?_
  · exact A.2.2.1
  refine And.intro ?_ ?_
  · intro D hl W
    exact integralHomReduction l E W D hl
  refine And.intro ?_ ?_
  · exact integralOperationsScalarExtension l Ω X Y f hXu hYu
  refine And.intro ?_ ?_
  · exact A.2.2.2
  refine And.intro ?_ ?_
  · intro L _ _ _ ι K
    exact (rationalPullbackScalarComparison_existsUnique l E L ι f).exists.choose_spec K
  refine And.intro ?_ ?_
  · intro L _ _ _ ι W _ M N
    exact (rationalTensorScalarComparison_existsUnique l E L ι W).exists.choose_spec M N
  refine And.intro ?_ ?_
  · intro L _ _ _ ι W P
    exact (rationalHomScalarComparison_existsUnique l E L ι W P).exists.choose_spec
  refine And.intro ?_ ?_
  · exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec
  refine And.intro ?_ ?_
  · intro W _
    exact (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec
  refine And.intro ?_ ?_
  · intro W
    exact (commonStageDerivedInternalHom_existsUnique l Ω W).exists.choose_spec
  refine And.intro ?_ ?_
  · exact B.1
  refine And.intro ?_ ?_
  · exact (derivedPullbackTensorIso l E f 0 Ω).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine And.intro ?_ ?_
  · exact (derivedPullbackTensorIso l E f 0 Ω).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine And.intro ?_ ?_
  · exact (derivedPullbackTensorIso l E f 0 Ω).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine And.intro ?_ ?_
  · exact (derivedPullbackTensorIso l E f 0 Ω).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine And.intro ?_ ?_
  · exact (derivedPullbackTensorIso l E f 0 Ω).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine And.intro ?_ ?_
  · exact (derivedPullbackTensorIso l E f 0 Ω).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine And.intro ?_ ?_
  · exact (derivedPullbackTensorIso l E f 0 Ω).2.2.2.2.2.2.2.2.1
  refine And.intro ?_ ?_
  · exact (derivedPullbackTensorIso l E f 0 Ω).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine And.intro ?_ ?_
  · exact (derivedPullbackTensorIso l E f 0 Ω).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine And.intro ?_ ?_
  · exact B.2.1
  refine And.intro ?_ ?_
  · exact B.2.2.1
  refine And.intro ?_ ?_
  · exact B.2.2.2.1
  refine And.intro ?_ ?_
  · exact B.2.2.2.2.1
  refine And.intro ?_ ?_
  · exact B.2.2.2.2.2.1
  refine And.intro ?_ ?_
  · exact B.2.2.2.2.2.2.1
  refine And.intro ?_ ?_
  · exact B.2.2.2.2.2.2.2
  refine And.intro ?_ ?_
  · intro n
    rcases derivedPullbackTensorIso l E f n Ω with ⟨_, ha, hu, _, hb, _⟩
    exact ⟨ha, hu, hb⟩
  intro S hS _ _ _ _ _ _ _ _ _ _ c h
  exact h

end WeilConjectures
