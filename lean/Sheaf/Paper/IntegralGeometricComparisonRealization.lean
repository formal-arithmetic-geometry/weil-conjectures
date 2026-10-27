/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND, SHEAF group F6
-/
module

public import Sheaf.Paper.IntegralGeometricComparisonData
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.Paper.CoefficientTowerSectionCoordinates
import Sheaf.Paper.GeometricSmoothReconstructionSetup
import Sheaf.Paper.IntegralGeometricReindexingRealization
import Sheaf.Paper.IntegralGeometricPurityRealization
import Sheaf.Paper.IntegralGeometricSupportRealization
import Sheaf.Paper.IntegralGeometricTransposeIdentity
import Sheaf.Paper.SmoothPurityTowerShriekLevels

/-! # Integral realization of the geometric comparison diagram -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.IntegralGeometricComparison

private theorem preservesKInjectives_of_reindexing
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T' T : Scheme.{u}} (g : T' ⟶ T) [IsIso g]
    (h : PurCompletedReindexingAt (pbcIntegralDatum l E) g) :
    PreservesKInjectives l E g := by
  obtain ⟨e, he, _⟩ := h.2.1
  obtain ⟨et, het, _⟩ := h.2.2.2.2.1
  constructor
  · intro I hI
    have : I.IsKInjective := hI
    have : (proEtaleRingModulePullback g ((pbcIntegralDatum l E).completedRing T)
        ((pbcIntegralDatum l E).completedRing T')
        ((pbcIntegralDatum l E).integralRingIso g)).IsEquivalence := by
      rw [← he]
      infer_instance
    infer_instance
  · intro I hI
    have : I.IsKInjective := hI
    have : ((pbcIntegralDatum l E).towerModulePull g).IsEquivalence := by
      rw [← het]
      infer_instance
    infer_instance

section Assembly
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  {X' X Y' Y : Scheme.{u}} {gx : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {gy : Y' ⟶ Y} {sq : IsPullback gx f' f gy}
  {c : Compactification f}
  [∀ z : X, Invertible (l : X.residueField z)]
  [∀ z : Y, Invertible (l : Y.residueField z)]
  [∀ z : X', Invertible (l : X'.residueField z)]
  [∀ z : Y', Invertible (l : Y'.residueField z)]
  (a : SpTowerMate.Data l E b o q sq c)
  (s : SpExceptionalBaseChange.IntegralData l E b o q a)


private def reconstructedIso
    (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (SpTowerMate.beta l E b o q a x))
    [IsIso (SpTowerMate.mate l E b o q a x hb)] :
    s.right ⋙ constructibleIntegralPullback l E gx ≅
      constructibleIntegralPullback l E gy ⋙ s.right' := by
  let r := SpExceptionalBaseChange.red l E b q s.rX'
  let src : (s.right ⋙ constructibleIntegralPullback l E gx) ⋙ r ≅
      SpExceptionalBaseChange.red l E b q s.rY ⋙
        (a.right ⋙ SpTowerMate.U l E b o q a) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ s.pullComparison ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight s.exceptionalComparison _ ≪≫ Functor.associator _ _ _
  let tgt : (constructibleIntegralPullback l E gy ⋙ s.right') ⋙ r ≅
      SpExceptionalBaseChange.red l E b q s.rY ⋙
        (SpTowerMate.V l E b o q a ⋙ a.right') :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ s.exceptionalComparison' ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight s.pullComparison' _ ≪≫ Functor.associator _ _ _
  exact (s.rX'.fullyFaithful.whiskeringRight _).preimageIso
    (src ≪≫ Functor.isoWhiskerLeft _ (asIso (SpTowerMate.mate l E b o q a x hb)) ≪≫ tgt.symm)

private theorem reconstructedIso_hom
    (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (SpTowerMate.beta l E b o q a x))
    [IsIso (SpTowerMate.mate l E b o q a x hb)]
    (K : sfIntegralConstructibleCategory l E Y) :
    (reconstructedIso l E b o q a s x hb).hom.app K =
      SpExceptionalBaseChange.reconstructed l E b o q a s x hb K := by
  simp [reconstructedIso, SpExceptionalBaseChange.reconstructed,
    SpExceptionalBaseChange.source, SpExceptionalBaseChange.target]

private theorem reconstructed_limit
    (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (SpTowerMate.beta l E b o q a x))
    (K : sfIntegralConstructibleCategory l E Y) :
    SpExceptionalBaseChange.IsLimitRealization l E b o q a s x hb K := by
  let h := SpExceptionalBaseChange.reconstructed l E b o q a s x hb K
  have hm : (SpExceptionalBaseChange.red l E b q s.rX').map h =
      (SpExceptionalBaseChange.source l E b o q a s K).hom ≫
        (SpTowerMate.mate l E b o q a x hb).app
          ((SpExceptionalBaseChange.red l E b q s.rY).obj K) ≫
        (SpExceptionalBaseChange.target l E b o q a s K).inv := by
    dsimp only [h]
    unfold SpExceptionalBaseChange.reconstructed
    exact s.rX'.fullyFaithful.map_preimage _
  unfold SpExceptionalBaseChange.IsLimitRealization
  apply heq_of_eq
  rw [Adjunction.homEquiv_unit]
  have hn := s.rX'.normalization.adjunction.unit.naturality h.hom
  change h.hom ≫ _ = _ at hn
  change h.hom ≫ _ = _
  rw [← hm]
  exact hn

private def imageIso
    [QuasiCompact (c.i ≫ c.g)] [HasCompactification (c.i ≫ c.g)] :
    SpIntegralAdjunction.support l E c s.support_closed ⋙
      (sfIntegralConstructible l E Y).ι ≅
    SpExceptionalBaseChange.red l E b q s.rX ⋙
      SpTowerGluing.support l E b o q c a.support_closed ⋙
        SpTowerCalculus.inclusion l E b q Y ⋙ SpExceptionalBaseChange.lim l E b q s.rY := by
  have hl (K : sfIntegralConstructibleCategory l E X) :
      (s.supportComparison.hom.app K).hom =
        (spCompletedReduction l E Y (q.abelian Y) s.rY.reduction).map
            (s.supportModel.imageComparison K).hom ≫
          s.rY.normalization.adjunction.counit.app _ := by
    have hs : s.supportComparison = s.supportModel.leftComparison :=
      eq_of_heq s.support_normalized
    rw [hs]
    exact s.supportModel.left_normalization K
  have hc (K : sfIntegralConstructibleCategory l E X) :
      s.rY.normalization.adjunction.homEquiv _ _ (s.supportComparison.hom.app K).hom =
        (s.supportModel.imageComparison K).hom := by
    apply (s.rY.normalization.adjunction.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact hl K
  refine NatIso.ofComponents (fun K ↦ s.supportModel.imageComparison K) ?_
  intro K L f
  rw [← hc K, ← hc L]
  apply s.rY.normalization.adjunction.homEquiv_naturality_left_square
  exact congrArg (fun z ↦ z.hom) (s.supportComparison.hom.naturality f)

end Assembly

/-- Realization identifies the integral geometric comparison diagram, including
its specified natural transformations and the exceptional counit transpose.
Source: latest blueprint integral-adjunction-bijection, Normalization, Bijections,
Purity, and geometric-equivariance proof Step 5
(blueprint: lem-pur-integral-geometric-comparison-realization).

Proof, following the node's nine steps:
1. Use the actual geometric automorphisms $g_T$ and the first Cartesian square, not the
scheme-Frobenius square. In applying the tower results requiring $k$-linear arrows, give the
source copies the structures $a'_T=\operatorname{Spec}(\gamma)a_T$. Then $a'_Yf=a'_X$ and
$a_Tg_T=a'_T$, so both horizontal arrows are $k$-linear between these copies. They are
isomorphisms, hence the twisted copies remain separated finite-type $k$-schemes, with the same
underlying smooth $f$ of dimension $d$. Choose one compactification and its base change for this
square. The tower direct image and its exchange are the proper/open composites in the cited
statements; retagging changes none of the underlying sites or coefficient quotient maps. The
schemes are Noetherian: a field is Noetherian since its only ideals are zero and the unit ideal,
and finite type over a Noetherian scheme preserves this property. Bounded constructible finite
reductions have bounded-below etale-origin witnesses by the constructible-origin equivalence.
These provide the witnesses required by the system operation and shift comparisons. Uses:
def-pur-scheme-geometric-frobenius, def-pur-tate-datum, det-sp-tower-shriek-levels,
det-sp-tower-exceptional-bc, lem-weil-pbc-finite-type-over-noetherian,
lem-sf-proetale-constructible-origin.

2. First compare the two indexing conventions. By the DVR statement, $\ell=u\varpi_E^e$ for a
unit $u$ and $e\geq1$, so $(\ell^m)=(\varpi_E^{em})$. Here $e>0$ since $\ell$ has absolute value
strictly between zero and one. Thus every ell-power quotient, transition, pullback and tensor
map used here is the selected level $em$ of its uniformizer-power construction. The completed
ring sheaves agree by their compatible projections. Apply the cofinal Roos restriction with
$\phi(m)=em$ after restricting to completed modules; its product maps $a_\phi,b_\phi$ give a
natural quasi-isomorphism, commute with strict tower maps, and preserve the quotient
augmentation with zero shifted-product component. Exact countable products on the pro-etale
module categories and the normalized Roos/total-limit comparison check its hypotheses.
Consequently all subsequent uniformizer-tower comparisons can be restricted to ell-power towers,
with the same reconstruction units and realized maps. Uses:
lem-weil-l-adic-extension-integers-dvr, lem-fix-cofinal-roos-restriction,
lem-weil-proetale-countable-products-exact, lem-sf-strict-roos-derived-limit-comparison.

3. Write $U_T$ for ordinary inverse-image reindexing along $g_T$ on completed modules and
$U_T^{\rm Tow}$ for its termwise action. The isomorphism-reindexing result gives exact
equivalences on these categories and the coefficient isomorphism respecting every projection;
the varying-coefficient systems also have componentwise exactness. Reindexing along $g_T^{-1}$
is an exact inverse, on either fixed-ring or varying-ring towers. These equivalences preserve
K-injectivity directly: if $I$ is K-injective and $A$ is acyclic, transpose a chain map $A\to
U_TI$ to $U_T^{-1}A\to I$ using the equivalence. Exactness makes $U_T^{-1}A$ acyclic, so this
map is null-homotopic. Transposing that homotopy makes the original map null-homotopic. The same
argument applies to $U_T^{\rm Tow}$ and to varying systems. This proves the K-injective clause
from its definition; it does not assert that evaluation or scalar restriction preserves
K-injectives. Uses: lem-pur-isomorphism-completed-reduction-reindexing,
lem-coef-semilinear-derived-sections, def-pur-kinjective-complex.

4. For a normalized constructible tower $C$, restrict its scalars to $R_T$ before taking total
limit, and choose a K-injective resolution of that fixed-ring tower. By step 3 its reindexing is
still K-injective. The inverse-image/ordinary-limit isomorphism applied termwise to that
resolution therefore gives $U_TL_TC\simeq L_TU_T^{\rm Tow}C$, with the projection normalization
of the cited reindexing theorem. This is a natural isomorphism of derived functors, rather than
a choice of a map in a Roos triangle. Ordinary and completed pullbacks agree on derived-complete
constructible objects by the automorphism-stage equivalence. Its reduction comparisons commute
with quotient transitions, completion units and projections. The normalized equivalence
reconstructs $L_TC$ and $K$ from their coherent reductions. Substituting these identifications
gives precisely $PL_Y\simeq L_YP_\bullet$ and $QL_X\simeq L_XQ_\bullet$, and the compatibility
with $K\to L_Tr_TK$. Step 2 transfers the projection-normalized construction to ell-power
indices. This proves also the asserted description using ordinary inverse limit on resolutions.
The same finite Tor interval is preserved: tensor a pulled-back object with an arbitrary module,
apply inverse reindexing, and use the original Tor test; exactness returns the same vanishing
interval. Uses: lem-pur-isomorphism-completed-reduction-reindexing,
lem-weil-pbc-ringed-strict-tower-homotopy-limit,
lem-sf-automorphism-constructible-stage-equivalence, det-sp-normalized-equivalence.

5. By the integral-direct-image theorem its canonical comparison is $F\simeq L_YF_\bullet r_X$,
including the coherent reduction identification, and the output tower is normalized
constructible. The integral-adjunction theorem gives $G^H=L_XG_\bullet r_Y$, its coherent
reductions, and the adjunction $F\dashv G^H$; its Hom bijection is exactly reduction full
faithfulness, the tower Hom bijection, and reconstruction. In particular its unit and counit are
the realizations of the tower unit and counit. The integral exceptional-adjoint theorem supplies
the independently specified integral right adjoint for this same $F$. Apply uniqueness of right
adjoints to obtain the unique counit-preserving identification $G^H\simeq G$. We use that
identification throughout. This does not identify adjoints merely by their evaluated objects.
Uses: det-sp-integral-direct-image-tower, det-sp-integral-adjunction-bijection,
prop-coef-integral-exceptional-adjoint, det-sp-unique-right-adjoint.

6. The completed-operation substitution theorem identifies completed pullback and tensor
expressions on reconstructed normalized systems with the limits of those whole expressions,
including canonical composition and tensor associators. The shift-compatibility theorem
identifies their signed shift comparisons under realization. Apply these to $f^*(-)(d)[2d]$ to
obtain $H\simeq L_XH_\bullet r_Y$. The integral purity in the statement is, by the
integral-adjunction theorem, exactly $L_X\Gamma_\bullet r_Y$ under this source comparison and
the target comparison of step 5. Hence its identification is an equality of the specified
natural transformations. The tower purity theorem supplies normalization of the output and the
isomorphism before realization. Uses: lem-pur-completed-operation-tower-substitution,
lem-pur-integral-basic-operation-shift, det-sp-integral-adjunction-bijection,
det-sp-tower-gamma.

7. For $b$, use the same substitution comparisons for the two pullbacks, the tensor with the
Tate line, and the shift. The Tate comparison is specified by the inverse limit of the
roots-of-unity maps, followed by tensor powers (here $d\geq0$); those maps respect the Kummer
and coefficient quotient transitions. Thus its restriction to the actual reduction tower is
exactly the Tate factor in $b_\bullet$. The integral datum definition specifies the remaining
pullback-composition, tensor and shift factors on those same strict reductions. Applying the
functor $L_X$ to that ordered composite, using the substitution and shift comparisons, gives the
prescribed $b$, with its specified Tate normalization. Step 2 retains that normalization at the
ell-power levels. Uses: def-weil-frobenius-coefficient-twists, def-pur-tate-datum,
lem-pur-completed-operation-tower-substitution, lem-pur-integral-basic-operation-shift.

8. It remains to identify the compact-support exchange as a map. Use the same compactification
and its base change from step 1. In the varying-system derived category the specified proper and
open exchanges are the actual adjunction-mate words of the semilinear-sections theorem.
Reindexing the diagram sites along the scheme isomorphisms identifies the proper factor with the
direct-image reindexing mate and the open factor with its unit-normalized reindexing comparison.
Scalar restriction preserves these specified mates: the scalar-derived comparison identifies the
direct-image mate and the open inverse mate before evaluation. The strict integral normalization
theorem gives $v_\bullet=r_\bullet$ for the proper completed factor before $R\lim$, and gives
the same unit-normalized open factor. The semilinear exchange-reindexing theorem identifies
their ordered composite with the specified compact-support exchange, including integral
reduction and its strict-tower construction. Therefore the whole-tower $B_\bullet$ and the
strict lift used to define $\operatorname{Ex}^{\rm comp}_!$ are these same proper/open
reindexing factors. Applying total limit and the comparisons of steps 4 and 5 gives
$B=\operatorname{Ex}^{\rm comp}_!=L_YB_\bullet r_X$, with the indicated conjugations. No
faithfulness of derived evaluation or restriction on maps is used. Uses:
lem-coef-semilinear-derived-sections, lem-sf-semilinear-scalar-derived-comparison,
lem-pur-isomorphism-completed-reduction-reindexing,
lem-pur-isomorphism-strict-integral-exchange-normalization,
lem-pur-weil-semilinear-exchange-reindexing.

9. Let $\widetilde e_K:QGK\to GPK$ denote the realized $e_\bullet(r_YK)$, using steps 4 and 5.
The defining tower transpose satisfies $$\varepsilon_{\bullet,P_\bullet r_YK}\circ
F_\bullet(e_{\bullet,r_YK})=P_\bullet(\varepsilon_{\bullet,r_YK})\circ B_{\bullet,G_\bullet
r_YK}^{-1}.$$ Apply the functorial realization and the coherent reconstruction isomorphisms.
Steps 4, 5 and 8 identify the two sides with $$\varepsilon_{PK}\circ F(\widetilde
e_K)=P(\varepsilon_K)\circ B_{GK}^{-1}.$$ Indeed functors preserve compositions and inverses,
and every inserted reconstruction isomorphism cancels with its inverse by naturality. The
adjunct-counit identity now says exactly that $\widetilde e_K$ is the integral adjoint transpose
of the displayed right side. The construction and the Hom bijection are natural in $K$, so this
identifies the natural transformations. Together with steps 4--8, it identifies every specified
arrow in the integral comparison diagrams. Uses: det-sp-tower-exceptional-bc,
det-sp-integral-adjunction-bijection, lem-weil-pbc-adjunct-counit-identity.
-/
theorem integral_geometric_comparison_realization (P : PurityFiniteSetting.{u})
    (X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
    [QuasiCompact f₀.left] (d : ℕ)
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)] :
    Result P X₀ Y₀ f₀ d := by
  classical
  let l₀ := P.coefficients.l
  let E₀ := P.extension
  let geom := P.schemeGeometricFrobenius_squares X₀ Y₀ f₀ d
  let : IsIso (P.frobeniusGaloisMap X₀) := geom.1
  let : IsIso (P.frobeniusGaloisMap Y₀) := geom.2.1
  let : ∀ z : (P.frobeniusFiber X₀).left,
      Invertible (l₀ : (P.frobeniusFiber X₀).left.residueField z) :=
    sfWeilPrimeInvertible P.field l₀ P.coefficients.different X₀
  let : ∀ z : (P.frobeniusFiber Y₀).left,
      Invertible (l₀ : (P.frobeniusFiber Y₀).left.residueField z) :=
    sfWeilPrimeInvertible P.field l₀ P.coefficients.different Y₀
  obtain ⟨b, o, x, laws⟩ := SpTowerShriek.tower_shriek_levels l₀ E₀
  obtain ⟨q⟩ := SpTowerCalculus.coordinates_realization l₀ E₀ b
  obtain ⟨c, a, hb, s, hm, he⟩ :=
    geometric_smooth_reconstruction_setup P X₀ Y₀ f₀ d b o q x laws
  let : QuasiCompact (P.frobeniusMap f₀) := s.quasiCompact
  let : QuasiCompact (c.i ≫ c.g) := c.comm ▸ s.quasiCompact
  let : HasCompactification (c.i ≫ c.g) :=
    (SpTowerGamma.factorization c.i c.g).hasCompactification
  let c' := c.ofIsPullback geom.2.2.1
  let : QuasiCompact (c'.i ≫ c'.g) := c'.comm ▸ s.quasiCompact'
  let : HasCompactification (c'.i ≫ c'.g) :=
    (SpTowerGamma.factorization c'.i c'.g).hasCompactification
  obtain ⟨m⟩ := hm
  obtain ⟨r⟩ := integral_geometric_reindexing_realization l₀ E₀ b o q a s
  obtain ⟨p⟩ := integral_geometric_purity_realization l₀ E₀ b o q a s d m
  obtain ⟨t, beta, ⟨ex⟩, hbeta⟩ :=
    integral_geometric_support_realization l₀ E₀ b o q a s x hb
  let : IsIso (SpTowerMate.mate l₀ E₀ b o q a x hb) := he
  refine ⟨b, o, q, x, c, a, hb, s, ⟨{
    coefficients := t
    pullX := r.pullX
    pullY := r.pullY
    reindexX := r.reindexX
    reindexY := r.reindexY
    injectiveX := preservesKInjectives_of_reindexing l₀ E₀ _ r.reindexX
    injectiveY := preservesKInjectives_of_reindexing l₀ E₀ _ r.reindexY
    varyingInjectiveX := r.varyingInjectiveX
    varyingInjectiveY := r.varyingInjectiveY
    tate := p.tate
    smooth := m.smooth
    smooth' := m.smooth'
    reconstruction := m.reconstruction
    reconstruction' := m.reconstruction'
    gamma := p.gamma
    gamma_realization := p.gamma_realization
    gamma' := p.gamma'
    gamma'_realization := p.gamma'_realization
    image := imageIso l₀ E₀ b o q a s
    image_normalization := fun _ ↦ rfl
    independent := fun G adj ↦ s.adjunction.rightAdjointUniq_hom_counit adj
    beta := beta
    exchange := ex
    exchange_reduction := hbeta
    exceptional := reconstructedIso l₀ E₀ b o q a s x hb
    exceptional_reconstruction := reconstructedIso_hom l₀ E₀ b o q a s x hb
    exceptional_limit := reconstructed_limit l₀ E₀ b o q a s x hb
    exceptional_transpose := ?_
    unit := m.unit
    unit' := m.unit' }⟩⟩
  intro K
  rw [reconstructedIso_hom]
  exact integral_geometric_transpose_identity l₀ E₀ b o q a s x hb beta hbeta K

end AlgebraicGeometry.ProEtale.IntegralGeometricComparison
