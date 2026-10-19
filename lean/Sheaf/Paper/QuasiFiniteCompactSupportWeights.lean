/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.WeilMixedUpperBounds
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
public import Sheaf.Paper.WeilCompactSupportCohomology
public import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.LocalFrobeniusTrace
import Sheaf.Paper.SfWeilSheafComplex
import Sheaf.Paper.ConstructiblePullbackTExact
import Sheaf.Paper.DlConstructibleFibresExact
import Sheaf.Paper.WeilPullbackLocalFrobenius
import Sheaf.AlgebraicGeometry.ClosedPointField
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.ZlFiniteAdicDirectImage
import Sheaf.Paper.ZlImmersionWeilLocalBehavior
import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
import Sheaf.Paper.FiniteExtensionCompactSupportBaseChange
import Sheaf.Paper.QbarCompactSupportBaseChange
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.Paper.A1FiniteWeilSectionsDecomposition
import Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison

/-! # Quasi-finite compact-support images and upper weights

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-l-dl-general-quasifinite, statement and finite-fibre argument
(blueprint: sk-l-dl-general-quasifinite).

The three clauses use the existing common-stage constructible Weil heart and its
compact-support higher images. The coefficient embedding need not be surjective.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- A separated quasi-finite morphism has no positive compact-support higher images;
its degree-zero image preserves mixed and punctual upper weight bounds.
Source: blueprint main-20261015, sk-l-dl-general-quasifinite, unit statement and
finite-fibre argument (blueprint: sk-l-dl-general-quasifinite).

Proof (the reviewed DAG route, including the repair of absolute separatedness):

1. The target Y_0 is quasi-compact because it is of finite type over a field, and is quasi-
   separated by hypothesis. Apply [thm-pqf-zmt-factorization] to obtain
   X_0\xrightarrow{j_0}T_0\xrightarrow{p_0}Y_0, with j_0 quasi-compact open, p_0 finite, and
   f_0=p_0j_0. This is a compactification since a finite morphism is proper [lem-weil-pbc-finite-
   proper]. It is over k_0, giving compatible geometric base changes. No absolute separatedness of
   Y_0 or T_0 is inferred. The false inference in the blueprint proof of lem-zl-quasi-finite is
   avoided: the identity of the affine line with doubled origin is a finite morphism whose source
   is not separated over k_0. The compact-support operation of [def-weil-integral-rational-qbar-
   compact-support] depends on a chosen compactification; by the comparison stated in [def-zl-
   weil-compact-support-cohomology] (for two compactifications of f_0, with no separatedness of
   X_0,Y_0 assumed, the higher images R^n_cf_!F are isomorphic as Weil sheaves), every assertion
   of the item for an arbitrary compactification follows from the same assertion for
   c_0=(j_0,p_0): vanishing, punctual bounds and mixedness are invariant under isomorphism of Weil
   sheaves. Steps 3-10 compute with c_0.

2. For each affine open V_0\subseteq Y_0, put T_{V_0}=T_0\times_{Y_0}V_0 and
   X_{V_0}=X_0\times_{Y_0}V_0. By [lem-weil-pbc-finite-morphism-permanence], p_{V_0}:T_{V_0}\to
   V_0 is finite and T_{V_0} is affine. By [lem-weil-pbc-open-immersion-base-change],
   j_{V_0}:X_{V_0}\hookrightarrow T_{V_0} is open. Both V_0 and T_{V_0} are separated over k_0 by
   [lem-weil-pbc-affine-source-morphism-separated]; X_{V_0} is separated over k_0 because its
   diagonal is the restriction of the closed diagonal of T_{V_0}. These schemes are finite type
   over k_0: Y_0 is Noetherian by [lem-weil-pbc-finite-type-over-noetherian], its open V_0 is
   quasi-compact by [lem-weil-pbc-noetherian-open-subscheme-noetherian] and locally finite type,
   T_{V_0} is finite over V_0, and X_{V_0} is a quasi-compact open of T_{V_0}. Their geometric
   base changes remain separated and finite type by [lem-pod-separated-finite-type-base-change].
   The affine opens cover Y_0 by [lem-weil-pbc-affine-opens-basis].

3. For V=V_0\times_{k_0}k, put u:X_V\hookrightarrow X and v:V\hookrightarrow Y. The four schemes
   and the finite compactification scheme T are Noetherian and finite-dimensional by [lem-weil-
   pbc-finite-type-over-noetherian] and [lem-kun-dimension-finite-type]; \ell is invertible. Apply
   [lem-zl-framework-pbc-open-exchange-comparison] to the supplied finite compactification. It
   identifies the actual framework functor R\lim_n\operatorname{Res}_n Rp_{*,n}j_!K_n with the
   completed PBC Rp_*j_! under the coefficient-presentation equivalences J. For the two composite
   functors it supplies the specified endpoint isomorphisms S,T and the equation
   \operatorname{Ex}^{\mathrm{pbc}}J\circ S=T\circ J(\operatorname{Ex}^{\mathrm{sf}}). Thus the
   exchange comparison includes the strict quotient transitions and the proper/open mates before
   taking the derived limit. This is the comparison of functors and arrows needed here; equality
   of their finite evaluations alone is not used.

4. Apply [thm-cbc-qbar] to J_XF in the PBC common-stage category. The hypotheses of its finite-
   stage theorem [thm-cbc-finite-extension] were checked in Step 3; these hypotheses impose
   relative separatedness of f, without absolute separatedness of X,Y. Its specified exchange
   \operatorname{Ex}^{\mathrm{pbc}} is invertible. The equation in Step 3 expresses
   J(\operatorname{Ex}^{\mathrm{sf}})=T^{-1}\operatorname{Ex}^{\mathrm{pbc}}J\,S, so the
   equivalence J reflects invertibility and gives v^*Rf_!F\simeq Rf_{V!}u^*F for the framework
   functors. The comparison lemma also identifies their Weil structures. Explicitly, the two
   pastings of the open square with geometric Frobenius are the same square, because V_0 and the
   compactification are over k_0. Identity/pasting coherence of the specified exchange in [thm-
   cbc-finite-extension] makes the composites equal; compose this equation with the image of the
   Weil arrow of F. Naturality of S,T under the semilinear diagram isomorphisms gives the same
   equality in the framework category. Hence this is an isomorphism of Weil complexes, using [def-
   weil-weil-sheaf-complex].

5. On the separated finite-type schemes of Step 2, the composition and properness laws of [prop-
   functor-package] give Rf_{V!}\simeq Rp_{V*}j_{V!}. Clause (2) of [lem-zl-immersion-weil-local-
   behavior] identifies the open compact-support operation with the exact j_{V!} on constructible
   Weil sheaves, without any assumption on a coefficient embedding. The finite direct image is
   standard-t-exact and exact on the constructible heart by [lem-zl-finite-adic-direct-image].
   Consequently for every constructible Weil sheaf A on X_{V_0}, Rf_{V!}A\simeq p_{V*}j_{V!}A is a
   sheaf in degree zero, and A\mapsto p_{V*}j_{V!}A is exact. Every invocation of these three
   statements is now on absolutely separated finite-type schemes, including T_{V_0} and its
   geometric base change.

6. Restriction to V commutes with cohomology and is exact on constructible hearts by
   [lem-a1-constructible-pullback-t-exact]. Steps 4 and 5 therefore show that every cohomology
   sheaf \mathcal H^i(Rf_!F) with i\ne0 restricts to zero on each V. The restrictions form
   compatible local-heart data: for nested opens, the transition isomorphisms are the restrictions
   of the same global object, and their identity and cocycle equations are the restriction/pasting
   equations of Step 4. The open-cover exactness criterion in [lem-dl-a1-constructible-fibres-
   exact] detects its vanishing: apply it to the short complex 0\to\mathcal H^i(Rf_!F)\to0, which
   is exact on each member of this separated open cover. Thus Rf_!F lies in the constructible
   heart, and in particular R^if_{0!}F=0 for i>0. For any short exact sequence of constructible
   Weil sheaves on X_0, restriction to X_V is exact by the pullback statement. By Step 5 its
   direct-image sequence is exact over each V. Applying the same open-cover criterion to that
   sequence proves that f_{0!}=R^0f_{0!} is an exact functor globally. These checks are on
   constructible adic sheaves, not arbitrary pro-etale sheaves.

7. Fix the arbitrary field embedding \iota:\Omega\hookrightarrow\mathbf C of [sk-d-dl-general-
   weights]; no surjectivity is assumed. Suppose F has punctual upper bound w, or is punctually
   pure of weight w, in the eigenvalue sense spelled out there. Restrict to X_{V_0}. A closed
   point of this open is closed in X_0: on both finite-type schemes this means its residue field
   is finite over k_0 by [lem-kun-closed-point-field]. Its stalk and local Frobenius are
   unchanged. Clause (2) of [lem-zl-immersion-weil-local-behavior] says that B=j_{V!}(F|_{X_V})
   has that identical stalk and local Frobenius on X_{V_0}, and zero stalk elsewhere in T_{V_0}.
   Thus B has the same bound or purity for this very embedding \iota. This uses the weight-free
   stalk assertion, not a weight-preservation theorem stated only for an isomorphism with \mathbf
   C.

8. Fix closed y\in V_0, set k_y=\kappa(y), and put Z_0=T_{V_0}\times_{V_0}\operatorname{Spec}k_y.
   The natural finite-fibre formula of [lem-zl-finite-adic-direct-image] identifies
   (p_{V*}B)_{\bar y} with H^0(Z,B|_Z), including its Frobenius action by the stated semilinear
   naturality. The fibre is finite, hence proper, so this is also H_c^0 by the properness law of
   [prop-functor-package]. Give B|_Z the Weil arrow \theta_B^{[d_y]}, where d_y=[k_y:k_0], and
   apply [lem-a1-finite-weil-sections-decomposition] over k_y, with algebraic closure k. For
   x\in|Z_0|, it gives a block of e=[\kappa(x):k_y] summands on which F_y acts cyclically and
   F_y^e on each summand is F_x. The same-residue-field case of [lem-fd-weil-pullback-local-
   frobenius] for Z_0\to T_{V_0} identifies its stalk operators over k_0. Over k_y, e iterations
   of \theta_B^{[d_y]} give \theta_B^{[ed_y]}, exactly the original F_x of [def-weil-local-
   frobenius-trace]. The point x is closed in T_{V_0}, and q_x=q_y^e because a k_y-basis of the
   degree-e residue extension identifies its underlying set with k_y^e. If \beta is an eigenvalue
   on this block, choose an eigenvector and a nonzero stalk component. The equation
   F_y^ev=\beta^ev on that component shows that \alpha=\beta^e is an eigenvalue of F_x. For the
   bound, multiplicativity of the given embedding and the complex absolute value gives
   |\iota(\beta)|^e=|\iota(\alpha)|\le q_x^{w/2}=(q_y^{w/2})^e. Taking the positive e-th root
   proves |\iota(\beta)|\le q_y^{w/2}. For purity use equality throughout. This works for every
   real w and uses no surjectivity of \iota.

9. By Steps 4 and 5, p_{V*}B is the restriction of f_{0!}F to V_0, as a Weil sheaf. Every closed
   point of Y_0 is in an affine V_0, with the same residue field, stalk and local Frobenius as on
   Y_0. Thus Steps 7 and 8 show that f_{0!} preserves punctual upper bounds and punctual purity
   globally for the original arbitrary embedding. There is no assertion about descent of local
   mixed filtrations; the punctual predicates are exactly the closed-point eigenvalue
   inequalities/equalities of [sk-d-dl-general-weights].

10. If F is mixed of weights at most w, choose its global finite filtration
   0=G_0\subset\cdots\subset G_n=F with punctually pure quotients Q_i of weights u_i\le w, as in
   [sk-d-dl-general-weights]. Exactness from Step 6 sends each 0\to G_{i-1}\to G_i\to Q_i\to0 to
   0\to f_{0!}G_{i-1}\to f_{0!}G_i\to f_{0!}Q_i\to0. Thus the inclusions give a finite filtration
   of f_{0!}F with quotients f_{0!}Q_i. Step 9 shows that these quotients are punctually pure of
   the same u_i. This is exactly the mixed upper bound w of [sk-d-dl-general-weights]. A zero
   quotient can be omitted. In particular this argument applies one global input filtration; it
   does not assume descent or uniqueness of independently chosen local mixed filtrations.
-/
theorem sfQuasiFiniteCompactSupport
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] (_hqf : Scheme.Hom.IsQuasiFinite f₀.left)
    (c : Compactification f₀.left) (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    (∀ i : ℕ, 0 < i → IsZero (zlWeilHigherShriek D l hl Ω f₀ c i F)) ∧
      ∀ (iota : Ω →+* ℂ) (w : ℝ),
        (SfIsMixedOfWeightsAtMost D l hl Ω X₀ iota F w →
          SfIsMixedOfWeightsAtMost D l hl Ω Y₀ iota
            (zlWeilHigherShriek D l hl Ω f₀ c 0 F) w) ∧
        ((∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left}) (α : Ω),
            SfPunctualEigenvalue D l hl Ω X₀ F x α →
              ‖iota α‖ ≤ (Nat.card (X₀.left.residueField x.val) : ℝ) ^ (w / 2)) →
          ∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) (β : Ω),
            SfPunctualEigenvalue D l hl Ω Y₀
                (zlWeilHigherShriek D l hl Ω f₀ c 0 F) y β →
              ‖iota β‖ ≤ (Nat.card (Y₀.left.residueField y.val) : ℝ) ^ (w / 2)) := by
  sorry

end WeilConjectures
