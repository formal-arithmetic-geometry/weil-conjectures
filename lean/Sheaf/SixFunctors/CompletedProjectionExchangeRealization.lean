module

public import Sheaf.SixFunctors.CompletedProjectionExchangeData
import Sheaf.SixFunctors.CompletedProjectionExchangeDomains
import Sheaf.SixFunctors.CompletedProjectionExchangeSystem
import Sheaf.SixFunctors.CompletedProjectionExchangePaths
import Sheaf.Paper.IntegralResidueTor
import Sheaf.Paper.DirectImagesConstructible

/-! # Completed projection/base-change diamond

Source: blueprint fix-prop-coherence and fix-prop-projection-formula, projection diamond;
Stacks 0GL1 and 0E48 (blueprint: lem-sf-completed-projection-exchange-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.CompletedProjectionExchange

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {D : FiniteFieldDatum.{u}} (o : Operations l E) (ρ : Realizations l E D o)
  (Q : SixFunctorCompactifiedSquare D)

/-- The strict-system diamond and its two normalization calculations. The first input
is only bounded constructible and derived complete; the finite-Tor condition is on L.
Every word domain, including its hidden open/proper intermediates, is a conclusion.
The final clause is the realization equation for any generator path in any outer context.
Source: blueprint fix-prop-coherence, projection diamond; Stacks 0GL1 and 0E48
(blueprint: lem-sf-completed-projection-exchange-realization).

Proof:

1. Set up the ambient system operations of [def-sf-integral-system-operations] without invoking the
domain-restricted realization conclusion. Choose $f=pj$ and its base change, as in
[def-exchange-projection]. Write $K_0=\mathcal RK$, $N=\mathcal RL$, $F=P_p$, $F'=P_{p'}$,
$G=P_g$, $H=P_h$ with $h:\bar X'\to\bar X$, $A=P_{g'}$, $J=J_j$, $J'=J_{j'}$, $U=P_j$,
$U'=P_{j'}$, $S=S_p$, $S'=S_{p'}$, $M=JK_0$, $Q=M\otimes FN$. Put $\theta:F'G\cong HF$ and
$\sigma:AU\cong U'H$. All tensors in system calculations are over the coefficient ring system.
The four vertices, with the canonical pullback/tensor identifications, are $$G(SM\otimes
N),\quad GSJ(K_0\otimes UFN),\quad S'J'AK_0\otimes GN,\quad S'J'(AK_0\otimes U'F'GN).$$ We next
prove the intermediate-domain properties, including the hidden open and proper intermediates. In
particular these properties are conclusions, not extra hypotheses on $K,L$.

2. Choose a cohomological interval $[a,b]$ for $K_1$; [lem-coef-integral-residue-tor] gives this
same Tor interval for every $K_n$. Choose $[c,d]$ for all $L_n$ from the hypothesis on $L$. For
every finite-level word use the following interval rules. Each separated finite-type pullback
preserves bounded constructibility and its Tor interval by [lem-sf-pullback-tor-amplitude];
tensor adds the two intervals and preserves bounded constructibility by [lem-sf-tensor-ctf]. A
quasi-compact open extension preserves bounded constructibility and the cohomological interval
by [lem-sf-open-finite-constructibility-interval]; its Tor interval is unchanged because
[lem-sf-open-tensor-normalization] identifies $(j_!B)\otimes^LV$ with $j_!(B\otimes^Lj^*V)$ for
every degree-zero test sheaf $V$, and both restriction and extension are exact. Thus these rules
apply uniformly in $n$ to $FN,UFN,K_0\otimes UFN,M,Q$ and their primed and pulled-back versions.
All schemes involved are finite type, hence Noetherian, so the open-extension theorem applies.
Neither a Tor assumption on $K$ nor a flatness assumption on its cohomology has been added.

3. For a proper letter $r:Z\to B$, choose a finite nonnegative bound $d_Z$ on $\dim Z$ using
[lem-cbc-compactification-geometry-fibre-bound], applied first to the finite-type structure maps
over $\operatorname{Spec}k$ (dimension zero and a Noetherian field). This also supplies finite
affine Noetherian covers; for an empty source take $d_Z=0$. Before each proper letter,
[lem-sf-proetale-constructible-origin] supplies bounded constructible etale origins of its
levels, and [lem-sf-comparison-tor-amplitude](ii) gives those origins the same Tor interval.
Apply [cor-sf-direct-image-ctf-etale-origin], in the setting explicitly given by
[cor-sf-direct-image-ctf-nonproper]: a proper letter sends $[u,v]$ to $[u,v+2d_Z]$ and preserves
bounded constructibility. This applies to $SM,SQ,SJ(K_0\otimes UFN)$ and the corresponding
primed outputs. Reapply the pullback and tensor rules of step 2 to these outputs. This is
induction on the actual finite expression trees: the input case is step 2 and each constructor
uses only its already treated children. Each tree has finitely many constructors; its endpoints
involve only input endpoints, sums, and finitely many $2d_Z$, so are independent of $n$. In
particular this proves bounds for all four vertices and for the extra pullback/tensor words in
their adjunction transposes.

4. Check normalization for these actual systems, not for a chosen family of evaluated objects.
Input reductions are normalized by [lem-pur-normalized-actual-reconstruction-maps].
[lem-pur-system-normalized-tensor-closure] gives normalization of pullbacks and tensors, with
the actual transition-adjoints and their quotient cocycles. For an open letter,
[lem-sf-open-tensor-normalization] applied also to scalar quotient tensors identifies its
transition-adjoint with $j_!\alpha_{m,n}$, hence an isomorphism. For a proper letter $r$,
[lem-pur-coefficient-system-derived-comparison] identifies its evaluated transitions and
adjunctions with the levelwise ones. Its transition-adjoint is
$$(Rr_{*,m}B_m)\otimes^L_{A_m}A_n
\xrightarrow{\chi_{r,B_m}}Rr_{*,n}(B_m\otimes^L_{A_m}A_n)
\xrightarrow{Rr_{*,n}(\alpha_{m,n})}Rr_{*,n}B_n.$$
The first arrow is exactly the counit-defined scalar mate by
[lem-fix-proetale-scalar-mate-normalization]; [lem-fix-proper-etale-origin-scalar-isomorphism]
makes it invertible. Its hypotheses hold: the origin of $B_m$ has the finite Tor interval of
step 3, so its tensor with the degree-zero $A_n$ is bounded below. The second arrow is
invertible by induction. Thus $S_r$ preserves normalization on these inputs. The formula is the
scalar-adjunction transpose of the actual transition, using the stated counit equation, so no
detection of equality of system maps by evaluation occurs. Induction treats every intermediate,
including $J_jK_0$ and $S_pJ_jK_0$.

5. For each intermediate normalized system $B$, choose bounded constructible origins $E_n$ with
$\alpha_n:\nu^*E_n\cong B_n$ by [lem-sf-proetale-constructible-origin].
[lem-weil-pbc-normalized-etale-origin-witnesses] supplies the unique quotient isomorphisms
$\beta_{m,n}$ satisfying $$\alpha_n\nu^*\beta_{m,n}=\rho^B_{m,n}(\alpha_m\otimes A_n),$$ and
their identity/tower cocycles. These are witnesses compatible with the actual transitions,
rather than presumed extra input data. By [lem-pur-normalized-actual-reconstruction-maps],
$\mathcal LB$ is complete and its actual counit $\mathcal R\mathcal LB\to B$ is invertible; the
constructibility and common cohomological interval already proved therefore put $\mathcal LB$ in
$D^b_c$ by [def-weil-derived-complete-integral-detailed]. In particular this constructs complete
integral inputs when a compact-support word is applied to a pulled-back or tensored input.
[lem-coef-compact-support-normalized-realization] specifies the normalized quotient transitions
of these compact-support outputs, and [lem-sf-integral-compact-support-constructible] puts their
specified total limits in $D^b_c$. This is consistent with the normalization just proved for the
actual $S_pJ_j$ system; it is not an identification of system maps from their finite
evaluations.

6. Restrict the preceding bounds to any chosen finite affine target cover and its inverse images.
Repeating the same constructor rules there gives local intervals independent of $n$. For the
finite set of chart/word intervals $[a_i,b_i]$, take $a=\min_i a_i$, $b=\max_i b_i$.
[lem-sf-finite-cover-ctf-locality] gives global constructibility and Tor amplitude $[a,b]$ on
each scheme: for every degree-zero test module the forbidden-degree cohomology restricts to zero
on the cover and hence is zero. For an empty scheme the zero object has interval $[0,0]$.
Origins are obtained by step 5 for the global constructible objects, not by gluing independently
chosen arrows. Consequently every intermediate in the four words satisfies the actual domain
proviso, and we may now apply [lem-sf-integral-compactification-system-realization]. It supplies
the simultaneous ringed-diagram-site models, canonical system adjunctions, and natural
realizations $c_V$ intertwining generators also inside the outer expressions. No absolute
separatedness over $k$, affine-intersection assertion, or restriction on $K$ beyond the original
statement was used.

7. Record the precise compositor/tensor identities used below. Put $C=AU$, $D=U'H$, and write
$\mu_C=\mu_A\,A\mu_U$, $\mu_D=\mu_{U'}\,U'\mu_H$, with the tensor factors indicated by
evaluation. Monoidality of the canonical open-square compositor is
$$(\sigma_B\otimes\sigma_P)\mu_{A;UB,UP}A(\mu_{U;B,P})=\mu_{U';HB,HP}U'(\mu_{H;B,P})\sigma_{B\otimes
P}.$$ For the proper square it is
$$(\theta_B\otimes\theta_P)\mu_{F';GB,GP}F'(\mu_{G;B,P})=\mu_{H;FB,FP}H(\mu_{F;B,P})\theta_{B\otimes
P}.$$ These identities are part of the canonical K-flat tensor/composition identifications
specified in [lem-sf-integral-compactification-system-realization]. Explicitly, on the
simultaneous flat-term K-flat models both routes pull back each factor and balance the same
scalar actions; a local pure tensor $m\otimes n$ is sent to its two pulled-back sections in both
orders. The structure-ring homomorphisms agree by the two commutative squares, so their scalar
multiples agree as well. Thus these are equal chain maps before localization; derived
localization preserves the equalities. They apply to the system site itself.

8. Use [lem-sf-open-tensor-normalization] on the simultaneous ringed diagram sites. Write
$\beta:HJ\cong J'A$, $\gamma_{j;B,P}:JB\otimes P\cong J(B\otimes UP)$, and set
$c=\gamma_{j;K_0,FN}$, $b=\beta_{K_0}$, $c'=\gamma_{j';AK_0,F'GN}$. Thus $c'$ has target
$J'(AK_0\otimes U'F'GN)$, retaining the essential $U'$. Put
$$d=(1\otimes\theta_N^{-1})\mu_{H;M,FN},\quad
z=J'((1\otimes\sigma_{FN})\mu_{A;K_0,UFN})\beta_{K_0\otimes UFN},\quad v=J'(1\otimes
U'\theta_N^{-1})z.$$ Both $vH(c)$ and $c'(b\otimes1)d$ have source $HQ$ and target
$J'(AK_0\otimes U'F'GN)$. Their source lies in the essential image of $J'$ by the isomorphisms
$H(c)$ and $\beta_{K_0\otimes UFN}$; their target visibly does. Apply $U'$ and the canonical
open units. The restrictions of $\beta,\gamma$ become the identity under the comparisons in the
cited theorem, and the remaining composites coincide by the explicit identities of step 7, with
the common final factor $1\otimes U'\theta_N^{-1}$. Full faithfulness of $J'$ gives
$$vH(c)=c'(b\otimes1)d.$$ This proves the equality in the derived system category, without
coefficient evaluation.

9. Apply [lem-weil-pbc-ringed-exchange-tensor-coherence] to the proper square on the simultaneous
ringed diagram sites of step 6. It applies to arbitrary derived system inputs and needs no
geometric separatedness of the schemes. With $e:GS\to S'H$ the proper exchange and $\pi,\pi'$
the counit projections, it gives
$$S'(d)e_QG(\pi_{p;M,N})=\pi_{p';HM,GN}(e_M\otimes1)\mu_{G;SM,N}.$$ For completeness the common
transpose is fixed, not just the equality: [def-exchange-projection] gives
$\varepsilon'_{HB}F'(e_B)=H(\varepsilon_B)\theta_{SB}$ and $\varepsilon_Q
F(\pi_{p;M,N})=(\varepsilon_M\otimes1)\mu_{F;SM,N}$. Thus the transpose of the left side above
is $dH(\varepsilon_Q)\theta_{SQ}F'G(\pi_{p;M,N})$. Naturality of $\theta$ moves $\pi$ next to
$\varepsilon_Q$; substituting the second formula and naturality of $\mu_H$ reduces this to
$$F'G(SM\otimes N)\cong HFSM\otimes F'GN\xrightarrow{H\varepsilon_M\otimes1}HM\otimes F'GN.$$
The initial isomorphism here is precisely $\theta_{SM\otimes N}$, then $H\mu_F$, then $\mu_H$,
then $1\otimes\theta_N^{-1}$. Equality from the cited ringed theorem gives this same transpose
for the right side. These are system adjunctions before total inverse limit.

10. Paste the preceding two equations explicitly. Put $T=J(K_0\otimes UFN)$, so $c:Q\to T$. The
definitions [def-exchange-projection], interpreted by
[lem-sf-integral-compactification-system-realization], are $\operatorname{PF}^c=S(c)\pi$ and
$\operatorname{Ex}_!^c=S'(b)e_M$. Naturality of $e$ at $c$, the open equation of step 8 and then
step 9 give $$\begin{aligned} S'(v)e_TG(S(c)\pi)&=S'(vH(c))e_QG\pi\\
&=S'(c')S'(b\otimes1)\pi'_{HM,GN}(e_M\otimes1)\mu_G\\
&=S'(c')\pi'_{J'AK_0,GN}(S'(b)e_M\otimes1)\mu_G. \end{aligned}$$ The last equality is naturality
of $\pi'$ at $b$ and tensor bifunctoriality. The first line is the top route, and the last line
the bottom route, with $v$ inserting exactly the target pullback/tensor identification. This
proves equality of the two actual derived system arrows. Only substitution, naturality and
functorial composition were used to paste the factors; no inverse of a projection or proper
exchange was taken.

11. Let $a,b$ now denote the complete top and bottom system routes of step 10, with common source
expression $V$ and target expression $W$. The generator and outer-context clause of
[lem-sf-integral-compactification-system-realization] identifies all four vertices and each edge
with the specified completed integral word and arrow. In particular it gives $$c_W\mathcal
L(a)=a_{\rm int}c_V,\qquad c_W\mathcal L(b)=b_{\rm int}c_V.$$ Here $S_pJ_j$ realizes exactly the
specified integral compact-support functor, not an independently chosen isomorphic functor.
Since $a=b$, functoriality gives $a_{\rm int}c_V=b_{\rm int}c_V$, and cancellation of the
isomorphism $c_V$ gives $a_{\rm int}=b_{\rm int}$. This is the displayed completed integral
diamond, with every tensor and pullback completed and all comparisons inserted. The same
argument includes each outer pullback, proper-image or tensor context because the cited theorem
intertwines generators in those contexts, not merely isolated objects.

12. For rational inputs, raw localization [def-weil-rationalization-karoubi] has exactly the
integral objects, so choose their integral presentations. Use the specified coefficient
comparisons in [def-exchange-projection]; they carry units, counits, open maps and the
tensor/pullback comparisons to the rational ones. Applying
[lem-sf-pf-coefficient-realization-transport] identifies each localized path with the
corresponding specified rational path, including whiskering. Explicitly, if $q$ is localization
and $s,t$ are its endpoint comparisons, the two paths are $tq(a_{\rm int})s^{-1}$ and $tq(b_{\rm
int})s^{-1}$, hence equal by step 11. For algebraically closed coefficients
[def-weil-algebraically-closed-coefficients], represent the two inputs over one common finite
field and form this rational equality there. The finite-field comparisons supplied in
[def-exchange-projection] meet the same transport lemma's hypotheses, including the
identity/tower cocycles, so both extended paths are conjugates of the images of the same
equality. Their common-stage morphism classes are equal; enlarging the coefficient field gives
the same class. Thus raw localization and scalar transport of the system-realized routes give
exactly both field diamonds. No rational-to-finite reduction or faithfulness of
reduction/evaluation enters.
-/
theorem completedProjectionExchangeRealization
    (_hl : l ≠ D.p)
    [IsSeparated Q.f.hom.left] [LocallyOfFiniteType Q.f.hom.left] [QuasiCompact Q.f.hom.left]
    [IsSeparated Q.g.hom.left] [LocallyOfFiniteType Q.g.hom.left] [QuasiCompact Q.g.hom.left]
    [IsSeparated Q.f'.hom.left] [LocallyOfFiniteType Q.f'.hom.left]
    [QuasiCompact Q.f'.hom.left]
    [IsSeparated Q.g'.hom.left] [LocallyOfFiniteType Q.g'.hom.left]
    [QuasiCompact Q.g'.hom.left]
    (K : Integral l E Q.X.obj.left) (L : Integral l E Q.Y.obj.left)
    (_hK : sfIntegralConstructible l E Q.X.obj.left K)
    (_hL : finiteTorConstructibleIntegral l E Q.Y.obj.left L) :
    Statement l E o ρ Q K L := by
  obtain ⟨hdomain, hsource, htarget⟩ :=
    completedProjectionExchangeDomains l E o Q _hl K L _hK _hL
  obtain ⟨hsystem, hopen, hproper⟩ := completedProjectionExchangeSystem l E o ρ Q
    ((calculus l E Q.X.obj.left).reduction.obj K)
    ((calculus l E Q.Y.obj.left).reduction.obj L)
  refine ⟨hdomain, hsystem, hopen, hproper, ⟨hsource, htarget⟩, ?_, ?_⟩
  · intro g₀ g₃ h₀ h₃
    obtain ⟨r₁, r₂, hp₁, hp₂⟩ :=
      completedProjectionExchangePaths l E o ρ Q K L g₀ g₃ h₀ h₃ hdomain
    have hr₁ := ρ.coherence (word Q 0) (word Q 3) g₀ g₃
      ⟨inputs l E Q K L, h₀⟩ h₃ _ r₁ hp₁
    have hr₂ := ρ.coherence (word Q 0) (word Q 3) g₀ g₃
      ⟨inputs l E Q K L, h₀⟩ h₃ _ r₂ hp₂
    have he₁ : integralLeft l E o ρ Q K L g₀ g₃ h₀ h₃ = r₁ := by
      dsimp only [integralLeft]
      rw [hr₁, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    have he₂ : integralRight l E o ρ Q K L g₀ g₃ h₀ h₃ = r₂ := by
      dsimp only [integralRight]
      rw [hr₂, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    have heq : integralLeft l E o ρ Q K L g₀ g₃ h₀ h₃ =
        integralRight l E o ρ Q K L g₀ g₃ h₀ h₃ := by
      dsimp only [integralLeft, integralRight]
      rw [hsystem]
    refine ⟨he₁.symm ▸ hp₁, he₂.symm ▸ hp₂, heq, ?_⟩
    intro hs ht
    unfold rationalLeft rationalRight
    rw [heq]
  · intro I _ X W e t ge gt A ht s r hpair
    exact ρ.coherence e t ge gt A ht s r hpair



/-- At the rational stage both inputs are arbitrary constructible rational objects,
represented by their integral objects in raw localization. Residue Tor supplies the
finite-Tor property of each integral representative rather than assuming it.
Source: blueprint projection diamond, proof step 12
(blueprint: lem-sf-completed-projection-exchange-realization).

Proof: apply lem-coef-integral-residue-tor to the integral representatives; the residue
cohomological interval is a uniform Tor interval for all reductions. Apply
completedProjectionExchangeRealization to obtain all four word domains and the
completed equality. Raw localization and the specified coefficient comparisons carry
this same equality to the rational diamond. No rational-to-finite functor is used. -/
theorem completedProjectionExchangeRational
    (_hl : l ≠ D.p)
    [IsSeparated Q.f.hom.left] [LocallyOfFiniteType Q.f.hom.left] [QuasiCompact Q.f.hom.left]
    [IsSeparated Q.g.hom.left] [LocallyOfFiniteType Q.g.hom.left] [QuasiCompact Q.g.hom.left]
    [IsSeparated Q.f'.hom.left] [LocallyOfFiniteType Q.f'.hom.left]
    [QuasiCompact Q.f'.hom.left]
    [IsSeparated Q.g'.hom.left] [LocallyOfFiniteType Q.g'.hom.left]
    [QuasiCompact Q.g'.hom.left]
    (K : Integral l E Q.X.obj.left) (L : Integral l E Q.Y.obj.left)
    (_hK : sfIntegralConstructible l E Q.X.obj.left K)
    (_hL : sfIntegralConstructible l E Q.Y.obj.left L) :
    (∀ i : Fin 4, (word Q i).geometric ∧
      (word Q i).domain l E o (inputs l E Q K L)) ∧
    sfIntegralConstructible l E Q.Y'.obj.left (integralSource l E Q K L) ∧
    sfIntegralConstructible l E Q.Y'.obj.left (integralTarget l E Q K L) ∧
    ∀ (g₀ : (word Q 0).geometric) (g₃ : (word Q 3).geometric)
      (h₀ : (word Q 0).domain l E o (inputs l E Q K L))
      (h₃ : (word Q 3).domain l E o (inputs l E Q K L))
      (hs : sfIntegralConstructible l E Q.Y'.obj.left (integralSource l E Q K L))
      (ht : sfIntegralConstructible l E Q.Y'.obj.left (integralTarget l E Q K L)),
      rationalLeft l E o ρ Q K L g₀ g₃ h₀ h₃ hs ht =
        rationalRight l E o ρ Q K L g₀ g₃ h₀ h₃ hs ht := by
  classical
  let (x : Q.Y.obj.left) : Invertible (l : Q.Y.obj.left.residueField x) :=
    (show IsUnit (l : Q.Y.obj.left.residueField x) by
      simpa using (finiteFieldDatumPrimeUnit D l _hl).map
        (Q.Y.obj.hom.residueFieldAlgebraMap x)).invertible
  have hL : finiteTorConstructibleIntegral l E Q.Y.obj.left L :=
    (integral_residue_tor D l _hl E Q.Y.obj.left).2 ▸ _hL
  have h := completedProjectionExchangeRealization l E o ρ Q _hl K L _hK hL
  exact ⟨h.1, h.2.2.2.2.1.1, h.2.2.2.2.1.2,
    fun g₀ g₃ h₀ h₃ hs ht ↦ (h.2.2.2.2.2.1 g₀ g₃ h₀ h₃).2.2.2 hs ht⟩

/-- The same realized diamond over an arbitrary common finite coefficient field,
taken to its morphism class in the recorded algebraically closed category.
No reduction from a field to a finite quotient is used.
Source: blueprint projection diamond, proof step 12
(blueprint: lem-sf-completed-projection-exchange-realization).

Proof: apply completedProjectionExchangeRealization at the small coefficient model
of F. Raw localization preserves the integral equality. Apply the canonical inclusion
of that finite stage into the common-stage pair category. The coefficient-comparison
identities of def-exchange-projection and lem-sf-pf-coefficient-realization-transport
identify the two resulting paths with the specified field paths. Scalar-extension
identity and tower cocycles identify their representatives after every further field
extension. Objects and both arrows are represented at this one common finite field,
so this proves the algebraically closed diamond, without a faithfulness argument. -/
theorem completedProjectionExchangeCommonStage
    (_hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (F : AlgebraicallyClosedCoefficients.Index l Ω)
    (oF : Operations l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F))
    (ρF : Realizations l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) D oF)
    [IsSeparated Q.f.hom.left] [LocallyOfFiniteType Q.f.hom.left] [QuasiCompact Q.f.hom.left]
    [IsSeparated Q.g.hom.left] [LocallyOfFiniteType Q.g.hom.left] [QuasiCompact Q.g.hom.left]
    [IsSeparated Q.f'.hom.left] [LocallyOfFiniteType Q.f'.hom.left]
    [QuasiCompact Q.f'.hom.left]
    [IsSeparated Q.g'.hom.left] [LocallyOfFiniteType Q.g'.hom.left]
    [QuasiCompact Q.g'.hom.left]
    (K : Integral l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) Q.X.obj.left)
    (L : Integral l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) Q.Y.obj.left)
    (_hK : sfIntegralConstructible l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) Q.X.obj.left K)
    (_hL : sfIntegralConstructible l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) Q.Y.obj.left L)
    (g₀ : (word Q 0).geometric) (g₃ : (word Q 3).geometric)
    (h₀ : (word Q 0).domain l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) oF
      (inputs l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) Q K L))
    (h₃ : (word Q 3).domain l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) oF
      (inputs l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) Q K L))
    (hs : sfIntegralConstructible l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
      Q.Y'.obj.left (integralSource l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
        Q K L))
    (ht : sfIntegralConstructible l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
      Q.Y'.obj.left (integralTarget l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
        Q K L)) :
    (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := Q.Y'.obj.left) F).map
        (rationalLeft l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
          oF ρF Q K L g₀ g₃ h₀ h₃ hs ht) =
      (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := Q.Y'.obj.left)
          F).map
        (rationalRight l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
          oF ρF Q K L g₀ g₃ h₀ h₃ hs ht) := by
  have h := completedProjectionExchangeRational l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) oF ρF Q _hl K L _hK _hL
  exact congrArg
    ((GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := Ω) (Y := Q.Y'.obj.left) F).map)
    (h.2.2.2 g₀ g₃ h₀ h₃ hs ht)

end WeilConjectures.CompletedProjectionExchange
