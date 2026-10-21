## Worker report

The module `Sheaf.Paper.FdCommonStageComparisonDescent` states this node in seven
named theorems, with every proof `sorry`. The finite input structure has real fields;
there are no data-valued sorries, local instances, private definitions or local notation.
No natural-language statement or proof dependency is changed.

### Hypotheses and clauses

- The global datum is `_D : FiniteFieldDatum`, and `_hl : l ≠ _D.p`; primality is
  `[Fact l.Prime]`. Coefficients are the fixed `Ω` with `Field`, `Algebra ℚ_[l] Ω`
  and `IsAlgClosure ℚ_[l] Ω`. Their universes `d`, `u`, `w` are independent.
- Allowed schemes are `Scheme.{u}`, `[IsNoetherian T]`,
  `[Fact (∃ n, topologicalKrullDim T ≤ n)]`, and stalkwise invertibility
  `[Fact (∀ t, IsUnit (l : T.presheaf.stalk t))]`. The pullback section repeats
  exactly these hypotheses for `U`. Each scheme is arbitrary, so the coefficient
  conclusion can be applied pointwise to every allowed W. No finite-type structure
  over k or nonempty-scheme hypothesis is introduced.
- The two finite categories and their actual transitions/associators are those of
  `GeneralAlgebraicallyClosedCoefficients.stageSystem` and `pbcScalarSystem`.
  `J : StageSystem.Morphism` supplies every finite functor and the natural scalar
  isomorphisms. Its `β` is inverse j, and `J.coh` is exactly the inverted displayed
  scalar cocycle, with both actual associators retained. `hadd`, `hequiv`, `hlinear`,
  `hexact`, the integer `CommShift` instances, and `hshift` render exact E-linear
  equivalences and shift-compatible scalar comparisons. Coherence at repeated
  stages forces the unit normalization relative to the specified tensor unitors:
  no extra arbitrary unit maps are introduced. The framework transition has its
  canonical tensor unitor rather than a syntactically literal identity; this is
  the same normalization expressed in the recorded, non-strict interface.
- `fdCommonStageComparisonDescent` returns an equivalence of the literal framework
  and PBC pairs. `e.functor = J.functor` fixes the field-preserving object formula
  and conjugation on all representatives, since these are the definition of
  `StageSystem.Morphism.functor` and `mapAt`. Additivity and `Linear Ω` hold for
  both functor and inverse. The existential shift structures are bound explicitly
  in instance-parameter lambdas. Both `IsTriangulated` clauses, the finite shift
  component equation, and the `distTriang` iff render shifts and common-stage
  triangles in both directions. No Karoubi category appears.
- `fdCommonStageHomDescent` states bijectivity of `J.mapAt` at EVERY common field,
  the actual `tr` compatibility square, a Hom equivalence whose forward map is
  `J.functor.map` with its representative formula, and compatibility with every
  actual finite-stage inclusion. An `Equiv` supplies the two-sided inverse on
  Hom colimits. Stage bijectivity plus the transport square also fixes the inverse
  stage maps and their transport; no transition-faithfulness hypothesis is used.
- `fdCommonStageComparisonEquations` states equality descent, identity descent,
  and composition descent for compatible transformation families. These apply to
  composite families, so also to the identity/composition/shift/scalar equations
  mentioned in the node. The actual `Morphism.comp`, `functorCompIso`, and their
  identity components keep the pullback and scalar associators.
- `fdFrameworkPullbackFamily_existsUnique` supplies the framework family from its
  actual finite rational pullbacks and its actual `commonStagePullbackComparison`;
  it also identifies its descended functor with `commonStageDerivedPullback`.
  This prevents an arbitrary replacement pullback from entering the statement.
- In `fdMixedPullbackDescent`, `h : U ≅ T` is the specified scheme isomorphism.
  `sfFinite`, `sfBeta`, `sfPair` describe the family just constructed, so those
  binders specify the actual objects rather than impose extra geometric hypotheses.
  The PBC family is the recorded `pbcQbarPullFamily`. The compatible `b` has finite
  invertible components `hb`; its `Hom.comm` is precisely the mixed scalar square
  in inverse-j orientation. The recorded Fd comparison points from PBC composite
  to framework composite, the inverse orientation to b in the TeX; inverting the
  supplied finite b gives this equivalent formulation. The conclusion is a UNIQUE
  natural isomorphism of the actual common-stage composites with finite-inclusion
  components. Inverting it gives exactly the orientation printed in the node.
- `FdFiniteCoefficientComparison` is the finite prefix of the EXISTING
  `FdCoefficientComparison` (through `chi`), including all normalized integral,
  ordinary-scalar, rational, shift and cocycle fields. This owning-node input
  helper has no pair field and asserts no existence. It is not a second definition
  of an integral category, scalar functor or comparison datum. Its fields refer
  directly to the recorded notions. `fdNormalizedCommonStageDescent` supplies the
  full datum while retaining its stages, family, shifts and normalized integral
  comparisons. Proof fields are propositions and hence proof irrelevant.
- `fdNormalizedPullbackDescent` returns the recorded `FdPullbackSystem` while
  retaining exactly the supplied finite comparisons, actual framework family and
  compatible mixed transformation. Thus the final conditional clause of the node
  supplies precisely the common-stage fields; it does not claim integral lifts
  exist or discard their normalization.

### Dependency declarations read and used

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalCoefficientEquiv` and its structures.
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalDerivedCategory`, underlying raw
  `PbcRationalCategory`; the PBC stage specializes this raw localization.
- `Sheaf.Paper.SfScalarExtensionComposition`: `sfRationalScalarComp`,
  `sfRationalScalarUnit`, `sfRationalScalar_coherence`.
- `Sheaf.Paper.PbcScalarExtension`: `pbcCoherentScalarExtension`, the normalized
  stage scalar functors and associators, and rational pullback comparisons.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, `Stage`, `stageSystem`,
  `stageTransitionCommShift`, `inclusionCommShift`, `distinguished_iff`.
- `Sheaf.Paper.PbcQbarCategory`: `pbcQbarCategory`, `qbarStageLinear`, `pbcQbarLinear`.
  `Sheaf.Paper.IntrinsicQbarCategory`: `intrinsicQbarStageLinear`, `intrinsicQbarLinear`
  supply the framework scalar actions. The latter module publicly imports the
  former, so the landed dependency record exposes both interfaces without rebinding.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `commonStagePullbackComparison`, `commonStageDerivedPullback` and its uniqueness.
- `Sheaf.Paper.PbcQbarCompletedPullback`: `pbcQbarPullFamily`, `pbcQbarCompletedPull`.
- `Sheaf.Paper.FdCoefficientComparison`: `FdRationalStageComparison`,
  `FdOrdinaryScalarTransport`, `FdCoefficientComparison`, `fdRawTensor`, `fdRawScale`.
- `Sheaf.Paper.FdCoefficientComparisonSystem`: `FdPullbackSystem`,
  `FdCoefficientComparisonSystem`; its imported finite `FdPullbackComparison`.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralStratifiedPerfectCharacterization`, `integralDetailedTransport`.
- Proof-only imports: `StageSystemFunctorDescent` (`coefficientPairFunctor_exists`),
  `FiniteStagePairCategory` (`PbcFiniteStagePairCategory`, `pbcScalarSystem`),
  `PbcCommonStageCones` (`pbcCommonStageDistinguished`), and Mathlib's
  `CategoryTheory.Equivalence` (`Functor.asEquivalence`, the exact match for
  lem-trf-fully-faithful-ess-surj-equivalence).

The blueprint trace-function final sentence was read. It names the PBC coefficient
category but contains no proof of this auxiliary comparison. The node's full
agent-written 12-step argument is therefore the proof source, retained below.
The pro-etale upstream framework note was read; no separate unrestricted module
category or coefficient universe restriction is introduced.

### Edge cases

Checked equal coefficient fields, repeated fields in towers, and identity scheme
isomorphisms. Every quantifier admits these cases. The actual unitors/associators
remain in the recorded systems. Checked differing endpoint field labels: the Hom
and natural-transformation formulas use the comparison at BOTH endpoints. Zero
objects, zero arrows and the empty scheme are admitted. Invertibility is local,
so the empty scheme is not excluded by a base-field condition. The fixed scalar
may be outside the representative field: the existing Omega-linear structures
adjoin its finite scalar field before multiplication. The index is the actual
finite-intermediate-field directed set, not an arbitrary empty index. No local
faithfulness of scalar transitions is assumed. Universes are explicit, including
independent scheme and closure sizes and the existing Shrink finite-field models.

### Searches

Ran prescribed msearch wrappers and direct source searches:
- leanfinder: “Coherent stagewise exact linear equivalences descend to equivalences
  on common stage pair categories and mixed pullback natural isomorphisms”. Eight
  hits, chiefly TwoSquare.GuitartExact composition criteria, DoldKan compatibility,
  categorical pullback mkNatIso, exact ladders. None states this node.
- loogle: `CategoryTheory.Functor.IsEquivalence, CategoryTheory.Linear`: zero hits.
- grep: `StageSystem|PairCategory|common.stage`, Mathlib CategoryTheory: zero hits.
- leansearch: “Coherent equivalences of filtered systems of linear triangulated
  categories induce an exact linear equivalence on their pair categories”. Eight
  hits, including Equivalence.IsTriangulated and its symmetry/constructor lemmas,
  filteredness under equivalence, and exact pairings. None supplies this descent.
- rg of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `lem-fd-common-stage-comparison-descent|FdCommonStage|commonStageComparisonDescent`:
  no prior declaration. Reading the StageSystem API found the functor and compatible
  transformation constructions used directly here, rather than redefined.

The proof dependency prop-weil-pbc-descent-functors is present transitively through
PbcQbarCompletedPullback. Its direct proof-only import was removed after preflight
flagged that its module also owns the route-pivot-dropped
`def-per-rational-direct-image-family`. No dropped declaration is used; the actual
PBC pullback and its normalized beta remain the recorded, imported constructions.

No STATEMENT-DISPUTED flag and no statement correction. The unnecessary dependency
record replacement is removed in this repair, as described below. Initial server
elaboration errors in explicit target endpoints
and dependent scalar-field projections were repaired; all proofs remain sorry.

## Returned-delivery repairs

H13: removed the sandbox node file for `def-weil-pbc-qbar-category`, as the
return requested. No replacement lean record is delivered. The live record stays
on `Sheaf.Paper.IntrinsicQbarCategory` / `WeilConjectures.intrinsicPbcQbarCategory`
with all eight declarations. I opened that module: its public import of
`Sheaf.Paper.PbcQbarCategory` exposes `pbcQbarCategory`, `qbarStageLinear` and
`pbcQbarLinear`. It also supplies the framework scalar structures needed here.
The landed `FdCoefficientComparison` already has exactly the framework-to-PBC
pair equivalence used by this item under that unchanged dependency record.
Consequently this delivery needs no dependency module or dependency record edit;
NM's module and its users retain their existing attachment.

H11: replaced the previous non-reading with the clause-by-clause second reading
below. This is a fresh reading by the repair worker of the retained packet,
not a claim that another agent was started. The dispatcher explicitly forbids
starting other agents. The maintainer's independent review remains separate.

## Agent-written argument retained verbatim

1. Fix $W$ and suppress it from the notation. All coefficient fields are subfields of the fixed $\Omega$; the index and each overfield index are small directed sets, since a compositum is a finite common overfield. The literal pair constructions in [def-weil-algebraically-closed-coefficients] and [def-weil-pbc-qbar-category] use the same index. Apply the additive pair-functor lemma [lem-sbc-coherent-pair-functor-descent] with $U=S$, $V=P$, $\Phi_E=J_E$, and its comparison $b_{L/E}=j_{L/E}^{-1}$. Inverting the stated scalar cocycle gives precisely that lemma's tower equation; identity normalization supplies its unit condition. It yields the functor on literal pairs with exactly the object and conjugation formulas in the statement. Only its pair-category conclusion is used, before its optional Karoubi extension.

2. Here is the transport calculation, including the associators. For endpoints $X=(E,K)$ and $Y=(F,H)$ put $r_X=j_{M/E,K}$, $t_X=j_{N/M,S_{M/E}K}$, $s_X=j_{N/E,K}$, $A_X=a^s_{N,M,E,K}$, $B_X=a^p_{N,M,E,J_EK}$, and use the analogous symbols for $Y$. The scalar cocycle says $s_XJ_N(A_X)=B_XP_{N/M}(r_X)t_X$. Write $\phi_M(u)=r_YJ_M(u)r_X^{-1}$. Since $u_N=A_YS_{N/M}(u)A_X^{-1}$, substitution gives
$$\phi_N(u_N)=B_YP(r_Y)t_YJ_N(Su)t_X^{-1}P(r_X)^{-1}B_X^{-1}=B_YP(\phi_M(u))B_X^{-1}=(\phi_M(u))_N.$$
The middle equality is naturality of $j_{N/M}$ at $u$. This proves the asserted commuting square on actual Hom transition maps, rather than on abstractly identified Hom groups.

3. At a fixed common field $M$, $J_M$ is fully faithful by the assumed equivalence, and conjugation by $r_X,r_Y$ is invertible. Thus $\phi_M$ is a bijection with inverse
$$\psi_M(v)=(J_M|_{\operatorname{Hom}})^{-1}(r_Y^{-1}vr_X).$$
The preceding transport identity and injectivity of $\phi_N$ give $\psi_N(v_N)=\psi_M(v)_N$. Therefore both maps respect eventual equality of representatives, the equality relation in the two pair categories. They descend to maps $[M,u]\mapsto[M,\phi_M(u)]$ and $[M,v]\mapsto[M,\psi_M(v)]$ on the two Hom colimits. Their composites are the identity on every representative. This proves both full faithfulness and the claimed inverse Hom-colimit maps without assuming any transition functor is faithful.

4. For any target pair $(E,A)$, choose $K\in\mathcal C^s_E(W)$ and a finite-stage isomorphism $J_EK\simeq A$ using essential surjectivity of $J_E$. Its class at $E$, with inverse represented by the inverse finite map, is an isomorphism $J_W(E,K)\simeq(E,A)$. Together with the preceding Hom bijections, [lem-trf-fully-faithful-ess-surj-equivalence] now makes $J_W$ an equivalence (take a common sufficiently large universe for both pair categories). The object choices and Hom inverses describe its quasi-inverse: choose such a preimage for each target pair and lift morphisms uniquely through the Hom bijections after conjugating by these chosen isomorphisms.

5. The functor is additive by step 1. For $\lambda\in\Omega$ and $f=[M,u]$, choose a finite $N$ containing $M$ and $\lambda$. The scalar action on both pair categories is represented by $\lambda u_N$. Since $J_N$ is $N$-linear and composition in its target is bilinear,
$$\phi_N(\lambda u_N)=j_YJ_N(\lambda u_N)j_X^{-1}=\lambda\phi_N(u_N).$$
Step 2 identifies this with the transport of $\phi_M(u)$, so $J_W(\lambda f)=\lambda J_W(f)$. The inverse Hom bijections are also $\Omega$-linear: apply the injective linear map $J_W$ to the proposed additive and scalar identities. Conjugating these inverse Hom maps by the chosen object isomorphisms preserves linearity, so the quasi-inverse is linear too.

6. At stage $E$, the identity comparison $j_{E/E}=1$ makes $J_W\iota^s_E=\iota^p_EJ_E$ on objects and arrows. Let $\delta_E:J_E(-[1])\xrightarrow{\sim}(J_E-)[1]$ be the given exact-functor shift comparison. Compatibility of $j$ with shifts is exactly the transformation-compatibility equation for the families $J_E\circ[1]$ and $[1]\circ J_E$. Apply the compatible-transformation clause of [lem-sbc-coherent-pair-functor-descent]: the classes $[E,\delta_{E,K}]$ give the shift comparison of $J_W$, with inverse given by their inverse classes. Thus the comparison restricts to the specified finite-stage comparison, for the actual pair shifts.

7. A distinguished source triangle is isomorphic to the inclusion of a distinguished triangle $D$ over a finite field $M$, by [def-weil-algebraically-closed-coefficients]. Step 6 identifies its image with the inclusion of $J_M(D)$ using the given shift comparison. The assumed exactness of $J_M$ makes this triangle distinguished, so the target definition [def-weil-pbc-qbar-category], whose distinguished triangles are those isomorphic to the common-stage cone triangles of [def-weil-pbc-common-stage-cones] (with $T_{M/M}=\operatorname{id}$, a stage-$M$ distinguished triangle is its own cone triangle there), shows that $J_W$ preserves distinguished triangles. This proves exactness directly on the raw pair categories.

8. Conversely, let a triangle $D$ in the source have distinguished image. In the target pair category choose a finite-stage distinguished triangle $A$ and an isomorphism $J_WD\simeq\iota^p_M A$: by [def-weil-pbc-common-stage-cones] $J_WD$ is isomorphic to a common-stage cone triangle of some $[M,u]$, and the classes $[M,\operatorname{id}]:(E,K)\simeq(M,T_{M/E}K)$ identify that triangle with $\iota^p_M$ of the stage-$M$ cone triangle of $u$, the third arrow by the shift comparison $\sigma_{M/E}$. Choose an exact quasi-inverse $R_M$ of the assumed exact equivalence $J_M$. Then $R_M A$ is distinguished, and $J_MR_M A\simeq A$ as triangles, with the exact-equivalence shift comparisons. Using step 6 gives $J_W\iota^s_M R_M A\simeq J_WD$. Lift the three component isomorphisms and their inverses through the Hom bijections of step 3. Faithfulness, together with the shift comparison, lifts all triangle commutativity equations and the inverse identities. Hence $D\simeq\iota^s_M R_M A$, so $D$ is distinguished by the source definition. Applying this to the chosen quasi-inverse proves reverse exactness. This argument uses only finite-stage exact equivalences already assumed, and never a Karoubi completion.

9. Fix $h:U\simeq T$. To compare the actual composites, set $A_E=J_{U,E}F^s_{h,E}$ and $B_E=F^p_{h,E}J_{T,E}$. In the orientation required by the pair-functor lemma their scalar comparisons are
$$a_{L/E}=J_{U,L}(\alpha^s)\circ j_{U,F^s_{h,E}K}^{-1},\qquad c_{L/E}=F^p_{h,L}(j_T)^{-1}\circ\alpha^p_{J_{T,E}K}.$$
Indeed both start with $P_{U,L/E}$ applied to the stage-$E$ composite and end with the stage-$L$ composite applied to $S_{T,L/E}$. The actual source pullback representative formula is specified in [def-weil-derived-pullback-tensor-hom]; the target scalar/pullback comparisons and their unit and tower equations are specified in [prop-weil-pbc-scalar-extension], and the actual target common-stage pullback $F^p_h$ is by [prop-weil-pbc-descent-functors] the functor descended from $(F^p_{h,E},\alpha^p)$ by the same conjugation formula $[M,u]\mapsto[M,(\alpha^p)^{-1}F^p_{h,M}(u)\alpha^p]$ as in the pair-functor lemma. Together with the assumed $j$ cocycle these give the composite stage families. The composition clause of [lem-sbc-coherent-pair-functor-descent] identifies their descended functors with the actual $J_UF_h^s$ and $F_h^pJ_T$, respectively.

10. Multiply the assumed mixed scalar square on the left by $F^p_{h,L}(j_T)^{-1}$ and on the right by $j_{U,F^s_{h,E}K}^{-1}$. With the comparisons just defined, it becomes
$$b_{h,L,S_TK}\circ a_{L/E}=c_{L/E}\circ P_U(b_{h,E,K}).$$
This is exactly the compatible-transformation hypothesis of [lem-sbc-coherent-pair-functor-descent], so the components $[E,b_{h,E,K}]$ define a natural transformation $b_h:A\Rightarrow B$. Each is invertible: $[E,b_{h,E,K}^{-1}]$ is its two-sided inverse since the composites are represented by the finite identity maps. Thus it is a natural isomorphism with precisely the claimed components.

11. For completeness, the naturality calculation uses the mixed square at both endpoints, not only at objects with field label $L$. For $u:S_{T,M/E}K\to S_{T,M/F}H$, suppress $h$ and write $a_E,c_E,a_F,c_F$ for the stage-$M$ comparisons. The representative of $B[u]\circ b_{E,K}$ is
$$c_F^{-1}B_M(u)c_EP_U(b_{E,K})=c_F^{-1}B_M(u)b_{M,S_EK}a_E=c_F^{-1}b_{M,S_FH}A_M(u)a_E=P_U(b_{F,H})a_F^{-1}A_M(u)a_E.$$
The middle equality is finite-stage naturality of $b_M$; the first and last use step 10. The last expression represents $b_{F,H}\circ A[u]$. Equality of these representatives proves naturality for arbitrary common-stage arrows.

12. The identity and composition clauses of [lem-sbc-coherent-pair-functor-descent] preserve composite stage families and equations of compatible transformations. Apply them to each finite identity or composition equation for $b$, retaining the actual pullback associators. Shift equations are equations of the shift comparisons descended in step 6, and scalar equations use the same compatible transformations and the scalar calculation of step 5. Thus every equation stipulated in the question descends; no new finite equation is being asserted. Finally [def-fd-coefficient-comparison-datum] asks, at common stage, for the field-preserving conjugation functor, its linearity, exactness in both directions and its induced shift comparisons, all proved in steps 1–8. [def-fd-pullback-comparison-datum] asks for the common-stage transformation of the two actual composites, with its prescribed finite components and mixed square, proved in steps 9–11. Under the stipulated normalized integral and finite rational data these supply exactly those common-stage fields; this does not construct the integral lifts.

## Second reading by NA

I opened the saved node, its complete Lean module, the node's blueprint source,
the current dependency records, and the relevant dependency declarations during
this repair. I compared the saved node with the live node: every field outside
`lean` is identical. The blueprint final sentence names the PBC coefficient
category; the detailed auxiliary assertion and its twelve-step argument are
those in this DAG node, not an extra theorem found in the blueprint sentence.
This reading found the needless dependency-record replacement (removed above).
It found no mathematical mismatch requiring a change to the item module.

1. Global hypotheses: the node fixes a finite-field datum and a prime distinct
   from its characteristic. `fdCommonStageComparisonDescent` binds
   `_D : FiniteFieldDatum.{d}` and `_hl : l ≠ _D.p`; the surrounding binders
   are `(l : ℕ) [Fact l.Prime]`, `(Ω : Type w) [Field Ω]`,
   `[Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`. The argument never uses an
   extra structure map from the scheme to the finite field. The remaining
   descent assertions are more generally independent of that unused datum;
   they do not impose a different characteristic condition.

2. Allowed schemes: `T : Scheme.{u}`, `[IsNoetherian T]`,
   `[dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]` and
   `[iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]` render exactly
   Noetherian, finite dimension and local invertibility. The pullback section
   repeats these assumptions for `U`. The coefficient theorem can be applied
   to any allowed `W`; it does not select only a finite-type or nonempty class.
   The datum universe `d`, scheme universe `u` and closure universe `w` remain
   independent. The supplied small coefficient models allow this independence.

3. Finite categories and equivalences: the endpoints of `J` are precisely
   `GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T` and
   `pbcScalarSystem l Ω T dT.out iT.out`. These use the recorded framework
   and PBC raw rationalizations, respectively. `J.Φ E` is the finite functor;
   `hequiv`, `hadd`, `hlinear` and `hexact` assert its equivalence, additivity,
   `E.val`-linearity and exactness. The `[∀ E, (J.Φ E).CommShift ℤ]` binder
   supplies the finite shift comparisons; `hshift` makes the scalar comparisons
   commute with them. No finite equivalence is replaced by an arbitrary map.

4. Scalar coherence and normalization: I read the full `StageSystem.Morphism`
   signature in `WeilConjectures.CategoryTheory.StageSystem.Functor`.
   Its `β h : J.Φ E ⋙ P.T h ≅ S.T h ⋙ J.Φ L` is the inverse of the node's
   `j`. Substitution into `J.coh` gives the node's displayed cocycle with
   both actual scalar associators. Repeated inclusions are quantified, so
   the unit normalization is included relative to the actual scalar unitors.
   The framework tensor transitions use those unitors rather than a new
   strictly identified identity transition. The statement retains that
   existing interface and its normalization, as the accepted review records.

5. Literal-pair functor: the conclusion of `fdCommonStageComparisonDescent`
   is an equivalence of `generalAlgebraicallyClosedConstructibleCategory`
   with `pbcQbarCategory`, with `e.functor = J.functor`. I checked the body
   of `Morphism.functor`: it sends `(E,K)` to `(E,(J.Φ E).obj K)` and maps
   a common-field representative using `J.mapAt`. The body of `mapAt` is
   source beta, finite functor map, inverse target beta. Since beta is inverse
   j and Lean composition is written left to right, this is exactly the
   node's conjugation formula at both endpoint field labels. Neither endpoint
   is a Karoubi envelope. The source and target are distinct recorded pair
   constructions; keeping NM's node record does not identify these types.

6. Equivalence, scalar action, shifts and triangles: the conclusion asserts
   additivity and `Linear Ω` for both `e.functor` and `e.inverse`. It binds
   their integer shift structures explicitly and asserts `IsTriangulated`
   in both directions. Its finite-component `HEq` pins the forward shift
   to the finite shift followed by the actual inclusion shift. Its final
   `distTriang` iff states reflection as well as preservation. Thus exactness
   is not merely asserted for some unspecified shift, and no common-stage
   triangle or reverse direction is omitted.

7. Hom descent and finite inclusions: `fdCommonStageHomDescent` quantifies
   all endpoint pairs, all common fields `M`, and every further `M ≤ N`.
   Its first conjunct is `Function.Bijective J.mapAt`; its second is the
   actual target `tr` / source `tr` commuting square. Its third supplies
   `(A ⟶ B) ≃ (J.functor.obj A ⟶ J.functor.obj B)` with forward map
   `J.functor.map` and the `mkHom` representative formula. The `Equiv`
   supplies the inverse on quotient Homs, so no transition-faithfulness
   assumption is needed. The last conjunct gives the finite-inclusion
   comparison. I checked the advisory about its `Nonempty` formulation:
   the upstream `J.ιCompFunctorIso E` has identity components, as stated
   by `ιCompFunctorIso_hom_app`; `functor_map_ι` fixes its arrow formula.
   The retained theorem asserts existence of that comparison and the
   already specified functor fixes its canonical realization. I have not
   altered this accepted signature to add the advisory component equation.

8. Descent of equations: `fdCommonStageComparisonEquations` binds three
   coherent stage families and compatible finite transformations. It states
   descent of componentwise equality, the identity transformation and vertical
   composition. In the upstream API, `descNatTrans` has the finite-inclusion
   components, while `Morphism.comp` and `functorCompIso` retain the actual
   composite comparisons. Hence the result applies also to the compatible
   composite, shift and scalar families in the node: it transfers equations
   assumed at finite stages and does not assert any new finite equation.

9. Actual pullbacks: `fdFrameworkPullbackFamily_existsUnique` fixes every
   finite functor by `HEq` to `rationalDerivedPullback` and every beta component
   by `HEq` to `commonStagePullbackComparison`; it identifies the descended
   functor with `commonStageDerivedPullback`. Thus the `F`, `sfFinite`,
   `sfBeta` and `sfPair` binders of the mixed theorem describe a family this
   preceding theorem supplies, rather than an extra geometric assumption.
   On the PBC side I opened `PbcQbarCompletedPullback`: its
   `pbcQbarCompletedPull` is exactly `(pbcQbarPullFamily ...).functor`, and
   the latter is normalized by the actual integral pullback and scalar beta.

10. Mixed square and descended isomorphism: `h : U ≅ T` is a scheme
    isomorphism as required. `b` is a `Morphism.Hom` from the composite
    `JT.comp (pbcQbarPullFamily ...)` to `F.comp JU`, and `hb` asserts
    invertibility of every finite transformation. I checked `Hom.comm`:
    substituting the composite betas yields the mixed scalar square, in
    inverse-j orientation. The node writes b in the opposite direction;
    inverting each isomorphism translates between them. The conclusion
    of `fdMixedPullbackDescent` is an `∃!` natural isomorphism between the
    actual common-stage composite functors, with components equal by `HEq`
    to inclusion of the supplied finite component. Inversion gives precisely
    the node's orientation. It is not a bare isomorphism existence assertion.
    The preceding equation theorem transfers the stipulated finite equations.

11. Normalized integral input: I compared `FdFiniteCoefficientComparison`
    field by field with `FdCoefficientComparison` in its owning module.
    `stage`, `family`, `finite_functor`, `finite_shift`, its normalization,
    `scalar_shift`, `ordinary`, `integral_scalar`, `integral_scalar_lift`
    and `chi` are exactly its prefix before `equivalence`. They include
    actual integral transport and the completion chain-map normalization,
    and contain no pair equivalence to be assumed circularly. The helper
    is a data structure with fully written fields and asserts no existence.
    `fdNormalizedCommonStageDescent` returns the full recorded datum with
    the same stages, family, finite shifts, ordinary transport and integral
    scalar comparisons. The other retained proof fields are propositions.

12. Common-stage pullback fields and scope: `fdNormalizedPullbackDescent`
    accepts the recorded finite `FdPullbackComparison`, the actual framework
    family and mixed transformation, with `components` identifying its
    finite rational maps. It returns `FdPullbackSystem` preserving `finite`,
    `sfFamily` and `mixed`; its `pair` and `pair_components` fields are exactly
    the common-stage output required by the final sentence. I read those
    fields in `FdCoefficientComparisonSystem`. The node only claims to fill
    common-stage fields under the stipulated normalized data; it does not
    claim to construct a simultaneous integral realization system here.

Edge-case rereading: all finite-field quantifiers include equal/repeated fields;
`h` includes identity scheme isomorphisms; zero objects/arrows and the empty
scheme are admitted. The local invertibility assumption does not impose base-field
invertibility on an empty scheme. Different source and target field labels both
appear in `mapAt`, and the fixed `Ω`-scalar action uses the existing finite
compositum construction. I found no omitted edge case or new hypothesis.

The retained module has seven named theorems with `sorry` as their whole proofs
and one structure with real data fields. Their docstrings include sources and
proof plans. No new node, statement correction, dependency module, proof, or
replacement definition is introduced in this repair. H13 is repaired by the
removed dependency node file; H11 is repaired by this explicit second reading.

Validation: the saved packet passed the initial server dry run at `6b0b99950e4`
without a push. The repaired packet is compiled and dry-run again before delivery;
its resulting checks and commit are recorded by the delivery wrapper.
