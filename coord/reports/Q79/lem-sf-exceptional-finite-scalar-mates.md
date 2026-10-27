## Worker report

The module `Sheaf.Paper.ExceptionalFiniteScalarMates` states
`WeilConjectures.ExceptionalFiniteScalar.exceptionalFiniteScalarMates` with one
`sorry`. All other declarations are real constructions, abbreviations, instances
from published theorems, or records specifying the conclusions of this node.
No statement correction, dependency repair, or new independent notion is needed.
The node copy changes only `lean`.

The theorem is an existence statement for the complete normalized construction,
not an assumption of the desired preservation or invertibility. Its `Construction`
record exposes every requested conclusion. Its support records are finite-stage
packaging of the node’s own data, not replacement definitions of constructibility,
Tor amplitude, scalar extension, compact support, or the exceptional functor.

Hypotheses, one by one:

- `D : FiniteFieldDatum.{u}` is the recorded finite-field datum, including its
  algebraic closure `D.k`. `l`, `[Fact l.Prime]`, and `_hl : l ≠ D.p` give the
  prime and invertibility condition. The underscore only suppresses the unused
  proof-binder linter; the hypothesis remains part of the theorem.
- `E L : Type u`, their field structures, `Algebra (Padic l)` structures and
  `FiniteDimensional (Padic l)` instances are the two finite coefficient fields.
  `Padic.coefficientExtensionRing l E (n + 1)` and its `L,m` counterpart are
  exactly the recorded valuation-ring quotients. Natural `n,m` shifted by one
  parametrize every positive level, including level one.
- `a : A →+* B` is every unital map between those finite rings. There is no
  flatness, injectivity, surjectivity, residue-field or generating-list condition.
- The two `Scheme.{u}` objects, their `Over (Spec (.of D.k))` structures and
  `LocallyOfFiniteType`/`QuasiCompact` structure morphisms give precisely the
  finite-type k-schemes. There is no absolute separatedness assumption.
- `f`, `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f`
  give the separated finite-type k-morphism. `c : Compactification f` retains
  the specified compactification; none is subsequently reselected.

Clauses, one by one:

- The actual category is `finiteTorConstructibleCategory`, with full inclusion
  `(finiteTorConstructible ...).ι`. Its predicate is the recorded bounded
  intrinsic constructibility intersected with finite pro-etale Tor amplitude.
  It is not a new abstract category or a predicate asserted equivalent to it.
- `Operation.left` realizes `F` as the recorded `sfIntrinsicCompactSupport c A`.
  `Operation.right` realizes `G` as `exceptional A c`. The latter is only the
  canonical intrinsic-coordinate realization of the recorded
  `ProEtale.sfFiniteExceptionalAt (ULift A) c`, whose formula is
  `Rν_* ⋙ f^×_{c,A} ⋙ ν^*` in Lean’s left-to-right composition convention.
- `etaleAdjunction` uses the published ordinary-etale adjoint at this exact `c`.
  `Operation.normalized` identifies its full-subcategory Hom bijection, under
  the two realization isomorphisms, with `specifiedExceptionalHomEquiv`.
  This recorded Hom equivalence uses the actual site-comparison unit and
  ordinary-etale adjunction. The bounded-below and origin witnesses in this
  normalization are inputs to the comparison formula, not additional hypotheses
  of the main theorem; these exist for every object of the actual finite category.
  The `CompactSpace Y` argument is available for finite-type Y over a field.
  `unitShift`, `counitShift`, and `leftShiftRealization` retain the transported
  adjunction and its adjoint shifts, rather than allowing a different right shift.
- `Scalar.preserves` says the ambient `pbcDerivedExtend` of the actual constant
  ring map stays in the actual category. `Scalar.torInterval` quantifies over
  every integer pair `r s` and preserves exactly the input Tor interval.
- `restrictScalar` is the literal `ObjectProperty.lift` of the full inclusion
  followed by that ambient scalar functor. Its objects and morphisms are the
  ambient objects and morphisms with membership proofs. `Scalar.scalar_eq` is
  equality of functors with the requested inclusions, and the realization is
  literally `eqToIso scalar_eq`. `Scalar.realizationShift` specifies the inherited
  shift. `Scalar.functor` merely makes that package visible to instance search.
- `Construction.scalarX` and `.scalarY` supply this scalar conclusion at both
  endpoints. `source` and `target` supply the actual F/G restrictions at both
  coefficient rings. Neither is supplied as a hypothesis to the theorem.
- `Construction.q` and `.b` are natural isomorphisms, with the orientations of
  the two displayed comparisons in the node. Their `qShift` and `bShift` are
  compatibility with every integer shift.
- `Construction.q_normalized` identifies the image of q with `leftScalarMap`,
  after the two compact-support realizations. `leftScalarMap` is the actual
  scalar-adjunction mate of the canonical proper/open restriction comparison
  `sfCompactSupportRestriction c a`. The imported
  `FiniteCompactScalar.intrinsicCompactScalarIsoOfOrigin_hom` identifies exactly
  this map with transport of the proper scalar mate followed by open balancing.
  No arbitrary isomorphism replaces that construction.
- `Construction.counit` is the node’s displayed equation in composition order.
  Since the target adjunction is fixed, its Hom bijection makes this exactly the
  transpose of `q.inv` followed by scalar extension of the source counit.
- `Construction.etale` retains the ordinary-etale calculation at `RingHom.ulift a`.
  `EtaleMates.q_normalized` fixes its q to `Etale.compactScalarMap a c`, the proper
  scalar mate followed by the open tensor map. `b_normalized` fixes its b to
  `mateEquiv` of q’s inverse, using those same two chosen adjunctions.
- `restrictionIso` is the canonical right-adjoint-uniqueness isomorphism of the
  scalar/exceptional Hom chain. It is defined from q and the fixed adjunctions,
  rather than posited independently. `EtaleMates.projection_normalized` fixes
  the ordered constant-B projection using `scalarTensorIso`,
  `projectionMapOfCompactification`, and `scalarCoefficientPullbackIso`.
  `EtaleMates.restricted_b` identifies restriction of the B-linear b through
  `restrictionIso` with the transpose of the inverse of this exact projection
  followed by extension/restriction of the same counit. This is the defining
  constant-B exceptional tensor comparison of Zheng Construction 2.26. The
  ordinary-etale data and full-category data share their adjunctions through
  `Operation.normalized`, and share their left map through the canonical
  proper/open transport theorem, so counit uniqueness identifies their right maps.
- `EtaleMates.properShift`, `.openShift`, and `.projectionShift` retain shifts
  for the actual proper scalar mate, open balancing map, and ordered projection.
  The scalar shift instance is the one adjoint to exact termwise restriction.
  The imported canonical pullback/tensor maps and proper/open site comparison
  supply the common flat-model and site-unit identifications. There is no
  independent family of Hom bijections or a free tensor comparison.

Dependency declarations used (read with signatures and documentation):

| Node | Published module / declarations used |
| --- | --- |
| def-weil-finite-field-fiber | `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` |
| def-weil-l-adic-coefficient-extension | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`; underlying ring from `CoefficientExtension` |
| def-weil-scheme-morphism-properties | Convention node; the existing Mathlib `Scheme.Over`, `IsOver`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` |
| def-weil-compactifications-refinements | `WeilConjectures.Compactification.RefinementCategory` and its imported `Defs`: `AlgebraicGeometry.Compactification` |
| def-weil-pbc-proetale-modules | `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: fixed finite-module presentation and canonical realization; intrinsic presentation through `sfIntrinsicDerivedEquivalence` |
| def-weil-finite-tor-amplitude | `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructible`, `finiteTorConstructibleCategory`, `HasProEtaleTorAmplitude` |
| def-compact-support-direct-image-detailed | `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: `Scheme.sfIntrinsicCompactSupport` |
| def-weil-exceptional-inverse-image | Recorded exported declaration `AlgebraicGeometry.ProEtale.sfFiniteExceptionalAt`, imported directly from its owning module `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`; the definition node explicitly retains this finite-stage declaration alongside its larger integral/rational `System` interface |

The module imports stated proof-dependency modules as plain imports. Canonical
comparison interfaces used in its signatures are public imports. In particular,
`SpecifiedExceptionalClassHom` supplies the fixed-site Hom normalization,
`FiniteCompactSupportScalarTransport` supplies proper/open scalar transport,
`EtaleCompactScalarCoherence` supplies the actual ordinary-etale scalar map,
and `EtaleExceptionalConstantTensor` supplies the constant-coefficient maps.
No unpublished operation is assumed and no dependency is redefined.

Edge cases checked against the source and the formulated types:

- Zero complexes, zero morphisms, empty X or Y: the formulas are functorial
  identities and transposes and impose no nonzero or nonempty condition.
- Level one and every higher positive level are covered by successor indexing;
  level zero is excluded exactly as in the node.
- Identity maps and arbitrary composites are raw `RingHom` inputs, with the
  literal restricted functor and equality realization in every case.
- Nonflat `Z/l² → Z/l`, all quotient maps, and ramified coefficient maps are
  included. No claim that restriction preserves finite Tor dimension is made:
  its use in `EtaleMates` is on the entire ordinary derived categories. Zheng
  Proposition 2.29(2) allows the constant complex B without perfection.
- Nonseparated finite-type X,Y are allowed; only f has `IsSeparated`.
- The Tor interval retains the same r,s, not a larger existential interval.
  All variables and the universe are explicitly bound (`autoImplicit false`).
  The intrinsic/fixed comparison uses `ULift` to the existing small-site size
  convention; no equality between site-object and morphism universes is imposed.

Searches for an existing exact statement (2026-10-24):

- `msearch.py ... leansearch "Derived scalar extension on constructible finite Tor etale complexes has exceptional inverse image scalar mates"`: eight hits, including `ModuleCat.ExtendRestrictScalarsAdj.homEquiv_symm_apply` and elementary module change-of-rings results; none states this theorem.
- `msearch.py ... leanfinder "Canonical scalar extension comparison for exceptional inverse image on constructible finite Tor etale and proetale complexes, normalized by adjunction counits"`: eight hits, mainly condensed solid-module counits and generic sheaf adjunctions; no exact statement.
- `msearch.py ... loogle "Adjunction.homEquiv, Functor.CommShift, ObjectProperty.lift"`: zero hits, unknown unqualified identifier; direct source search supplied the category-theory interfaces.
- `msearch.py ... grep "exceptional.*[Ss]calar|finiteScalar|[Ss]calar.*[Mm]ate"`: zero Mathlib hits.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` found the ordinary-etale
  coefficient maps, fixed finite exceptional composite, existing larger coefficient
  system, and proper/open scalar transport used here. The existing system’s
  generated `Allowed` coefficient changes do not state the arbitrary RingHom
  theorem here, and its interface alone does not assert existence of this result.
- `grep -rn "lem-sf-exceptional-finite-scalar-mates" lean/WeilConjectures` and
  search of `dag/lean_names_upstream.json` found no exact upstream declaration.
  DAG/source searches found this node and its consumers, not another exact theorem.

Source reading: current blueprint under `literature/blueprint/latest/`; Zheng
Propositions 2.23, 2.29, 3.16, Construction 2.26, Lemma 5.22 and Proposition 5.24;
the recorded dependency declarations and canonical transport modules. The constant
coefficient restriction is essential: Zheng explicitly warns that the analogous
projection formula for a general sheaf factor can fail. This formulation uses
only the constant coefficient B. No STATEMENT-DISPUTED flag or known node fault.

Validation: the full module compiled with `scompile.py`, both sandbox and library
names, with no errors or unexpected warnings. The prescribed `deliver2.py --no-push` passed preflight and per-file
compilation (dry-run commit `990f0920ab1`; nothing pushed).

## Second reading by Q79

I performed a second pass with the node and final signatures open. The dispatcher
explicitly prohibits starting other agents; this is a self-check, not a claim of
independent group review. The maintainer’s independent review remains separate.
The pass checked every hypothesis and clause in the mapping above. It caught an
initially overbroad scalar package over all schemes and narrowed its use to the
actual endpoints X,Y. It also made the projection shift clause explicit. No
statement or dependency record was changed. In particular the raw RingHom binder,
nonflat case, fixed compactification, literal restriction and same Tor interval
were preserved.

## Returned construction steps 4–7 (verbatim)

4. Put $U_T=\operatorname{Res}_{a,T}$. Derived ringed direct-image composition applied to the two factorizations of the same ringed-topos map gives $U_YRp_{c,B,*}\cong Rp_{c,A,*}U_{\overline X}$. Open extension by zero commutes with $U$ termwise: it changes only the ring action on the open and both sides are zero off the open. Consequently $h:U_YF^e_B\cong F^e_AU_X$ is the canonical restriction comparison. For any $N\in D(Y_{\mathrm{et}},B)$ and $K\in D(X_{\mathrm{et}},A)$ the scalar adjunction, the two exceptional adjunctions and $q^e_a$ give natural bijections
$$\operatorname{Hom}_A(K,U_XG^e_BN)\cong\operatorname{Hom}_B(S_XK,G^e_BN)\cong\operatorname{Hom}_B(F^e_BS_XK,N)\cong\operatorname{Hom}_B(S_YF^e_AK,N)\cong\operatorname{Hom}_A(K,G^e_AU_YN).$$
Yoneda gives a canonical isomorphism $d_N:U_XG^e_BN\cong G^e_AU_YN$. Explicitly $d_N$ is the transpose of $F^e_AU_XG^e_BN\xrightarrow{h^{-1}}U_YF^e_BG^e_BN\xrightarrow{U_Y\epsilon^e_{B,N}}U_YN$. Indeed, following $\mathrm{id}$ through the chain, its image is $U_Y(\epsilon^e_{B,N}F^e_B(c)\,q^e)\circ\eta$, with $\eta:x\mapsto x\otimes1$ the scalar unit and $c:x\otimes b\mapsto b\,x$ the scalar counit. By the proper coefficient theorem and the open balancing map, $h\circ U_Yq^e_K$ is the projection map $P_K:B_Y\otimes^L_AF^e_AK\to F^e_A(B_X\otimes^L_AK)$. Naturality of $h$ then rewrites the image as $U_Y\epsilon^e_{B,N}\,h^{-1}\,F^e_A(U_Xc)\,P\,\eta$. Since $P$ is natural in the constant factor and is the identity for the unit $A$, $F^e_A(U_Xc)\,P\,\eta=\mathrm{id}$.

5. For $L\in D(Y_{\mathrm{et}},A)$ define $b^e_{a,L}$ to be the $F^e_B\dashv G^e_B$ transpose of
$$F^e_BS_XG^e_AL\xrightarrow{(q^e_{a,G^e_AL})^{-1}}S_YF^e_AG^e_AL\xrightarrow{S_Y\epsilon^e_{A,L}}S_YL.$$
The adjunction bijection gives naturality in $L$ and exactly
$$\epsilon^e_{B,S_YL}\,F^e_B(b^e_{a,L})\,q^e_{a,G^e_AL}=S_Y\epsilon^e_{A,L}.$$
Under $d_{S_YL}$ and $U_TS_T(-)=B_T\otimes_A^L(-)$, its restriction has $F^e_A$-transpose
$$F^e_A(B_X\otimes_A^LG^e_AL)\xrightarrow{P^{-1}}B_Y\otimes_A^LF^e_AG^e_AL\xrightarrow{1\otimes\epsilon^e_{A,L}}B_Y\otimes_A^LL.$$
Indeed substitute the transpose formula for $d$ from step 4 into the preceding counit equation; $U_Yq^e$ is $P$, since its proper factor is precisely the ordered projection by the proper coefficient theorem and its open factor is the balancing map. Naturality of $h$ and the counit equation replace $U_Y\epsilon^e_B\,U_YF^e_B(b^e)$ by $U_YS_Y\epsilon^e_A\,(U_Yq^e)^{-1}$. This is the displayed formula. It is the defining transpose of the exceptional constant-$B$ tensor map. The constant-tensor theorem applies to $B\in D(A\text{-}\mathrm{Mod})$ without requiring perfection or bounded projective dimension, so this restricted map is invertible. Restriction detects quasi-isomorphisms: the cohomology of a cone is unchanged as an abelian sheaf. Hence the $B$-linear map $b^e_a$ is invertible.

6. The finite-operations theorem supplies the actual constructible restrictions of $F_R,G_R$, their adjunction and their adjoint shift structures, without absolute separatedness. Steps 1–2 apply both to its inputs and to $F_RK,G_RL$, so every endpoint of $q,b$ lies in the stated full categories. Use constructible origin and the invertible bounded-below site-comparison unit to transport $q^e,b^e$ through $\nu^*$ and $R\nu_*$. The compact-support comparison identifies $\nu_Y^*F^e_R$ with $F_R\nu_X^*$; the exceptional realization is $G_R=\nu_X^*G^e_RR\nu_{Y,*}$. Its unit and counit are precisely those of the transported adjunction. Applying the equivalence to the equation in step 5 therefore gives
$$\epsilon_{B,T_{a,Y}L}F_B(b_{a,L})q_{a,G_AL}=T_{a,Y}(\epsilon_{A,L}).$$
Fullness identifies the transported arrows with natural transformations on the actual full subcategories, and full faithfulness makes this the unique transpose there.

7. For the realization of $q$, expand the compact-support site comparison into its two factors. The proper factor is the counit-normalized direct-image mate, not an unspecified site isomorphism. The open factor is the termwise comparison $\nu_{\overline X}^*j^e_!\cong j^p_!\nu_X^*$. Substitute their defining counit and open-unit transposes into step 3. The adjacent site units cancel with the site counits, and the remaining proper transpose is the scalar extension of the same proper counit followed by the same open balancing map. The tensor/pullback comparison identifies the intervening tensors on K-flat models. Thus this transport is exactly the pro-etale proper scalar-adjunction mate followed by the open tensor map. The counit equation of step 6 then identifies $b$ with its required normalized transpose; no second choice of Hom bijections is introduced. The restriction description in step 5 transports to etale-origin objects using these same identifications and site units.

