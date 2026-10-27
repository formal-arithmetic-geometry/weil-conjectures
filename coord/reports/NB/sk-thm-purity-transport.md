## Worker report

The main module `Sheaf.SecSmoothPurity.Transport` states smooth purity, its corrected
étale specialization, and its integral curve specialization. Proofs are postponed
with `sorry`. The supporting modules give real canonical constructions or explicit
normalization predicates; they do not select an arbitrary purity map or trace.

Clause and hypothesis audit:

- The standing finite-field datum is `D : WeilConjectures.FiniteFieldDatum` and
  `[Fact ell.Prime]`, with `hEll : ell ≠ D.p`. `SmoothDatum D` records schemes over
  `Spec D.k`, their separated finite-type hypotheses, a morphism over that field,
  its relative dimension, and a compactification. Smoothness is the recorded
  `AlgebraicGeometry.SmoothOfRelativeDimension`. The extra displayed finite-type
  and quasi-compact instances on the morphism follow in this geometric setting;
  they do not restrict the class of morphisms in the source.
- All six coefficients are constructors of `Coefficient ell`. `finite` permits
  every finite commutative ring annihilated by a positive power of ell, with no
  field, regularity, reducedness, nonzero, or flatness assumption. These are small
  presentations of finite rings. `integral` and `rational` use the fixed
  `PadicAlgCl.FiniteIntermediateField`; `closure` is the recorded finite-stage
  condensed algebraic closure. Integral and field coefficients use continuous
  functions, not discrete non-torsion constant sheaves.
- `Coefficient.ctf` is `ConstantModelConstructibleFiniteTor` and `property` is its
  bounded-constructible/finite-Tor predicate. No replacement morphisms, tensor
  product, or constructibility condition is imposed.
- `Coefficient.firstLine` is scalar extension of the actual `tateModule`, not a
  free rank-one module with a chosen basis. Its nonnegative powers and the shift
  `2 * (d : ℤ)` define `derivedLine`. Only nonnegative powers occur because the
  pure smooth dimension is a natural number. Finite coordinates identify it with
  the existing Cartier root line by its actual root projection and scalar unit.
  The root, scalar, tensor-power and shift comparisons specify the ordinary and
  derived maps used in the compatibility equations.
- `Coefficient.smoothSource` is literally derived pullback followed by tensor
  with that shifted line. `support` is the restriction of the actual
  `CondensedRing.rightDerivedLowerShriekOfCompactification`. The family supplies
  membership proofs and an adjunction for these literal functors.
- `BrownComparison` quantifies over a specified Brown adjoint and adjunction on
  the recorded localizing closure. It asserts preservation of the finite-Tor
  category, a restricted adjunction with the same ambient Brown counit, and a
  **unique natural isomorphism** from the explicit source to that restriction.
  `CounitCompatible` is the actual equation `F.map gamma ≫ epsilon = trace`.
  Thus the result identifies the specified right adjoint; it does not introduce
  another unconstrained exceptional functor.
- `ScalarCompatible` states the equation for scalar extension of the same trace,
  with the proper direct-image coefficient mate, open-extension comparison and
  normalized source scalar comparison. It includes nonflat finite changes and
  the existing listed integral, rational and closure coefficient maps.
- `BaseChangeCompatible` states the trace equation through the canonical
  proper/open base-change map and the source's root-normalized line comparison.
  The open exchange is fixed by requiring its inverse to be the published arrow.
- `CompositionCompatible` states the two-successive-counits equation through the
  source compositor and compact-support compositor. The proper/open interchange
  satisfies the exact restriction equation defining the published
  `compositionInterchangeIsNormalized`.
- `AffineNormalized` evaluates the **same** family at the actual affine-line
  projection and unit. Its equation uses the standard projective compactification,
  the sectionwise finite encoding, fixed site comparison, the open counit and
  `Etale.projectiveLineTrace`, whose Kummer Chern generator maps to +1.
  `FiniteLineCoordinates` fixes the line and unit comparisons on roots and
  constant generators, preventing an arbitrary scalar rescaling. Scalar
  compatibility transports this finite normalization to integral, rational and
  common-stage coefficients.
- `etale_purity_transport` applies dimension zero. It does not infer that an
  arbitrary dimension supplied for an empty source equals zero. It compares the
  actual derived pullback with the specified exceptional restriction.
- `curve_purity_transport` uses a smooth structure map of relative dimension one,
  evaluates the same integral statement on the coefficient unit, identifies the
  result with the actual `tateModule C ell` shifted by two, and states vanishing
  of every other cohomology degree, namely all degrees different from -2.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField`, the actual compactification and
  derived compact-support framework. The theorem is presented uniformly for a
  displayed compactification; it therefore includes the chosen one.
- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.FiniteFieldDatum` and the
  finite-field conventions. No finite coefficient is required to be a quotient
  of a valuation ring.
- `Sheaf.Paper.ProfiniteFiniteConstantLocalModel`, through the public
  `SectionwiseFiniteConstantLocalModel` interface:
  `ConstantModelConstructibleFiniteTor`, `constantModelBoundedConstructible`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `SmoothOfRelativeDimension`; the recorded étale notion is `Etale`.
- `Sheaf.Paper.LocalizingExceptionalAdjoint`:
  `localizingClosureProEtale`, the literal body of `localizingLowerShriek`, and the Brown adjunction
  interface of `exists_localizingExceptionalAdjoint`.
- `WeilConjectures.TateTwist.ProEtale`: `tateModule`, `tateModuleLevel`,
  `tateModuleSystem`, and `coefficientMap`. These are the actual root-limit and
  relative scalar constructions. `Sheaf.Paper.CartesianCoefficientTwists`
  supplies the ordinary canonical inverse-image framework.
- `Sheaf.SecSmoothPurity.FiniteGeneralRing` was read for its arbitrary finite-ring
  conclusion and its existing Cartier finite-line interface. The normalization
  here uses `geoCartierLine`, `geoCartierProRootMap`, and the corresponding
  `Etale.ordinaryFiniteLine`, rather than a new finite twist.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` was read: its recorded
  integral twist is in the completed sheaf-module category, and its rational and
  closure twists are in the intrinsic localization/common-stage categories.
  Those are comparison models, not literal internal condensed-module categories.
  The present coordinate interface keeps the root-tower line in the actual
  condensed category, where the statement is made. It does not identify a
  completed category with a discrete constant category or introduce a basis.
- `Sheaf.Paper.IntegralModels.integral_models`,
  `Sheaf.Paper.RationalLocalizedHom.RationalLocalizedHom.rationalLocalizedHom`,
  and `Sheaf.Paper.FiniteCoefficientDescentTwoColimit.finiteCoefficientDescentTwoColimit`
  were read as the context's comparison results. Their completed, localized and
  finite-stage categories are not substituted for the ambient condensed category
  in this statement. They supply the proof route described in the main docstring.
- Existing canonical finite encoding and site comparison ingredients are in
  `FiniteDiscreteCoefficientEncodingData`, `FiniteDiscreteCondensedRing`,
  `CanonicalCompactSupportSiteComparison` and `ComparisonConstantGenerator`.
  The scalar pullback comparison is the actual scalar-unit mate
  `scalarSixPullHom` from `Sheaf.SixFunctors.ScalarSixDefinitions`; direct-image and support maps here are
  its actual adjunction mates, without importing the downstream rigidity proof.

Edge cases checked: dimension zero; empty source and empty base; the zero ring;
nonregular rings such as Z/ell²; arbitrary positive annihilating exponent; the
zeroth tensor power; K=0; identity coefficient changes; the bottom finite
subextension E=Q_ell; ramified extensions; arbitrary allowed base change; the
cohomological sign [2] giving degree -2. No disputed assertion or new correction
of the item is introduced. The existing maintenance correction is preserved.

Searches: LeanSearch for “canonical normalized root Tate coefficient pullback
scalar extension compact support adjunction counit equations” returned eight
ordinary ModuleCat/locally-constant adjunction counits. Loogle for
`CategoryTheory.Adjunction.rightAdjointUniq` returned the generic uniqueness
isomorphism and eleven laws; these are ingredients, not this theorem. LeanFinder
for smooth purity and for the scalar/Tate compatibility package returned scheme
smoothness and condensed monoidal interfaces, with no matching statement. Grep
of Mathlib, WeilConjectures and Sheaf for `PurityTransport`,
`smooth_purity_transport`, `AffineNormalized`, `ScalarLineCoordinates` and
`LinePullCoordinates` found no such interface. Upstream blueprint-marker hits
were read: `derivedCompleteIntegral_rightDerivedUpperShriek` only preserves
completeness in a discrete étale category, and `SmoothPurity/Defs` concerns the
finite formalism. DAG search found no new owner ids; `blueprint_refs.py search
"normalized root Tate"` returned zero nodes. Exact queries/results are recorded
in each new node's `mathlib_searches`.

## Second reading by NB

This dispatcher assignment prohibits starting another agent and specifies the
maintainer's independent review of the delivery. This section is a second pass
by the same worker, not a claim of independent human or agent review.

With the node and declarations open, the pass checked each clause listed above.
It found and repaired: an unnormalized finite unit comparison; finite line
comparison needing the actual scalar unit and root projection; an overly broad
upstream import chain; a missing relative-dimension-one instance for affine
space; and finite encoding elaboration details. Compatibility equations all
refer to the single adjunction family. The Brown natural isomorphism has the
correct direction and uniqueness refers to its counit equation. The integral
curve statement has degree -2, not +2. No item statement text was changed.
The independent mathematical review remains the maintainer's delivery review.

## New nodes

`def-pur-transport-adjunction-family`: Use [def-pur-transport-geometric-indices]. An adjunction family assigns an explicit adjunction to every admissible coefficient presentation and every smooth geometric index. Its Brown comparison property means that for every specified right adjunction to the same compact-support functor on the localizing closures, the right functor preserves $P_c$, its restriction has an adjunction whose counit is the underlying Brown counit, and there is a unique natural isomorphism from the family's explicit source to that restriction compatible with those two counits.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-adjunction-restrictions`: Use [def-pur-transport-concrete-coefficients], [sk-prop-sf-existence], [sk-def-sfb-constructible]. Write $P_c(X)$ for the intersection of bounded finite-constant-model constructibility and finite Tor amplitude, and $\mathcal L_c(X)$ for its recorded localizing closure. The inclusion $P_c(X)\to\mathcal L_c(X)$ is the full-subcategory inclusion. Given proofs of preservation, support is the full-subcategory restriction of the actual compactification functor $R\bar f_*j_!$, source is the restriction of $J_{f,c,d}$, and the exceptional functor is the restriction of the specified Brown right adjoint on $\mathcal L$. For two adjunctions with the same left functor, an isomorphism of right functors is counit-compatible precisely when applying the left functor to it and then the second counit gives the first counit at every object.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-affine-counit-normalization`: Use [def-pur-transport-affine-integration], [det-sp-finite-general-ring]. The affine normalization property of an adjunction family is the following equality for every finite commutative ring killed by a positive power of $\ell$ and every scheme $Y$ in the standing setting. Its counit for the affine-line projection, evaluated on the coefficient unit, after the fixed sectionwise encoding and unit comparison equals: compact-support encoding comparison, compact support of the canonical source-on-unit and root-normalized finite-line comparisons, the recorded compact-support site comparison, and the site image of ordinary affine integration. The finite line and unit coordinates satisfy their generator normalizations; invertibility and bounded-below witnesses are conclusions of the property. Together with the scalar counit property this is the normalization of the integral, rational and closure family.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-affine-index`: Use [def-pur-transport-geometric-indices]. For every separated finite-type $k$-scheme $Y$, the affine-line geometric index is $\mathbb A^1_Y\to Y$ with dimension one, structure map the projection followed by that of $Y$, and its actual standard projective-line compactification. The finite-type, quasi-compactness, separation and pure relative dimension structures are those supplied by this construction.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-affine-integration`: Use [def-pur-transport-affine-index], [def-pur-transport-finite-derived-line-coordinates], [def-pur-transport-finite-support-encoding]. For a finite ring $A$ killed by a positive invertible integer $N$, define ordinary affine integration as the direct image by the projective-line projection of: open extension of the inverse normalized pullback comparison on the shifted finite line, followed by the open adjunction counit. Then apply the existing projective-line trace, normalized so that the Kummer Chern generator maps to $+1$. This map has target the ordinary constant coefficient module in degree zero.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-canonical-pullback`: Use [def-pur-transport-root-coordinates]. For $f:X\to Y$ with $\ell$ invertible in all residue fields, the integral Tate pullback isomorphism is characterized by commuting with every projection of the root tower, whose finite comparison is pull-normalized on roots. The interface asserts existence of this normalized isomorphism. For an internal ring map $a:R\to S$, define scalar transport of an ordinary pullback isomorphism by the canonical scalar/inverse-image comparison followed by extension of scalars of that isomorphism.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-compact-support-coordinates`: Use [def-pur-transport-source-comparisons]. The existing derived scalar-unit inverse-image mate is invertible; use its isomorphism, whose hom is literally that mate, to define the proper direct-image coefficient mate through the actual exact-pullback/derived-direct-image adjunctions. The compact-support scalar arrow is this proper mate after the canonical open extension coefficient comparison. The direct-image compositor is the right-adjoint conjugate of the exact inverse-image compositor; the open compositor is the unique left-adjoint comparison for inverse-image composition. Given a normalized proper/open interchange, the compact-support compositor is its proper image followed by these proper and open compositors.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-concrete-coefficients`: Use [sk-def-sfb-dc-setting], [def-pur-conventions], [sk-def-sfb-constructible], [def-coefficient-twists-detailed]. Fix a prime $\ell$. A coefficient presentation is one of: a finite commutative ring $A$ killed by $\ell^{n+1}$ ($n\ge0$), $\mathbf Z_\ell$, $\mathbf Q_\ell$, the valuation ring or field of a finite subextension of the fixed $\overline{\mathbf Q}_\ell$, or that algebraic closure. Its condensed ring is respectively continuous functions into the discrete finite ring, the integral or rational topological ring, or the existing finite-subextension-valued closure. Write $R_{c,X}=p_X^*R_c$ on the small pro-etale site and $D_c(X)=D(\operatorname{Mod}_{R_{c,X}})$. Its constructible finite-Tor subcategory is the recorded finite-constant-model subcategory. The canonical map $\mathbf Z_\ell\to R_c$ gives $L_{c,X}=R_{c,X}\otimes_{\mathbf Z_{\ell,X}}\mathbf Z_{\ell,X}(1)$, where the integral line is the existing root-tower limit. Define $L^{(0)}=R$, $L^{(d+1)}=L^{(d)}\otimes_R L$, $T_c(d)=L^{(d)}[2d]$, and $J_{f,c,d}=Lf_c^*(-)\otimes^L T_c(d)$. All rings, coefficient maps, categories and lines are these actual constructions.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-counit-equations`: Use [def-pur-transport-geometric-base-change], [def-pur-transport-compact-support-coordinates]. The base-change property of an adjunction family is the equality between inverse image of its counit and canonical proper/open exchange, followed by compact support of the normalized source comparison and the base-changed counit. The open exchange is required to have inverse equal to the recorded open base-change map. The composition property is the equality between the two successive counits after the normalized source compositor and the composite counit after the compact-support compositor, for every proper/open interchange satisfying its recorded restriction normalization. These are equations for the same family of counits.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-derived-coordinates`: Use [def-pur-transport-tensor-coordinates]. The degree-zero derived tensor comparison for flat module objects is the canonical K-flat tensor comparison, normalized by the ordinary module tensor map. The derived pullback comparison of a shifted degree-zero Tate line is the ordinary inverse-image comparison, followed by the recorded single-object/left-derived comparison and the adjunction-induced shift comparison. The product of shifted derived Tate lines is the even-shift tensor comparison followed by the ordinary line product, so the resulting shift is $2(d+e)$.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-finite-derived-line-coordinates`: Use [def-pur-transport-finite-line-coordinates], [def-pur-transport-unit-coordinates]. Derive the finite unit comparison through the exact encoding and the fixed etale-to-pro-etale constant-sheaf comparison. Derive the finite first-line comparison through the exact encoding, its unit isomorphism and the fixed site comparison, then shift by two using the canonical shift comparisons. The resulting maps identify the same finite unit and shifted finite root line in the actual internal, sectionwise pro-etale and ordinary etale derived categories.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-finite-encoding`: Use [def-pur-transport-concrete-coefficients]. For any finite discrete commutative ring $A$, the map from the constant sheaf to continuous $A$-valued functions is constant functions followed by the sheafification ring comparison. It is a monoid isomorphism. Internal modules at the point are encoded as ordinary modules by their actual scalar action, with the same underlying additive groups and maps; this is an equivalence and its additive forget functor is literally the original one. Apply the existing sectionwise finite coefficient equivalence using these two fixed encodings, and derive it termwise. The direct-image comparison is the identity on sections and scalar actions; the inverse-image comparison is its adjunction mate.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-finite-line-coordinates`: Use [def-pur-transport-finite-encoding], [def-pur-transport-root-coordinates], [det-sp-finite-general-ring]. For a finite coefficient ring $A$ killed by $\ell^{n+1}$, use its universe lift with the same annihilator. Finite line coordinates identify the scalar extension of the integral root-tower line with the sectionwise encoding of the existing Cartier finite Tate line at that positive level. The map is fixed by precomposition with the scalar unit: it equals the integral tower projection followed by the free-module map on the identical root sections. The coefficient-unit comparison is fixed on each sheafification generator by the identical constant section. Thus both the line and the unit are normalized, without choosing a basis of roots.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-finite-support-encoding`: Use [def-pur-transport-finite-encoding]. The finite encoding comparison for open extension is the left-adjoint mate of the sectionwise inverse-image comparison. The derived direct-image comparison is obtained from the exact equivalence/total-derived composition comparisons and the sectionwise direct-image comparison. The open comparison is derived termwise. The compact-support encoding comparison is their composite on the actual proper/open compactification functor.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-geometric-base-change`: Use [def-pur-transport-adjunction-family]. For a smooth geometric index and a morphism $Y'\to Y$ in the standing setting, its base-change index has source the literal fiber product, map its second projection, the same dimension, and the base-changed compactification. For two composable smooth indices, the composite has the literal composite map, dimension the sum, and the compactification formed from a boundary compactification of the proper/open middle composite. All maps retain their structure morphisms over the same base field.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-geometric-indices`: Use [def-pur-transport-adjunction-restrictions], [def-pur-transport-source-comparisons]. A smooth geometric index over the fixed algebraic closure of the finite field consists of separated finite-type schemes $X,Y$, a morphism over that field, its pure smooth dimension $d\ge0$, and a compactification. The coefficient prime distinct from the base characteristic is a unit in the field. An explicit adjunction at such an index consists of proofs that actual compact support and $J_{f,c,d}$ preserve $P_c$, and an adjunction between these literal restricted functors. Its trace is the underlying ambient counit, not an additional map.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-line-pullback`: Use [def-pur-transport-derived-coordinates]. A system of line pullback coordinates for $f:X\to Y$ consists of an integral line isomorphism commuting with every finite root-tower projection and its root-normalized comparison, its scalar extension to the coefficient $c$ fixed by scalar transport, and the power comparisons fixed by the recursive monoidal construction for every $d\ge0$. The derived comparison is induced by these ordinary comparisons. Such a system exists when $\ell$ is invertible on $X,Y$. No root frame is selected.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-root-coordinates`: Use [def-pur-transport-concrete-coefficients]. For a scheme $X$ and integer $N$, let the root comparison be the unique isomorphism from the existing abelian roots-of-unity sheaf to the section-defined pro-etale root sheaf whose map on every sheafification generator is the same root. Pullback of roots is the sectionwise pullback, conjugated by these comparisons. Tensor it with the canonical coefficient inverse-image isomorphism to obtain the raw finite integral root pullback. An internal module isomorphism is pull-normalized when, after forgetting scalars and using the canonical inverse-image/forget comparison, its map equals that raw root pullback. Existence and uniqueness of the generator-normalized root comparison are part of this interface.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-scalar-coordinates`: Use [def-pur-transport-geometric-indices], [def-pur-transport-compact-support-coordinates]. Bundle each coefficient's existing condensed ring as a scalar-six ring. For a coefficient map commuting with its integral coefficient maps, the first-line scalar comparison is scalar-extension associativity and that commutative triangle. The derived tensor scalar comparison is the canonical monoidal tensorator of derived extension of scalars. For an ordinary line map its degree-zero derived scalar map is obtained by transposing across the scalar adjunction and the recorded single/derived-restriction comparison; the shifted map uses the same adjunction's shift comparison.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-scalar-counit-equation`: Use [def-pur-transport-scalar-line-coordinates], [def-pur-transport-adjunction-family]. The scalar property of an adjunction family means: for every listed admissible coefficient map, it commutes with the integral coefficient maps; there are scalar line coordinates as above; derived scalar extension preserves $P_c$; and scalar extension of each family counit equals the proper/open coefficient mate followed by compact support of the normalized source scalar arrow and then the target family counit. Thus the property compares the actual coefficient maps and the same family, including nonflat finite coefficient changes.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-scalar-line-coordinates`: Use [def-pur-transport-scalar-coordinates]. Scalar line coordinates for a coefficient map $a:c\to c'$ commuting with integral maps consist of the ordinary first-line isomorphism fixed by scalar associativity, and power isomorphisms for every nonnegative exponent fixed by the ordinary scalar tensorators and unit. The source scalar arrow $T_XJ_{f,c,d}\to J_{f,c',d}T_Y$ is the inverse derived scalar tensorator followed by the canonical scalar pullback comparison tensor the shifted line map determined by these coordinates.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-source-comparisons`: Use [def-pur-transport-line-pullback]. For a Cartesian square with smooth vertical map, define the source comparison $Lg'^*J_f\simeq J_{f'}Lg^*$ by the inverse-image tensorator, canonical pullback-square isomorphism, and normalized derived line pullback. For composable smooth maps of dimensions $d,e$, define $J_{gf,d+e}\simeq J_{f,d}J_{g,e}$ by pullback composition, the inverse derived line product, symmetry, associativity, line pullback and the tensorator. The composite compactification is the literal open/open and proper/proper factorization through a boundary compactification of the intervening proper/open composite.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-tensor-coordinates`: Use [def-pur-transport-canonical-pullback]. For a strong monoidal functor $F$ and $e:F(L)\simeq M$, define the comparison on nonnegative tensor powers recursively: the zeroth comparison is the inverse unit tensorator, and the successor comparison is the inverse binary tensorator followed by the previous comparison tensor $e$. The positive Tate lines are flat when $\ell$ is invertible on the scheme. Their product isomorphism is the recursion using the unitors and associators, with target the sum of the two exponents.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

`def-pur-transport-unit-coordinates`: Use [def-pur-transport-adjunction-family]. The derived coefficient unit is the actual regular module in degree zero. The source on this unit is compared with the shifted derived Tate line by the single/left-derived comparison, inverse-image monoidal unit comparison, single-object unit comparison, and the tensor unitor. This fixes the unit comparison by the actual canonical maps.

Source: the current smooth-purity transport statement, its canonical functors, comparisons and integration clauses. The searches above found the individual imported ingredients but not this normalized interface; this node owns the additional packaging and its explicit canonical maps.

Compilation repair: the newly published Brown-existence proof import reached
`EmbeddedFiniteHeartMonoidalPresentation`, whose private proof failed with an
unresolved universe. The statement needs the localizing closure and the exact
restricted functor, not that existence proof. It now imports `LocalizingClosure`
and spells the recorded `localizingLowerShriek` body literally as
`Q.lift (P.ι ⋙ rightDerivedLowerShriekOfCompactification ...) ...` in the Brown
adjunction binders. This is the identical full-subcategory restriction, with
identical objects and maps; there is no replacement operation or added hypothesis.
The published definition and its full signature were read before this expansion.

The next published proof failure was in `CoefficientScalarTensorRealization`,
reached through `ProEtaleProperOpenInterchange`'s private localizing proof.
The composition clause now spells out `compositionInterchangeIsNormalized`'s
exact restriction equation: the open adjunction transpose, followed by the
proper direct-image mate of the literal pullback-composition square, equals
proper direct image of the source open unit. Its defining source and all three
signatures were read in full. This removes the proof import without replacing
the normalization with a free map or changing the equation.

The high-level base-change definitions also imported that proof through
compactification coherence. Their three maps were read with their full types
and definitions. The base-change clause now writes those same constructions
in place: the literal pullback square, `condensedAmbientExchange`, the proper
image of the normalized open comparison, and the open-unit / pullback-square /
open-counit formula fixing its inverse. No new declaration duplicates these
maps; the equality displays their defining expressions. Only the proof-heavy
import was removed. Both previously failed proof modules are absent from the
resulting import graph.

A third newly published statement failure, `IntegralObjectPullbackQuotientBasis`,
was reached by the broad Cartesian-twist imports. The statement uses the
archived actual internal root tower, whose source is independent of that proof.
Those broad imports were narrowed to the coefficient ring and actual internal
pullback modules. `PullNormalized` now writes the exact published
`cartesianCoefficientPullbackIso` expression in place: whisker module inverse
image with `Mod.extendScalarsIsoComapInv (condensedPullbackHom R f)`. Thus its
normalization compares the same underlying map, with no new comparison chosen.
The ordinary scalar pullback comparison remains the existing `CondensedRing.pullIso`.

The scalar pullback constructor itself also imported the third failed proof.
The final narrow interface uses the already defined `scalarSixPullHom` directly.
Its invertibility is a named theorem with a complete K-flat proof in words and
postponed Lean proof. `scalarPullbackIso` is `asIso` of this literal map, so its
inverse is determined uniquely; no comparison data is selected from Nonempty.
This is recorded explicitly in the compact-support coordinates node. Proper
coefficient mates and the source coefficient arrow use that same isomorphism.


## Published dependency repair

The published `IntegralObjectPullbackQuotientBasis` signature originally failed
because its fixed site-size instance was private. A sandbox repair making the
actual `essentiallySmallSelf` specialization public compiled successfully.
While this delivery was being checked, Q8 published the same repair as the public
`WeilConjectures.integralObjectPullbackSiteSmall` theorem with a local instance
attribute. The current live source was read again. This packet therefore omits
its temporary replacement module and node record and uses Q8's published repair.
The original quotient-basis theorem signature and hypotheses are unchanged.

The compatibility equations use `actualPull`, `actualPush` and `actualOpen`,
public abbreviations of the existing derived functors with their ambient
categories explicitly typed. These abbreviations do not construct another
pullback, pushforward or open extension. They prevent repeated inference of
those categories while elaborating the canonical equations. The base-change
formula abstracts its coefficient ring before forming the existing open mate.
