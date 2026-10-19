## Worker report

`Sheaf.Paper.ExceptionalMateSiteComparison` states
`AlgebraicGeometry.ProEtale.exceptionalMateSiteComparison`, with its whole proof postponed.
The twelve other recorded declarations construct the normalized maps appearing in this
one notion; they do not introduce independent notions or any additional postponed theorem.
All definitions have actual data. No statement or dependency record was changed.

Hypothesis and clause correspondence:

- `D : WeilConjectures.PurityFiniteSetting` retains the fixed finite-field datum,
  the prime different from the characteristic, the chosen finite coefficient extension,
  and its positive quotient level. `D.Coefficient` is the conventions' canonical ULift
  of `D.Ring`. The two finiteness instances use the recorded quotient-finiteness theorem
  and `Equiv.ulift`; neither is an extra hypothesis or a new coefficient ring.
- `aX`, `aY`, `aY'`, with `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`,
  give precisely the separated finite-type k-schemes. `_hf`, `_hg` say f and g are
  k-morphisms. `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` retain the
  morphism hypotheses. No smoothness or property of g is imposed.
- `sq : IsPullback g' f' f g` permits the specified Cartesian square with any chosen
  realization of its fibre product. The k-structure on X' is induced through g'.
  `c : Compactification f` and `c.ofIsPullback sq` are the dependency's actual compactifications;
  they carry open immersions and proper maps. The four instances on `c.g ≫ aY` and
  its primed version state that both ambient schemes are finite type over k.
  `d d' : ℕ`, `_hd`, `_hd'` are exactly the two nonnegative dimension bounds, using
  `topologicalKrullDim`, including its value bottom on the empty scheme.
- Every category is the ordinary constant-module-sheaf `DerivedCategory.Plus` of the
  etale or pro-etale small site, with `ModuleCat.{u+1} D.Coefficient`. These are the
  full bounded-below domains specified in the node, with no constructibility restriction.
  The small-site object universe is u+1 and its morphism universe is u.
- `A`, `B`, `l`, `p`, `He`, `Hp` from `CompactSupportTransport` are the published
  comparison inverse image, comparison direct image, etale/pro-etale exact pullback,
  and chosen-compactification compact-support functors. They are used directly,
  rather than copied under new aliases. `R`, `R'`, `adj`, `adj'` express the ordinary
  etale right adjoints on their bounded-below domains. The node explicitly assumes all
  right-adjoint values and Hom-chain arguments are bounded below. Restricting its ordinary
  etale adjunctions to these full subcategories gives precisely these adjunctions;
  all counits and transposes are those of the restricted ordinary etale adjunctions.
  Conversely uniqueness of right adjoints identifies any such restriction with the
  given one. This introduces no adjunction for all pro-etale inputs.
- `exceptionalMateH` is literally `B Y ⋙ R ⋙ A X`, the finite exceptional functor
  with the supplied ordinary etale right adjoint. The recorded
  `sfFiniteExceptionalFixed` instead fixes an upstream chosen ordinary adjoint; it is
  read and imported, but is not substituted for the node's explicitly chosen R.
- `exceptionalMateTranspose` implements every arrow of the prescribed Hom chain:
  precompose by `Hp.map α.hom`, then by `(Cc c).hom.app G` (a_G inverse), apply
  `derivedComparisonAdjunctionPlus.homEquiv` (unit followed by U of that map), apply
  `adj.homEquiv`, apply `A X`, and precompose by `α.inv`. The chain is a definition,
  not an arbitrary bijection assumed as a parameter. Its bijectivity on these domains
  is the cited relative-adjunction construction, used in the proof docstring.
- `exceptionalMateCounit` reverses this chain at the identity: `Cc.inv`, then
  `A Y` of the ordinary etale counit, then the actual comparison counit. The triangle
  identities show that its normalized relative transpose is the identity. Thus the
  counit is constructed, rather than supplied as an unconstrained map.
- `exceptionalMateUnit` applies `R ⋙ A X` to `compactSupportComparisonUnit`.
  This is exactly h, including its normalization by the actual site-comparison unit.
- `exceptionalMateEtaleExchange` is the actual recorded etale exchange component made
  an isomorphism using `compactSupportFiniteTorsion`. `exceptionalMateProExchange`
  is the exact `S.symm ≪≫ A.mapIso B^e ≪≫ T` chart transport from the node.
  Here `S`, `T`, `Cc` are the published definitions built from the normalized proper
  counit mate and extension-by-zero comparison. There is no freely chosen exchange.
- `exceptionalMateEtale` is the primed etale transpose of inverse exchange followed
  by the pullback of the etale counit. `exceptionalMatePro` is the primed normalized
  relative transpose of inverse chart exchange followed by the pullback of the
  constructed relative counit. The source witness is the actual `a g'` comparison
  on `R.obj (B.obj N)`. No exceptional mate is assumed invertible.
- `exceptionalMateV` is `(p g').mapIso h.symm` followed by `kappa_g'.symm`.
  `exceptionalMateW` is `H'.mapIso kappa_g.symm` followed by `h'.symm`.
  Both are actual endpoint isomorphisms with exactly the node's directions.
- The first conjunct, for every L, is `beta^p ≫ w.hom = v.hom ≫ C_X'.map beta^e`.
  The next two conjuncts give naturality of the actual pro-etale and etale mates for
  every morphism `b : L ⟶ M`. The endpoint isomorphisms are composites of the natural
  comparison unit and pullback comparisons, so this is naturality of the displayed
  equality in L.
- The final conjunct quantifies every `α : C_Y L ≅ N`. Its left side uses
  `beta^p_N`, then `H' S(α.inv)` and w; its right side uses `T H(α.inv)`, v,
  and `C_X'(beta^e)`. These are exactly the conjugated endpoints in proof step 8.
  Thus replacement by an arbitrary isomorphic witnessed input is explicitly retained.

Dependency declarations read and used (directly or through the imported construction):
`WeilConjectures.PurityFiniteSetting` (Sheaf.Paper.PurityFiniteSetting);
`Compactification.baseChange`, `.ofIsPullback` (WeilConjectures.Compactification.BaseChange)
and `.Refinement` (WeilConjectures.Compactification.Refinement);
`topologicalKrullDim` (Mathlib.Topology.KrullDimension);
`Etale.DerivedCategory.torsionCohomology` and the module's ordinary `DerivedCategory.Plus`
encoding (WeilConjectures.AlgebraicGeometry.DerivedCategories);
`FiniteCoefficientModules` and its fixed-ring presentation
(Sheaf.AlgebraicGeometry.ProEtaleFiniteModules);
`siteComparisonDerivedPullbackPlus` (Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed);
`Etale.rightDerivedLowerShriekOfCompactification` and its Plus restriction
(WeilConjectures.SixFunctors.Etale.Derived.LowerShriek);
`Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`
(Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint);
`Scheme.sfIntrinsicCompactSupport` (Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport);
`sfFiniteExceptional` and `.sfFiniteExceptionalFixed`
(Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage);
`ComparisonClassAdjunction`, `exists_comparisonClassAdjunction`
(Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass);
`supportSiteComparison_pullback_coherent`
(Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence);
`isIso_compactSupportComparisonUnit`, `compactSupportComparisonUnit`
(Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit);
`Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`
(WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange);
`Etale.compactSupportFiniteTorsion` (Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion);
`finiteLevelCompactSupportExchange_isIso`
(Sheaf.Paper.FiniteLevelProEtaleCompactSupportBaseChange);
`CategoryTheory.mateEquiv` (Mathlib.CategoryTheory.Adjunction.Mates);
`compactSupportSiteComparison` (Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison);
and `CompactSupportTransport.Cc`, `.S`, `.T`, `.chartPhi`,
`.globalTransportChartNormalization` (Sheaf.Paper.GlobalTransportChartNormalization).
The scheme-properties dependency is a convention node and has no declaration of its own.
Missing/stale local upstream sources were read with `scompile.py --source`.

Edge cases checked: identity squares (the counit-transpose conventions reduce to the
ordinary triangle identities); L zero and maps to/from zero; empty X or Y, including
bottom dimension; d=d'=0; identity witnesses and arbitrary isomorphic replacements;
non-smooth separated maps. No nonempty site, nonzero point, equality of site object and
morphism universes, or global pro-etale adjunction is assumed. The constructions also
make sense for the zero finite ring, although the fixed positive DVR quotient is nonzero.

Searches actually run for this delivery:
`msearch.py leanfinder` on "Comparison between etale and pro etale sites preserves the
exceptional counit transpose mate of compact support base change" returned eight hits
on condensed counits or ordinary module-sheaf adjunctions, with no matching theorem.
`msearch.py loogle` on "CategoryTheory.Adjunction.homEquiv, CategoryTheory.conjugateEquiv"
returned no hits. `msearch.py leansearch` on "The counit transpose exceptional base change
mate commutes with etale pro etale comparison" returned generic adjunction, monoidal and
exponentiable-morphism identities, not this theorem. Mathlib grep on
`exceptionalMateSiteComparison|mate.*[Cc]omparison` in CategoryTheory returned only three
monoidal-closed-functor uses of mateEquiv; grep on `exceptional.*[Mm]ate|[Mm]ate.*[Ss]ite`
returned only an unrelated dense-subsite line. Direct rg in the upstream WeilConjectures
and project lean/Sheaf trees found open-restriction or smooth-specific exceptional
comparisons, including SmoothExceptionalBaseChangeStatement, not the arbitrary-square
normalized relative-mate equality here. The exact blueprint-id grep in upstream found
no declaration. All helper full names were also searched in both trees with no collision.

The author checked the node and final file together. This caught and repaired the draft's
unconstrained Hom maps and unit isomorphisms, an exchange applied at the wrong witness,
missing separated/ambient-finite-type hypotheses, and missing naturality and witnessed-input
conclusions. The final version defines every map from the actual dependency constructions.
There is no independent worker second reading; the maintainer supplies independent review.
The module compiles with scompile.py; all theorem proofs in this delivery consist of sorry.

## Second reading by Q95

Independent maintainer second reading of immutable delivery
172601c50bb50dbea33e6cd12ecd3ffb02503f26, performed on 2026-10-18. I did not
write or previously second-read this delivery. The snapshot, rather than the mutable
group checkout, supplied the item, dependency records, delivered module and worker report.

I read check-brief2.md in full, packet.md, the stage-2 brief, delivery-errors section H,
the module docstrings and all thirteen recorded declarations. I read all twenty-one
statement dependencies, including their Lean records, and the actual interfaces used.
The source is literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-prop-an/thm-pur-affine-line-purity.proof.md, especially the actual-adjoint
comparison paragraph and its final arbitrary-base-change sentences. Its transport
of the defining adjunction and counit is exactly the subject of this lemma.

Hypothesis and conclusion audit:

- The coefficient binder D uses PurityFiniteSetting, with FiniteFieldDatum and
  CoefficientDatum: prime characteristic, positive finite-field exponent, the fixed
  algebraic closures, ell different from p, finite coefficient subextension and n>=1.
  D.Ring is the recorded DVR quotient and D.Coefficient its standard ULift. The two
  finite instances apply the existing quotient theorem and transport along Equiv.ulift;
  they add no coefficient assumption or new choice.
- aX, aY, aY' and their separated/locally-finite-type/quasi-compact instances state
  exactly separated finite-type k-schemes. _hf and _hg state k-linearity of f and g.
  The three instances on f give separated finite type. There is no condition of
  smoothness, flatness or properness on f, or additional condition on g.
- sq is IsPullback g' f' f g. This admits any realization of the fiber product.
  Compactification f supplies its actual open i, proper g and factorization equation;
  ofIsPullback uses ambient pullback c.g g and the induced open immersion. The ambient
  finite-type hypotheses and both natural-number Krull-dimension bounds match the node.
  They neither require nonempty schemes nor assert nonnegative dimension of an empty one.
- All categories are the ordinary constant-module small-site DerivedCategory.Plus
  categories; no constructibility or finite-Tor restriction appears. A, B, l, p, He,
  Hp are the recorded CompactSupportTransport interfaces, not substitute operations.
  R,R',adj,adj' are chosen ordinary etale adjoints restricted to D+. The node explicitly
  puts their values and all Hom-chain arguments in D+; restriction along the fully
  faithful inclusions gives these very adjunctions. Conversely uniqueness identifies
  any supplied adjunction with that restriction. No arbitrary pro-etale adjunction is
  hypothesized. The finite exceptional helper parametrizes the chosen R, rather than
  silently replacing it by the separately published chosen right adjoint.
- exceptionalMateH is B Y followed by R followed by A X. exceptionalMateUnit applies
  R followed by A X to compactSupportComparisonUnit, whose hom is the specified
  comparison-adjunction unit. Thus h has exactly the node's normalization.
- exceptionalMateTranspose first inserts Hp(alpha.hom), precomposes with Cc.hom,
  uses the actual comparison homEquiv, then adj.homEquiv, applies A X, and removes
  the witness with alpha.inv. This is every arrow of the displayed Hom chain.
- exceptionalMateCounit is Cc.inv followed by A of the etale counit and the comparison
  counit. Reversing the two adjunction Hom equivalences and full faithfulness on the
  identity gives precisely this map; triangle identities verify its normalization.
  It is neither an arbitrary counit nor data extracted from a bare existence theorem.
- exceptionalMateEtaleExchange uses the actual compactification exchange component;
  its inverse is justified by compactSupportFiniteTorsion. exceptionalMateProExchange
  is S.symm, A applied to that exchange, then T. Cc is exactly proper b followed by
  direct image of open e; the proper b is the normalized right-derived counit mate.
  This is the chart formula fixed in the item, with the correct orientations.
- exceptionalMateEtale transposes inverse exchange followed by g-pullback of the
  etale counit under adj'. exceptionalMatePro uses the same normalized relative
  transpose, the pullback-comparison witness a g', inverse chart exchange at
  R(B N), and g-pullback of the constructed counit. At H N = A R B N this uses the
  identity etale-origin witness. Naturality gives the node's alternative h witness.
- exceptionalMateV and exceptionalMateW are the two displayed endpoint isomorphisms
  in exactly their stated order. The first conjunct is beta^p followed by w equal
  to v followed by C(beta^e). The next two conjuncts assert naturality of both actual
  mates for every b:L->M. The endpoints are already natural composites. The final
  conjunct quantifies every alpha:C_Y L ~= N and inserts TH(alpha.inv) and
  H'S(alpha.inv); it is exactly the witnessed-replacement equation. No exceptional
  mate is assumed invertible.

Dependency/source checks: I opened PurityFiniteSetting and FiniteFieldFiber;
Compactification.Defs, BaseChange and Refinement; Mathlib.Topology.KrullDimension;
the recorded derived-category and finite-module presentations; ComparisonDerivedPullbackFixed;
EtaleExceptionalAdjoint; SfIntrinsicCompactSupport; SfFiniteExceptionalInverseImage;
EtaleOriginAdjointClass; SupportComparisonPullbackCoherence; CompactSupportComparisonUnit;
CompactSupportFiniteTorsion; CanonicalCompactSupportSiteComparison; and
GlobalTransportChartNormalization (in particular A,B,l,p,a,He,Hp,b,e,Cc,S,T,chartPhi).
The finite-module realization extends constant scalar actions by sheafification and
is the published equivalence, so this is the required constant-module presentation.
The two compact-support formulas are the bounded-below restrictions of the ordinary
unbounded formulas. I also checked Mathlib.CategoryTheory.Adjunction.Mates.mateEquiv
and the current exact etale exchange and pro-etale comparison/lower-shriek sources.
Missing current finite-coefficient source files were read using scompile.py --source,
not replaced by similarly named legacy modules in the older source tree. The group
clone's coord/pefw-upstream-framework.md was read. No dependency repair or new DAG
prerequisite is needed for these chosen-adjoint, chosen-compactification formulas.

Proof-docstring check: all eight DAG steps are retained. (1) Bounds and comparison
exhibit witnesses. (2) Unit naturality gives Psi(C(b)a)=h C(Jb). (3) Transposing the
counit gives E P(h)=C(e)a. (4) The specified S/T chart formula gives the inverse-exchange
identity by cancellation. (5) Exchange naturality at h and pullback-comparison
naturality at e give the displayed z identity. (6) Primed transposition gives the
claimed mate equality. (7) Naturality of both Hom equivalences gives both mate
naturality equations. (8) Isomorphic replacement conjugates the endpoints. I checked
the types and order of these composites; these steps use the cited statements and
the explicitly stipulated normalizations. They do not infer compatibility from an
arbitrarily chosen bijection or isomorphism.

Edge cases: L=0 and zero morphisms; identity base change; identity witness and any
isomorphic replacement; empty X and empty Y (then its incoming schemes are empty);
bottom Krull dimension; d=d'=0; proper f with j=id; nonsmooth separated finite-type f.
No nonempty-index maximum or nonzero-object hypothesis occurs. Level zero is correctly
excluded by the node's n>=1. The universe u remains arbitrary; small sites retain object
universe u+1 and morphism universe u, with ModuleCat at u+1. The coefficient ULift
is the published size convention, not an equality imposed on site universes.

Independent searches actually run: msearch.py LeanSearch on "etale proetale site
comparison preserves exceptional base change counit transpose mate" returned eight
hits, including mateEquiv and its counit identities but no theorem stating this
normalized site comparison. LeanFinder on "A fully faithful derived site comparison
preserves the counit transpose mate of compact support base change" returned eight
general module-sheaf adjunction/sheafification hits, no match. Direct rg searches of
Mathlib/CategoryTheory, both permitted upstream trees and the group lean/Sheaf tree
for exceptional mates and site comparison found trace-pairing mates and the existing
smooth/open exceptional comparisons. I opened SmoothExceptionalBaseChangeStatement:
its chosen upstream-adjoint comparison-site paste is not this theorem about the two
specified counit transposes for arbitrary chosen etale adjunctions. The delivered
helper names have no prior collision. The underlying functors and comparisons are
reused; the new helpers construct this node's normalized maps with its chosen R.

Compiler evidence: the worker records a successful scompile.py run without its log.
I independently ran
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q95
lem-pur-exceptional-mate-site-comparison
snapshot/lean/Sheaf/Paper/ExceptionalMateSiteComparison.lean
from this review directory. Exit status was 0. Output reported sandbox
Sheaf/Stage2/Sandbox0.lean [6.3 s] and library
Sheaf/Paper/ExceptionalMateSiteComparison.lean [12.0 s], with no diagnostics.
The installed wrapper currently runs the server side-overlay compiler; its banner
says "on the server, one at a time". This reproduced the exact snapshot through the
prescribed wrapper with its default per-file 60-second limits; no local/global lake
build or direct ssh command was run. Source reads through --source also succeeded.

Mechanical checks: all thirteen names are listed in lean.declarations; the main
statement field equals the complete signature under the delivery tool's whitespace
normalization (no token or binder difference). All lines are <=100 characters.
autoImplicit is false, u is declared and every binder is bound. Module and declaration
docstrings name the source and blueprint, and the main docstring contains all eight
steps. Every definition has real data; the sole theorem body is exactly by sorry.
The finite instances only reuse existing evidence. There are no new axioms, local
proofs of postponed results, private definitions or file-local notation.

Finding and correction: H1/H11, the original Second reading by Q95 section was only
a disclaimer that no worker second reading occurred. The complete replacement report
preserves the entire Worker report and replaces that placeholder with this independent
substantive reading. There is no mathematical or Lean-source correction, no source-based
statement correction, and no changed dependency record. No other findings.
