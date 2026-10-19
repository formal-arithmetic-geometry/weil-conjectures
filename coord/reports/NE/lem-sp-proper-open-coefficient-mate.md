## Worker report

The delivery states `lem-sp-proper-open-coefficient-mate` in
`Sheaf.Paper.ProperOpenCoefficientMate`. It has four postponed theorems: the
coefficient equality, its naturality, the site equality, and its naturality.
Definitions contain actual maps and canonical inclusion comparisons. No theorem
is proved. No statement correction or disputed statement is required.

Hypotheses and clauses, matched individually:

| Node text | Lean rendering |
| --- | --- |
| A and B finite commutative rings | `A B : Type (u + 1)`, `[CommRing A] [CommRing B] [Finite A] [Finite B]` |
| A unital map A → B | `φ : A →+* B` |
| Schemes U, V, W, Z | `U V W Z : Scheme.{u}` |
| All four schemes Noetherian, equivalently finite affine Noetherian covers | Section instances `[IsNoetherian U]`, `[IsNoetherian V]`, `[IsNoetherian W]`, `[IsNoetherian Z]`; Mathlib's `isNoetherian_iff_of_finite_affine_openCover` identifies this with the specified cover criterion. These instances enter the interchange selected from `unboundedProperOpenInterchange`, and hence the square theorems. |
| Edges and commutativity pk = ir, with the square cartesian | `k : U ⟶ V`, `r : U ⟶ W`, `p : V ⟶ Z`, `i : W ⟶ Z`, `sq : IsPullback k r p i`; `sq.toCommSq` retains the specified commutativity |
| r and p proper | `[IsProper r] [IsProper p]` |
| k and i open immersions | `[IsOpenImmersion k] [IsOpenImmersion i]` |
| Ordinary constant-ring module derived categories on the small etale site | `Etale.DerivedCategoryModule A U`, i.e. `DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))` |
| Ordinary constant-ring module categories on the small pro-etale site | `Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)` and its derived categories, the fixed-scalar presentation of `ProEtaleFiniteModules` |
| T is derived coefficient extension | Existing `Etale.scalarExtension φ T`, definitionally `ProEtale.pbcFixedScalarExtension T.smallEtaleTopology φ`; the published left adjoint to exact derived restriction of coefficients, with its K-flat tensor normalization |
| q is the B-linear transpose of T of the A-counit | Existing `Etale.finiteCoefficientDirectImageMap φ v K`. Its `IsFiniteCoefficientDirectImageMap` equation and `finiteCoefficientDirectImageMap_existsUnique` uniquely fix precisely this B-linear transpose. No arbitrary arrow or isomorphism is a parameter. |
| t is the summandwise tensor comparison for open extension | Existing `Etale.openScalarExtension φ a`, with the ordinary comparison and K-flat representative normalizations of `EtaleOpenTensor` |
| No assumption that T preserves D+ | T acts on the unbounded categories throughout; no such typeclass or hypothesis occurs |
| Gamma et is the specified proper/open isomorphism | `properOpenCoefficientInterchange A sq` selects the family in the recorded `unboundedProperOpenInterchange A`, retaining its representative and open-adjunction normalizations. This is not choice from a mere endpoint-isomorphism existence assertion: the full support and K-injective representative conditions determine the selected map. |
| The exchange in Gamma's open adjunct is the specified counit mate | The third normalization of `unboundedProperOpenInterchange` explicitly uses `exactDerivedBaseChangeMap` and inverse open unit. `properOpenCoefficientRestriction` recovers that same lambda from Gamma by the open unit and restriction of Gamma, then inversion. Triangle identities and the third normalization identify its hom with that recorded exchange followed by inverse open unit. |
| E in D+(U_et,A) | `E : DerivedCategoryModule A U`, `_hE : ∃ n : ℤ, E.IsGE n` |
| E_B in D+(U_et,B) | Separate `_hEB : ∃ n : ℤ, ((scalarExtension φ U).obj E).IsGE n` |
| Coefficient equality in unbounded D(B) | `properOpen_coefficient_mate`: its left side is T(Gamma_A), then q_p(k!E), then Rp_B(t_k(E)); its right side is `properOpenCoefficientComposite`, defined as t_i(Rr_A E), then i!_B(q_r(E)), then Gamma_B(E_B). Lean composition is written in the opposite textual order to the displayed mathematical composition. |
| R any finite commutative ring for site comparison | The site theorems use an independent parameter `A : Type (u + 1)` with `[CommRing A] [Finite A]`; this A denotes the node's arbitrary R, unrelated to the two rings in the coefficient theorem. |
| N is exact site comparison | `(ProEtale.comparisonUpperStar (ModuleCat A) T).mapDerivedCategoryPlus` is the exact comparison on D+, with the canonical unbounded-inclusion compatibility |
| e_a is the canonical open-extension comparison | Existing `ProEtale.properOpenSiteExtensionIso A a`, obtained termwise from `openImmersionLowerShriekComparisonUpperStarIso` |
| d_v is the specified counit mate | Existing `ProEtale.fixedComparisonDirectImageMatePlus A v`, with `isIso_fixedComparisonDirectImageMatePlus` for proper v and the published counit normalization |
| Gamma pro is the open adjunct of inverse transported restriction and open unit | `properOpenSiteRestrictionInverse` first inverts d_r, applies N to inverse etale lambda, uses `fixedComparisonPullbackPlus` for i, then applies i* to d_p followed by Rp(e_k). `properOpenSiteInterchange` applies the inverse open-adjunction Hom bijection to that composite. It is not defined by the desired site equation. |
| Every bounded-below etale-origin object is included | `E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat A))`; the pro-etale input is its comparison image, retaining E as its origin. No constructibility or Tor-amplitude hypothesis occurs. |
| Site equality in the unbounded category | `properOpen_site_mate` maps both Plus composites through `DerivedCategory.Plus.ι.map`. `properOpenSiteComposite` is N(Gamma_et), then d_p(k!E), then Rp(e_k(E)); the other side is e_i(RrE), then i!pro(d_r(E)), then Gamma_pro(N E). The canonical inclusion comparisons in `properOpenCoefficientInterchangePlus` identify these endpoints and maps with the displayed unbounded equation. Fully faithful inclusion loses no morphism information. |
| Both squares natural in E | `properOpen_coefficient_mate_naturality` and `properOpen_site_mate_naturality` give the actual naturality equations for their respective composites. The square equalities identify the other paths with these at each endpoint. The coefficient naturality theorem separately retains both lower bounds at both endpoints. |
| No flatness of B over A | No flatness, finite projective dimension, Tor amplitude, or scalar boundedness-preservation hypothesis is present. |

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: `Etale.DerivedCategoryModule`, `DerivedCategory.Plus`, standard cohomology/t-structure; current source was read with `scompile.py --source` because the upstream module is absent locally.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`, `finiteCoefficientRealization`, `finiteCoefficientComparison`, and `finiteCoefficientDerivedComparison` identify the fixed-ring presentation with the recorded ring-sheaf presentation. The small site retains object universe u+1 and morphism universe u.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`, including its full flat K-flat representative normalization; imported as the canonical tensor/pullback input in the proof plan.
- `Sheaf.Paper.UnboundedProperOpenInterchange`: `Etale.unboundedProperOpenInterchange`; the chosen family is used, and its full representative, open-adjunct, composition, identity and base-change signature was read.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`: `Etale.exactDerivedSquareUpperStarIso`, `Etale.exactDerivedBaseChangeMap`; read their complete definitions and adjunction-mate formula, used through the preceding theorem's open normalization.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`: `ProEtale.openImmersionLowerShriekComparisonUpperStarIso`, `openImmersionLowerShriekComparison_coherence`; read canonical comparison, identity and composition clauses.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`: `ProEtale.fixedComparisonPullbackPlus`, `fixedComparisonDirectImageMatePlus`, `isIso_fixedComparisonDirectImageMatePlus`, `fixedComparisonDirectImageMatePlus_counit`; read all signatures and docstrings. Current finite-coefficient upstream derived interfaces were read through `scompile.py --source`.
- Mathlib `AlgebraicGeometry.Scheme`, `IsProper`, `IsOpenImmersion`, `IsNoetherianRing` and `IsNoetherian`: read definitions and docstrings; Noetherian schemes include quasi-compactness, and universally closed proper maps supply quasi-compactness.
- Proof input `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`: `ProEtale.supportSiteComparison_pullback_coherent` and its canonical restriction/adjunction comparisons.
- Mathlib `CategoryTheory.Adjunction.Mates`: `mateEquiv_vcomp`, `mateEquiv_hcomp`, conjugate/mate composition lemmas and identity normalization, matching the Mathlib record of `lem-weil-pbc-mate-pasting`.

Three already-landed statement dependencies are added, with no new nodes and no dependency repairs:

- `lem-coef-finite-direct-image`, module `Sheaf.Paper.FiniteCoefficientDirectImage`, owns the specified coefficient arrow and its naturality. Only its general construction is used, not its later special finite-field invertibility theorem.
- `lem-coef-etale-open-tensor`, module `Sheaf.SixFunctors.EtaleOpenTensor`, owns `Etale.scalarExtension` via its public tensor import and `Etale.openScalarExtension`, with canonical K-flat/summandwise normalization.
- `lem-weil-pbc-proper-open-comparison-proetale`, module `Sheaf.Paper.ProEtaleProperOpenComparison`, owns `ProEtale.properOpenSiteExtensionIso`, used for arbitrary open edges. Its compactification-specific comparison is not substituted for the item's cartesian interchange.

The added dependencies were traversed through statement and proof edges; none reaches this item, so no cycle is introduced.

Edge cases checked before writing:

- Identity proper maps, identity open maps, and the all-identity cartesian square: the recorded interchange, open unit, coefficient unit and comparison counit reduce to their identity normalizations. Both equalities have matching endpoints and become their naturality/unit squares.
- Empty opens and empty schemes: every functor and open adjunction remains defined, and the zero extension yields zero objects. There is no nonempty-open or nonempty-scheme hypothesis.
- Zero ring and zero complex: commutative rings allow 0=1, and all maps are maps in the same zero categories; no cardinality or nonzero restriction is imposed.
- Non-flat coefficient quotients, for example Z/4 → Z/2: a degree-zero input may acquire unbounded negative Tor. The hypothesis on E_B is separately imposed, not inferred. Inputs such as the free A-complex satisfy both bounds and remain covered. The construction of q and t itself is unbounded and has no scalar flatness assumption.
- Arbitrary finite coefficients, including identity maps and nonquotient unital maps: no surjectivity or coefficient-field hypothesis appears. Finite rings in smaller universes can be lifted to the common coefficient universe without identifying the small-site object and morphism universes.
- Site inputs include every D+ etale complex, without any constructibility or finite cohomological-dimension condition.

Searches for an existing full statement:

- LeanFinder query `Derived extension of coefficients commutes with proper open interchange and etale proetale comparison by adjunction mates`: eight hits, chiefly `Adjunction.derivedε_fac_app`, `derivedη_fac_app`, and condensed adjunction constructions; no full coefficient/site proper-open square.
- Loogle query `CategoryTheory.mateEquiv_square`: one generic double-mate pasting theorem; not the node's geometric normalized squares.
- Mathlib grep query `properOpen.*(tensor|coefficient)|interchange.*(tensor|scalar)` in `AlgebraicGeometry`: zero hits.
- LeanSearch query `Extension of scalar coefficients and etale proetale comparison commute with proper open interchange`: eight hits in intermediate fields, proper restriction, and Kaehler differentials; no match.
- `rg` in the prescribed upstream `WeilConjectures` and project `lean/Sheaf` for proper/open, scalar/coefficient mates and scalar/open extension: found and reused `FiniteCoefficientDirectImage`, `EtaleOpenTensor`, `ProEtaleProperOpenComparison`, and the recorded interchange/mate interfaces. Found specialized existing proper-open site normalizations, but none covers this arbitrary finite-ring cartesian square together with the coefficient square.
- Search for the node id in upstream `WeilConjectures`: no matching declaration.
- No duplicate names for the delivery's declarations were found in `dag/lean_names_upstream.json` or the source searches.

Source check: read the local Stacks statements/proofs at
`more-etale.tex`, `lemma-shriek-proper-and-open` (0F7B), and
`remark-Rf-lower-shriek-change-of-rings` (0GL6), and the current blueprint
`main-20261015` exceptional-comparison proof. The two squares are the node's
agent-stated naturality consequence of these normalized maps, rather than claims
that Stacks quotes these equations verbatim.

Validation: `scompile.py NE lem-sp-proper-open-coefficient-mate` compiled the module cleanly, with no errors or warnings. The final `deliver2.py NE lem-sp-proper-open-coefficient-mate --no-push` returned `OK (dry run): commit 5751d7a441 passes the preflight and compiles; nothing pushed`. The delivery contains exactly the module, the item node, and this report. Earlier elaboration timeouts were repaired by reconstructing the normalized restriction through the open unit and interchange and by making the inclusion categories explicit; the 60-second limit was not changed.

## Second reading by NE

Independent maintainer second reading, 2026-10-18, of immutable delivery
`aed056efca962700a1d14b00d8e0a0be69d84066`. This section records the independent
review performed after worker delivery; it does not claim a worker-group review.

Read the item node, all fourteen statement dependency records, the complete
ProperOpenCoefficientMate module and its docstrings, the worker report, and the
exact supporting declarations. Read Stacks more-etale.tex at
lemma-shriek-proper-and-open (0F7B, lines 2460–2614),
remark-Rf-lower-shriek-change-of-rings (0GL6, lines 3739–3784), and the
main-20261015 exceptional-reduction proof's existence/uniqueness/naturality
paragraph. The displayed squares are the agent-stated consequences of those
canonical maps; they are not attributed verbatim to Stacks.

Clause-by-clause reading:

- The four schemes are `Scheme.{u}`. The section's four `IsNoetherian` instances
  match finite affine Noetherian covers: Mathlib Noetherian.lean:280–309 gives
  precisely the compact locally Noetherian definition and cover equivalence.
  `IsProper r`, `IsProper p`, and the two `IsOpenImmersion` instances match the
  node. Properness supplies quasi-compactness and quasi-separatedness for the
  specified direct-image site mates. `IsPullback k r p i` includes the stated
  commutativity and has the correct edge order.
- `CommRing`, `Finite`, and `φ : A →+* B` express arbitrary finite commutative
  rings and a unital map. There is no flatness, field, surjectivity, constructibility,
  dimension, or nonzero hypothesis.
- `DerivedCategoryModule` is the ordinary unbounded category of fixed-ring module
  sheaves on the small etale site. `scalarExtension` is the published abbreviation
  for `pbcFixedScalarExtension`, with its K-flat tensor characterization. The
  fixed-ring pro-etale presentation is identified with the node's ring-sheaf
  modules by `finiteCoefficientRealization` and its equivalence theorem. The
  small pro-etale site is retained; no condensed or other site replaces it.
- `finiteCoefficientDirectImageMap` is selected from an existence-and-uniqueness
  theorem fixing the B-linear counit transpose. Its construction has no lower-bound
  assumption. `openScalarExtension` is the canonical comparison of composite left
  adjoints; its `OpenScalarExtensionNormalization` fixes the degreewise K-flat
  comparison. These are the specified q and t, rather than free arrows.
- `properOpenCoefficientInterchange` selects the Gamma family from
  `unboundedProperOpenInterchange`. That theorem fixes its sheaf map into the
  common direct image, its K-injective representative, and its cartesian
  open-adjunct normalization. Thus this choice is determined, not hollow.
  `properOpenCoefficientRestriction` recovers lambda as the inverse of the composite of the open
  unit with the restriction of Gamma; the adjunction triangle identities
  identify it with the exchange/open-unit lambda in the dependency theorem.
- The coefficient theorem has independent existential lower bounds on E and
  scalarExtension(E), as required. Its left path is T(Gamma_A), then q_p, then
  Rp_B(t_k). Its right path, expanded through `properOpenCoefficientComposite`,
  is t_i, then i!_B(q_r), then Gamma_B. All arrows are B-linear in the ordinary
  unbounded target. No assertion that T preserves D+ is introduced.
- The site parameter A denotes the node's independent arbitrary ring R.
  `properOpenSiteExtensionIso` is termwise descent of the canonical open-extension
  mate; `fixedComparisonDirectImageMatePlus` is right-derived base change with
  the recorded counit normalization. Their qcqs hypotheses follow from properness.
  `fixedComparisonPullbackPlus` has the required orientation.
- `properOpenSiteRestrictionInverse` composes inverse d_r, N(lambda inverse),
  pullback comparison for i, and i* of d_p followed by Rp(e_k).
  `properOpenSiteInterchange` then takes its open adjunct. This is the node's
  prescribed transported construction and is not defined by the desired site
  equality. The input retains its bounded-below etale origin.
- `properOpen_site_mate` compares N(Gamma_et), d_p, Rp(e_k) with e_i, i!(d_r),
  Gamma_pro. Both sides are mapped by the fully faithful D+ inclusion into D.
  The explicitly constructed Plus compatibility isomorphisms identify these
  with the displayed ambient maps without changing their morphisms.
- The two additional naturality theorems give the actual composite naturality
  equations. The square equations identify the other paths, so both squares are
  natural in precisely the inputs stated by the node.

Edge cases: empty schemes and empty opens require no extra hypotheses; zero rings
and zero complexes are admitted; identity opens, proper maps and ring maps retain
canonical unit normalizations. A nonflat map Z/4 → Z/2 is allowed. For inputs with
unbounded negative Tor, the separate E_B lower-bound hypothesis correctly limits
the coefficient assertion without limiting the definitions of q or t. Arbitrary
bounded-below etale-origin objects are covered by the site assertion. Coefficients
use the established u+1 convention with Scheme.{u}; site object and morphism
universes are not equated. No universe-repair hypothesis is needed.

One-definition audit: independently searched project lean/Sheaf, upstream
WeilConjectures, and Mathlib AlgebraicGeometry for properOpen, coefficient/scalar
interchange, and mate variants. Reused the recorded scalar, open, direct-image,
exchange and comparison interfaces. Existing proper-open site normalization is
restricted to the compactification/Padic-coefficient case, while existing
interchange coherence lacks this pair of arbitrary-finite-ring squares. No exact
existing full statement or new duplicate was found. The worker's three search
kinds are recorded above. All thirteen declarations are listed in lean.declarations;
lean.statement is byte-for-byte the primary signature preceding `:= by`.
There are no new nodes, dependency-module replacements, or statement corrections.
The three added dependencies already have landed records; a read-only traversal
of statement/proof dependencies found no path back to this item.

Maintainer gates: all definitions have actual construction bodies, and the four
and only four theorem bodies are `by sorry`. Every declaration and the module
have source/blueprint docstrings; theorem docstrings explain the corresponding
mate-pasting or naturality argument. No line exceeds 100 characters. All variables
and universes are bound (`autoImplicit false`). The proof-dependency imports are
present. The item directly cites no node in route-pivot-dropped.txt at checked ref
5bfad3aa7102cf1d58026ec7d5c7da54ad5e66ec. No item repair note exists there. The
proof uses ordinary derived adjunctions and K-flat resolutions and introduces no
infinity/dg/model-category machinery.

Finding and repair: the original section contained only a statement that no worker
second reading had occurred. Under the explicit maintainer requirement this was
H11 (a second-reading heading without a reading). The complete replacement report
preserves the Worker report and supplies this actual independent reading. No
mathematical or Lean change is needed. Compiler reproduction is recorded in the
maintainer review.md. No project clone, delivery head, or live Lean file was edited;
no build, claim, merge, or delivery command was run.

Compiler reproduction, 2026-10-18: ran the immutable file through
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NE lem-sp-proper-open-coefficient-mate snapshot/lean/Sheaf/Paper/ProperOpenCoefficientMate.lean`.
The wrapper returned exit code 0 with no diagnostics, reporting the isolated sandbox
pass (reported elapsed time 106.3 seconds) and the library-path check
`Sheaf/Paper/ProperOpenCoefficientMate.lean` (52.3 seconds). The installed wrapper
identifies itself as the 2026-10-17 server-overlay implementation and delegated both
checks to its prescribed isolated compilation service; it did not perform a local
global build. This is direct server confirmation through scompile.py. The earlier
worker dry-run success at 5751d7a441 is recorded evidence, not a dry run repeated by
this maintainer. Report-only replacement requires no Lean recompilation.
