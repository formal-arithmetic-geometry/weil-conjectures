## Worker report

Item: lem-pur-relative-extension-cohomology-normalization. Module:
`Sheaf.AlgebraicGeometry.RelativeExtensionCohomologyNormalization`.
Namespace: `AlgebraicGeometry.Etale`. Stage 2 only: every theorem has proof `by sorry`.
The definitions contain actual predicates, maps and uniquely characterized choices.
No statement correction, new definition node or dependency repair was needed.

The main theorem is `relative_extension_cohomology_normalization`. Its companion
declarations record every other clause, including the canonical maps rather than
unspecified functions. All declarations are listed in the item's `lean.declarations`.

Hypothesis and clause correspondence:

- T and Z are arbitrary `Scheme.{u}`; `i : Z ⟶ T` has `[IsClosedImmersion i]`.
  The complement j is literally `i.openComplement.ι`, an open immersion supplied by
  Mathlib. No finiteness, Cartier, characteristic, torsion or global triviality
  hypothesis occurs. Using this canonical complement loses no chosen-complement
  case: a specified open complement is uniquely isomorphic over T to this one.
- G is `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`. The size is the published
  small-etale coefficient size. Ext is `Ext.{u + 1}` in that same abelian category,
  not Ext in a module category or an ad hoc extension quotient.
- `(P,s)` is the recorded `Sheaf.Torsor.WithSection G
  (Scheme.Etale.mk i.openComplement.ι)`: P.1 is the torsor and P.2 the section.
  Evaluation on that etale object is the existing interface for a section of j^-1 P
  over W. The frame is never replaced by an ordinary unpointed class.
- Q is the existing `(lowerStar AddCommGrpCat i).obj
  (supportedIntegralConstant Z)`. The restriction p is the existing
  `supportedIntegralUnit i`, the adjunction mate of the canonical inverse-image
  comparison of constant integers. `supportedIntegralOne` is sheafification of 1.
- `RelativeExtensionRepresents` writes the short exact sequence, the natural map
  from P to the underlying E, its equivariance `f(g+t)=f(t)+a(g)`, its fibre equation
  `b(f(t))=p(1)` on every etale object, its zero value on s, and equality of beta
  with the Yoneda `hE.extClass`. Thus it records both the action and the frame.
  `relativeExtension_existsUnique` specializes the recorded relative-extension
  theorem using the open-closed integer sequence. `relativeExtension` selects only
  this unique Ext element; no representative extension object is chosen.
- I is an arbitrary `InjectiveResolution G`. `relativeSectionComplex` is exactly the
  existing zero-extended, shifted mapping cone. Its first coordinate is
  `relativeForgetComplex`; the second is the shifted cone's `sndX`. Negating the
  latter is the signed coordinate b, so its vanishing is exactly b=0 in every
  degree, including degree zero, with D(a,b)=(da,res(a)-db).
- `RelativeExtensionComparisonNormalization` specifies the comparison in *every*
  nonnegative degree q. For each closed Hom cocycle k and each relative cycle z
  with first coordinate `(kp)(1)` and zero second coordinate, it requires
  `e q (I.extMk k ...)=homologyπ z`. It therefore fixes the inclusion of the
  supported Hom kernel, evaluation at 1 and the usual Ext resolution roof.
  `relativeExtensionComparison_existsUnique` states existence and uniqueness of
  the whole additive comparison family. `relativeExtensionComparison` chooses
  this unique family. These are not arbitrary maps selected from mere existence.
  The comparison with supported cohomology is the kernel-inclusion convention
  of `relativeConeSupportComparison`; that theorem is a proof import.
- `relative_extension_cohomology_normalization` is precisely Psi(beta)=c.
  Its right side is `-relativeTorsorEquiv ... (Quotient.mk _ P)`. This is the
  Ext-normalized c of the recorded `relative_torsor_cohomology`: the published
  proof constructs its family by negating the existing raw equivalence (lines
  319 onward). The sign is not an added convention or a free assumption.
- `relative_extension_coefficient` includes coefficient maps f, arbitrary lifts
  `a : I.Hom J f`, and arbitrary f-equivariant maps sigma to a target torsor.
  The new frame is sigma(s). Its first equation uses actual Yoneda
  postcomposition `(relativeExtension i P).comp (Ext.mk₀ f) ...`; its second uses
  homology of the recorded `relativeSectionMap`. Identity coefficients include
  framed torsor isomorphisms and independence of resolution-comparison choices.
- `relative_extension_pullback` uses an arbitrary etale h and actual Cartesian
  square `sq : IsPullback w i' i h`. `hW` records the resulting complement equality;
  it imposes no extra geometric condition. `relativeExtensionExchange` is the
  existing base-change mate followed by the canonical constant-sheaf comparison.
  Its named invertibility theorem is specific to this Cartesian etale setting.
  `relativeExtensionPullback` uses exact inverse image on Ext, precomposition by
  the inverse exchange, and the adjoint of the coefficient map. The theorem allows
  a following coefficient map as well. The torsor map b and resolution map a are
  arbitrary equivariant/augmented representatives; their equations are explicit.
  `relativeExtensionPulledFrame` carries the specified section along b and the
  actual open-section pullback, transporting hW by `eqToHom`. The first equation
  identifies the Ext pullback with the pulled framed extension; the second is the
  normalized relative pullback under the existing `relativeTransfer`.
- `relative_extension_enlarge` allows *every* pair of closed immersions with
  `hW : i'.openComplement ≤ i.openComplement`. It never assumes that their closed
  scheme structures admit a factorization Z -> Z'. Quotient restriction is
  defined by its unique equation `p' ≫ q = p`; the defining theorem follows from
  the cokernel property of p'. Thus arbitrary nonreduced supports are included.
  `relativeExtensionRestrictedFrame` uses presheaf restriction on s.
  `relativeExtensionEnlargeComplex` is the existing shifted-cone map with identity
  on global sections and actual restriction of the open term. Its commutative
  square is stated as a separate named theorem. The two equations give the
  canonical Ext precomposition and relative enlargement of support.
- `relative_extension_fibre` explicitly states componentwise bijectivity of the
  given equivariant map from P onto the fibre b^-1(p(1)), on *every* site object.
  The map is already a natural transformation and its action equation hfa is
  with the original G-action. The fibre of p^*E over 1 is that same fibre. This
  states the fibre/action clause in addition to equality of extension classes.
- `relative_extension_forget` quantifies over any ordinary free torsor extension
  `ExtensionPresentation T P.1` and its short-exactness proof. Its first equation
  says precomposition by the actual p gives exactly `hE.extClass`. Its second
  equation uses `relativeForgetH1` with an arbitrary
  `ResolutionSectionCanonicalComparison G I` and identifies the result with the
  *positive* `Sheaf.Torsor.classH1` of P. Together with the previous fibre theorem
  it records the full ordinary extension, not just an equality after forgetting
  to a bare set of classes.

Dependency declarations inspected and used:

- Mathlib's `Scheme`, `IsClosedImmersion`, `IsOpenImmersion`, `Sheaf`,
  `constantSheaf`, `InjectiveResolution`, and `Abelian.Ext` at the recorded paths.
  Ext functoriality is `Ext.comp`, `Ext.mk₀`, and `Ext.mapExactFunctor`;
  resolution cocycles are `InjectiveResolution.extMk`.
- `Sheaf.CategoryTheory.Sites.RelativeTorsorExtension`:
  `CategoryTheory.Sheaf.Torsor.relative_extension_existsUnique` (read its full
  signature, including the sectionwise normalization of the integer generator).
- `Sheaf.CategoryTheory.Sites.TorsorWithSection`: `WithSection` and its `Classes`.
- `Sheaf.AlgebraicGeometry.RelativeEtaleCohomology`: `relativeSections`,
  `relativeSectionRestriction`, `relativeSectionComplex`, `relativeCohomology`,
  `relativeFiberMap`, and `relativeForgetComplex`.
- `Sheaf.AlgebraicGeometry.RelativeTorsorCohomology`: `relative_torsor_cohomology`,
  `relativeSectionMap`, `relativeTransfer`, `relativeForgetH1`.
- `Sheaf.AlgebraicGeometry.RelativeCocycleCoordinates`: `relativeTorsorEquiv`.
  Its landed node is added to stmt_deps because the formula uses that exact
  existing raw classification, never a duplicate definition.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary`:
  `supportedIntegralConstant`, `supportedIntegralUnit`, `supportedIntegralOne`.
  Its landed node is added to stmt_deps for these three existing general helpers;
  their signatures impose none of the Cartier/Kummer assumptions of that module's
  other declarations.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `lowerStar`, `upperStar`,
  `upperStarLowerStarAdjunction`; `Scheme.upperStarConstantSheafIso` and
  `WeilConjectures.SixFunctors.BaseChange.Square`, `Etale.baseChangeMap` are the
  existing canonical constant comparison and exchange mate.
- `WeilConjectures.CategoryTheory.Sites.Torsor`: `Sheaf.Torsor.classH1`, whose
  docstring and full signature fix the ordinary torsor convention.
- `Sheaf.AlgebraicGeometry.ClosedSupportHom`, `closedSupportHom`; and
  `Sheaf.AlgebraicGeometry.PurityRelativeCone`, `relativeConeSupportComparison`:
  inspected the complete comparison signatures and kernel normalizations. Used
  as proof dependencies for the corresponding integral degreewise interface.
- Proof imports also include `DivisorTorsorBoundarySigns`,
  `FirstResolutionExtensionClass`, `RHomDerivedRoof`, `OpenClosedIntegralSections`,
  `SupportedKummerSupportHomNaturality`, exact inverse image, pushout short exactness,
  the open-closed short exact sequence and extension-by-zero adjunction. The full
  DAG proof is distributed among the docstrings: extend the augmentation, factor
  dh to k, use extMk(k)=-beta, evaluate k at p(1), identify the ordinary free
  torsor fibre, apply raw/normalized sign comparison, then pushout, pullback,
  quotient restriction and forget-support naturality.

Sources read: local Stacks `sites-cohomology.tex`, lemma-torsors-h1 (03AJ), and
`etale-cohomology.tex`, lemma-cohomology-with-support-triangle (0A45); the current
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/`
`lem-pur-divisor-class.proof.md`. The node is an agent-stated relative refinement;
no assertion is attributed as a verbatim extra clause of Stacks.

Edge cases checked before and after writing:

- Empty ambient scheme: all section and extension data reduce to zero objects;
  the formulas and unique choices are still typed.
- Empty support (W=T): Q=0; the extension and relative class are zero. P has its
  supplied global section, so the ordinary class is also zero.
- Full support (W empty): the open term is zero, the frame on the empty object is
  unique, and the comparison reduces to ordinary Ext/sections normalization.
- G=0 and the trivial framed torsor: both classes vanish. A nonzero frame of a
  trivial torsor need not give zero relative class; no assertion discards it.
- q=0: normalization uses the actual shifted cone coordinate in degree -1,
  whose open term is zero by extension of the nonnegative resolution. There is
  no predecessor-natural-number assumption or excluded degree.
- Identity coefficients and pullbacks, equality of complementary opens, and
  identity support enlargement are included, with arbitrary augmented comparison
  lifts. No extra universe equality or nonemptiness binder is used.
- Closed subscheme structures with the same support need not factor into each
  other. Support enlargement uses the universal quotient map, avoiding such an
  unsupported hypothesis. Etale pullback is genuinely Cartesian; hW is only its
  explicit typing identification.

Searches (2026-10-24; via the prescribed msearch.py):

- LeanFinder: "Relative torsor extension class equals relative cohomology class
  under supported Hom comparison" returned eight results, including
  `InjectiveResolution.extEquivCohomologyClass_extMk` and analogous projective
  results; no relative framed supported-comparison theorem.
- Loogle: "InjectiveResolution.extMk, Abelian.Ext, constantSheaf" returned zero
  results with "unknown identifier 'InjectiveResolution.extMk'". The declaration
  was located and its exact type read directly in Mathlib instead.
- Mathlib grep: `extMk|relativeTorsor|closedSupport` in
  `CategoryTheory/Abelian/Injective` returned five hits in Injective/Ext.lean,
  including extMk and its cohomology-class formula. These are used.
- LeanSearch: "Ext from a closed supported constant integer sheaf computes
  relative cohomology of a torsor with section" returned eight results, including
  `Sheaf.H`, `InjectiveResolution.extEquivCohomologyClass`, and general sheaf
  cohomology functors; none states this relative torsor normalization.
- Project `rg` searches for relative torsor, relative extension, supported integral
  constants/unit/exchange, normalization and this node id were run in both
  `lean/WeilConjectures` and `lean/Sheaf`; the exact node-id search in upstream had
  no declaration. Existing matches were the recorded relative extension theorem,
  the cone and torsor comparison modules, and the specialized framed-line
  extension. The latter is restricted to line-bundle/Gm torsors and does not
  state this arbitrary-abelian-torsor theorem. Existing constants and the raw
  relative equivalence were reused through the added landed dependencies.
- The upstream declaration-name index was searched for relative extension and
  cohomology names: no exact declaration of this item.

Validation: scompile.py compiled the completed module in both sandbox and library
module modes. The one long-line warning found after adding the fibre clause was
fixed. deliver2.py --no-push then compiled the final module cleanly and reported
OK (dry run), commit 14862f3941b: preflight passes and the file compiles. All 11
theorem proofs are exactly by sorry; all 21 declarations are recorded. The main
recorded signature was checked verbatim and every Lean line is at most 100
characters. No global build or direct repository write was performed.

## Second reading by Q151

This is the author's second reading under the dispatcher instruction not to start
other agents; the maintainer supplies the independent review. I re-opened the node
and checked its clauses against the complete module and the actual upstream types.
The following issues found during that pass were repaired before delivery:

1. The raw cocycle equivalence is not the positive ordinary class. The theorem uses
   its negative, matching the actual construction of relative_torsor_cohomology.
2. Canonical supported integral constants and the unit already exist. They are
   imported unchanged and their owning landed node is explicitly cited.
3. Inclusion of open complements does not imply a morphism between arbitrary
   closed subscheme structures. The support map is instead defined by the unique
   factorization p' q=p, and the theorem assumes only the required open inclusion.
4. Equality of the ordinary Ext class should retain the fibre/action clause.
   Added relative_extension_fibre, with a componentwise bijection from the original
   torsor and its original equivariance equation, as well as the ordinary
   presentation equality and positive H1 forget-support equation.
5. The comparison must be normalized in every degree, including zero. Its unique
   characterization uses the actual first projection and zero second coordinate,
   and is imposed on all Ext resolution cocycles. No independent comparison or
   hidden sign may be chosen.

Every hypothesis has its counterpart listed above. The coefficient and pullback
representatives are arbitrary models of the canonical maps, not extra purity or
triviality assumptions. All choices are justified by uniqueness statements. The
module retains the prescribed frame, original action, ordinary Ext convention and
signed cone; no statement defect or unresolved disputed statement was found.
