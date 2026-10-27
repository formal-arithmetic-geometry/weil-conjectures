## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleAlgebraExtensionExt` states
`AlgebraicGeometry.AlgebraicSpace.etale_algebra_extension_ext`. Its only theorem has
proof `sorry`. It asserts `Nonempty (EtaleAlgebraExtensionClassification f)`;
the record includes the actual class bijections and all their normalizations and
compatibilities. All definitions have actual data; no object is chosen from this
existence theorem.

Read the complete item, its nine proof steps, all four statement dependencies and
their recorded interfaces. Read Stacks `defos.tex`, the statements and constructions
at 0GQ5 (extension classification), 0GQ6 (positive conormal representative), 0GQ7--0GQ8
(coefficient pushout), and 08UG(2) (degree-zero automorphisms). This is the lower
supporting lemma of the direct-image/tangent-finiteness route, not a blueprint unit
statement. The original natural-language statement and proof are unchanged.

Hypotheses and clauses, individually:

- `S : Scheme.{u}` is the arbitrary base scheme; `X B : AlgebraicSpace S` are
  precisely the existing fppf-sheaf algebraic spaces, and `f : X ⟶ B` is arbitrary.
  No separatedness, finite type, flatness, or characteristic condition is imposed.
- `G : X.Modules` is an arbitrary module sheaf on the full small etale site.
  No quasi-coherence, projectivity, injectivity or finiteness hypothesis appears.
- `SpaceSquareZeroExtension f G` is the already-landed extension notion. Its
  `algebra` is a ring sheaf with `commutative`; `quotient` and `inclusion` are the
  displayed p and i. `inclusion_naturality`, `injective`, `kernel` and
  `locally_surjective` express exactness of sheaves, not sectionwise surjectivity.
  `square_zero` states the kernel ideal has square zero; `scalar` gives exactly the
  specified O_X-action. Its existing `base : ChartRingMap ...` and `base_quotient`
  give the f-inverse-image O_B algebra structure on all compatible chart pairs.
- `EtaleExtensionHom v E F` fixes quotient and base and induces the specified
  coefficient map v on the named kernel. At `v = 𝟙 G`, `EtaleExtensionIso` retains
  an actual ring-presheaf isomorphism with these conditions. Sheaf conditions are
  properties, so such isomorphisms are exactly isomorphisms of sheaves. The
  `Quot` in `etaleExtensionClasses` is therefore pi_0 of the marked groupoid;
  `etaleExtensionClass` is its quotient map.
- `etaleCotangentExt f G n` uses the dependency's `derivedExt`, `naiveCotangent`,
  and `cotangentCoefficient`; it first applies the actual `X.smallModuleRestriction`
  to G. This is the existing equivalent affine-basis model, not a second module
  category or coefficient lift. `[HasDerivedCategory.{w} X.SmallModules]` retains
  arbitrary localization morphism universe w, as the recorded cotangent interface
  does. There is no equality restriction on u and w.
- `classes G` is the required bijection to Ext^1. Its `class_normalization` uses
  `EtaleExtensionCoordinates`: the sheaf-surjective polynomial presentation,
  actual base-compatible lift, actual conormal quotient and differential term,
  conormal map `delta`, and the canonical generator-map comparison into the fixed
  naive cotangent complex. `delta_formula` says the kernel image equals the lifted
  polynomial. `comparison_conormal` and `comparison_differentials` normalize the
  comparison on all quotient classes and universal tensors; `projection_normalization`
  fixes the projection to degree -1 as the identity. `Represents` is the POSITIVE
  conormal boundary followed by this comparison, using Mathlib's specified
  single-functor shift isomorphism. This prevents an arbitrary sign or an arbitrary
  abstract Ext bijection from satisfying the record.
- `split_exists` and `split` express the O_X ⊕ G origin. `EtaleExtensionIsSplit`
  retains an actual base-compatible algebra section; its isomorphism from the
  trivial extension is (a,g) ↦ s(a)+i(g). Conversely that trivial extension has its
  standard section. Thus this is exactly the split class, whose image is zero.
- `pushout_exists` supplies an extension and an actual `EtaleExtensionHom v` for
  EVERY linear v, even when v is neither monic nor epic. Any such map between
  square-zero extensions is the coefficient pushout: locally lift the common
  quotient, and the difference is in H, yielding the quotient of E ⋉ H by the
  graph (i(g),-v(g)). This establishes the universal pushout characterization
  without choosing an arbitrary operation. `naturality` identifies its class with
  `etaleCotangentExtMap v 1`, which is exactly shifted derived postcomposition.
- `EtaleExtensionBaer E F T` uses `Limits.pullback E.quotient F.quotient` in ring
  presheaves. This is the sheaf fibre product, since ring sheaves are closed under
  limits. Its map is natural and multiplicative by its type, is over the quotient
  and base, and has kernel map `(g,h) ↦ g+h`. Since T is already an extension,
  this is precisely pushout of the fibre product along addition. `baer_exists`
  ensures existence, and `baer` equates its class with the sum of classes.
- `augmentation` maps the fixed complex to the existing differential sheaf in
  degree zero. `augmentation_formula` fixes its value on EVERY b tensor dp to
  b d(eval(p)); `omegaIso_hom` identifies `omegaIso` with its homology map, giving
  the stated Omega = H^0(NL) identification with the usual differential module.
- `homZero G` is the additive equivalence Ext^0 ≃ Hom(Omega,G). Its
  `homZero_normalization` is factorization through the normalized augmentation
  after the standard shift-zero identification, not a bare additive equivalence.
  `homZero_natural` states postcomposition naturality for every coefficient map.
- `automorphisms E` is a bijection from Ext^0 to automorphisms fixing both ends.
  `automorphism_formula` is a ↦ a+i(d(p(a))), where d is exactly the universal
  derivation postcomposed by `homZero G x`. The formula is given on every affine
  chart of the actual etale site; the basis comparison uniquely determines its
  extension to all charts. It is therefore the same formula on the entire site.
- `automorphism_add` says composition is addition; the order displayed is
  T_(x+y)=T_x composed with T_y. `automorphism_natural` is the full equality
  T_x ≫ q = q ≫ T_(v_*x), the coefficient-pushout compatibility. Together with
  `homZero_natural` it gives naturality on both Hom(Omega,-) and Ext^0.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `structurePresheaf`, `structureSheaf`, `Modules`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib's `SheafOfModules` and its existing morphisms.
- `Sheaf.AlgebraicGeometry.SpaceNaiveCotangentComplex`: `naiveCotangentComplex`,
  `naiveCotangent`, `derivedExt`, `cotangentCoefficient`, `cotangentPresentation`,
  `cotangentConormalClass`, `naiveCotangentTerm_degrees`.
- `Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData`: `SpaceSquareZeroExtension`,
  `ChartRingMap`. This existing definition is cited by the added already-landed
  `def-sfb-space-square-zero-extension-data` statement dependency.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `SmallModules`,
  `smallEtaleInclusion`, `smallStructureSheaf`, `smallModuleRestriction`,
  `smallModuleEquivalence`. Added its existing node `def-sfb-space-small-ringed-model`.
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`: `cotangentRingMap`,
  `cotangentRingInverse`, `cotangentRingAdjunction`, `cotangentRingDirect`,
  `cotangentSmallEquivalence`, `enlargedCommEquivalence`. The explicit helper
  `cotangentInverseChartSection` uses the adjunction unit, actual enlarged-chart
  restriction, equivalence counit and affine comparison unit; there is no arbitrary
  coefficient section map or new geometric morphism.
- `Sheaf.CategoryTheory.SheafPolynomialCotangentComparison`: `Presentation`,
  `Model`, `polynomialSheaf`, `base`, `evaluation`, `kernelIdeal`, `polynomialMap`,
  `tensorD`, `differentialTerm`, `sheaf_polynomial_cotangent_comparison`. Its existing
  definition node `def-sfb-sheaf-polynomial-cotangent-presentation` is added.
- `Sheaf.CategoryTheory.Sites.InverseImageDifferentials`: `SheafDifferentials.omega`
  and `derivation`, cited through the existing `def-sfb-sheaf-differentials` node.
- Proof imports: `Sheaf.Algebra.Homology.TwoTermDerivedHomBoundary`
  (`twoTermBoundary_exact`, `twoTermCokernelHomEquiv` and naturality),
  `Sheaf.CategoryTheory.Sites.SheafifiedDifferentialsCokernel`
  (`sheafified_differentials_cokernel`), `Mathlib.Algebra.MvPolynomial.Basic`
  (`MvPolynomial`), `Mathlib.CategoryTheory.Sites.Sheafification`
  (`presheafToSheaf`). The comparison module is already public through the
  cotangent dependency. The proof node `lem-sfb-sheaf-cotangent-ext-representative`
  has no recorded declaration yet, so no import is invented for it; step 4 of the
  theorem docstring explicitly records its role for stage 3.

No new nodes or dependency repairs are needed. The helper declarations are the
morphism, isomorphism, component, Baer-diagram and normalization interfaces of
this one classification statement. Every one carries its source and blueprint id.
The theorem docstring gives all nine natural-language proof steps. No statement
correction or STATEMENT-DISPUTED flag is needed.

Edge cases checked before and during drafting: the empty scheme/empty etale site;
zero and arbitrary non-quasi-coherent coefficient modules; identity and zero
coefficient maps, including G→0 and 0→H; coefficients maps neither injective nor
surjective; identity morphism f, where the split extension is the only class but
its full base structure is still retained; arbitrary characteristic; arbitrary
u and derived localization universe w. Quotient surjectivity remains local, so
nonzero higher cohomology on charts is not excluded. No chosen finite atlas or
sectionwise lift of all quotient sections is assumed. The base-compatible
polynomial lift is available by using the extension's own underlying generator
sheaf, not a global splitting of its quotient.

Searches (all no match for this item; logged in sandbox searches.jsonl):

- msearch leanfinder: "Square zero extensions of sheaves of algebras classified
  by cotangent Ext one with automorphisms Ext zero"; eight ring-cotangent hits,
  including `Algebra.Extension.H1Cotangent`; no global sheaf Ext classification.
- msearch loogle: `"cotangentComplex", "Ext"`; eleven ring-level cotangent
  presentation hits, not the statement on arbitrary sheaves on an etale topos.
- msearch grep: `SquareZero|squareZero|square_zero` in Mathlib/CategoryTheory;
  zero matches.
- msearch leansearch: "Square zero sheaf algebra extensions and morphisms fixing
  kernel and quotient"; eight hits, `TrivSqZeroExt` and `Algebra.Extension`,
  which concern rings, not the etale sheaf classification.
- Direct rg in lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for the item id, new declaration names, square-zero extension and cotangent Ext
  patterns found no matching etale classification. It found the reused
  `SpaceSquareZeroExtension` and the Zariski-only `SquareZeroSheaf` interfaces.
  `Topology.ZariskiSheafAlgebraExtensionExt` concerns opens of a topological space,
  not arbitrary etale sites, so it is not an existing match. Its normalized
  conormal and derivation interfaces confirm the need to specify normalizations.

Validation: prescribed scompile.py compiles both sandbox and actual library module
forms cleanly, no warnings. The final checked module has autoImplicit=false and
explicit universe binders; only the requested theorem has sorry. Initial namespace
shadowing of `pullback` was fixed by qualifying `Limits.pullback`; the term-degree
casts use the actual existing `CochainComplex.of_X` equalities. No live source was
edited, no direct git command or global build was run.

## Second reading by Q46

This is an explicit self-review; no independent worker was started, as the dispatch
brief forbids other agents. The maintainer supplies the independent reading.

Re-read the complete node beside the final module. I matched every hypothesis and
clause as listed above. Found and fixed two substantive omissions in the first
draft: naturality/additivity alone did not normalize the canonical class bijection,
and the Ext-zero/Hom equivalence was not fixed by its augmentation. The final
`EtaleExtensionCoordinates.Represents`, `class_normalization`,
`augmentation_formula`, `omegaIso_hom`, and `homZero_normalization` address those
points. The existing extension kernel and chart base action are reused verbatim,
and the restricted coefficient is precisely the module in the source, through the
already-recorded affine-basis equivalence. The Baer diagram uses the actual
fibre product, and coefficient maps are completely arbitrary. Both the additive
automorphism law and its naturality are actual equations of ring-presheaf maps.
No hidden quasi-coherence or size restriction was found. All four added
statement dependencies are already landed definitions, not duplicate notions.
