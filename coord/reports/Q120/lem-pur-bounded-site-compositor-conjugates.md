## Worker report

Item: lem-pur-bounded-site-compositor-conjugates. Module:
`Sheaf.Paper.BoundedSiteCompositorConjugates`. Main declaration:
`AlgebraicGeometry.ProEtale.BoundedSiteConjugates.boundedSiteCompositorConjugates`.
All declarations in this module belong to this node and are listed in its lean record.
There is one postponed theorem, with proof `sorry`; every helper has real data.
No node statement, dependency list, proof plan, or other base field is changed.

The main statement quantifies over the finite words and pastes required by the last
paragraph of the node, so includes both displayed equations as its primitive instances.
The constructions do not posit an ambient exceptional adjunction on the pro-etale site.

Hypothesis and clause correspondence:

- The finite-field datum, ell different from p, the finite extension and positive level
  are precisely `P : WeilConjectures.PurityFiniteSetting.{u}`. The ring is its existing
  `P.Coefficient`, the standard ULift of O_E/(varpi^n). No arbitrary coefficient ring
  or alternative ring sheaf is substituted.
- A k-scheme is an object of `Over (Spec (.of P.field.k))`. `Stage` contains exactly
  the locally-finite-type and quasi-compact structure morphisms of source and target.
  The main theorem repeats these conditions for its external endpoints, also allowing
  the empty identity word. Its `f` is a morphism in that over category, so its triangle
  over k is built in. `separated`, `finiteType`, `quasiCompact` are imposed on f.left,
  not on the structure morphisms. Thus no absolute separatedness is assumed.
- A stage's `c : Compactification f.left` is the chosen j,p factorization. Its ordinary
  etale right adjoint and adjunction are `right`, `adjunction`. They are the ordinary
  compactification-relative functor and its right adjoint, not arbitrary pro-etale data.
  The finite dimension bound carried by the stage is auxiliary and exists for every
  such compactification: its proper ambient is finite type over the finite-type target,
  and `exists_topologicalKrullDim_le` applies. Empty ambient has bound zero.
- The ordinary module derived categories are exactly `DerivedCategory (Sheaf ...
  (ModuleCat.{u+1} P.Coefficient))` on the actual small sites. The lower-bounded
  subcategory is `DerivedCategory.Plus`. Site object and morphism universes are not
  equated. No constructibility or finite-Tor hypothesis is introduced.
- `Word.left` is the ordinary etale F word. `Word.leftPlus` uses the recorded bounded
  functor; `Word.homEquiv` inserts the existing PlusCompatibility isomorphism into the
  ordinary adjunction Hom bijection. The Plus and unbounded models are not silently
  identified by definitional equality. On a composite its bijection is the composite
  first through the last word and then through the first, exactly Adjunction.comp.
- `Word.proLeft` is the actual unbounded pro-etale compact-support word. Its single
  stage is the existing `coherenceProEtaleFunctor` (Rp_* j_!). `Word.boundaryIso` uses
  the existing proper-mate/open comparison, `coherenceBoundaryComponent`, and on
  a word is recursively B_V followed by F_V^p(B_U).
- `Word.right` reverses the ordinary etale right adjoints. `Word.proRight` reverses
  the transported functors Rnu_* then H then nu^*. This is exactly the finite exceptional
  construction in `sfFiniteExceptionalAt`, retaining the supplied ordinary adjunction.
  `Word.rho` at a single stage is literally `asIso (boundedSiteRho ... H K)`;
  invertibility is taken from the existing boundedSiteAdjunctionTranspose theorem.
  For U followed by V, rho is a_U at G_V^e K followed by G_U^p(a_V,K).
- `K : DerivedCategory.Plus ...` is the bounded input. `Word.Admissible` requires its
  lower bound, that of the full ordinary exceptional image and those of the recursive
  intermediate exceptional images. `Paste.IntermediateBounds` additionally records
  exceptional images at each vertical intermediate word and recursively after
  whiskering. These are precisely the stipulated intermediate witnesses, not a
  restriction on arbitrary unbounded pro-etale exceptional adjoints. Compact-support
  intermediate etale images are in Plus by the existing functors' domains.
- `Paste.compositor s t v` uses f, g, and f ≫ g, with their three chosen compactifications.
  Its etale arrow is the recorded `coherenceEtaleCompositor.hom.app`; its pro-etale
  arrow is the recorded `coherenceProEtaleCompositor`. These are the choices of
  def-pur-chosen-compactification-compositors and not arbitrary isomorphic maps.
- `Paste.refinement s t r` requires the actual proper refinement `r : s.c.Refinement t.c`.
  Its etale arrow is the inverse of the existing d-to-c refinement isomorphism,
  hence has the node's c-to-c' direction. Its pro-etale arrow is precisely
  `(properTransportRefinement ... r J).hom` with the same direction.
- `Paste.etaleConjugate` is the actual transpose of the chosen etale left arrow at
  J=G_V^e K followed by the target counit. `Word.counit` is the inverse ordinary
  Hom bijection at identity. Thus it is the conjugate from conjugateEquiv, evaluated
  with the canonical bounded-below compatibility maps, not a newly selected arrow.
- `Paste.proConjugate` is the actual bounded-origin transpose at the witness
  J=G_V^e K with the witness isomorphism a_V. The arrow B_V inverse followed by
  C(epsilon_V) is exactly F_V(a_V) followed by epsilon_V^p by the existing
  normalized counit equation, iterated for words. This computes the conjugate
  of the actual pro-etale left arrow, then removes the witness using a_V inverse.
  It never defines a pro-etale conjugate as C of its etale counterpart.
- The main theorem's second conjunct is
  `C_X.map D.etaleConjugate ≫ U.rho = V.rho ≫ D.rightMap`.
  For compositor U=[f,g], V=[h], this expands to
  C_X(t_e) then a_f at G_g^e K then G_f^p(a_g) = a_h then t_p,
  exactly the first displayed formula in diagrammatic composition order.
  For refinement U=[f,c], V=[f,c'], it expands to
  C_X(q_e) then a_c = a_c' then q_p, exactly the second displayed formula.
- The first conjunct states that the conjugate of the entire chosen left paste is
  the independently assembled `Paste.rightMap`. The latter reverses vertical
  composition; before-whiskering applies the right word; after-whiskering uses the
  actual a_W witness to evaluate the component. Primitive arrows alone are transposed.
  Thus the first conjunct is the final finite-pasting assertion, not a tautological
  equality of two identical definitions. Identity, associator and both unitor
  constructors of Paste evaluate to their canonical identity components, while the
  conjugate of the entire diagram is still calculated by transposition. This includes
  identity preservation, reassociation and mixed refinement/compositor pasting.
- No tensor, projection, Cartesian exchange, smoothness or purity conclusion occurs.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: WeilConjectures.PurityFiniteSetting and Coefficient.
- Scheme morphism properties are the recorded convention's Mathlib LocallyOfFiniteType,
  QuasiCompact and IsSeparated; the convention has no module of its own.
- `WeilConjectures.Compactification.RefinementCategory`: Compactification.Refinement.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: ordinary Sheaf/ModuleCat derived
  category encoding; DerivedCategory.Plus is the Mathlib lower-bounded category.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: FiniteCoefficientModules and its
  fixed-ring realization, as retained by the bounded transpose dependency. This node
  explicitly asks for its ordinary fixed-ring coordinates.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  siteComparisonDerivedPullbackPlus and the existing comparisonUpperStar.mapDerivedCategory.
- `Sheaf.Paper.CompactSupportSiteCoherence`: coherenceEtaleFunctor, coherenceProEtaleFunctor,
  coherenceSiteFunctor, coherenceBoundaryComponent, coherenceEtaleCompositor,
  coherenceProEtaleCompositor, properTransportRefinement; the existing site coherence
  theorem supplies the squares in the proof plan. The helper syntax here is the smaller
  refinement/compositor-only fragment, with adjoints and exceptional boundedness retained.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`:
  isLeftAdjoint_rightDerivedLowerShriekOfCompactification, the ordinary etale adjoint.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: the recorded declaration
  System concerns all coefficient stages. The finite declaration the same record retains
  is `AlgebraicGeometry.ProEtale.sfFiniteExceptionalAt` in the publicly imported
  `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`; its actual U H C construction is
  used here with the ordinary adjunction supplied as in the bounded transpose node.
  No integral/rational system is needed for this exclusively finite statement.
- `Sheaf.Paper.BoundedSiteAdjunctionTranspose`: boundedSiteRho, boundedSiteTranspose,
  boundedSiteAdjunctionTranspose. This is the specified forward Hom-chain normalization;
  its published theorem, not an ambient adjunction assumption, supplies invertibility.
- `Mathlib.CategoryTheory.Adjunction.Mates`: conjugateEquiv and the component/counit,
  identity and pasting formulas. `Adjunction.comp` and `Adjunction.id` are used in
  Word.adjunction. The word Hom bijection recursively uses their exact composition order.
- Proof imports: `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  exists_topologicalKrullDim_le; `WeilConjectures.Mathlib.Topology.KrullDimension`,
  topologicalKrullDimAt; Mathlib.Topology.KrullDimension, topologicalKrullDim, is already
  public through the transpose dependency. Mate-pasting is the cited Mathlib mates module.

Edge cases checked before and during writing: zero K; empty schemes and empty
compactification ambient (bound zero); no absolute separatedness; n=1 and all positive
levels; identical compactifications and identity refinements; one-stage and empty words;
identity on either side of composition; both bracketings of triples; successive refinements;
vertical paste and both whiskerings, including whiskering after a nontrivial exceptional
word where the intermediate witness is essential. Universes keep schemes at u, actual
site objects at u+1 and ModuleCat values at u+1, without new site equalities.

Searches actually run:

- msearch.py leanfinder: "Bounded etale proetale site comparison respects conjugates of
  compact support compositors and refinement diagrams". Eight hits, ordinary small
  etale site definitions and general condensed site constructions; no matching theorem.
- msearch.py loogle: "CategoryTheory.conjugateEquiv, CategoryTheory.Adjunction.comp".
  Twelve hits, including conjugateEquiv associator/unitor/whiskering lemmas and
  CompositionIso. These cover the categorical calculus, not the bounded site theorem.
- msearch.py grep: "conjugateEquiv|mateEquiv_hcomp" in CategoryTheory/Adjunction.
  Twelve hits in Mates/CompositionIso/Unique; reused the existing calculus.
- rg of lean/WeilConjectures and lean/Sheaf:
  "boundedSite.*[Cc]onjug|compositor.*[Cc]onjug|lem-pur-bounded-site-compositor-conjugates".
  Related coefficient-compositor and general equivalence-conjugation files, no exact match.
  Read CompositorEquivalenceConjugation: it concerns equivalences and arbitrary functors,
  not the actual bounded-origin exceptional Hom chain and chosen compactifications.
- grep -rn of the item id in lean/WeilConjectures: no hit. rg of the proposed namespace
  and main name in lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no hit.

Source checked at literature/blueprint/latest, lem-pur-co-smooth-etale-locality.proof.md
Step 3 (ordinary transitive counits), thm-pur-composition-coherence.proof.md Steps 1--2,
and Stacks categories.tex labels lemma-transformation-between-functors-and-adjoints
and lemma-compose-counits (Tags 0B65 and 0DV0). The node's older snapshot source field
was preserved, while source reading used latest as instructed.

Validation: scompile.py on this complete delivered file passed both sandbox and library
module compilation, with no errors or warnings (14.6 s and 12.6 s in the final run).
No global build, local Lean invocation, git command or source modification was performed.

## Second reading by Q120

The dispatcher instructs this worker to deliver itself and prohibits starting other agents;
this is an explicit self-check, not a claim of an independent second worker's review.
Opened the node and the full generated module together. Checked the coefficient carrier,
finite-type assumptions on each stage and endpoint, morphisms over k, relative separatedness,
actual compactifications, ordinary adjunction, exact U H C exceptional construction and rho.
Expanded the compositor/refinement constructors and checked each source and target against
both displayed formulas. Checked the reversed refinement direction and the g-then-f Hom
bijection. Inspected rightMap's recursion: vertical reversal and both whiskerings produce
exactly the right words, with the W.rho witness inserted after whiskering. Identity and
associator constructors have identity components; the entire diagram's conjugate remains
computed separately, so preservation is a theorem clause rather than a definition.
No statement correction, weakening, hollow map or unbounded pro-etale adjunction is present.
The compiler-discovered mismatch between Plus and unbounded compact-support models was
repaired with the published PlusCompatibility isomorphism, not an equality assumption.
An independent maintainer delivery review remains required as the brief specifies.
