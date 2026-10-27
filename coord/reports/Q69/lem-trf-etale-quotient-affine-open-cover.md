## Worker report

Q69, stage 2, 2026-10-22. Module:
`Sheaf.AlgebraicGeometry.EtaleQuotientAffineOpenCover`.
Main statement: `AlgebraicGeometry.AlgebraicSpace.etale_quotient_affine_open_cover`.
The only postponed proof is this named theorem. Its docstring gives all seven
steps of the existing node proof, with the source places and dependency ids.
The eight helpers in `AlgebraicGeometry.AlgebraicSpace.AffineQuotientCover` have
real data: chart objects and their coproduct in `Over S`, the coproduct inclusions,
the induced coproduct map, and the two projections of each iterated restriction.
They introduce the canonical constructions belonging to this item, using Mathlib pullbacks and their projections directly, not a new independent
mathematical notion.

This repairs the independent review of head `8ce5851f2fc9`. The accepted
statement and seven-step proof remain verbatim; only the Lean interface and its
record are repaired.

Hypotheses and clauses, in order:

- A scheme S and schemes R,V over S are `{S : Scheme.{u}} {R V : Over S}`.
  Their structure morphisms are part of `Over S`.
- The morphism j=(s,t) is `prod.lift s t` in `Over S`; its monomorphism condition
  is `[Mono (prod.lift s t)]`. The product in the slice is the fibre product
  over S. The maps s,t are the explicitly bound `s t : R ⟶ V`.
- Identification with an equivalence relation for every test scheme is `hrel`:
  `∀ T : Over S, Equivalence (fun a b : T ⟶ V ↦ ∃ r : T ⟶ R,
  r ≫ s = a ∧ r ≫ t = b)`. Monicity makes a relation witness unique.
- The two étaleness hypotheses are `[Etale s.left] [Etale t.left]`.
- F is `Sheaf (Scheme.fppfTopology.over S) (Type u)`. The presheaf
  `coequalizer (yoneda.map s) (yoneda.map t)` is the pointwise quotient presheaf.
  Its map `η` to `F.obj` and `hη` (bijection by precomposition with η for every
  fppf sheaf G) are precisely the sheafification universal property. The quotient
  map q is written explicitly as `coequalizer.π ... ≫ η`. This is the recorded
  restriction/finding-opens interface, without assuming that all small-valued
  presheaves on the big site admit small-valued sheafification.
- The chosen set-indexed affine open covering is
  `𝒰 : Scheme.OpenCover.{u} V.left` with `[∀ i : 𝒰.I₀, IsAffine (𝒰.X i)]`.
  An open cover already supplies open immersions and joint surjectivity.
  Mathlib's `IsAffine` means isomorphism with the spectrum of the global sections;
  conversely a scheme isomorphic to a spectrum is affine. Thus this includes
  arbitrary affine charts, not only charts supplied literally as spectra.
- U is the actual categorical coproduct `AffineQuotientCover.coproduct V 𝒰`
  of the chart objects in `Over S`; its underlying object is a scheme. The
  forgetful functor from the slice creates coproducts, so its underlying scheme
  is the scheme coproduct. The inclusions are `inclusion V 𝒰 i` and g is
  `map V 𝒰`, constructed by `Sigma.desc` from the given open inclusions.
  No arbitrary replacement map is supplied as a hypothesis.
- Open and closed summand inclusions are the first conclusion:
  `∀ i, IsOpenImmersion (inclusion V 𝒰 i).left ∧
  IsClopen (Set.range (inclusion V 𝒰 i).left)`.
- Surjective étaleness of g is
  `Surjective (map V 𝒰).left ∧ Etale (map V 𝒰).left`.
- R_U is `Limits.pullback (pullback.snd (map V 𝒰) s ≫ t) (map V 𝒰)`,
  the genuine iterated pullback, with projections `source s t 𝒰` and
  `target s t 𝒰`.
  The next conclusions give its monomorphism into the product, its pointwise
  equivalence-relation condition for all T, and étaleness of both projections.
- R_i is the second iterated restriction
  `Limits.pullback (pullback.snd (inclusion V 𝒰 i) (source s t 𝒰) ≫
  target s t 𝒰) (inclusion V 𝒰 i)`.
  Its projections are `chartSource s t 𝒰 i`, `chartTarget s t 𝒰 i`.
  The next family of conclusions gives all three equivalence-relation clauses:
  monicity, pointwise equivalence for all T, and étaleness of both projections.
- Q and F_i are the subsequent universally quantified sheaves `Q` and `Fi i`,
  with units `ηQ`, `ηi i` from the respective presheaf coequalizers and the same
  sheafification universal properties `_hηQ`, `_hηi`. These are arbitrary choices
  of the named sheafifications in the node, not arbitrary sheaves with arbitrary
  arrows. Moving their binders inside the conclusion keeps the earlier geometric
  conclusions independent of quotient choices.
- The canonical Q→F is the existential `β : Q.obj ⟶ F.obj`. `IsIso β` is the
  isomorphism clause. Its quotient-projection equation says it sends [a] to [ga].
  That equation uniquely determines β: the presheaf coequalizer projection is epi,
  and the injectivity part of `_hηQ` then gives equality of any two such maps.
- The canonical F_i→Q are `α i`. Their quotient-projection equations say [a] maps
  to [ι_i a]. They are likewise uniquely determined by `_hηi`. Consequently
  `α i ≫ β` is exactly the canonical composite specified by the node.
- The open-immersion assertion is
  `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) (α i ≫ β)`.
  Unfolding the existing definition quantifies over every T and every
  `yoneda.obj T ⟶ F.obj`, and supplies a scheme over T and a representing
  pullback square with an open immersion to T. This is precisely representability
  by an open subscheme, without any algebraic-space assumption.
- Covering as a sheaf is the final clause `∀ T x, ∃ C : Presieve T, ...`.
  The condition `C.map (Over.forget S) ∈ Scheme.fppfPrecoverage T.left`
  says that this is an actual jointly surjective flat locally finitely presented
  covering family after forgetting to schemes. For every arrow f in C there are
  an index i and a section y of F_i over its domain W such that
  `(α i ≫ β).app (op W) y = F.obj.map f.op x`. Thus every restriction of x on
  the covering is the image of a section of one of the chart quotients. A
  presieve is a set-indexed family of arrows and does not impose finiteness.
- There is no `IsAlgebraicSpace F`, `IsAlgebraicSpace (Fi i)`, Noetherian,
  quasi-compactness, separatedness, nonempty-index, or finite-index hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `AlgebraicGeometry.Spec`, `Spec.map` (def-pc-scheme and
  def-weil-affine-spectrum); the affine condition is Mathlib's `IsAffine`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd` (def-pc-fibre-product),
  used directly in the helper types, helper data and theorem statement.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`
  and `Etale.instOfIsOpenImmersion` (def-weil-etale-morphism and the
  open-immersion-etale proof leaf). `IsZariskiLocalAtSource.iff_of_iSup_eq_top`
  in `Mathlib.AlgebraicGeometry.Morphisms.Basic` is the source-locality leaf.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`
  (def-weil-open-immersion).
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`,
  `toSheafify`, `sheafificationAdjunction` (def-weil-pbc-sheafification).
  The hη interfaces express that adjunction for the specific quotient presheaves.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`, together with `GrothendieckTopology.over` from
  `Mathlib.CategoryTheory.Sites.Over` (def-pc-fppf-site).
- `Sheaf.AlgebraicGeometry.EtaleRelationRestrictionQuotient`:
  `AlgebraicGeometry.AlgebraicSpace.etale_relation_restriction_quotient` is
  used by proof steps 3 and 4 only. Its import is now plain `import`, never
  `public import`; it remains in proof_deps and is absent from stmt_deps.
  The statement does not refer to any of its restriction helper definitions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`. The existing
  predicate renders the representable-open-immersion clause only; its
  algebraic-space predicate is not a hypothesis. The advisory stmt_deps addition
  is removed to preserve the base dependency list exactly under H2.
- `Mathlib.AlgebraicGeometry.Limits`: `sigmaOpenCover`,
  `disjoint_opensRange_sigmaι`, and the coproduct existence instance
  (lem-weil-pbc-scheme-coproduct-family). The construction itself uses
  `CategoryTheory.Limits.Sigma.ι` and `Sigma.desc` in the slice category.
- Proof imports are `Sheaf.AlgebraicGeometry.EtaleRelationFindingOpens`
  (`AlgebraicGeometry.AlgebraicSpace.etale_relation_finding_opens`),
  `Sheaf.CategoryTheory.SiteCoveringAxioms`
  (`CategoryTheory.Precoverage.IsSiteForCoverings`), and
  `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
  (`CategoryTheory.sheafification_sections_local`). Mathlib proof leaves are
  exported by the public imports. No import of the parent quotient theorem is
  used, avoiding a cycle when this item is imported into that theorem's module.

Edge cases checked before writing:

- Empty covering index: the open-cover condition then forces V empty, and U
  is the empty coproduct; no `Nonempty` assumption occurs. Empty T admits the
  empty fppf covering, so the last clause works without choosing a chart.
- Infinite index: the construction uses all u-small coproducts of schemes,
  not finite coproducts or quasi-compact morphisms. The chosen universe is the
  universe of the schemes, as required by the project's size convention.
- Empty R with nonempty V fails hrel (reflexivity), as it should. The diagonal
  relation gives Q≅h_V with the original chart open cover.
- Overlapping/repeated chart images are allowed; only their images inside the
  coproduct are disjoint. No pairwise-disjointness hypothesis is imposed on V.
- No condition that intersections of affine charts are affine is imposed.
- Non-affine or non-algebraic-space quotient sheaves are not excluded by the
  signature. All representability is a conclusion.

Searches actually run through `/home/ubuntu/weil-launcher-all/batch2/msearch.py`
with group Q69 and this item:

- LeanFinder, query: "Affine open charts of an etale equivalence relation give
  representable open immersions covering its fppf sheaf quotient". Eight hits
  on affine-transition-limit covers and scheme étale sites; no quotient theorem.
- Loogle, query: `AlgebraicGeometry.Etale, AlgebraicGeometry.IsOpenImmersion`.
  One hit: `AlgebraicGeometry.Etale.instOfIsOpenImmersion`, the existing proof
  leaf, not this statement.
- grep, query: `quotient.*[Oo]pen[Cc]over|[Aa]ffine.*[Qq]uotient`, subdirectory
  `AlgebraicGeometry`: zero Mathlib hits.
- LeanSearch, same sentence as the LeanFinder query: eight hits including
  `Scheme.affineOpenCover`, `Scheme.affineCover`, `Scheme.AffineOpenCover`,
  and affine-open image lemmas; no quotient theorem.
- `rg` in the project's `lean/WeilConjectures` and `lean/Sheaf` for
  `(quotient|Quotient).*(openCover|open_cover)|(openCover|open_cover).*(quotient|Quotient)`
  and `AffineQuotientCover|etale_quotient_affine_open_cover`: no exact existing
  statement or helper namespace. Searching the node id in both trees returned
  no existing module. Broader etale-relation searches found the recorded
  restriction and finding-opens modules, which this delivery reuses.

Source read: `literature/stacks-project/spaces.tex`, theorem-presentation,
particularly its affine-coproduct replacement and chart-quotient paragraphs.
This agrees with the existing stage-1 split. No statement correction, new node,
unusable-dependency repair, or STATEMENT-DISPUTED issue is needed.

## Second reading by Q69

This is a direct worker delivery; no independent second worker was started or
claimed. The maintainer's independent review is pending. I performed a second
self-check against the node and the full module: all listed hypotheses occur
in the main signature, the actual coproduct and two iterated restrictions
appear in the helper data, and every geometric and sheaf-cover conclusion is
present. In particular the existential maps are constrained by quotient-unit
compatibility equations, not arbitrary maps; the cover is fppf, not just a
pointwise statement or an epimorphism without local lifts; and no algebraic-space
hypothesis is introduced. All helper declarations have the owning node's tag,
all universes and variables are explicitly bound, and `autoImplicit` is false.
The only change to the live node is its lean record. The base stmt_deps list is
restored exactly, and every statement/proof field is unchanged. I checked that
the new pullback expressions and projections are definitionally the same as
the formerly imported helpers: first pull back g along s, compose its R
projection with t, then pull back along g; the source is the composite of the
two first projections and the target is the second projection. Repeat this
construction with the summand inclusion for each chart. This preserves each
relation clause and each quotient compatibility equation.

## Repair of the return

H2 / theorem stmt_dep: chose the reviewer's inline-pullback repair. There is no
new generic restriction definition and no new definition node. The source,
target, chartSource and chartTarget helpers now use Mathlib pullbacks and
projections directly; the two quantified relation objects are written as the
same pullbacks. The public restriction-quotient import and its added stmt_dep
are removed. A plain proof import is retained because the theorem remains in
proof_deps and is the required input to proof steps 3 and 4 (stage-2 rule 7).
No definition in the delivered statement depends on that theorem or its helpers.
The algebraic-space dependency addition noted in the advisory is also removed;
its existing representability predicate is still used without duplication.

Compared the saved packet with current live: before the repair it changed
stmt_deps by adding restriction-quotient and algebraic-space. After the repair,
all fields except lean match the current live node exactly. The initial saved
packet passed dry run at `54311beb192`; that mechanical pass did not resolve
the independent mathematical review, hence the substantive repair above.

## Validation

The repaired module passed the prescribed server `scompile.py` in sandbox and
library module modes (19.1 s and 11.0 s), with no errors or unexpected warnings.
The first repair probe caught a name collision with AlgebraicSpace.pullback;
qualifying the object construction as Limits.pullback resolved it without any
change in mathematical content. All lines are at most 100 characters, every
variable and universe is explicitly bound, and the lean.statement record is
the signature verbatim. The only sorry is the named main theorem.

The repaired packet passed `deliver2.py --no-push`: OK at `0ffd8d401c9`,
including server preflight and per-file compilation. The final self-check also
confirmed the verbatim signature, the lean-only node delta and the absence of
all restrictedEtaleRelation helper references in the module.
