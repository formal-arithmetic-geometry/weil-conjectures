## Worker report

The module `Sheaf.AlgebraicGeometry.UniversalConormalChartTransitivity` states all
clauses of lem-sfb-universal-conormal-chart-transitivity. Every theorem has exactly
`sorry` as its proof. Definitions have real data and choose only from unique
universal properties. No statement correction, new node, or dependency repair is needed.
The item's stmt_deps directly cites the landed owners of the normalized tensor
composition and square comparisons, universal-thickening predicate, structural
module map and tensor-to-etale-restriction comparison.

Hypotheses and clauses, checked against the node:

- The base scheme is `{S : Scheme.{u}}`, and all spaces are `AlgebraicSpace S`.
  Explicit `universe u` and `set_option autoImplicit false` retain the dependency
  framework's universes, including its small-site module categories. The size
  convention is metatheoretic and needs no new object or derived-category instance.
- The tower is `(a : Z ⟶ Y) (b : Y ⟶ X)`, with exactly
  `SpaceFormallyUnramified a` and `SpaceFormallyUnramified b`. There is no
  representability, finite presentation, lci, smoothness, affineness or separation
  hypothesis on these maps.
- `UniversalConormalThickening f` packages an arbitrary ambient space, inclusion,
  projection and the existing `IsUniversalSpaceFirstOrderThickening f` predicate.
  Thus the thickenings are specified universal representatives, not arbitrary
  first-order thickenings or arbitrary maps. Its `conormal` is exactly the existing
  `spaceConormal inclusion`.
- `space_formallyUnramified_comp` asserts formal unramifiedness of the composite,
  as well as existence of a universal representative by the existing existence
  theorem. Arbitrary representatives, rather than one chosen representative, are
  used throughout the remaining statements.
- `universalConormalThickening_map_existsUnique` gives the unique ambient map
  for any commuting square, with both reduction and base equations.
  `UniversalConormalThickening.map` selects that uniquely determined map;
  `universalConormalThickening_map_spec` states its two equations and specifies
  its conormal map using the existing `IsSpaceConormalMap` normalization.
- In `universal_conormal_transitivity`, D is W(Z/X), E is W(Z/Y), and F is W(Y/X).
  The `IsPullback E.projection (E.map D ...) F.inclusion (D.map F ...)` clause
  identifies E.ambient with precisely Y times over W(Y/X) W(Z/X). Since E carries
  the universal-property predicate over Y, this states the asserted intermediate
  universality, including its actual structure maps.
- The first arrow is `D.conormalMap F a (𝟙 X) ...`; its definition uses
  `space_conormal_map` and therefore the prescribed ideal-tensor formula.
  The second is `universalConormalQuotient a b D E`. Its defining uniqueness
  theorem explicitly says that each pulled-back ideal section goes to the image
  under the actual ambient ring map, with every compatible chart and lift
  quantified. This is the quotient ideal map, rather than an arbitrary epimorphism.
  Its formula is the identity-source specialization of the recorded conormal map.
- Right exactness is `∃ w : lam ≫ rho = 0, (ShortComplex.mk _ _ w).Exact ∧ Epi rho`.
  This asserts exactness at C(Z/X) and surjectivity onto C(Z/Y), with no assertion
  that lambda is monic.
- `universal_conormal_etale_localization` quantifies over any square
  `(f : V ⟶ U) (g : B ⟶ A) (p : V ⟶ B) (q : U ⟶ A)` satisfying
  `p ≫ g = f ≫ q`. Its only geometric hypotheses are etaleness of p and q and
  formal unramifiedness of g. It concludes formal unramifiedness of f,
  etaleness of the canonical ambient map, cartesianness of its reduction square,
  and invertibility of the actual canonical conormal map. The final e identifies
  C(V/U) with `(pullback p hp).obj C(B/A)`; its equation factors the canonical
  conormal map through the existing tensor-to-restriction comparison. Consequently
  this identification is the induced ideal map itself.
- `universal_conormal_etale_ambient` is the explicit special case B_D inside D:
  an arbitrary pullback square with an etale ambient map gives a universal
  thickening over the original A, with its map `d ≫ r` and reduction `p ≫ g`.
  It does not require an atlas, surjectivity, or a finiteness condition.
- `universalConormalThickening_map_functorial` gives identity and composition for
  ambient maps and the composition equation for canonical conormal maps. The
  iterated tensor sources are identified by the existing normalized
  `moduleTensorComposition`, rather than an unspecified comparison.
- `universalConormalTower_square` supplies the outer tower-square equation from
  the two inner square equations. `universal_conormal_transitivity_etale_charts`
  takes arbitrary compatible etale changes z, y and x. It concludes formal
  unramifiedness of the chart tower, invertibility of all three canonical vertical
  conormal maps, and explicitly states the commuting equations for BOTH lambda
  and rho. The lambda source comparison is the existing `moduleTensorSquare`.
  The variable x is any etale map and may be the identity on X. Scheme charts
  are included as the scheme objects among algebraic spaces.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `EtaleSite`, `Modules`, `structureSheaf` and the etale restriction `pullback`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, used
  through the recorded scheme-test meaning of space `IsEtale`.
- `Sheaf.AlgebraicGeometry.SpaceUniversalConormal`: `SpaceFormallyUnramified`,
  `spaceKernel`, `spaceConormal`, `spaceConormalSection`, `IsSpaceConormalMap`,
  `space_universal_firstOrderThickening_exists` and `space_conormal_map`.
- `Sheaf.AlgebraicGeometry.SpaceUniversalThickeningEtaleTransfer`:
  `IsUniversalSpaceFirstOrderThickening`, owned by
  def-sfb-space-universal-first-order-thickening and now directly cited in stmt_deps,
  and its etale-transfer statements.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleTensorPullback` and the specified local tensor and adjunction constructions
  used in conormal maps.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap`: `moduleStructureMap`,
  owned by def-sfb-space-module-structure-map and now directly cited in stmt_deps.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction`:
  `moduleTensorPullback_etale_restriction`, with its multiplication normalization.
  Its owner lem-trf-space-etale-module-pushforward-restriction is now in stmt_deps
  as well as proof_deps because its selected comparison occurs in the signature.
- `Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange`:
  `moduleTensorComposition` and `moduleTensorSquare`. These are the recorded
  declarations of the additional landed stmt_deps
  def-sfb-space-module-tensor-composition and def-sfb-space-module-base-change.
- The proof-only imports are the recorded modules for the stalk/ideal calculation,
  space fibre products, ideal/closed-subspace correspondence,
  enlarged ringed-site model, flat unramified scheme lifting, and closed immersions.
  The transferred closed and etale predicates are not replaced by private versions.

Sources read: Stacks spaces-more-morphisms.tex, the full statements and proofs of
lemma-universal-thickening-functorial (060A), lemma-universal-thickening-localize
(060D), lemma-etale-morphism-of-universal-thickenings (0605), and
lemma-transitivity-conormal-unramified (06BF). The seven node proof steps are
carried into the theorem docstrings, including the ideal-image calculation and
both naturality equations.

Edge cases checked before and after writing: empty spaces and zero conormals;
a or b the identity; all chart maps identity; x identity with nontrivial y and z;
noncartesian etale squares (for example U = A disjoint union A); nonsurjective
etale charts; ordinary closed immersions with their ideal-square neighbourhoods;
and a general first arrow with nonzero kernel. None is excluded. The exactness
clause deliberately makes no monicity claim. Site values and test schemes remain
in the universes of the dependency declarations.

Searches (2026-10-24):

- msearch.py LeanSearch: `right exact conormal transitivity universal first order
  thickening etale localization`. Eight ring-level etale/localization hits,
  including `Algebra.FormallyEtale.localization_map`; none states this space result.
- msearch.py LeanFinder: `Universal conormal modules of formally unramified
  algebraic spaces form a right exact transitivity sequence compatible with etale
  charts`. Eight hits on scheme formal unramifiedness and etaleness; none exact.
- msearch.py Loogle: `IsSpaceConormalMap, IsUniversalSpaceFirstOrderThickening`.
  Zero hits; unknown identifier `IsSpaceConormalMap` in the Mathlib index.
- msearch.py grep: `conormal.*transitiv|universal.*thickening.*localiz`.
  Zero Mathlib hits.
- Local rg and id search in lean/WeilConjectures and lean/Sheaf: no declaration
  of the full item; the downstream AffineLciConormalSplitting cites it in a proof
  docstring, and only proves the distinct lci splitting result. Its
  IsSpaceConormalQuotient definition was read; importing that downstream module
  would reverse the proof dependency. This module introduces no duplicate
  quotient predicate: it spells out the ideal-section equation directly in the
  quotient arrow's uniqueness theorem. The existing general conormal-map
  predicate, tensor composition and square comparisons are reused.
- Source searches for identity/composition comparisons found the existing
  moduleTensorComposition and moduleTensorSquare. Their signatures and normalized
  local-tensor docstrings were read in full. No replacement comparison is defined.

Validation: scompile.py ran the single file against the published server library;
the server compile succeeded in 7.3 s. The wrapper's local attempt reported
OSError(28), then its normal server confirmation succeeded. Every subsequent
validation is through the prescribed wrappers.

## Second reading by NX

A second pass by this worker reopened the node and the completed module and checked
all the correspondences above. This is a dispatcher-started worker and the brief
forbids spawning another agent; the maintainer supplies the independent review.
The main checks were the orientation of the intermediate pullback square, the
identity-source quotient map's ring-map direction, the inverse direction of the
lambda tensor-square comparison, and the placement of all three chart conormal
maps. Both lambda paths start at z-star a-star C(Y/X) and end at C(Z0/X0).
Both rho paths start at z-star C(Z/X) and end at C(Z0/Y0). The explicit quotient
normalization matches the already recorded downstream consumer's normalization
without importing that consumer. The localization square has no cartesianness
hypothesis; the cartesian reduction square is a conclusion. No clause was dropped
and no hypothesis was added. All helper data is determined by existing universal
properties; all theorem proofs remain sorry. The second pass added the two landed
tensor-comparison definition nodes to stmt_deps so that these comparisons are
explicitly cited rather than silently imported.

## Repair of returned head 344f09e21394

The maintainer found three H2 ownership omissions; each is repaired explicitly.

1. Added def-sfb-space-universal-first-order-thickening to stmt_deps. Its existing
   declaration IsUniversalSpaceFirstOrderThickening is used in the wrapper's
   universal field and the ambient-etale theorem. Its owning module
   SpaceUniversalThickeningEtaleTransfer is now a public import.
2. Added def-sfb-space-module-structure-map to stmt_deps. Its existing
   moduleStructureMap occurs in the quotient arrow's ideal-section normalization.
   AlgebraicSpaceModuleStructureMap is now explicitly publicly imported.
3. Added lem-trf-space-etale-module-pushforward-restriction to stmt_deps, retaining
   it in proof_deps. Its module was already publicly imported. The localization
   statement uses Classical.choose of its uniquely tensor-normalized comparison
   moduleTensorPullback_etale_restriction; the theorem owner is now directly cited.

The sandbox node was compared with current main: only lean and stmt_deps differed
before this repair. Its current non-stage-2 metadata was taken from current main.
The returned Lean declarations and signatures are retained; only import visibility
and the explicit structural-map import changed. The independent review of the
returned head accepted the mathematics and all clauses; this repair addresses
exactly its three missing-owner findings. A fresh reading checked these three
signature occurrences against the corresponding node records and declarations.
Repair validation: the prescribed scompile.py completed successfully for both
sandbox and library module modes, with no errors or unexpected warnings.
The dry run and delivery are performed with deliver2.py after this report update.
