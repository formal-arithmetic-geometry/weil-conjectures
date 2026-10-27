## Worker report

The module Sheaf.AlgebraicGeometry.SpaceAlternatingSignCohomologySpectral states
AlgebraicGeometry.AlgebraicSpace.space_alternating_sign_cohomology_spectral with one
postponed theorem proof. Its definitions contain real data. The node statement and
proof are unchanged. Statement dependencies now name the new definition owner for
the existing configuration definitions, the landed separated-diagonal definition
owner, and the recorded filtration interface. The two theorem nodes cited only
for plain definitions in the returned packet are removed from stmt_deps.

Source read: literature/stacks-project/spaces-cohomology.tex, lemma-twist (0727),
its complete proof, and lemma-alternating-spectral-sequence (0728), its complete
proof. The node specializes its scheme source U as it already explicitly states.

Hypotheses and clauses, matched individually:

* Size convention: explicit universe u, Scheme.{u}, and AddCommGrpCat.{u+1}; the
  coefficient functor category has object and morphism universe u+2. The small
  étale site retains its different object and morphism universes. No extra
  equality of site universes or size hypothesis is imposed.
* Base scheme and algebraic space: `{S : Scheme.{u}} (X : AlgebraicSpace S)`.
* Representable surjective étale cover by a scheme: `U : X.EtaleSite` already
  packages its scheme and representable étale arrow, and `hsurj` is
  `IsSurjective U.obj.hom`.
* Separated cover: `hsep : IsSeparatedPresheafMap U.obj.hom`, the existing
  predicate saying the representable relative diagonal is a closed immersion.
* Every p>=0: the family `D : ∀ p : ℕ, ConfigurationQuotient X U p`.
* Iterated scheme fibre product: `D.T`, `D.pr`, `D.product`. A product of objects
  over X in this étale scheme category is exactly this iterated scheme fibre
  product; the recorded fibre-product dependency guarantees its availability.
* Complement of every pairwise equality locus: `D.W`, `D.j`, `D.distinct` using
  the existing `configurationDistinctSet`. Both `D.openImmersion` and
  `D.closedImmersion` are asserted, including their scheme structures.
* Free permutation action: `D.ρ` is a monoid homomorphism into automorphisms;
  `D.coordinates` specifies its inverse-coordinate convention and `D.free`
  tests freeness on every nonempty scheme, with the empty-test exception needed
  because all maps from the empty scheme agree.
* Orbit fppf sheafification and algebraic-space existence: `D.Q : AlgebraicSpace S`;
  `configurationOrbitPresheaf` is the pointwise coequalizer of the coproduct of
  all permutation arrows and of identities. This computes the orbit presheaf.
  `D.η` and `D.sheafification` give its complete universal property against every
  fppf sheaf, rather than choosing an arbitrary quotient map.
* Quotient arrow: `configurationOrbitMap ... ≫ D.η` is the coequalizer arrow
  followed by the sheafification unit. `D.quotientEtale` and
  `D.quotientSurjective` include representability in both predicates.
* Constant-group torsor: `D.torsor` says that two lifts with the same quotient
  are related étale locally by a unique permutation. Combined with the
  quotient's representable étale surjectivity, this is the usual torsor
  condition; a locally constant permutation may vary between components.
* Induced étale map g: `D.g`, `D.gEtale`, `D.triangle`; the triangle identifies
  it with descent of the specified configuration arrow to X.
* The sign line: `IsConfigurationSignLine ... (L p)` identifies its sections,
  compatibly with restriction, with `configurationSignSections`. On each slice
  these are maps from the restriction of the existing free represented sheaf
  Z[W] to the constant integer sheaf which are sign-transforming under the
  coordinate action. The free-sheaf adjunction identifies these with the sign
  subsheaf of pi_* Z. No mere abstract rank-one sheaf is substituted.
* The chart is the same W over Q: `D.chartIso` and `D.chartMap` identify its map
  with the quotient arrow, while `D.chartAction_eq` identifies its permutation
  action. The sign-line predicate includes `L.over D.chart ≅ Z.over D.chart`.
  Together with the representable surjective étale quotient this states the
  asserted étale local rank one, with trivialization by pi itself.
* Every abelian coefficient sheaf and naturality: the spectral sequence takes
  values in `Sheaf X.etaleTopology AddCommGrpCat.{u+1} ⥤ AddCommGrpCat.{u+1}`.
  Thus pages, differentials, page homology comparisons, E1 comparisons,
  abutment filtration, and graded comparisons are natural in A, including all
  coefficient morphisms. This is stronger data packaging, not an additional
  mathematical hypothesis or a change of coefficients.
* First quadrant and cohomological: `CohomologicalSpectralSequenceNat ... 1`
  is Mathlib's actual spectral sequence on ℕ×ℕ with d_r of bidegree (r,1-r),
  starting at E1; all page homology isomorphisms are part of that structure.
* E1 page: its (p,q) functor is isomorphic to
  `configurationRestriction D.g D.gEtale ⋙ configurationTwist D.Q (L p) ⋙
  configurationCohomology D.Q q`. Restriction is the already defined étale
  inclusion of small sites. Twist uses sectionwise integer tensor in
  AddCommGrpCat followed by the actual abelian sheafification functor.
* Right derived global sections: `configurationSections X` is the additive
  represented functor Hom(Z_X,-), canonically global sections by the constant
  integer adjunction; `configurationCohomology X q` is literally its
  `Functor.rightDerived q`. `configurationEnoughInjectives` selects the existing
  Grothendieck-category instance at the coefficient universe, not a hypothesis.
* Abutment H^m: `F m` is a decreasing filtration of the functor
  `configurationCohomology X m` using the existing DecreasingFiltration.
  `IsIso ((F m).step 0).arrow` is exactly F^0=H^m, and `IsZero` of the
  (m+1)-st subobject is exactly F^(m+1)=0. These equivalent endpoints avoid
  an unresolved universe in the generic functor-category top/bottom instance.
* Graded pieces: `(F (p+q)).gr p` is the cokernel F^(p+1)->F^p and is
  isomorphic to page p+q+2 at (p,q). This covers p<=m by q=m-p.
* Stabilization: for every r>max(p,q+1), the entry is isomorphic to that same
  page p+q+2, the existing upstream convention for E_infinity.
* No quasi-coherence, finite degree of the cover, or factorial invertibility
  occurs anywhere in the binders or auxiliary interfaces.

Dependency declarations read and used:

* Mathlib.AlgebraicGeometry.Scheme: Scheme and Scheme.Hom.
* Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, EtaleSite,
  IsRepresentableWith, IsSurjective, IsEtale, etaleTopology, etaleMap,
  etaleMap_isContinuous; these are the exact recorded interfaces.
* Mathlib.AlgebraicGeometry.Morphisms.Etale: Etale; ClosedImmersion:
  IsClosedImmersion; Mathlib.AlgebraicGeometry.OpenImmersion: IsOpenImmersion.
* Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace, etaleCover_pullback, etale_fibreProduct_isScheme.
* Mathlib.AlgebraicGeometry.Sites.Fpqc: Scheme.fppfPrecoverage and fppfTopology;
  Mathlib.CategoryTheory.Sites.Over: GrothendieckTopology.over and Sheaf.over.
* Mathlib.CategoryTheory.Sites.Sheafification: presheafToSheaf, toSheafify,
  sheafificationAdjunction. The quotient uses its universal property because
  the existing algebraic-space interface uses Type u on the big site.
* Mathlib.Algebra.Homology.SpectralSequence.Basic: SpectralSequence and
  CohomologicalSpectralSequenceNat; the full page and morphism signatures read.
* Mathlib.CategoryTheory.Abelian.RightDerived: Functor.rightDerived;
  Mathlib.CategoryTheory.Preadditive.Injective.Basic: Injective;
  Mathlib.CategoryTheory.Preadditive.Injective.Resolution: InjectiveResolution.
* Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses:
  cochainModulesMonoidal, cochainModulesSymmetric and their sectionwise tensor
  interface, retained through public configuration imports. Since our inputs
  are abelian sheaves, not variable-ring modules, the coefficient tensor is
  the existing integral AddCommGrpCat tensor of
  WeilConjectures.CategoryTheory.RingObjects.Ab followed by sheafification.
  This uses exactly the same sectionwise-tensor-then-sheafify definition.
* Sheaf.CategoryTheory.SiteCoveringAxioms: IsSiteForCoverings and its public
  abelian sheaf cohomology API. Global sections over the space, which is not
  an object of the scheme-valued small site, use Hom(Z,-) as explained above.
* Sheaf.AlgebraicGeometry.EtaleConfigurationExteriorHom:
  configurationFreeSheaf and configurationDistinctSet, owned by the new node
  def-sfb-etale-configuration-free-sheaf-distinct-locus (existing:true).
* Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal: IsSeparatedPresheafMap, owned
  by the landed def-sfb-presheaf-map-separated-diagonal (existing:true).
* WeilConjectures.CategoryTheory.Abelian.Filtration / CanonicalFiltration:
  DecreasingFiltration, step and gr. No new filtration is defined.

The modules of all recorded non-Mathlib proof dependencies are imported:
EtaleConfigurationExteriorHom, EtaleRelationQuotient,
SpaceEtaleSourceAtlasDetection, SpaceCotangentRingMap,
OverPullbackPreservesInjectives, DoubleComplexTotal,
ExactCouple.DoubleComplex (the current location of exists_spectralSequence),
and LiftToInjectiveUniqueUpToHomotopy. The coproduct, enough-injectives,
equivalence-transport and resolution-lift Mathlib leaves arrive through these
and the explicit Mathlib imports. The trace-Koszul resolution and finite-torsor
character-line nodes have no recorded Lean declaration, so there is no module
to import for them yet. They are only proof inputs and are not assumed as
hypotheses of the statement.

Edge cases checked against the source and signature: empty X and empty cover
(no freeness test over the empty scheme forces the group trivial); p=0
(trivial permutation group and ordinary cover); identity cover (all higher
configuration schemes empty); split cover of degree two (the integral sign
condition remains valid with Z/2 coefficients); unbounded or infinite fibres
(no finite-cover or eventual-empty assumption); m=0 (one graded piece, last
filtration step 1); p>m imposes no spurious natural-subtraction graded term.

Searches actually run with msearch.py for this item and group:

* leanfinder: "Alternating configuration spectral sequence for etale sheaf
  cohomology of algebraic spaces" returned the small étale site, scheme site,
  and Mayer-Vietoris complexes; none states this theorem.
* loogle: `"SpectralSequence", "Sheaf"` returned zero hits.
* grep: `alternating.*spectral|sign.*localSystem|configuration.*quotient`
  returned zero Mathlib hits.
* leansearch: "Alternating spectral sequence sign subsheaf of a finite etale
  torsor on an algebraic space" returned ordinary AlternatingMap permutation
  lemmas, alternatingGroup and the affine structure sheaf; none is the item.
* rg across lean/WeilConjectures and lean/Sheaf for configuration, quotient,
  character lines and spectral sequence interfaces found the exact exterior
  configuration dependency and general E2 convergence, but no item theorem.
* The exact node id was searched in lean/WeilConjectures; no hit. All fifteen
  new declaration names were searched together in lean/WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json; no preexisting name was found.

No STATEMENT-DISPUTED finding or source correction. The added declarations are
helpers specifying the canonical objects of this node, not new independent
notions; they all carry its blueprint id. Every variable and universe is
explicit, autoImplicit is false, no file-local notation or private definition
is used. scompile.py compiles both its sandbox and library-module forms cleanly.

## Second reading by Q43

This is a worker self-review; no independent worker was launched, as the
assignment explicitly forbids subagents and assigns independent review to the
maintainer. On rereading the source, node and complete signature together, the
important checks were the canonical quotient arrow, the same W after changing
site to Q, the transported permutation action, integral sign sections rather
than rational averaging, and naturality of filtration and graded isomorphisms.
They are all explicit in ConfigurationQuotient, IsConfigurationSignLine and the
functor-category conclusion. The first compile found an unresolved universe
in the functor-category top/bottom endpoint notation; it was replaced with
the equivalent isomorphism/zero endpoint conditions. No mathematical hypothesis
was added. Final line-width check found no line above 100 columns.

## Repair of returned delivery

Returned immutable head: 5c9068dc2de0. Comparing the retained sandbox node with
current main found changes only to lean and stmt_deps; the Lean source and
mathematical signature accepted by the clause check are retained. The item node
was regenerated from current main, preserving all of its other fields.

(a) Replaced lem-trf-space-qc-separated-etale-local in stmt_deps with
 def-sfb-presheaf-map-separated-diagonal. Its recorded existing definition
IsSeparatedPresheafMap is exactly the hsep binder, including the canonical
presheaf relative diagonal and the scheme-test closed-immersion condition.

(b) Replaced lem-sfb-etale-configuration-exterior-hom in stmt_deps with
 def-sfb-etale-configuration-free-sheaf-distinct-locus. The theorem remains in
proof_deps and its module remains imported. The new node owns the actual plain
definitions already present in that module; it does not copy, move or redefine
them. This follows the landed existing:true ownership pattern used in (a), and
brief-stage2 §5's explicit rule that an already landed declaration is recorded
existing:true without a new module. Neither definition relies on the theorem.

Tensor advisory: def-pur-sheaf-tensor-product is an existing dependency in main,
not an added theorem dependency. Its mathematical notion is still used: the
coefficient is an integral sheaf tensor product, constructed as the
sheafification of sectionwise tensor products. Its recorded cochainModulesMonoidal
instance concerns sheaves of modules over a variable sheaf of rings; it is not
applied to this AddCommGrpCat-valued statement. configurationTwist instead uses
the already canonical integral AddCommGrpCat tensorRight and the existing
presheafToSheaf. This is the constant-integer specialization described by the
node, with genuine functorial data, rather than a new independent tensor notion.
No claim of direct use of cochainModulesMonoidal is made.

The second reading above is explicitly a worker self-review, not independent
review. The dispatcher prohibits launching other agents; the maintainer's
independent review is the delivery review.

## New nodes

Added def-sfb-etale-configuration-free-sheaf-distinct-locus, sourced to Stacks
0726/0728. It records existing:true in the owning module
Sheaf.AlgebraicGeometry.EtaleConfigurationExteriorHom, listing both
AlgebraicGeometry.AlgebraicSpace.configurationFreeSheaf and
AlgebraicGeometry.AlgebraicSpace.configurationDistinctSet.

Every new-node hypothesis and clause:

* S, X, and the small étale site: explicit {S : Scheme.{u}}, X : AlgebraicSpace S,
  and X.EtaleSite in both existing signatures.
* U an arbitrary étale site object: U : X.EtaleSite, without any surjectivity,
  separatedness or finite-degree assumption.
* The free abelian sheaf on U: presheafToSheaf applied to uliftYoneda.obj U
  composed with AddCommGrpCat.free, including precomposition restrictions and
  the exact u+1 coefficient lift.
* Arbitrary T and finite family of maps: T : X.EtaleSite, n : ℕ,
  pr : Fin n → (T ⟶ U).
* The distinct subset: for each i ≠ j, exclude Set.range of the base map of
  equalizer.ι for the two underlying scheme maps. This does not assert clopenness
  or take a chosen product or impose a new hypothesis.

For n=0 and n=1 the pairwise condition is vacuous, yielding all of |T|; for
empty T it is empty. Sheafification uses real free-group data, not a choice from
the postponed exterior-Hom theorem.

Actual searches are copied into the new node's mathlib_searches: LeanSearch
on free represented abelian sheaves and distinct tuple loci, LeanFinder on
sheafified represented free groups and distinct configuration loci, and Mathlib
grep for configurationFreeSheaf|configurationDistinctSet|free.*Sheaf|distinct.*[Ll]ocus.
General freeYoneda/free-module results were found; none replaces the existing
specialized pair of definitions. Repository rg finds the two definitions only
in EtaleConfigurationExteriorHom and their uses; no WeilConjectures hit. All
definition-node Lean records were inspected: neither had a definition owner.
Blueprint search for configuration found only two unrelated surface-blowup
units. blueprint_refs.py ancestor of the item returned null, retained in the
new node's ancestry along with the complete inherited route.
