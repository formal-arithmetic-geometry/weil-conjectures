## Worker report

Item: lem-trf-oriented-closed-base-extension. Module:
`Sheaf.Paper.OrientedClosedBaseExtension`; primary declaration:
`AlgebraicGeometry.OrientedNearbyCycles.ClosedBase.orientedClosedBaseExtension`.
The natural statement, stmt_deps, proof and proof_deps are unchanged. The item node
changes only in lean. No dependency modules or new nodes are needed.

The module states the closed-base theorem, including the precise supported-subtopos
identification and the actual comparison maps. Definitions have real data. Every theorem
has proof `sorry`, a source/blueprint docstring and a natural-language proof. All 18
auxiliary declarations concern the canonical constructions used in this one statement,
and are enumerated in lean.declarations.

Hypotheses, individually:

- The schemes X,F,S are `Scheme.{u}`. Noetherian S is
  `[IsLocallyNoetherian S] [CompactSpace S]`, exactly the two fields of Mathlib's
  `IsNoetherian S`, with no separation assumption on the underlying topology.
- The proper morphism is `(f : X ⟶ S) [IsProper f]`.
- The closed immersion is `(k : F ⟶ S) [IsClosedImmersion k]`.
- Its factorization is `(fF : X ⟶ F) (hfac : fF ≫ k = f)`.
- The finite commutative coefficient ring is `(Λ : Type (u+1)) [CommRing Λ] [Finite Λ]`,
  following the recorded small-etale constructible-complex size convention. `Coeff Λ`
  is the existing canonical ULift ring, with its canonical ring equivalence to Λ.
- `[HasInvertibleExponent Λ S]` means there exists a positive integer annihilating Λ
  whose image in Γ(S,top) is a unit. This is the node's invertible annihilator, including
  the zero ring and empty base; it is not a prime-order or field restriction.
- `K : EtaleDerived X Λ` is the recorded unbounded constant-module derived category.
  `_hKb : IsBounded (etaleDatum X) (Coeff Λ) K` supplies bounded cohomology.
  `_hKc` requires, in every integer degree, an original-site constructible Fq and an
  isomorphism between its AsSmall precomposition and the cohomology sheaf after
  restriction along the constant-ring sheafification unit. This is the expanded
  recorded bounded-constructible condition in the constant-ring presentation. The
  expansion is the already published one in `Sheaf.Paper.NearbyClosedImage`, rather
  than a second definition of constructibility. The Fq isomorphism retains the module
  action, not merely its underlying abelian group. Combined with boundedness this is
  exactly D^b_c, with every positive, zero and negative cohomology degree included.

Conclusions, individually:

- `embedding f fF k hfac` is exactly `squareMorphism f fF (𝟙 X) k ...` from
  def-trf-oriented-nearby-cycles. It is the induced v, not an arbitrary morphism.
- Its set-sheaf direct image is Full and Faithful. Its essential image at H is
  equivalent to `IsIso (prod.fst : openComplement f k ⨯ H ⟶ openComplement f k)`.
  Here openComplement is p2 inverse image of the associated representable for S minus
  range k. This is exactly the defining full subcategory of the closed complement in
  lem-trf-oriented-closed-base-localization. Full faithfulness plus this exact essential
  image identifies the source with that closed subtopos. No arbitrary equivalence or
  merely nonempty choice is substituted for the induced v.
- `modules` is the existing canonical constant-module lift of v. Preservation of
  finite limits and finite colimits states exactness; Full and Faithful state full
  faithfulness of its modulePush. As usual its total right derived functor push is
  therefore its exact, termwise direct image on complexes; the theorem uses this same
  right adjoint, not a second derived functor.
- For every module G on V_fF, constructibility in the recorded
  `OrientedConstructibleSheaf.IsConstructible fF (𝟙 F) Λ` implies constructibility of
  its modulePush in `IsConstructible f (𝟙 S) Λ`. The canonical constructiblePresentation
  changes only the coefficient/site presentation: realizationRingIso changes
  CommRingCat to RingCat, constantRingModuleRestriction retains the scalar action, and
  sheafified Kan extension along toProduct normalizes base change by the identity.
  The existing constant-ring-module equivalence then returns to its recorded module
  category. The underlying triple functor uses the canonical pullback-identity
  isomorphism, so the predicate is the dependency's exact rectangular-stratum notion.
- `restrictionComparison` is the recorded ordinary baseChange for (1_X,k), followed
  by its canonical identity-pullback normalization. `extensionComparison` is precisely
  its transpose under `(modules ...).adj`. The main theorem says this morphism is an
  isomorphism. `extensionComparison_naturality`, stated separately in this same owning
  module, gives naturality for every morphism of coefficient complexes, hence in
  particular the requested natural isomorphism on D^b_c.
- The last clause quantifies over every scheme S' and every g:S'→S, with arbitrary
  Cartesian presentations `hp : IsPullback h f' f g` and
  `hk : IsPullback gF k' k g`. Its remaining equalities name the induced factorization
  and its commutative square; they impose no condition on g. These presentations
  include the canonical fibre products, any isomorphic presentations, and the identity
  base change. Neither S' Noetherian nor g finite type is assumed.
- The square of vanishing topoi is the unique direct-image isomorphism normalized by
  both projection identifications, obtained from the universal oriented product. Its
  inverse-image mate is square. `exchange` is the existing ordinaryExchange for that
  square: it is the unit for v', the square identification, and the counit for v.
  The theorem says exchange is invertible for every derived A on V_fF, and gives the
  exact equation `beta ≫ alpha' = w^*(alpha) ≫ gamma ≫ v'_*(beta_F)` at K. Both beta
  and beta_F are the recorded ordinary baseChange maps. Thus the final clause is
  actual compatibility, not just an unspecified isomorphism or Psi-goodness transfer.

Canonical helper obligations (all belong to clauses of this node):

- etaleIdentity_existsUnique fixes the site identity by pullback.fst.
- moduleIdentity_existsUnique fixes the module identity by scalar insertion and the
  normalized underlying set-sheaf identity. Its exact localization defines identityPull.
- square_existsUnique fixes the base-change square by its first and second projection
  isomorphisms, using the existing universal-property squareLift.
- extensionComparison_naturality is the naturality part of the requested isomorphism.
- orientedClosedBaseExtension is the full node statement.

These are the five postponed theorems. Each carries a full proof docstring. Every
choice of data is fixed by the indicated uniqueness statement (or the already recorded
canonical equivalence's inverse); none is a choice from an unconstrained existence claim.

Dependency interfaces read and used:

- `Sheaf.Paper.OrientedNearbyCycles`: etaleDatum, vanishingDatum, nearbyCycles,
  squareMorphism/squareLift, squareModules, baseChange, etaleModules, Coeff, IsBounded,
  moduleMorphism, etaleBaseChange, etaleBaseChangeComp and etaleComposition.
- `Sheaf.Paper.OrientedConstructibleSheaf`: ProductSite, productTopology, Modules,
  IsConstructible. Its full source and scalar/stratum conventions were read.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  Etale.DerivedCategory.isBoundedConstructible and the full subcategory declaration;
  read with `scompile.py --source`, since this current upstream module is missing in
  the older checkout. The theorem uses its expanded boundedness and original-site
  constructibility conditions through the canonical presentation described above.
- `Mathlib.AlgebraicGeometry.Noetherian`: IsLocallyNoetherian; IsNoetherian is precisely
  locally Noetherian plus CompactSpace. `Mathlib.Topology.Defs.Filter`: CompactSpace.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: IsProper; universally closed implies
  quasi-compact, so this is the recorded finite-type properness definition.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: IsClosedImmersion and its
  closed embedding, also its base-change stability used in the proof plan.
- def-weil-pbc-scheme-conventions is a convention node without its own declaration;
  the constituent Mathlib notions above are used directly.
- `Sheaf.Paper.CompletionMateComparison` (imported publicly by nearby cycles): Site,
  Morphism.modulePush, moduleAdjunction, pull, push, adj, ordinaryExchange.
- `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`:
  realizationRingIso; `Sheaf.CategoryTheory.ConstantRingModuleSheaves`:
  constantRingModuleRestriction and constant_ring_module_sheaves.
- Recorded proof interfaces imported: OrientedProductLargeSites;
  FiniteLocallyClosedStratification; Mathlib.Topology.Constructible; pullback;
  StrictHenselizationClosedImmersionCartesian; StrictHenselizationClosedLift;
  OrientedPointCohomology; OrientedProductPointsConservative; Mathlib's mates.
  lem-trf-oriented-closed-base-localization and lem-trf-finite-cover-tube-comparison
  currently have no Lean record or Mathlib match, so no proof import exists for them;
  their natural proof steps remain explicitly in this theorem's docstring.

Edge cases checked before stating:

- F empty forces X empty, and the closed-complement image condition is the terminal
  set-sheaf condition, while the module image is zero. No nonemptiness is assumed.
- k an identity yields the whole vanishing topos. Its represented open complement is
  initial, so the essential-image condition holds for every H, as required.
- A nilpotent closed immersion is retained scheme-theoretically. No reducedness or
  replacement by topological support is made; the proof's strict-local comparison
  explicitly keeps nilpotents.
- K=0 and the zero coefficient ring are allowed. Boundedness permits negative
  degrees and arbitrary finite intervals. Constructibility permits empty strata.
- S' can be empty, non-Noetherian or an arbitrary scheme; identity and repeated
  presentations of fibre products remain included. The module-exchange clause is
  on the unbounded derived category, justified by exact inverse images/direct images.
- No extra Tor-amplitude, Psi-goodness, flatness, dominance, surjectivity, finite
  presentation of g, or reducedness hypothesis appears.

Searches made (2026-10-17 UTC):

- msearch.py leanfinder: "Nearby cycles of a proper morphism factoring through a
  closed subscheme are extension by zero from the vanishing topos over the closed
  base". Eight hits, including exists_appTop_map_eq_zero_of_isLimit and unrelated
  open/limit lemmas; none is this oriented-topos theorem.
- msearch.py loogle: `"Sheaf", "FullyFaithful"`. Eleven hits, including
  fullyFaithfulSheafToPresheaf, fullyFaithfulSheafCompose and
  SheafOfModules.fullyFaithfulForget. They describe forgetful functors, not the
  induced closed-base map on vanishing topoi.
- msearch.py grep in AlgebraicGeometry:
  `nearby.?[Cc]ycle|vanishing.?[Tt]opos|closed.?[Ss]ubtopos`. No hits.
- rg in Mathlib, upstream WeilConjectures, shared lean/Sheaf and
  dag/lean_names_upstream.json for
  `orientedClosedBaseExtension|namespace.*ClosedBase|closed.?[Bb]ase.?[Ee]xtension`:
  no existing declaration of this statement or collisions with this namespace.
- grep -rn of the exact item id in the upstream WeilConjectures: no match.
- Existing nearby-cycle results were read, especially NearbyClosedImage and
  PsiGoodOrientedCohomologyStrata. The former states transfer of truncated/universal
  comparison and Psi-goodness, without this theorem's embedding, exactness,
  constructibility preservation, or natural extension isomorphism. It is not an
  existing match. The latter concerns Psi-good cohomology strata, not closed extension.

Source verification: opened the actual Orgogozo PDF at the node's URL. §3.2.2,
printed pp. 7--8, treats empty tubes off F and the isomorphism of tubes over F;
§9.2, printed pp. 21--22, gives the proper non-dominant reduction. §6.1, printed
p. 15, additionally displays the corresponding strict-local closed-immersion
pushforward and base-change calculation. The module follows the reviewed node's
more explicit closed-topos and mate formulation. The relevant current blueprint
ancestor statement and proof were also read. No statement dispute or correction.

Validation: scompile.py compiled the completed module without errors or warnings;
the local sandbox compile took 8.5 s and the server-confirmed library-file compile
11.8 s, each within the required 60 s. One earlier spelling error in the exact-derived
identity API was corrected to mapDerivedCategoryIdIso before this successful compile.
The final import/formatting changes were recompiled by the required delivery dry run.
`deliver2.py --no-push` reported OK at c6d3d06a01: preflight passed and the module compiled.
The node signature was checked byte-for-byte against the file; the only changed node
field is lean, and every source line is at most 100 characters.

## Second reading by Q89

This is a direct worker delivery under the dispatcher's brief; I have not represented
this self-check as an independent agent review. The independent maintainer review is
external to this packet. I reread the full node, dependency records and final module.
Each hypothesis and clause matches as listed above. In particular I checked the
orientation of the two adjunction transposes and the final equality, verified that
both projection normalizations refer to the same composite h and k'≫g, and checked
that the arbitrary base-change binder imposes no Noetherian condition on S'.
No natural-statement change, new definition of constructibility, unconstrained
comparison map, or hollow definition was introduced. The identity and nilpotent
closed-immersion cases remain in the statement. All five theorem bodies are sorry;
no proof work is claimed.
