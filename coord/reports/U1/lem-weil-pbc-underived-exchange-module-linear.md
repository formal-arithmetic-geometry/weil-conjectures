## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear` states
`AlgebraicGeometry.etaleUnderivedExchange_moduleLinear`. Its sole proof is `sorry`.
It does not define any new notion. The original node is unchanged except for `lean`.

Hypotheses and clauses, in order:

- The four schemes and four arrows are the explicit binders `X' X Y' Y`, `g' f' f g`.
  `sq : IsPullback g' f' f g` supplies precisely the cartesian square, with
  `sq.toCommSq` its commutativity for the recorded exchange construction. The chosen
  identification with the fibre product is equivalently its pullback universal property;
  `squareUpperStarIso` depends only on the commutativity equality.
- The commutative coefficient ring is `R : CommRingCat.{u + 1}`. The lambda arguments
  `RX RY RX' RY'` are immediately applied to the constant sheaves of its underlying
  ring, and `etaX etaY etaX' etaY'` to their sheafification units. These are reducible
  parameters for writing the expression, not universally quantified arbitrary rings.
  `SheafOfModules.{u + 1} RX`, and its three analogues, mean exactly the categories of
  modules over those constant ring sheaves. Using the constant RingCat sheaf instead of
  first sheafifying in CommRingCat and then forgetting is the same canonical constant
  ring sheaf: sheafification of either constant presheaf has the same ring operations.
- Each `gamma_f`, `gamma_fp`, `gamma_g`, `gamma_gp` is the coefficient map from the
  target constant ring to the direct image of the source constant ring. The following
  equality for every etale object `W` and constant `r : R` fixes it to be the canonical
  map sending constant sections to constant sections. This is precisely the coefficient
  map specified by the inverse-image-exactness dependency, not an arbitrary ring map.
- The direct images are the existing `SheafOfModules.pushforward` along the etale
  base-change functor, with those coefficient maps. Their abelian underlying objects
  and maps are definitionally `Etale.lowerStar`.
- For each of the four arrows, `L_f`, `L_fp`, `L_g`, `L_gp` are its module inverse
  images; `e_f`, `e_fp`, `e_g`, `e_gp` identify their abelian underlying functors with
  `Etale.upperStar AddCommGrpCat`. `a_f`, `a_fp`, `a_g`, `a_gp` are their adjunctions
  to the corresponding module direct images. Each following universally quantified
  hom-equivalence equality states compatibility with the recorded abelian adjunction.
  These are the inverse images and compatible adjunctions stipulated in the node,
  furnished by `etaleInverseImageModulesExact`. They are not additional geometric or
  exactness hypotheses. Quantifying over compatible choices avoids an arbitrary chosen
  witness of that existential theorem. The compatible adjunction characterizes the
  canonical inverse image up to its unique compatible natural isomorphism, so a
  second definition of module pullback is unnecessary.
- Linearity of every exchange component and the consequent naturality are expressed
  together by `∃ t : pushforward gamma_f ⋙ L_g ⟶ L_gp ⋙ pushforward gamma_fp`.
  An arrow between functors is a natural transformation, whose components are morphisms
  of the stated categories of constant-ring modules; their section maps are linear
  over the entire ring sheaf, not merely over constant elements.
- The final equality, for every `G : SheafOfModules RX`, identifies the underlying
  abelian morphism `(SheafOfModules.toSheaf RY').map (t.app G)` with the existing
  `Etale.baseChangeMap AddCommGrpCat sq.toCommSq` at the underlying sheaf of `G`.
  On the left side of that abelian exchange, `e_g.hom.app (pushforward gamma_f |>.obj G)`
  identifies the module inverse image with the abelian inverse image; on the right,
  `Etale.lowerStar f'` of `e_gp.inv.app G` identifies the abelian inverse image with
  the module inverse image. Thus the asserted linear map is exactly the node's
  abelian exchange map, not an unspecified module map or the zero transformation.
  Existence of `t` implies linearity for each `G`; conversely these linear components
  assemble by the existing abelian naturality and faithfulness of `toSheaf`.

Dependencies read and used:

- `WeilConjectures.SixFunctors.BaseChange.Square`: `AlgebraicGeometry.Etale.squareUpperStarIso`
  and `AlgebraicGeometry.Etale.baseChangeMap` (full signatures and docstrings read).
  The latter is the actual abelian map appearing in the conclusion.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `AlgebraicGeometry.Scheme.smallEtaleTopology`.
  The module and abelian categories use this topology literally.
- `def-weil-sheaf-of-modules-category` has recorded general `mathlib_match`
  `SheafOfModules` in `Mathlib.Algebra.Category.ModuleCat.Sheaf`; this is the applicable
  declaration, rather than its scheme-structure-sheaf specialization `Scheme.Modules`.
  Its data, morphism type, and `toSheaf` were read. The existing continuous pushforward
  is in `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`, read in full, supplies precisely
  the compatible constant-ring module inverse images/adjunctions quantified here.
  Exactness is not an extra assumption in this statement.
- `def-weil-pbc-etale-sheaves` was read with
  `Sheaf.AlgebraicGeometry.EtaleSheaves`. Its recorded locally constant predicate is
  unnecessary here: no locally constant, finite, torsion, or constructible restriction
  is imposed. The module categories in its first paragraph are the existing
  `SheafOfModules` construction above.

Source verification: the locally referenced Stacks tex files are absent on this machine,
so the exact source was read online at https://stacks.math.columbia.edu/tag/03S6
and https://stacks.math.columbia.edu/tag/03D3. The former uses the exchange on module
sheaves, and the latter identifies linear maps with linear adjoints. The four-step
node proof is included in the theorem docstring, naming its DAG dependencies.

Edge cases checked before writing: no nonempty scheme hypothesis (all four schemes may
be empty); the zero coefficient ring and the zero module are allowed; identity squares
are allowed; there is no properness, finiteness, torsion, or etaleness hypothesis on any
of the four arrows. Scheme universe `u`, coefficient-ring and section universe `u+1`
are the same convention as the dependency, admitting the small etale sheafification.
All variables and universes are explicitly bound. No `let`, file-local instance,
notation, private definition, or hollow data is introduced.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "base change exchange morphism of etale sheaves of modules
  commutes with forgetting to abelian sheaves"`: eight hits, chiefly
  `SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom`, pullback of free
  modules, unit hom equivalences, and forget-to-module-category formulas; no exchange
  compatibility statement.
- `msearch.py ... loogle "SheafOfModules.pushforward, SheafOfModules.pullback"`:
  twelve hits including pullback, pullbackPushforwardAdjunction, pullbackComp and its
  conjugate-equivalence formula; no abelian-exchange linearity statement.
- `msearch.py ... grep 'baseChangeMap|exchange' Algebra/Category/ModuleCat/Sheaf`:
  zero hits.
- `msearch.py ... leansearch "base change morphism for sheaves of modules forgetful
  functor abelian sheaves"`: service unavailable, Internal Server Error; no verdict.
- `rg` of upstream `WeilConjectures` for the item id: no hits. Searches for
  `upperStar.*(forget|Forget)|forget.*upperStar|baseChangeMap.*(forget|Forget)|sheafCompose.*upperStar`
  found the unrelated WeilComplex forgetful comparison, no relevant exchange theorem.
  Generic `Etale.baseChangeMap` was read in full; it constructs an exchange for each
  coefficient category, but does not identify its module components with the abelian
  exchange under forgetting. Recording it alone would omit the node's central clause.
- `rg` of `lean/Sheaf` for module/exchange/forgetful formulas: the existing exactness
  and adjunction modules supply the structures, but no theorem supplies this exchange
  comparison. `dag/lean_names_upstream.json` and both source trees were searched for
  the item id, the proposed name, and base-change/forget formulas: no exact match or
  declaration-name collision.

Validation: server single-file compile succeeded without errors or warnings (5.2 seconds
before the final formatting cleanup). Delivery dry run is run after the final file and
node record have been written. No mathematical dispute or statement correction.

## Second reading by U1

I independently opened the sandbox node and its 188-line Lean module, all eight
statement-dependency nodes, the recorded source declarations, and the applicable
Mathlib declarations. No mathematical mismatch was found; the Lean and node
signature are retained. This reading adds this report and independent searches.
There are no new definition nodes, dependency modules, or statement corrections.

The node's objects, hypotheses, and conclusion clauses, matched in order:

1. Four schemes X', X, Y', Y and morphisms g', f', f, g in the displayed square:
   the explicitly bound `Scheme.{u}` objects and four typed arrows have precisely
   those sources and targets. PASS.
2. A chosen cartesian square, including its commutativity and induced inverse-image
   comparison: `sq : IsPullback g' f' f g` gives the pullback universal property,
   hence the unique compatible identification with the chosen fibre product.
   `sq.toCommSq` supplies the equality used by the dependency's
   `Etale.squareUpperStarIso`. The comparison there is the composite of
   `upperStarComp` isomorphisms, rather than an arbitrary chosen comparison. PASS.
3. A commutative ring Lambda: `R : CommRingCat.{u + 1}`, with no field, domain,
   nontriviality, finite, torsion, or characteristic requirement. PASS.
4. The small etale sites and constant ring sheaves Lambda_T: each topology is
   literally `T.smallEtaleTopology`, whose definition and jointly-surjective-cover
   characterization I read in Mathlib. The lambda arguments `RX RY RX' RY'`
   are immediately instantiated with `constantSheaf ... RingCat` of the underlying
   ring of R; they are not arbitrary universally quantified coefficient sheaves.
   `etaX etaY etaX' etaY'` are instantiated with the sheafification units. PASS.
5. Mod(T_et,Lambda): `SheafOfModules.{u + 1}` of those ring sheaves. Its Mathlib
   structure is a presheaf of modules with an abelian-sheaf condition; its morphisms
   have sectionwise linear maps. I checked `Hom`, its category instance, and
   `toSheaf`, including faithfulness. This uses the general-site `mathlib_match`
   of def-weil-sheaf-of-modules-category, not its O_T-module specialization
   `Scheme.Modules`. PASS.
6. The four module direct images: `SheafOfModules.pushforward gamma_f`, and the
   analogous f', g, g' terms, along the etale base-change functors. I read its
   construction in PushforwardContinuous: underlying abelian objects and maps are
   precisely the dependency's `Etale.lowerStar`. For each gamma, its equality
   on `eta*.app W r` says that it sends constant sections to constant sections.
   By the sheafification universal property this determines the entire sheaf map,
   including locally varying sections; no arbitrary coefficient action is allowed.
   PASS.
7. The four module inverse images and adjunctions, forgetting to abelian inverse
   images: `L_f`, `L_fp`, `L_g`, `L_gp`; `e_f`, `e_fp`, `e_g`, `e_gp`; and
   `a_f`, `a_fp`, `a_g`, `a_gp`. Each universally quantified hom-equivalence
   equality identifies its module adjunction with
   `Etale.upperStarLowerStarAdjunction` after applying `e_*.inv`.
   These equalities encode the stipulated compatibility, not an extra geometric
   hypothesis. Any such left adjoint is uniquely isomorphic to the canonical
   module inverse image as a left adjoint of the fixed direct image; compatibility
   forces its forgetful comparison to agree under that isomorphism. Thus the
   quantification over compatible choices does not change the mathematical claim.
   PASS.
8. An arbitrary G in Mod(X_et,Lambda): `forall G : SheafOfModules RX` follows
   the existence of the natural transformation; it includes every module sheaf,
   without constructibility or local constancy. PASS.
9. The abelian underived exchange Ex^0_square,G: the right-hand side is exactly
   `(Etale.baseChangeMap AddCommGrpCat sq.toCommSq).app` at the underlying abelian
   sheaf of G. I read Square.lean: this is the mate of `squareUpperStarIso` under
   the f and f' abelian adjunctions, with the counit formula stated immediately
   afterwards. The source map is transported by `e_g.hom` and the target by
   `lowerStar f'` applied to `e_gp.inv`; their directions are correct. PASS.
10. Lambda_Y'-linearity of that exchange: `t.app G` is a morphism between the
    specified module objects, so is linear over all sections of RY'. Its image
    under `toSheaf RY'` equals the transported abelian exchange. This asserts
    linearity of the actual exchange, not existence of an unrelated linear map
    or linearity only on constant scalar sections. PASS.
11. Consequent naturality and underlying-component compatibility:
    `exists t : pushforward gamma_f ... >> L_g -->
    L_gp >> pushforward gamma_fp ...` is one natural transformation for all G;
    the displayed equality is quantified over all its components. Conversely,
    linear lifts of the existing abelian components assemble uniquely by their
    abelian naturality and the faithfulness of `toSheaf`. Combining the two
    clauses in this existential neither adds nor omits a conclusion. PASS.

Dependency and source checks: I read `etaleInverseImageModulesExact` in full,
including the constant-section characterization of gamma, LM/e/am, the
hom-equivalence formula, and the unit and counit formulas. It uses the underlying
ring sheaf of the constant CommRingCat sheaf, while this item uses the constant
RingCat sheaf directly. These are canonically isomorphic via sheafification,
preserving the units, constant sections, and ring operations; transport gives
exactly the same module categories and compatible adjunction data. They need not
be definitionally equal, and no second definition is introduced here.
`EtaleSheaves.lean` supplies set-valued local-constancy predicates that are not
hypotheses of this node; the underlying module-category notion is the general
Mathlib declaration just checked. The source inverse/direct-image signatures
accept arbitrary scheme morphisms and AddCommGrpCat, with the needed site
sheafification instances already provided by their imported modules.

The local literature checkout lacks the Stacks tex files. I fetched the original
tex into this sandbox's scratchpad and read the labelled passages and surrounding
sections: etale-cohomology.tex lines 11353 onward and 11493--11514 (03S6), and
sites-modules.tex lines 987--1094, 1197--1231 (03D7), 1236--1251 (03D8).
I also checked the tag pages:
https://stacks.math.columbia.edu/tag/03S6,
https://stacks.math.columbia.edu/tag/03D3,
https://stacks.math.columbia.edu/tag/03D7,
https://stacks.math.columbia.edu/tag/03D8.
The 03S6 application has an etale horizontal arrow to obtain an isomorphism and
extension by zero. The present node claims only linearity of the exchange for
an arbitrary cartesian square, supplied by the general module adjunction and
composition constructions of 03D3/03D7/03D8; it does not claim invertibility or
extension by zero for an arbitrary horizontal arrow. Neither surrounding section
imposes Noetherian, properness, finiteness, or characteristic assumptions.

Edge cases: empty schemes are permitted by all scheme binders and `IsPullback`;
there is no inhabitance assumption. The zero coefficient ring and zero sheaf are
included by CommRingCat and SheafOfModules. Identity squares are included. No
index set or degree n occurs, so empty-index and n=0 restrictions are inapplicable.
All characteristics are allowed. The common scheme universe u and coefficient
and section universe u+1 follow the recorded inverse-image dependency; increasing
u accommodates larger rings, schemes and sections, with no independent smaller
universe test quantifier. Every variable and the single universe are explicitly
bound; there is no file-local notation, instance or private copy.

Independent H4 searches (recorded also in searches.jsonl):

- LeanFinder: `linear lift of the mate of a commutative square through the
  forgetful functor from sheaves of modules to abelian sheaves`. Eight hits:
  unit/free Hom equivalences, presheaf module sheafification equivalences, and a
  Mayer-Vietoris differential; none states this exchange comparison.
- Loogle: `SheafOfModules.toSheaf, CategoryTheory.NatTrans`. Zero hits.
- LeanSearch: `forgetful functor sheaves modules base change exchange natural
  transformation`. Service returned Internal Server Error; unavailable, no verdict.
- `rg 'baseChange|exchange|mateEquiv'` in Mathlib's ModuleCat/Sheaf directory:
  no hits. Searches for moduleLinear and baseChange/forget or exchange/linear in
  both WeilConjectures and lean/Sheaf found no applicable comparison. The hits in
  AffineTransitionLimit, finite etale neighbourhoods and pro-etale adic base change
  concern different objects. The project's moduleBaseChangeMap family is for
  structure-sheaf modules on schemes, not constant-ring modules on the etale site.
  The item id and proposed name have no upstream-name-table/source collision.
  Generic `Etale.baseChangeMap` at ModuleCat coefficients is not this theorem:
  it alone does not give compatibility with the abelian exchange after forgetting.

H5/H6/H8/H9: the delivery has one named theorem with proof `by sorry`, no definitions
or unnamed holes, and both imports are used. The module and theorem docstrings name
this node and the source tags. The theorem docstring carries all four proof steps:
composition-comparison linearity, counit linearity, linear adjunction, and naturality
through the faithful forgetful functor. Lines fit 100 characters. The recorded
`lean.statement` was checked verbatim against the full signature before `:= by`.

Validation: independent server single-file compile via scompile.py completed in
6.2 seconds, exit code 0, with no errors or warnings. No Lean or node repair was
needed. The report is the only content changed in this second reading; preflight
and delivery are run after appending it.
