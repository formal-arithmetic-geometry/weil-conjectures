## Worker report

The module lean/Sheaf/AlgebraicGeometry/OpenRestrictionPullbackUnit.lean states
AlgebraicGeometry.open_restriction_pullback_unit, with only a sorry theorem proof.
The node is unchanged except for its lean record. No new definitions or dependency modules
are needed. The statement is expressed as equality of abelian-group homomorphisms, equivalent
to equality on every section a.

Hypotheses and objects, clause by clause:

- Schemes X,Y and their morphism g are `{X Y : Scheme.{u}} (g : Y ⟶ X)`.
- An arbitrary open subscheme W is `(W : X.Opens)`, with scheme `W.toScheme`.
  The inverse-image open W' is `(g ⁻¹ᵁ W).toScheme`; it is constructed, not extra input.
- j_W is `p := W.ι`; j_W' is `p' := (g ⁻¹ᵁ W).ι`.
  Their étaleness witnesses hp,hp' are inferred from open-immersion instances, not hypotheses.
- g_W is `g' := morphismRestrict g W`. `morphismRestrict_ι g W` identifies
  `g' ≫ p` and `p' ≫ g`, so h in the first comparison and the second is the same morphism.
- Abelian sheaves are `F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u+1}`.
  Inverse images pF,gF,K are the recorded `Etale.upperStar` objects. Direct images and their
  sections occur in the codomains of the units of `Etale.upperStarLowerStarAdjunction`.
- w,w' are identity étale objects (global sections on W,W'); wx,wy' are those same schemes
  viewed over X,Y via their open inclusions. eW,eW' are identity-scheme site isomorphisms
  removing identity composites in structure maps. Contravariance requires their inverses.
- `theta` is the map (g_W,id) from W' into W ×_W W'. Applying `K.obj.map theta.op`
  identifies the codomain of the g_W unit with sections on W'.
- `iotaSite` is (g_W,j_W') from W' into W ×_X Y. Applying `gF.obj.map iotaSite.op`
  implements the stipulated open-fibre-product identification. This map is the inverse
  projection of the canonical isomorphism: the cartesian square is
  `isPullback_morphismRestrict g W`, and the open-subscheme identification is also supplied by
  `pullbackRestrictIsoRestrict g W` with the pullback symmetry. Both projections are correct.
- rhoF,rhoG are the hom components of the recorded
  `Etale.upperStarIsoLocalizationRestriction`. Their evaluations at w,w' and the eW/eW'
  maps are exactly rho_F(W) and rho_(g^-1 F)(W') in the node.
- `Etale.upperStarComp` has the reverse orientation to the node's c. Accordingly kappa is
  `(upperStarComp A g' p).inv.app F ≫
  (upperStarComp A p' g (g' ≫ p) (morphismRestrict_ι g W)).hom.app F`:
  first c_(jW,gW), then inverse c_(g,jW'). These are natural isomorphism components.
- The left side is eta_gW at w, followed by the theta identification, kappa at w', rhoG
  at w', and eW' identification. The right side is rhoF at w, eW identification,
  eta_g at wx, and the iotaSite identification. This is every map of the displayed equation
  in the node, in its order. Both codomains are `(g^-1 F)(W')` over Y.

Dependency declarations read and used:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, AlgebraicGeometry.Scheme and Scheme.Hom;
  docstrings and signatures read at lines 35–76.
- def-weil-etale-morphism: Mathlib.AlgebraicGeometry.Morphisms.Etale,
  AlgebraicGeometry.Etale, lines 38–44; open inclusions supply the instance.
- def-weil-pbc-abelian-etale-sheaves: Mathlib.CategoryTheory.Sites.Sheaf,
  CategoryTheory.Sheaf (lines 294–303), specialized to the small étale topology and abelian groups.
- def-weil-pbc-inverse-image and def-weil-pbc-direct-image:
  WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs,
  AlgebraicGeometry.Etale.upperStar, lowerStar, upperStarLowerStarAdjunction;
  read their docstrings and full signatures in the Star section.
- lem-weil-pbc-inverse-image-composition: the same module,
  AlgebraicGeometry.Etale.upperStarComp and lowerStarComp, read the Comp section.
  Also read the unit compatibility in UpperLowerStar.Coherence, lines 157–174.
- lem-weil-pbc-etale-inverse-image-restriction:
  WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs,
  AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction,
  localizationRestriction, localizationRestrictionLowerStarAdjunction, read the Restriction
  section, including signatures and docstrings.
- lem-weil-pbc-open-fibre-product: its Mathlib matches
  AlgebraicGeometry.Scheme.pullback_map_isOpenImmersion (Pullbacks.lean:701–707) and
  Scheme.Pullback.range_map (PullbackCarrier.lean:355–361) were read. The canonical open square
  is represented using Mathlib.AlgebraicGeometry.Restrict.morphismRestrict and
  morphismRestrict_ι (Restrict.lean:553–588); no replacement notion is introduced.

The imported coefficient-category module supplies the Grothendieck abelian structure for
AddCommGrpCat; the imported open-immersion module supplies the recorded functors and comparisons.

Edge cases: W empty, W=X, Y empty, g an identity, and F the zero sheaf remain allowed.
No nonemptiness, quasi-compactness, or separation is imposed; neither g nor g_W must be étale.
The universe u is arbitrary and abelian groups use u+1, as the recorded functors require.
The construction contains no hollow definition or axiom. The only sorry is the named theorem.

Searches actually run (full tool results are in searches.jsonl):

- msearch leansearch: "inverse image sheaf adjunction unit compatible with restriction to an
  open subscheme" returned HTTP Internal Server Error; unavailable, not a no-match result.
- msearch loogle: "CategoryTheory.Adjunction.comp_unit_app,
  CategoryTheory.Adjunction.leftAdjointUniq" returned zero hits.
- msearch leanfinder: "pullback of etale sheaves along restricted scheme morphism compatibility
  adjunction unit open restriction" returned eight hits, all on Zariski/structure-sheaf
  restriction or O_X-module adjunctions, none this statement on small étale sheaves.
- msearch grep: "unit.*restrict|restrict.*unit" in CategoryTheory/Sites returned four generic
  adjunction hits (CoverLifting:332,350; Adjunction:60,74), no exact statement.
- rg over WeilConjectures and lean/Sheaf for restriction/unit and upperStar/restriction:
  found the recorded comparisons, generic composition-unit identity, module-pullback units,
  and Sheaf.Paper.EtaleRestrictionPullbackUnit.etale_restriction_pullback_unit. The latter
  concerns arbitrary étale objects and independent cartesian-square data; it is a more
  general related theorem, not the exact open-subscheme statement. Its declaration and
  docstring were read; this module specializes the presentation to the actual inverse-image
  open without added data or hypotheses, and introduces no second definition.
- rg for the exact item id and proposed declaration in WeilConjectures and
  dag/lean_names_upstream.json returned no hits.

Source read: https://stacks.math.columbia.edu/tag/03F3, Lemma 21.7.1 (locality of cohomology).
Local literature/stacks-project/sites-cohomology.tex is absent on this machine, so the tag
was read online. The tag supplies the localization setting, not this compatibility assertion;
this agrees with the node's explicitly agent-written source and proof. The five proof steps
of the node are carried in the declaration docstring. No statement dispute or correction.

Validation: scompile.py compiled the single file cleanly on the server in 2.4 seconds,
with exit code 0 and no warnings. Delivery dry run follows; the independent second reader
will write the second-reading section and deliver.

## Second reading by C1

Independent verdict: the Lean says exactly what this node says. No mathematical,
statement, dependency, docstring or convention mismatch found; the module and node
copy are unchanged. This section is the only delivery change from the first reading.

Source checked first: the local Stacks checkout is absent. I opened Tag 03F3 and the
actual sites-cohomology.tex at
https://raw.githubusercontent.com/stacks/stacks-project/master/sites-cohomology.tex,
section Locality of cohomology, label lemma-cohomology-of-open, lines 549–582.
It assumes a ringed site and an object of it; it imposes no Noetherian, finiteness,
nonemptiness or characteristic condition. It supplies the localization setting, not
this unit-compatibility assertion. The node and docstring correctly say this is an
agent-identified gap with an agent-written proof; I did not treat 03F3 as a statement
of the displayed equation. No statement_change is present, so the correction/citer
checks do not apply.

Object, hypothesis and conclusion checklist, extracted from the node before comparison:

1. Arbitrary schemes X,Y and morphism g:Y→X. Lean: `{X Y : Scheme.{u}} (g : Y ⟶ X)`.
   Verdict: exact; no extra property of g, X or Y. I opened Scheme and Scheme.Hom,
   Mathlib.AlgebraicGeometry.Scheme, lines 35–76, and read their signatures.
2. An open W of X and its inverse-image open W' of Y. Lean: `(W : X.Opens)` and
   `(g ⁻¹ᵁ W).toScheme`. Verdict: exact, not an independently chosen subscheme.
3. The open inclusions jW,jW' and restricted gW, with their common composite h.
   Lean: `p := W.ι`, `p' := (g ⁻¹ᵁ W).ι`, `g' := morphismRestrict g W`, and
   `morphismRestrict_ι g W`. Verdict: exact. `hp` and `hp'` are inferred Etale
   proofs for these inclusions, not extra assumptions. I read Etale's signature
   in Morphisms/Etale.lean and morphismRestrict, its square equation, and
   isPullback_morphismRestrict in Restrict.lean, lines 550–594.
4. The small étale sites and an arbitrary abelian sheaf F on X. Lean:
   `∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u+1}` (using abbreviation A).
   Verdict: exact; I opened smallEtaleTopology in Sites/Etale.lean and Sheaf in
   CategoryTheory/Sites/Sheaf.lean. The AB import supplies coefficient instances,
   rather than assumptions on F. No coefficient ring restriction is introduced.
5. Inverse image, direct image and their units. Lean: `Etale.upperStar A p`,
   `Etale.upperStar A g`, `Etale.upperStar A g'`, and the unit components of
   `Etale.upperStarLowerStarAdjunction`. Verdict: exact. I read the Star section
   of WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs, including lowerStar's
   base-change evaluation and upperStar's sheafified Kan extension and adjunction.
   Their binders allow arbitrary scheme morphisms; g and g' need not be étale.
6. W×_X Y=W' and W×_W W'=W', compatibly with projections, for section evaluation.
   Lean: `iotaSite` has underlying `pullback.lift g' p' (morphismRestrict_ι g W)`;
   `theta` has underlying `pullback.lift g' (𝟙 _)`. The sheaf maps of their opposites
   carry sections on the chosen pullbacks to W'. Verdict: exact canonical maps.
   The restricted square is cartesian by isPullback_morphismRestrict; the lift is
   the inverse of its pullback comparison. The second lift is the inverse of the
   second projection over the identity of W. I also opened the dependency's
   Mathlib matches pullback_map_isOpenImmersion and Pullback.range_map and checked
   their full signatures and projection-compatible construction. No private
   fibre-product or restriction definition is made.
7. The canonical natural comparison κ=c_(g,jW')⁻¹ c_(jW,gW).
   Lean: `kappa := (Etale.upperStarComp A g' p).inv.app F ≫
   (Etale.upperStarComp A p' g (g' ≫ p) (morphismRestrict_ι g W)).hom.app F`.
   Verdict: exact. I opened the Comp section: upperStarComp points from the
   composite pullback to successive pullbacks, so its inv is the node's c.
   Both comparisons use the same h. I also read the unit equation
   upperStarComp_hom_app_unit_app in UpperLowerStar.Coherence, lines 157–174.
8. Canonical restriction comparisons ρF and ρ_(g⁻¹F), evaluated at W,W'.
   Lean: `rhoF`, `rhoG` are the hom components of
   `Etale.upperStarIsoLocalizationRestriction`; `eW`, `eW'` remove identity
   composites from the terminal étale objects. Verdict: exact orientation and
   evaluation. I read localizationRestriction, localizationRestrictionLowerStarAdjunction
   and upperStarIsoLocalizationRestriction in LowerShriek.OpenImmersion.Defs,
   lines 114–185: the comparison is the unique left-adjoint comparison to the
   restriction functor. The e-isomorphisms have identity underlying scheme maps;
   their inverses in opposite maps transport to the requested objects.
9. Every section a of Γ(W,jW⁻¹F), with equality in (g⁻¹F)(W').
   Lean's left side is the g' unit at w, theta, κ at w', ρG at w', then eW'.
   The right side is ρF at w, eW, the g unit at wx, then iotaSite.
   Verdict: every factor is present in the node's order, with the same source
   pF(w) and target gF(wy'). Equality of abelian-group homomorphisms is equivalent
   to equality on every a by extensionality; it adds no stronger conclusion.

Edge cases: W=∅, W=X, empty X or Y (for each available g), identity g, and zero F
are all allowed by the binders and canonical constructions. There is no index set,
integer n or characteristic binder; thus no empty-index or n=0 exclusion arises.
The universe u is arbitrary; AddCommGrpCat.{u+1} is the recorded site's coefficient
convention, and arbitrary larger data can be covered by raising u. No test-object
quantification in a smaller independent universe appears. All variables and
universes are bound. The let-bound constructions are explicit data, not hypotheses.

Independent searches (different wording from the first reader):

- msearch leanfinder: "compatibility of pullback of sections with localization
  comparison on small etale sites for an open immersion": eight matches, all
  structure-presheaf/open-immersion maps, not this abelian étale assertion.
- msearch loogle: "AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction":
  service reported unknown identifier and no hits; not evidence of nonexistence
  in upstream, whose declaration I opened directly.
- msearch leansearch: "The adjunction unit of inverse image of abelian etale
  sheaves commutes with restriction to an open subset": unavailable, HTTP internal
  server error. No no-match verdict is inferred from this failure.
- msearch grep: "localization.*unit|unit.*localization": 25 matches, mostly ring
  localization and categorical localization, none the required statement.
- Direct rg on Mathlib/CategoryTheory/Sites for unit/restrict and unit/localization
  found generic CoverLifting and Adjunction lemmas only. Direct rg on upstream
  WeilConjectures and repository lean/Sheaf for unit/localization/open found the
  recorded comparisons, derived/unit identities and the related
  AlgebraicGeometry.etale_restriction_pullback_unit. I opened that entire module:
  it takes independent schemes, cartesian-square maps and an isomorphism witness,
  with an existential étaleness conclusion. It does not have this node's open W
  input and canonical restricted morphism. No exact existing statement was found;
  the current module introduces no new definition. Exact name and blueprint-id
  search on upstream and dag/lean_names_upstream.json found no collision.

There are no new definition nodes or dependency modules to review. All eight
statement-dependency nodes and their recorded declarations or Mathlib matches were
read; none needs replacing. The docstring carries all five proof steps, their
citations, and the source qualification. There is one named theorem with `sorry`,
no hollow definition, no axiom and no theorem proved. The little typing proofs for
canonical site morphisms introduce no auxiliary proved statement. All lines fit
100 characters, namespaces have no Sheaf prefix, and both imports are used.

Validation: signature whitespace comparison with lean.statement returned True;
there are no overlong lines. Remote scompile of the absolute sandbox module path
compiled cleanly in 2.2 seconds, exit 0, with no warnings. An initial relative-path
invocation could not find the sandbox file; the absolute-path invocation fixed
that command error without changing the module. Delivery preflight and push follow.
