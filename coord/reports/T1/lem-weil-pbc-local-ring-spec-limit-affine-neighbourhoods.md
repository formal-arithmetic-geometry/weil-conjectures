## Worker report

The module `Sheaf.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods` states
`AlgebraicGeometry.Scheme.fromSpecStalk_limit_affine_neighbourhoods`, with its sole proof
`sorry`. No definitions, new nodes, dependency modules, or statement corrections were needed.
The original node is unchanged except for its `lean` record.

Hypotheses and objects:

- `X : Scheme.{u}` is the arbitrary scheme, and `x : X` its point. There are no finiteness,
  separatedness, closed-point, or affine hypotheses on `X`.
- `X.presheaf.stalk x` is the structure-sheaf local ring, using Mathlib's existing ring stalk,
  the ring case of `def-weil-pbc-module-stalk`.
- `Spec (X.presheaf.stalk x)` and `X.fromSpecStalk x` are exactly the spectrum and canonical
  morphism already used by the recorded canonical-morphism dependency.
- Throughout the statement, `N_x` is written inline as
  `{W : X.Opens // IsAffineOpen W ∧ x ∈ W}`. It is the set of all affine opens containing `x`,
  not a chosen affine cover or a selected basis. `W.1.toScheme` is its open subscheme.
- The node's reverse-inclusion order `W' ≥ W` is rendered by `W'.1 ≤ W.1` on the underlying
  opens. The corresponding inverse-system transition is Mathlib's `X.homOfLE hVW`.
  Thus transitions always go from smaller open subschemes to larger ones.

Clause-by-clause correspondence:

1. The first conjunct `∀ U, x ∈ U → ∃ W, IsAffineOpen W ∧ x ∈ W ∧ W ≤ U`
   expresses cofinality among all open neighbourhoods. The next conjunct is `Nonempty N_x`.
   Directedness is the following `∀ W V, ∃ Z, Z.1 ≤ W.1 ⊓ V.1` with all three in `N_x`.
   The next two conjuncts explicitly state identity and composition laws for the inclusion
   transitions. These are exactly the assertion that the indicated objects and maps form
   an inverse system, rather than an additional conclusion about some other diagram.
2. `∀ W : N_x, CompactSpace W.1.toScheme ∧ QuasiSeparatedSpace W.1.toScheme` states that
   every object is quasi-compact and quasi-separated. CompactSpace is topological
   quasi-compactness (no Hausdorff condition). For every `V ≤ W` in `N_x`, the next conjunct
   gives both `IsOpenImmersion (X.homOfLE hVW)` (the inclusion stipulated before clause (1))
   and `IsAffineHom (X.homOfLE hVW)` (clause (2)). Neither property is assumed.
3. For every open neighbourhood `U`,
   `∃! g : Spec (X.presheaf.stalk x) ⟶ U.toScheme, g ≫ U.ι = X.fromSpecStalk x`
   is exactly existence and uniqueness of the factorization through `j_U`.
   The projections used subsequently are the already defined `U.fromSpecStalkOfMem x hxU`;
   Mathlib's `Opens.fromSpecStalkOfMem_ι` identifies this map with that unique factorization.
   The following conjunct states compatibility of these projections with every transition.
   Finally, for every `T : Scheme.{u}` and family `tW : ∀ W : N_x, T ⟶ W.1.toScheme`
   satisfying `tW V ≫ X.homOfLE hVW = tW W`, it asserts
   `∃! t : T ⟶ Spec (X.presheaf.stalk x), ∀ W, t ≫ W.1.fromSpecStalkOfMem x W.2.2 = tW W`.
   This is the node's full universal property in schemes. It is the unbundled formulation
   of `CategoryTheory.Limits.IsLimit` (lift, fac, uniq), not an affine-test-only property.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`,
  and `Spec.map` (recorded by def-pc-scheme and def-weil-affine-spectrum).
- `Sheaf.Topology.PresheafModuleStalkFunctor`: read `PresheafOfModules.moduleStalkFunctor`
  and its carrier `stalkObj` for def-weil-pbc-module-stalk. This item uses only the ring-stalk
  clause of that dependency, which is already `TopCat.Presheaf.stalk` from
  `Mathlib.Topology.Sheaves.Stalks`; it does not involve a module or module morphism, so
  importing or applying the module functor would introduce irrelevant structure.
- Imported `Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`: read the signatures
  and docstrings of `Scheme.fromSpecStalk_affine_description`,
  `Scheme.fromSpecStalk_local_properties`, `Scheme.fromSpecStalk_module_stalk`, and
  `Scheme.fromSpecStalk_quotient_factorization`. Its canonical map and ring carrier are
  Mathlib's `Scheme.fromSpecStalk` and `X.presheaf.stalk x`, used here without copying them.
- `Mathlib.AlgebraicGeometry.Stalk`: `Scheme.fromSpecStalk`,
  `Scheme.Opens.fromSpecStalkOfMem`, and `Scheme.Opens.fromSpecStalkOfMem_ι`; full definitions
  and signatures read. `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Opens.toScheme`,
  `Scheme.Opens.ι`, `Scheme.homOfLE`, and the identity and composition lemmas read.
- def-weil-pbc-scheme-conventions is explicitly a convention node with no declaration.
  Its affine and qcqs meanings are the existing `IsAffineOpen`, `CompactSpace` and
  `QuasiSeparatedSpace`; no dependency module or substitute predicate is required.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`, the
  recorded mathlib_match of def-weil-open-immersion.
- Imported `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`,
  the recorded mathlib_match of pqf-def-affine-morphism; read its complete definition.
- `Mathlib.CategoryTheory.Limits.HasLimits`: the colimit dependency's recorded declarations
  `colimit`, `Cocone`, `IsColimit`; read the universal-property signatures in their defining
  modules `Cones` and `IsLimit`. The node explicitly states the dual universal property,
  which is written out using `∃!`; no alternative notion of limit is defined.

Edge cases checked before writing:

- The empty scheme has no `x`, hence is correctly covered vacuously by the theorem binder;
  no unnecessary Nonempty X assumption appears.
- Every nonempty pointed scheme has at least one affine neighbourhood. Nonemptiness of
  `N_x` is a conclusion; an empty indexing family cannot sneak into the universal property.
- `X` need not be quasi-separated: an intersection of two affine opens need not itself be
  affine. Directedness asserts a smaller affine neighbourhood inside that intersection.
- No point is required to be closed. In particular generic points and their field stalks
  are covered. For `X = Spec k` the system has the whole one-point scheme and the canonical
  map is its usual stalk-spectrum map.
- `T` is any scheme in `Scheme.{u}`, including the empty scheme, not merely an affine
  scheme. Its morphism family has the full compatibility condition, and uniqueness is
  equality of scheme morphisms. Index opens and local rings live in the same universe u;
  no independent index universe or undersized test category is imposed.
- Identity transitions are included when `V = W`; the inclusion order is reversed exactly
  as in the node. The structure-sheaf stalk at an actual point is a local ring, including
  nonreduced schemes; no reducedness/domain condition is imposed.

Searches for an existing statement:

- `msearch.py ... leanfinder "Spec of the stalk is the inverse limit of the affine open
  neighbourhoods of a scheme point"`: eight hits on `Scheme.fromSpecStalk`,
  `IsAffineOpen.fromSpecStalk`, its independence and closed-point lemmas, and `over_def`.
  None is the neighbourhood limit theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.fromSpecStalk,
  CategoryTheory.Limits.IsLimit"`: zero hits.
- `msearch.py ... grep "fromSpecStalk|isLimit.*[Ss]talk|[Ss]talk.*[Ll]imit"
  AlgebraicGeometry`: 25 displayed hits, principally the canonical morphism and its uses
  in Stalk, SpreadingOut, ValuativeCriterion, QuasiFinite, and Geometrically/Reduced;
  no theorem of the requested limit property.
- `msearch.py ... leansearch "spectrum stalk inverse limit affine neighbourhoods scheme"`:
  unavailable, Internal Server Error. Recorded as unavailable, no negative verdict inferred.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and repository `lean/Sheaf`
  for `affine.*(neigh|Neigh)|fromSpecStalk|local-ring-spec-limit` found the existing
  canonical-morphism module and routine uses of stalk-spectrum maps, not this statement.
  More specifically `lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods|
  [Ii]sLimit.*[Ss]talk|[Ss]talk.*[Ii]sLimit` found no existing declaration in either tree.
- `rg` for `fromSpecStalk_limit_affine_neighbourhoods|SpecStalkLimitAffineNeighbourhoods`
  in Mathlib, the source repository, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no collisions.

Source check: local `literature/stacks-project/limits.tex` is absent on this machine, so
read the named places directly at https://stacks.math.columbia.edu/tag/0GWT (proof) and
https://stacks.math.columbia.edu/tag/01YW. The former identifies the stalk as the ring
colimit and its spectrum as the neighbourhood limit; the latter gives the scheme limit
of affine schemes as Spec of their section-ring colimit. The extra closed-point and
finite-presentation assumptions belong to the ambient glueing lemma, not to this
intermediate stalk-limit assertion. The source typo “neighbourhoods of s” refers to x.

Validation: `scompile.py T1 lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods
<module path>` compiled cleanly on the server in 1.8 s, exit code 0, no warnings.
Every universe and variable is explicitly bound, with `set_option autoImplicit false`.
The declaration docstring carries the node's seven proof steps and their dependencies.
No statement dispute or node fault was found. Independent second reading is left to
its assigned reader; the worker has not supplied a second-reading section.

## Second reading by T1

Independent reading of the sandbox node and module, all eight statement-dependency
nodes and their recorded declarations, and the Stacks source. No mismatch was found;
no Lean, node, dependency record, or mathematical statement was changed. This section
is the only addition to the delivery.

Source: the local Stacks checkout is absent. Read the actual `limits.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/limits.tex,
labels `lemma-morphism-glueing-near-closed-point` (Tag 0GWT) and
`lemma-directed-inverse-system-affine-schemes-has-limit` (Tag 01YW), including the
complete statements and proofs; also checked https://stacks.math.columbia.edu/tag/0GWT
and https://stacks.math.columbia.edu/tag/01YW. The stalk-colimit/spectrum-limit
argument depends only on the scheme and its point. Closedness of x, quasi-compactness
of the punctured-open inclusion, and finite presentation of Y are used in the subsequent
spreading/glueing argument, not in this intermediate result. The printed `s` in the
neighbourhood sentence is the source's typo for x. Tag 01YW asserts a limit in schemes,
indeed in locally ringed spaces, and does not restrict test schemes to affine schemes.

Objects and hypotheses, matched individually (all PASS):

- Arbitrary scheme X: `(X : Scheme.{u})`; no field, Noetherian, separation, finiteness,
  affineness, or nonemptiness instance. Read the `Scheme` structure in Mathlib Scheme.lean:
  it is a locally ringed space with affine neighbourhoods.
- Point x: `(x : X)`, any underlying point, with no closed-point restriction.
- Local ring O_{X,x}: `X.presheaf.stalk x`. Read Mathlib's `stalkFunctor` and `stalk`:
  the ring presheaf's colimit over opposite open neighbourhoods. Read the recorded
  `PresheafOfModules.stalkObj` and `moduleStalkFunctor`: these reuse that ring stalk;
  this item needs the ring clause, not a module carrier or its induced linear maps.
- Spectrum: `Spec (X.presheaf.stalk x)` uses recorded `AlgebraicGeometry.Spec`;
  read its definition and `Spec.map` in Scheme.lean.
- Canonical morphism g_x: `X.fromSpecStalk x`. Read its affine-cover definition in
  Stalk.lean and all four statements in the recorded SpecLocalRingCanonicalMorphism
  module, especially `fromSpecStalk_affine_description` and
  `fromSpecStalk_local_properties`. They use the same carrier and canonical morphism.
- All affine open neighbourhoods N_x:
  `{W : X.Opens // IsAffineOpen W ∧ x ∈ W}`. Read `IsAffineOpen` and `IsAffine`:
  affineness of the actual open subscheme, with no selected cover/basis restriction.
  The convention dependency fixes no new notion and requires no private replacement.
- W as open subscheme: `W.1.toScheme`; arbitrary U as open subscheme: `U.toScheme`.
  Read `Opens.toScheme` and `Opens.ι` in Restrict.lean: structure-sheaf restriction
  and its canonical open immersion.
- Reverse inclusion W' ≥ W: smaller underlying opens are encoded by `hVW : V.1 ≤ W.1`;
  the inverse-system arrow is `X.homOfLE hVW : V.1.toScheme ⟶ W.1.toScheme`.
  Read `Scheme.homOfLE`, `homOfLE_ι`, and its underlying inclusion and open-immersion
  instance. Thus the arrow orientation agrees with the node, without needing a new
  ordered-neighbourhood definition.

Conclusion checklist (all PASS):

1. Every open U containing x contains an affine neighbourhood:
   `∀ U : X.Opens, x ∈ U → ∃ W, IsAffineOpen W ∧ x ∈ W ∧ W ≤ U`.
2. N_x is nonempty: `Nonempty {W : X.Opens // IsAffineOpen W ∧ x ∈ W}`,
   a conclusion rather than an assumption.
3. N_x is directed: `∀ W V, ∃ Z, Z.1 ≤ W.1 ⊓ V.1`, all in N_x.
   It does not falsely assert that intersections themselves are affine.
4. The displayed objects/inclusions form an inverse system: the identity conjunct
   `X.homOfLE (le_refl W.1) = 𝟙 W.1.toScheme` and composition conjunct
   `X.homOfLE hZV ≫ X.homOfLE hVW = X.homOfLE (hZV.trans hVW)` are precisely the
   functor laws of the node's stipulated system. They encode its clause (1).
5. Every object is qcqs: `∀ W, CompactSpace W.1.toScheme ∧
   QuasiSeparatedSpace W.1.toScheme`. Read both class definitions: compactness does
   not impose Hausdorffness, and quasi-separatedness means compact-open intersections
   are compact, the standard scheme condition.
6. Every transition is an open immersion and affine:
   `∀ W V hVW, IsOpenImmersion (X.homOfLE hVW) ∧ IsAffineHom (X.homOfLE hVW)`.
   Open immersion is stipulated in the node's introduction; affineness is clause (2).
   Read the recorded Mathlib definitions: locally-ringed-space open immersion, and
   inverse images of all affine opens affine. Neither is an extra hypothesis.
7. Factorization through every open neighbourhood U, not only affine ones:
   `∀ U (hxU : x ∈ U), ∃! g : Spec (X.presheaf.stalk x) ⟶ U.toScheme,
   g ≫ U.ι = X.fromSpecStalk x`. The hypothesis and equation exactly match clause (3).
8. The indicated factorizations are the cone projections:
   `V.1.fromSpecStalkOfMem x V.2.2 ≫ X.homOfLE hVW =
   W.1.fromSpecStalkOfMem x W.2.2`. Read `Opens.fromSpecStalkOfMem` and
   `Opens.fromSpecStalkOfMem_ι`; these existing maps factor g_x, so the preceding
   uniqueness identifies them with the node's g_{x,W}, not arbitrary alternative maps.
9. Full scheme-limit universal property: `∀ (T : Scheme.{u}) (tW : ∀ W, T ⟶
   W.1.toScheme), (∀ W V hVW, tW V ≫ X.homOfLE hVW = tW W) →
   ∃! t : T ⟶ Spec (X.presheaf.stalk x), ∀ W,
   t ≫ W.1.fromSpecStalkOfMem x W.2.2 = tW W`.
   T precedes the compatible family and its compatibility assumption; the mediating
   arrow is unique as a scheme morphism. Read `IsLimit`'s lift/fac/uniq and the dual
   `IsColimit` in Mathlib CategoryTheory/Limits/IsLimit.lean: this is the node's explicitly
   unbundled universal property. No new definition of a limit is introduced.

Edge cases: an empty X has no x, correctly making this pointed theorem vacuous;
Spec of the zero ring is included on the same basis. An empty test scheme T is allowed.
N_x cannot be empty at an actual point: nonemptiness is concluded from the affine
basis, not assumed. Generic and nonclosed points, nonreduced schemes, arbitrary
characteristics, and schemes which are not quasi-separated are all allowed.
There is no numerical parameter n. Universe u is bound explicitly and arbitrary;
X, its opens (hence the index set), the stalk ring, and the test schemes all live in
that universe, giving the full universal property in Scheme.{u}. There is no independent
index universe or vacuous smaller test universe. `autoImplicit false` is set and all
binders/universes are visibly bound.

Independent searches (different conceptual wording from the worker):

- `msearch.py ... leanfinder "The spectrum of a scheme local ring is a projective limit
  of Zariski neighborhoods"`: eight hits, on toSpecΓ, local-ring morphism correspondence,
  Spec.locallyRingedSpaceObj and Spec_fromSpecStalk; none states the neighbourhood limit.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem"`: eight hits;
  existing factorization maps/equations and spreading-out lemmas, no complete theorem.
  Opened the factorization declaration and equation and reused them as above.
- `msearch.py ... leansearch "Local scheme as projective limit of open neighborhoods"`:
  unavailable (Internal Server Error). This is an unavailable service, not a negative hit.
- `rg` for `([Ll]imit.*([Ss]talk|[Nn]eigh)|([Ss]talk|[Nn]eigh).*([Ll]imit|[Cc]one))`
  in Mathlib/AlgebraicGeometry, source WeilConjectures, and repository lean/Sheaf:
  module/geometric-stalk colimit results and affine pointed étale-neighbourhood cofinality,
  no instance of this theorem. Opened AffinePointedNeighbourhoodCofinal.lean: it concerns
  geometric points and the small étale site, not this Zariski-open scheme limit.
- `rg` for the delivered declaration in dag/lean_names_upstream.json: no collision.
  The worker's existing name/concept searches were also read; no duplicate notion found.

Delivery checks: exactly one statement module and one node copy, no new nodes or
additional dependency modules; no `statement_change`, hence no correction/citer review
is applicable. The sole theorem has proof `sorry`; there is no definition, hollow data,
private notation, file-local instance, or proved lemma. The source-tagged module and
statement docstrings name this blueprint item and reproduce all seven proof steps.
Both imports supply the canonical-map dependency and affine-morphism class respectively.
All lines are at most 100 characters. The node's `lean.statement` is byte-for-byte equal
to the theorem signature in the module. Compilation and delivery validation follow below.

Second-reader validation: `scompile.py T1
lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods <module>` completed on the server
in 2.5 seconds, exit code 0, with no errors or warnings. The unchanged signature and
all binders were also checked by eye.
