## Worker report

Item: `lem-sfb-smooth-normal-ascent`. The module
`Sheaf.AlgebraicGeometry.SmoothNormalAscent` states
`AlgebraicGeometry.Scheme.normalStalks_of_smooth`, with its sole proof `sorry`.
The node is unchanged except for its `lean` record. There are no new definitions,
new nodes, dependency repairs, or statement corrections.

Hypothesis and clause correspondence:

- Schemes V and W: `{V W : Scheme.{u}}`, with the universe `u` explicitly declared.
  This is Mathlib's category of schemes, with no finiteness or separation restrictions.
- The morphism g: V → W: `(g : V ⟶ W)`.
- Smoothness, def-sbc-smooth-morphisms: `[Smooth g]`. I read the recorded declaration
  and its docstring in `Mathlib.AlgebraicGeometry.Morphisms.Smooth`; its affine-chart
  ring-map criterion agrees with Stacks 02H6, as the dependency's record explains.
- W normal, meaning each O_{W,w} is an integrally closed domain:
  `(hW : ∀ w : W, IsDomain (W.presheaf.stalk w) ∧
  IsIntegrallyClosed (W.presheaf.stalk w))`.
- Every O_{V,v} is an integrally closed domain, hence V is normal:
  `∀ v : V, IsDomain (V.presheaf.stalk v) ∧ IsIntegrallyClosed (V.presheaf.stalk v)`.
  The domain and integral-closedness clauses are both retained.
- No Noetherianity, quasi-compactness, connectedness or surjectivity: none appears
  among the binders or instances. No `Nonempty` assumption excludes empty schemes.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, the
  recorded interface of def-sbc-smooth-morphisms.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, together
  with `IsDomain` on the commutative stalk rings, exactly the normal-domain inline
  convention of def-weil-pbc-normal-ring. Its abbreviation is integral closedness
  in `FractionRing`; it alone would not imply domainhood, so the conjunction matters.
- Proof imports retain the already stated proof dependencies: affine-open basis,
  canonical affine open immersion and induced Spec square, and stalk localization
  in `Mathlib.AlgebraicGeometry.AffineScheme`; open factorization in
  `Mathlib.AlgebraicGeometry.OpenImmersion` and `Mathlib.AlgebraicGeometry.Restrict`;
  smooth restriction in `Mathlib.AlgebraicGeometry.Morphisms.Smooth`; affine/ring-map
  identification in `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`; algebra
  smoothness in `Mathlib.RingTheory.Smooth.Basic`; and `RingHom.Smooth.isNormalRing`
  in `WeilConjectures.RingTheory.SmoothNormalRing`. I read the latter's full statement
  and proof docstring: it covers arbitrary commutative rings and universes, with no
  Noetherian or injectivity assumption.

Source checked: local `literature/stacks-project/descent.tex`,
`lemma-normal-local-smooth` (Tag 034F), including its affine ascent paragraph using
Algebra 033C. The theorem docstring records all five DAG proof steps: affine chart
choice; restricted smooth map and affine comparison; normality of R from stalks;
smooth algebra ascent; and transfer from S_q back to the source stalk.

Edge cases checked before writing:

- Empty V: the conclusion universally quantifies over its empty point type.
- Empty W: hW is vacuous and existence of g forces V empty; no extraneous point
  or nonemptiness is chosen in the statement.
- Disconnected normal W, for example Spec(k × k): every stalk can be a normal domain
  even though the global section ring is not a domain. Only stalks occur here.
- Smooth non-surjective morphisms, including open immersions and the empty source,
  satisfy the exact binders. No faithful flatness is introduced.
- Non-Noetherian normal bases and schemes without a finite affine cover are admitted;
  the natural-language argument chooses charts at one point at a time.
- The zero ring defines the empty affine scheme, already covered by the empty cases.

Searches for an existing public statement (2026-10-24):

- `msearch.py ... leanfinder "A smooth morphism of schemes with normal target has
  normal source"`: eight hits, chiefly `AlgebraicGeometry.IsSmooth`, stability of
  smoothness and relative normalization; no normal-stalk ascent theorem.
- `msearch.py ... leansearch "Normality ascends along smooth morphisms of schemes"`:
  eight hits on smoothness and normalization, no exact theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsSmooth, IsIntegrallyClosed"`: no hits;
  service reported unknown identifier `AlgebraicGeometry.IsSmooth`. The installed
  source instead supplies `Smooth` and a deprecated alias, so this failed lookup
  is not taken as evidence of nonexistence on its own.
- `msearch.py ... grep "IsNormal|normal_goes_up|isNormal_of_smooth"
  AlgebraicGeometry`: zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for smooth/normal combinations,
  followed by exact searches for `smooth_normal_stalks`, `normal_stalks_of_smooth`,
  `smooth_normal_ascent`, and the item id. The item id occurs in proof docstrings
  of consumers, not an existing public declaration for this node. The semantic
  search also finds field-specific smooth-geometric-normality statements, which
  impose extra assumptions and do not supply the present theorem.
- An exact mathematical statement does occur as the PRIVATE helper
  `smooth_normal_stalks` in `WeilConjectures.AlgebraicGeometry.Morphisms.TraitEtaleExtension`
  (lines 31 onward). I read its full signature and docstring. It is not an exported
  interface and cannot supply the recorded public declaration by an import. The
  present theorem exposes this general statement under a fresh public name; it
  introduces no duplicate definition. Other private smooth-normal helpers require
  an integral base and are strictly more specialized.
- Read `WeilConjectures.AlgebraicGeometry.NormalScheme.IsNormalScheme`: its actual
  declaration is `AlgebraicGeometry.IsNormalScheme`, defined with an additional
  `IsIntegral S` conjunct. It cannot express this node, which admits empty and
  disconnected schemes. The normal-domain inline convention from the recorded
  dependency is used instead; no new normality predicate is introduced.
- Exact proposed-name search through Mathlib, project sources, and
  `dag/lean_names_upstream.json` found no `normalStalks_of_smooth` declaration.

Validation: prescribed `scompile.py Q86 lem-sfb-smooth-normal-ascent` compiled the
file both as a sandbox module and at its library module name, cleanly (1.6 s and
1.8 s respectively). `autoImplicit` is disabled, all variables/universes are bound,
and every line is at most 100 characters.

No statement dispute or mathematical node fault found.

## Second reading by Q86

This is a second pass by the same worker, not a claimed independent agent review;
the assignment prohibits starting other agents and reserves independent review
for the maintainer. I reopened the node and the final file and checked each binder
and conjunct against the statement: arbitrary schemes, the given smooth g, all
base stalks normal domains, all source stalks normal domains. No extra structure,
integrality, finiteness or nonemptiness appears. In particular replacing the inline
condition by the existing integral-scheme predicate would have excluded the empty
and disconnected cases, so that predicate was not used. The sole theorem has the
required `sorry` proof and a docstring reproducing the five-step proof plan.
No mismatch was found and no statement correction was needed.
