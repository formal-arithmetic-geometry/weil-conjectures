## Worker report

The module `Sheaf.CategoryTheory.SiteHypercoverInjectiveSections` states
`CategoryTheory.siteHypercover_injective_sections_exact`, with one `sorry` and no new
definitions. It preserves the current Q37-reviewed DAG split verbatim. The earlier
worker's stage-1 live-sync rejection is avoided by supplying only the stage-2 `lean`
record, the statement module, and this report. There is no statement correction.

Hypothesis and clause correspondence:

- A small site with finite limits is `{C : Type u} [Category.{v} C]
  [HasFiniteLimits C]`, `(J : Precoverage C)` and
  `(hsite : J.IsSiteForCoverings)`. The recorded site predicate is used directly;
  sheaves are for the associated `J.toGrothendieck`. All objects and morphisms are
  sets. Object and morphism universes are independent.
- The object `W`, simplicial object `V` and augmentation are `(W : C)`,
  `(U : SimplicialObject C)` and
  `(e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W)`. The natural transformation
  includes compatibility with every simplicial operator, not just the face maps.
- The matching-cover assumption is `hcover`. A map from `T` to the degree-`n`
  matching object in `C/W` consists precisely of `w : T ⟶ W` and the family
  `p Δ h θ`, compatible with augmentation and all maps between simplices of
  degree less than `n`. This is a cone over the truncated slice diagram defining
  the coskeleton in degree `n`. Since a lower-dimensional simplex operator misses
  a vertex, it factors through a proper face; the full family is therefore
  equivalent to the compatible proper faces used in the node. The displayed
  compatibility equations ensure independence of the chosen face factorization.
  Finite completeness supplies that matching object. The conclusion of `hcover`
  supplies a covering sieve and local lifts of this cone. This is equivalent to
  the generated sieve of `Uₙ → Nₙ` being covering: pull back that sieve along every
  `T → Nₙ` for one direction; for the other take `T = Nₙ` and its universal cone.
  A covering sieve here contains a covering family of the given site. None of
  this invokes subcanonicality; representable *presheaves* preserve limits.
- An injective abelian sheaf is
  `(I : Sheaf J.toGrothendieck AddCommGrpCat.{max u v r}) [Injective I]`.
  The coefficient universe contains the site sizes and the independent level `r`;
  it does not identify the site object and morphism universes.
- `C^n(V,I) = I(V_n)` is the type `I.obj.obj (op (U _⦋n⦌))`.
  Its actual differential is the displayed function
  `fun s ↦ ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • I.obj.map (U.δ j).op s`.
  These are the canonical additive restriction maps and their signed sum; no
  arbitrary differential is supplied as a hypothesis.
- Exactness at `I(W)` is the first conjunct `Function.Injective` of restriction
  along `e.app (op (SimplexCategory.mk 0))`.
- Exactness at `I(V₀)` is the next `Function.Exact` conjunct for that same
  restriction and the degree-zero signed sum. Thus the degree-zero identification
  is specifically induced by restriction from `W`.
- Exactness at every `I(V_{n+1})`, with `n : ℕ`, is the final universally quantified
  `Function.Exact` between successive displayed differentials. Together these
  three clauses give exactly the entire augmented sequence in the node.
- There is no `Subcanonical`, splitting, affineness, nonemptiness, or weak
  contractibility assumption.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: the recorded site component,
  with sheaves and cohomology interpreted through Mathlib.
- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`,
  `CategoryTheory.SimplicialObject`, its face maps `.δ`, and natural transformations
  to the constant functor.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`,
  `CategoryTheory.Injective`: its `factors` field is the extension property used
  in the natural-language proof.
- `def-weil-size-convention` has a metatheoretic convention record, rather than a
  module. Explicit `u`, `v`, `r` implement it here.
- The Mathlib proof dependency `lem-trf-site-free-sheaf-sections` records
  `CategoryTheory.Sheaf.freeYonedaHomEquiv` in
  `Mathlib.CategoryTheory.Generator.Sheaf`. Its full signature and implementation
  identify Hom from the sheafified free representable with Hom from the free
  generator to `I(U)`. `uliftZMultiplesHom` in
  `Mathlib.Algebra.Category.Grp.ForgetCorepresentable` then identifies the latter
  with sections. Both modules are imported without `public` for the later proof.
- `lem-trf-site-hypercover-free-resolution` has no recorded Lean declaration on
  the current base, so it supplies the recorded mathematical proof plan, without
  an import to a nonexistent module. It is needed only for the proof, not to type
  the statement. The module docstring reproduces all three proof steps.

Sources checked: `literature/stacks-project/hypercovering.tex`, the full statement
and proof of `lemma-injective-trivial-cech` (Tag 01GW), including
`equation-identify-cech`, degree zero from `lemma-h0-cech`, and the free resolution
from Tag 01GE. The theorem is the representable case, retaining the arbitrary site.

Edge cases checked before writing:

- Degree zero: `Δ.len < 0` has no solutions, so the matching family is empty.
  The local lifting condition is precisely the covering condition on `U₀ → W`.
- Degree one: the matching data are two vertices over the same `W`, giving
  `U₀ ×_W U₀`; the differential is the difference of their restrictions.
- Identity hypercover: augmentation is identity; differentials alternate zero
  and identity, so all displayed exactness clauses hold.
- Zero sheaf: every map is the unique zero map between zero groups and exactness
  holds. Empty covering families remain allowed; the sheaf condition forces the
  relevant sections to be zero, and no nonempty family is assumed.
- An empty category has no `W`, making the universal theorem vacuous in the
  mathematically correct way. No universe equality excludes a site.
- No splitting or subcanonicality is used in the local lifting formulation.

Duplicate searches:

- `msearch.py leanfinder`, query "For an arbitrary site the augmented alternating
  complex of sections of an injective abelian sheaf on a hypercover is exact":
  eight hits, including Mayer--Vietoris exactness, injective-resolution exactness,
  and the alternating constant complex; none is the stated general theorem.
- `msearch.py loogle`, query `SimplicialObject, Injective, Function.Exact`:
  no hits, unknown identifier `SimplicialObject` at the service.
- `msearch.py leansearch`, query "exact alternating section sequence injective
  abelian sheaf arbitrary site hypercover": eight hits on stalk injectivity,
  one-hypercover gluing, injective resolutions and Mayer--Vietoris; no match.
- `msearch.py grep`, query
  `hypercover.*(injective|exact)|injective.*hypercover`: two hits on
  `CoproductSheafCondition` and `Hypercover/Saturate`, both low-degree results.
- `rg` in upstream `WeilConjectures`, Mathlib and project `lean/Sheaf` for
  `hypercover`, `Hypercover`, matching objects, injective sections and the proposed
  declaration; the proposed name has no match in those trees or in
  `dag/lean_names_upstream.json`. The required upstream grep for this node id also
  has no hit.
- The closest project declarations are
  `ringedHypercover_injective_augmentation_exact` and its noncommutative ring
  variant. Their full signatures require a subcanonical topology and ring-module
  sheaves, so they are not the present arbitrary-site abelian theorem.
  `RingedHypercover.HasLocalLifts` in the published
  `Sheaf.CategoryTheory.RingedHypercoverFiniteCones` was read using
  `scompile.py --source`; its local matching condition is the same one spelled
  out here, but its category binder is `SmallCategory C`. No second definition
  is introduced to generalize that helper: the theorem states the condition
  directly, retaining independent object and morphism universes.

Validation: the prescribed `scompile.py N3 lem-trf-site-hypercover-injective-sections`
compiled this file in both its sandbox and library locations under the standard
60-second limits, with no errors or warnings. All theorem binders and universe
levels are explicit (`set_option autoImplicit false`), and every line is at most
100 characters.

## Second reading by N3

No independent second worker was started, as required by the dispatch brief.
The maintainer's independent review reads the delivered module and report.
