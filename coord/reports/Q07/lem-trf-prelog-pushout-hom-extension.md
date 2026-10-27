## Worker report

The module `Sheaf.AlgebraicGeometry.PrelogPushoutHomExtension` states
`AlgebraicGeometry.prelog_pushout_hom_extension`, with one `sorry` and no definitions
or additional postponed results. The node is unchanged except for `lean`.

The source was read at ILO VI 1.1, printed p.69: log structures are on the étale
topology and the schemes are locally Noetherian unless stated otherwise. That
paragraph refers to Kato for log terminology; the node explicitly identifies its
quotient argument as agent supplied. Stacks `sites.tex`, section
`section-sheaves-algebraic-structures`, assertion (epsilon), supplies the
sheafification Hom bijection, as recorded by the dependency.

Hypothesis and clause correspondence:

- The locally Noetherian scheme is `(X : Scheme.{u}) [IsLocallyNoetherian X]`.
  Its small étale site is `X.Etale` with `X.smallEtaleTopology`.
- An arbitrary monoid **presheaf**, with no sheaf, finiteness, cancellation, or
  saturation assumption, is `M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}`.
  The structural natural monoid map is `γ`; the existing
  `X.etaleStructurePresheaf` has value `Γ(U.unop.left, ⊤)` and ring restrictions.
- At `U`, the ring `B_V` is `X.etaleStructurePresheaf.obj U` and its units are
  `(X.etaleStructurePresheaf.obj U)ˣ`.
  `divisorialChartPushout (A := ...) (γ.app U).hom.mrangeRestrict` is the real
  congruence quotient of `M.obj U × B_Vˣ`. Its existing congruence identifies
  `(e,1)` with `(1,a)` exactly when `γ(e) = a.val`. Multiplying by `(m,u)`
  gives the node's `(me,u) ~ (m,γ(e)u)`; conversely the node's relations with
  `m=u=1` give those generators. The range restriction preserves every value
  of `γ` and imposes no injectivity or surjectivity hypothesis.
- `L : EtaleLogStructure X` is the dependency's log structure. The family `η`
  consists of monoid maps out of these actual quotients; `hη` is exactly their
  naturality under restriction, expressed on all pair representatives. Quotient
  representatives exhaust the sectionwise quotients.
- `hα` is precisely `α_L η([m,u]) = γ(m)u`. The `@id` only makes the ring
  carrier explicit when moving from the forgotten multiplicative monoid.
- `hsh` says that every natural monoid map from this quotient presheaf into
  **every monoid sheaf** extends uniquely through `η`. It is the stated
  sheafification property, not a universal property restricted to log structures.
  Giving naturality on pairs is equivalent to giving it on quotient sections.
  No existence of sheafification on a larger site is assumed: this is the given
  sheafification, as in proof step 4 of the node.
- `i` and `hi` render the node's `i_V(m) = η_V([m,1])`. This introduces its
  canonical natural transformation by an exhaustive defining equality, not an
  additional choice or restriction: `hη` makes that formula natural and `η` is
  multiplicative. The node's `j_V(u)` is the inline expression
  `η U ((divisorialChartCongruence ...).mk' (1,a))` in the final clause.
- `K : EtaleLogStructure X` is arbitrary. The existential family `jK` is
  characterized as the inverse of the unit isomorphism: it is multiplicative,
  its structural image is `a.val`, and every section with that structural image
  equals `jK U a`. This determines the inverse uniquely. Its naturality follows
  from the same uniqueness and naturality of `K.alpha`, so no arbitrary lift
  replaces the canonical inverse. Sectionwise unit lifts are obtained from the
  dependency's geometric-stalk log condition by étale sheaf descent.
- The first substantive conclusion, `∀ v, v ≫ K.alpha = γ → ∃! f, ...`, is the
  bijection expressed by its singleton fibres. Its source consists of sheaf
  maps satisfying `f.hom ≫ K.alpha = L.alpha`; its target consists of natural
  monoid maps satisfying `v ≫ K.alpha = γ`. The fibre equation is exactly
  `i ≫ f.hom = v`. Well-definedness of restriction follows from `hi` and `hα`
  with unit `1`, which give `i ≫ L.alpha = γ`.
- The next conclusion gives the inverse formula on **every** pair:
  `f.hom.app U (η U [m,a]) = v.app U m * jK U a`. Together with `hsh`, this
  states the unique extension through `η` of the natural quotient homomorphism
  specified in the node; it does not replace that homomorphism by an arbitrary map.
- The last conclusion quantifies over every compatible `f` independently of
  `v`, and asserts `f(η[1,a]) = jK(a)`, exactly the automatic unit condition.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Sites.Etale` and `Morphisms.Etale`:
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and `Scheme.Etale`.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `EtalePrelogStructure` (including `monoidSheaf`, `alpha`), `EtaleLogStructure`
  (including `reflectsUnits`, `unitsBijective`, its inherited section data).
  Its imported `Sheaf.AlgebraicGeometry.LogRegularPair` supplies
  `divisorialChartCongruence` and `divisorialChartPushout`; its imported
  `WeilConjectures.AlgebraicGeometry.Sites.Gm` supplies
  `Scheme.etaleStructurePresheaf`. No copy of these notions is declared.
- `lem-trf-commutative-monoid-sheafification` is a Mathlib leaf with no `lean`
  record. Its recorded `CategoryTheory.sheafificationAdjunction` in
  `Mathlib.CategoryTheory.Sites.Sheafification` and `sheafifyComposeIso`,
  `sheafComposeIso_hom_fac` in `Sites.PreservesSheafification` were read;
  their modules are public imports. The given unit's universal property is `hsh`.
- Recorded proof dependencies are imported without `public`:
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` (`Etale`),
  `Morphisms.UniversallyOpen` (`UniversallyOpen.of_flat`), `Sites.Fpqc`
  (`Scheme.fpqcPrecoverage`, its subcanonical topology instance), and
  `GammaSpecAdjunction` (`ΓSpec.locallyRingedSpaceAdjunction`).

Edge cases checked before the final statement: empty schemes/étale objects and
zero section rings are allowed; a zero ring has its trivial unit group, not an
empty unit group. The terminal monoid presheaf and the case where all structural
images are units need no exceptions. Nonintegral and noncancellative monoids are
allowed by the congruence quotient. No fs hypothesis on either log structure is
added. There is no nonempty index set or nontrivial-ring hypothesis. Universes
follow the dependency's existing `EtaleLogStructure` and ring-section carriers;
all variables and universe parameters are explicitly bound, with auto implicits
disabled.

Searches actually run, 2026-10-24:

- `msearch.py ... leanfinder "A map from a prelog presheaf to a log structure
  extends uniquely over the sheafification of its pushout with units"`: eight
  generic sheafification hits, including `sheafifyLift_unique`; no exact statement.
- `msearch.py ... leansearch "A prelog presheaf map to a log structure extends
  uniquely over the unit pushout sheafification"`: eight generic sheafification
  hits, including `sheafify_hom_ext`; no exact prelog assertion.
- `msearch.py ... loogle '"prelog"'`: zero hits.
- `msearch.py ... grep 'prelog|Prelog|LogStructure|logification'`: zero Mathlib hits.
- `rg` for the node id and `prelogPushout_hom|pushout.*[Ee]xtension` in both
  `lean/WeilConjectures` and `lean/Sheaf`: no existing statement. A mention of
  this node occurs in the proof docstring of `ZariskiPrelogLogificationComparison`.
- `rg` for prelog/log structures in `lean/Sheaf/AlgebraicGeometry` found the
  existing quotient construction, log structures and the downstream
  `PrelogPushoutPresentation` interface. The downstream node cites this item in
  `proof_deps`, so importing it and adding its node as a dependency would make a
  cycle. The final file uses the original quotient declaration from this item's
  existing dependency and writes the hypotheses explicitly; it declares no copy
  of that presentation interface. The initial downstream import was removed.
- The node-id search in `dag/lean_names_upstream.json` returned no declaration.
  `rg` of `lean/WeilConjectures` for `prelogPairClass|PrelogPushoutPresentation`
  found no upstream copy; those helpers are in the downstream Sheaf module.

No statement correction, new node, dependency-module repair, or unresolved
statement dispute is needed.

Validation: `scompile.py` compiled the final interface successfully in both sandbox
and library modes (2.7s and 2.8s before whitespace-only formatting). An initial
elaboration failure was repaired by explicitly giving the ring parameter `A` to
the congruence constructor, rather than letting inference select the forgotten
multiplicative-monoid carrier. No diagnostic declarations remain.

## Second reading by Q07

Author's second pass; the dispatcher brief forbids starting another agent, and
independent review belongs to the maintainer. I reopened the node and final file
and compared the arbitrary presheaf, compatible structural maps, actual quotient
relations, full sheafification universal property, inclusion formulas, inverse
unit lift, bijection, inverse extension formula and automatic unit clause.
The singleton-fibre formulation quantifies over all compatible natural maps and
all compatible sheaf maps, and both inverse identities follow exactly as in the
node. In particular `M` is not required to be a sheaf or integral, and `hsh`
is not restricted to log targets. The extra-looking parameters `i` and `hi`
are the explicitly specified canonical map, and `jK` is fully determined by its
unit-preimage equations. I removed the downstream presentation import after
checking its node's proof-dependency list; no DAG field needed changing.
The node's statement and all its original dependency fields are preserved.
