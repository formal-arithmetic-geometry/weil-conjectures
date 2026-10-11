## Worker report

The module `Sheaf.Algebra.Homology.QuasiIsoHomComplexMap` states
`CategoryTheory.quasiIso_homComplex_map`, with its only proof `sorry`.
No definitions, new nodes, dependency modules, or statement corrections are needed.
The source was read at https://stacks.math.columbia.edu/tag/0A95 (Lemma
sites-cohomology-lemma-RHom-well-defined) and
https://stacks.math.columbia.edu/tag/0A94 (Lemma
sites-cohomology-lemma-RHom-into-K-injective); the local literature checkout
is absent. The node matches 0A95. Its two-step expanded proof is in the docstring.

Hypothesis and clause correspondence:

- The site is `{C : Type u} [Category.{u} C] {J : GrothendieckTopology C}`.
- The sheaf of commutative rings is `{R : Sheaf J CommRingCat.{u}}`.
  Composition with `forget₂ CommRingCat RingCat` supplies the ring sheaf for modules.
- The four unbounded cochain complexes of module sheaves are `{I' I L' L :
  CochainComplex (SheafOfModules ... R_as_ring_sheaf) ℤ}`.
- The first chain map is `(s : I' ⟶ I)`; its two K-injectivity hypotheses are
  `[I'.IsKInjective] [I.IsKInjective]`, and its quasi-isomorphism hypothesis is
  `[QuasiIso s]`.
- The second chain map is `(t : L' ⟶ L)` with `[QuasiIso t]`; neither source
  complex is required to be K-injective, bounded, or termwise injective.
- The displayed Hom-complex morphism is
  `((homComplexFunctor (R := R)).map t.op).app I' ≫
  ((homComplexFunctor (R := R)).obj (op L')).map s`.
  The first factor maps Hom(L,I') to Hom(L',I') by precomposition with t;
  the second maps Hom(L',I') to Hom(L',I) by postcomposition with s.
  `CategoryTheory.homComplex_exists` specifies that its component under each
  product projection is `SheafOfModules.homObjMap (t.f p) (s.f q)`;
  hence this is exactly f ↦ s ∘ f ∘ t, with the node's domain and codomain.
- The conclusion `QuasiIso (...)` means an isomorphism on every cohomology sheaf,
  not merely on global-section cohomology or in degree zero.

Dependencies read and used:

- `def-pc-quasi-iso-modules`: `QuasiIso`,
  `Mathlib.Algebra.Homology.QuasiIso`, lines 138–143, with
  `quasiIsoAt_iff_isIso_homologyMap`, lines 68–72. This leaf needs no replacement.
- `def-pur-kinjective-complex`: `CochainComplex.IsKInjective`,
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`, lines 40–45:
  every map from an acyclic complex admits a homotopy to zero.
- `def-pc-cochain-complex-modules`: `CochainComplex`,
  `Mathlib.Algebra.Homology.HomologicalComplex`, lines 154–158, with ambient
  category/zero-morphism binders at line 47 and chain-map structure at 213–219.
- `def-pur-hom-complex`: `CategoryTheory.homComplexFunctor` and its recorded
  specification `CategoryTheory.homComplex_exists`, from
  `Sheaf.Algebra.Homology.HomComplex`. The recorded `homComplex` is the object
  part of this same bifunctor. No private Hom-complex construction is used.

The universe `u` is explicitly declared and arbitrary. The site objects and
morphisms, the coefficient rings, and module sections use this common universe,
as in the standard universe-polymorphic presentation of a ringed site. It can
be chosen as large as the given data require; this is not a fixed small universe.
The output universe `max u u u` of the recorded Hom complex reduces to `u`.
The imported ring-limit, group filtered-colimit, and module-sheaf abelian
instances supply ring-sheaf composition, sheafification, and homology without
extra mathematical assumptions. Independently sized universes initially caused
instance-synthesis timeouts; the shared-universe signature compiles in 2.2 seconds.
All variables are explicitly bound.

Edge cases checked before writing: zero complexes, identity quasi-isomorphisms,
acyclic K-injectives, an empty underlying site, and unbounded complexes are all
allowed. Integer degrees include zero and negative degrees. No restriction on
characteristic or on the nonzero nature of R occurs. Composition has the correct
variance and ordering even for nonidentity s and t.

Searches actually run (logged in searches.jsonl):

- LeanSearch: `sheaf internal Hom complex quasi isomorphism K injective
  precomposition postcomposition` — unavailable, HTTP Internal Server Error.
- LeanFinder: `Hom complex of sheaves into K injective complexes respects quasi
  isomorphisms` — eight hits, including `CochainComplex.IsKInjective` and
  derived-category Hom-complex cohomology results. None states the sheaf-valued
  internal Hom assertion.
- Loogle: `CochainComplex.IsKInjective, QuasiIso` — one hit,
  `CochainComplex.IsKInjective.quasiIso_iff`; this characterizes quasi-isomorphisms
  between K-injectives as homotopy equivalences, not the requested sheaf map.
- Mathlib grep through msearch: `homComplex.*[Qq]uasi|[Qq]uasi.*homComplex|RHom.*well`
  — one unrelated order-theory hit, no match.
- Direct rg in upstream `WeilConjectures/Algebra/Category/ModuleCat/Sheaf` for
  `homComplex|HomComplex|RHom` — no hits; upstream rg by item id — no hits.
- Direct rg in `lean/Sheaf` for `homComplex.*[Qq]uasi|[Qq]uasi.*homComplex|rhom_well`
  — no hits. Search for `homComplexFunctor` found only the dependency's module.
- Full declaration name search for `quasiIso_homComplex_map` in Mathlib,
  upstream WeilConjectures, and dag/lean_names_upstream.json — no hits.

No STATEMENT-DISPUTED finding or node fault was found. Server compilation passed cleanly (2.2 seconds). Maintainer preflight is
run via deliver2.py --no-push;
the independent second reader will add their own reading and deliver.

## Second reading by J1

I independently opened the node copy, the delivered Lean module, all four
statement-dependency nodes, their recorded declarations, and the Hom-complex
bifunctor's existence specification. I read the Stacks TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/sites-cohomology.tex,
saved only under scratchpad, at section-hom-complexes,
lemma-RHom-into-K-injective and lemma-RHom-well-defined (tags 0A8X, 0A94, 0A95).
The section assumes a ringed site throughout; it adds no boundedness, finiteness,
Noetherian, characteristic, or termwise-injectivity condition. The node's
commutative ring coefficients are precisely those used for the internal module
Hom construction. No statement correction is present or needed.

Independent object/hypothesis/conclusion list and matching verdicts:

1. A site C: `{C : Type u} [Category.{u} C] {J : GrothendieckTopology C}`.
   A Grothendieck topology is the site's covering structure. MATCH.
2. A sheaf O of commutative rings: `{R : Sheaf J CommRingCat.{u}}`.
   The displayed `sheafCompose ... (forget₂ CommRingCat RingCat)` forgets
   commutativity only for the module-category argument, preserving the underlying
   coefficient sheaf; the Hom functor still uses the same commutative R. MATCH.
3. Four cochain complexes of O-module sheaves: `{I' I L' L : CochainComplex
   (SheafOfModules ... ) ℤ}`. I checked `CochainComplex` in
   Mathlib.Algebra.Homology.HomologicalComplex: shape up, all integer degrees,
   square-zero differentials and degreewise commuting chain maps. MATCH.
4. A morphism s from I' to I: `(s : I' ⟶ I)`. MATCH.
5. Both I' and I K-injective: `[I'.IsKInjective] [I.IsKInjective]`.
   I opened Mathlib.Algebra.Homology.HomotopyCategory.KInjective:
   `nonempty_homotopy_zero` quantifies over every acyclic input and every map
   into the target, exactly the dependency node's definition. It does not require
   each term to be injective. MATCH.
6. s a quasi-isomorphism: `[QuasiIso s]`. I opened
   Mathlib.Algebra.Homology.QuasiIso: the class requires `QuasiIsoAt` in every
   degree; `quasiIsoAt_iff_isIso_homologyMap` identifies this with isomorphisms on
   cohomology in the ambient module-sheaf category. MATCH.
7. A morphism t from L' to L which is a quasi-isomorphism:
   `(t : L' ⟶ L) [QuasiIso t]`. No K-injectivity is imposed on L or L'. MATCH.
8. The map from Hom(L,I') to Hom(L',I), f mapped to s composed with f composed
   with t: `((homComplexFunctor (R := R)).map t.op).app I'` first maps
   Hom(L,I') to Hom(L',I'); `((homComplexFunctor (R := R)).obj (op L')).map s`
   then maps to Hom(L',I). The Lean composite `≫` has exactly this order.
   I checked `CategoryTheory.homComplex_exists` in the recorded dependency
   Sheaf.Algebra.Homology.HomComplex: its last conjunct specifies this composite
   under each projection as `SheafOfModules.homObjMap (t.f p) (s.f q)`.
   I also opened the upstream InternalHom module: `homObj` is the localized
   module-map sheaf and `homObjMap` has exactly these two variances. Its degree-n
   product and differential agree with the dependency node and Stacks 0A8X.
   Thus no merely group-valued or global-sections Hom is substituted. MATCH.
9. The displayed map is a quasi-isomorphism: the concluding `QuasiIso (...)`
   asserts isomorphisms on every cohomology sheaf of precisely this map. MATCH.

Edge cases: the site may be empty and the coefficient ring may be zero or have
any characteristic; none of the binders excludes these. Zero complexes and
identity maps are allowed. All integer degrees, including zero and negative
ones, occur, and no boundedness is imposed. The Hom product is indexed by ℤ,
not a finite or nonempty auxiliary index set. Schemes and n-natural-number
bounds are not part of this statement. The universe u is arbitrary, not fixed:
a site, its rings and the section sets of these four complexes can be placed in
one common ambient universe. This uses the standard small-site presentation;
no assumption of essential smallness of the module category is added.
The enlarged internal-Hom section universe `max u u u` is u. I checked the
module-sheaf Abelian source: its documentation specifically supplies the
instance in this common-universe presentation from FilteredColimits. The
ring-limit import supplies sheaf composition, and the remaining imports supply
the Hom construction, homology and K-injectivity; no extra instance is a
mathematical hypothesis on the ring or complexes.

Independent searches, using different wording from the first reader:

- LeanFinder via msearch: `internal sheaf Hom bifunctor preserves
  quasi-isomorphisms between homotopically injective complexes` returned eight
  hits, including `CochainComplex.IsKInjective.Qh_map_bijective`, localization
  inversion and injective-resolution results. None states this sheaf-valued map.
- Loogle via msearch: `SheafOfModules.homObjMap` returned zero hits with unknown
  identifier (the upstream primitive is not in that Mathlib search index).
- LeanSearch via msearch: `quasi-isomorphism induced on internal Hom sheaves by
  maps of K-injective complexes` was unavailable: Internal Server Error.
- Direct rg across Mathlib/Algebra/Homology, upstream WeilConjectures and the
  repository's lean/Sheaf for `homComplex.*[Qq]uasi`,
  `[Qq]uasi.*homComplex`, `internalHom.*[Qq]uasi`, and
  `[Qq]uasi.*internalHom` found no matching declaration. A separate search for
  `quasiIso_homComplex_map` and the blueprint id in the upstream name table and
  WeilConjectures found no existing declaration. The existing group-valued
  `CochainComplex.HomComplex` does not have the required sheaf-valued codomain.

H4/H5/H6/H8/H9: the item uses the recorded dependency bifunctor, introduces no
private notion and no definition, and has only one theorem with proof `sorry`.
The dependency obtains its data by Classical.choose from its named existence
statement rather than a hollow definition. The theorem and module docstrings
name the source and blueprint id; the theorem carries both node proof steps,
including the shift by -n, localized derived Hom and exact sheafification.
Every variable and universe is bound and all Lean lines meet the width rule.
The stored lean.statement matches the theorem signature verbatim. There are
no new definition nodes or replacement dependency modules to review (H12/H13).

Mismatches found: none. Changes: appended this independent reading and its
search evidence; no Lean or node change was justified. Single-file server
compilation and the delivery dry run are recorded below after they complete.

Validation: scompile.py compiled the unchanged module on the server in 2.0 s,
exit code 0, with no errors or warnings. deliver2.py --no-push printed OK:
preflight and server compilation both passed (dry-run commit 95dd7e2a7).

## Reviewer fix (R-rwd1419)

The delivered signature put the site and coefficients in one universe
(`C : Type u`, `[Category.{u} C]`, `CommRingCat.{u}`, `SheafOfModules.{u}`,
`homComplexFunctor.{u, u, u, u}`), i.e. only small sites. Restated in the
large-site universes of the landed siblings (G1 846abea62, M1 0e8e9db2e):
`{C : Type u} [Category.{v} C]`, `CommRingCat.{max u v}`,
`SheafOfModules.{max u v}`, with `homComplexFunctor` universes inferred.
The claimed instance-synthesis timeout does not occur: the fixed file compiles
in 2.3 s. The two universe paragraphs above are superseded. Hypotheses and
conclusion are otherwise unchanged and match the node.
