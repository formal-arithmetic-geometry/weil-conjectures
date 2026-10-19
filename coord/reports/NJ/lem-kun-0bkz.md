## Worker report

The module `Sheaf.AlgebraicGeometry.UnboundedEtaleCohomologyAcyclicBasis` states
`AlgebraicGeometry.Etale.cohomology_iso_sections_of_acyclic_covering_class`, with `sorry`.
There are no new definitions, extra nodes, dependency repairs, or statement corrections.

Sources read: the imported blueprint node `lem-kun-0bkz.md` in
`sec-smooth-purity/sk-prop-sf-kunneth-ordinary`, and Stacks Project Tag 0BKZ,
`sites-cohomology.tex`, label `lemma-cohomology-over-U-trivial` (the local source lines
5467–5504 and https://stacks.math.columbia.edu/tag/0BKZ). The theorem is the blueprint's
abelian-sheaf specialization of the ringed-site result. Its docstring gives all seven
DAG proof steps, including bounded-below truncation spectral sequences, compatible edge
maps, derived-limit reconstruction, Milnor, and the eventual-constant Roos calculation.
It does not assert spectral-sequence convergence for arbitrary unbounded complexes.

Hypothesis and conclusion matching:

- A scheme X: `(X : Scheme.{u})`, with no separation, finiteness, characteristic, or
  quasi-compactness assumption.
- An arbitrary K in D(X_et):
  `(K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))`.
  There is no boundedness, torsion, or coefficient assumption.
- A class of objects B of X_et: `(B : Set X.Etale)`.
- Every object has a covering by B: `hcover` quantifies over `V : X.Etale`, a family
  `W`, and arrows `f : ∀ i, W i ⟶ V`; it requires both `∀ i, W i ∈ B` and
  `Sieve.ofArrows W f ∈ X.smallEtaleTopology V`. By
  `Scheme.ofArrows_mem_smallEtaleTopology_iff`, this is precisely joint surjectivity.
  The index universe `u + 1` is sufficient: any jointly surjective family admits a
  subfamily chosen at the points of `V.left`, whose type is in universe u. Thus this
  encoding imposes no finite or countable restriction on coverings.
- All positive p, all integral q, all U in B: `hacyclic` binds U, its membership,
  `p : ℕ`, `0 < p`, and `q : ℤ`, in that order.
- Vanishing of H^p(U_et,H^q(K)): `Subsingleton (Sheaf.H ... p)` expresses the zero
  abelian group. Its argument is the cohomology sheaf
  `(DerivedCategory.homologyFunctor ... q).obj K`, restricted to U_et by
  `(upperStar AddCommGrpCat.{u + 1} U.hom).obj`.
- For every U in B and every integer q, the conclusion is `Nonempty` of an isomorphism
  of abelian groups. The left object is `(cohomology ... U.left q).obj` of the exact
  derived pullback of K along U.hom. This is H^q(U_et,K|U). The right object evaluates
  H^q(K) at `op U`, which is H^0(U_et,H^q(K)|U). Equality of cohomology groups in the
  source is rendered as isomorphism, rather than equality of chosen models. The node
  does not specify a particular comparison morphism or a naturality clause.

Dependency declarations used, with their complete signatures/docstrings inspected:

- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and `Scheme.Etale`;
  the covering-family test is `Scheme.ofArrows_mem_smallEtaleTopology_iff`.
- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`;
  its documented abelian-sheaf encoding is precisely the K binder above.
- `def-weil-derived-cohomology-sheaves`: its Mathlib match
  `DerivedCategory.homologyFunctor`, in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`; its
  `homologyFunctorFactors` identifies this with cohomology of representing complexes.
- `def-kun-rgamma-unbounded`: the recorded existing declarations
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections` and `Etale.cohomology` in
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`. Here A is AddCommGrpCat,
  the integer-coefficient case of the dependency.
- `def-weil-pbc-sites-and-cohomology`:
  `Sheaf.CategoryTheory.SiteCoveringAxioms` retains Mathlib's `Sheaf.H`, used for
  the ordinary cohomology hypothesis. `Sheaf.H` is defined in
  `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` as Ext from the constant
  integer sheaf; this is ordinary sheaf cohomology.
- Restriction uses existing `AlgebraicGeometry.Etale.upperStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, and its
  `mapDerivedCategory`. The upstream docstring identifies étale pullback with
  restriction. The derived exact-functor interface is imported by LowerShriek.

All already recorded proof-dependency modules are imported (ordinary, non-public imports
where needed only for the proof). The two proof dependencies
`lem-kun-site-truncation-derived-limit` and `lem-kun-site-rgamma-derived-limit` have no
recorded Lean modules; they are named in the proof docstring and supply no notion needed
to type this statement. No imports for absent modules have been invented.

Edge cases checked: negative and zero q remain included; p=0 is excluded only in the
vanishing premise; K may be unbounded in both directions; K=0 is allowed; B may be
empty if the covering premise holds; covering index types may be empty; X and U may be
empty schemes; U need not be an open immersion, affine, or quasi-compact. No universe
equality between the étale site's hom universe u and coefficient universe u+1 was added.
The initial attempt using `Sheaf.H'` failed precisely because it ties those universes;
using `Sheaf.H` after restriction avoids that limitation without altering the statement.

Searches actually run using msearch.py for group NJ and item lem-kun-0bkz:

- LeanFinder: “For unbounded etale complexes with cohomology sheaves acyclic on a covering
  class of objects, hypercohomology equals sections of cohomology sheaves”. Eight hits,
  including `Sheaf.H`, `Sheaf.cohomologyPresheaf`, and Hom-complex cohomology APIs;
  none gives the unbounded acyclic-covering-class comparison.
- Loogle: `CategoryTheory.Sheaf.H, DerivedCategory.homologyFunctor`: zero hits.
- LeanSearch: “Hypercohomology equals sections of cohomology sheaves acyclic on a basis”:
  service unavailable, Internal Server Error; no mathematical verdict inferred.
- Mathlib grep: `hypercohomology|cohomology.*acyclic|acyclic.*cohomology` in
  CategoryTheory: zero hits.
- Direct rg in upstream WeilConjectures and project lean/Sheaf for
  `lem-kun-0bkz|0BKZ|cohomology.*[Aa]cyclic|acyclic.*cohomology` found ordinary,
  bounded-below, affine, and Čech acyclicity results, not this statement. Node-id search
  and `dag/lean_names_upstream.json` search found no attachment.
- Direct rg of Mathlib, upstream WeilConjectures and project lean/Sheaf for the proposed
  declaration name found no collision.

No STATEMENT-DISPUTED issue: the blueprint agrees with Tag 0BKZ, and the DAG's repaired
proof uses the source's truncation/derived-limit route.


## Second reading by NJ

Independent second reading of the sandbox module and node against Stacks Project
Tag 0BKZ, `sites-cohomology.tex`, label `lemma-cohomology-over-U-trivial`.
The shared clone does not contain the literature checkout, so I fetched the official
Stacks `.tex` into this item's scratchpad and read lines 5462–5499, the section context,
and the introductory definition of cohomology over an object. The tag's ringed-site
statement has precisely the two displayed hypotheses, with no standing boundedness,
Noetherian, separation, quasi-compactness, or characteristic assumption. The node is its
specialization to abelian sheaves on a scheme's small étale site. No statement correction
is needed; there are no new nodes or dependency modules to review.

The complete object/hypothesis/conclusion checklist, in node order:

1. **Scheme X.** `(X : Scheme.{u})` introduces an arbitrary scheme. Verdict: exact;
   there is no additional instance on X or on its structure morphism.
2. **K in the unbounded D(X_et).**
   `(K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))` is exactly
   the abelian-sheaf case documented in the recorded
   `Sheaf.AlgebraicGeometry.DerivedCategories` module. It is neither `Plus` nor `Bounded`,
   and carries no torsion condition. Verdict: exact.
3. **Class B of étale objects.** `(B : Set X.Etale)` uses the category of the recorded
   `Scheme.smallEtaleTopology`, not merely affine objects or open subsets. Verdict: exact.
4. **Every étale object has a covering by B.** `hcover` quantifies over every V,
   then chooses an index type, objects W, and arrows `f : ∀ i, W i ⟶ V`; it requires
   membership in B for every member and covering of the sieve generated by that same
   family. I opened `Scheme.ofArrows_mem_smallEtaleTopology_iff`: its right side is
   `⋃ i, Set.range (f i).left = .univ`. Thus this is precisely a jointly surjective
   étale family, not merely a sieve locally generated by unrelated B objects.
   The fixed index universe `u + 1` loses no covers: for each point of V.left choose
   an original family member and a point above it, and retain those original members,
   indexed by the points of V.left (lifted if necessary). This also preserves B even
   if B is not closed under isomorphism. Verdict: exact, with no finiteness restriction.
5. **All positive p, all integral q, every U in B.** `hacyclic` quantifies over
   `U : X.Etale`, `U ∈ B`, `p : ℕ`, `0 < p`, and `q : ℤ`. Moving universal binders
   between the displayed mathematical order and this order changes no dependency:
   none of these indices is existential. Verdict: exact.
6. **H^p(U_et,H^q(K)) vanishes.** `DerivedCategory.homologyFunctor ... q` is applied to
   this same K, then `upperStar ... U.hom` restricts the cohomology sheaf to U.left.
   `Subsingleton (Sheaf.H ... p)` expresses vanishing of its abelian cohomology group.
   I opened Mathlib's `Sheaf.H`: it is Ext from the constant integer sheaf, with an
   additive group structure; `H.equiv₀` identifies degree zero with sections at a
   terminal object. Hence this is ordinary cohomology on U_et. I also opened upstream
   `upperStar` and its étale Kan-extension description: for the étale U.hom it is
   precomposition with localization, hence the usual exact restriction. Verdict: exact;
   no ordinary-versus-derived or coefficient-category substitution occurs.
7. **For all U in B and all integral q, H^q(U_et,K) = H^0(U_et,H^q(K)).** The conclusion
   binds exactly U, membership, and q. Its left object is
   `(cohomology AddCommGrpCat.{u + 1} U.left q).obj` of the exact derived restriction of
   K. I opened upstream `rightDerivedGlobalSections` and `cohomology`: the latter is
   total right derived global sections followed by `DerivedCategory.homologyFunctor`.
   The right object is `((DerivedCategory.homologyFunctor ... q).obj K).obj.obj (op U)`,
   i.e. sections of the original cohomology sheaf over this same U. Via localization,
   these are exactly H^0 on U_et. `Nonempty (... ≅ ...)` renders the source's equality
   of cohomology groups as an isomorphism of abelian groups, independently of chosen
   models. The node adds no specified comparison arrow or naturality clause.
   Verdict: every conclusion clause is present, with no extra clause.

Dependency interfaces were read, not inferred from their names: Mathlib's
`Scheme.smallEtaleTopology`, its covering-family test, and
`DerivedCategory.homologyFunctor`/`homologyFunctorFactors`; the project's
`DerivedCategories` and `SiteCoveringAxioms` modules; and upstream
`Etale.upperStar`, `Etale.rightDerivedGlobalSections`, and `Etale.cohomology`.
These give the objects above with the same coefficient and site universes. All recorded
proof-dependency modules are imported. The two site derived-limit proof nodes currently
have no recorded module and are named in the proof docstring rather than replaced by
invented declarations. This is a stage-2 statement, not a proof depending on their
present availability.

Edge cases: q=0 and negative q are included by `ℤ`; p=0 is excluded only in the
positive-degree acyclicity premise. K may be zero or unbounded in either direction.
No nonemptiness condition is imposed on a covering index type, so the empty covering
of an empty target is permitted. B may be empty precisely when hcover can hold (in
particular on the empty scheme); the result then has no U in B. Empty schemes and
empty étale objects are allowed, with their zero groups of sections. U need not be
open, affine, quasi-compact, or nonempty. There is no characteristic restriction.
The site's morphism universe u and coefficient universe u+1 remain distinct under
the recorded size convention; every variable and universe is bound explicitly.

Independent H4 searches (2026-10-16):

- LeanFinder via msearch.py: "Unbounded derived sheaf sections are concentrated
  columnwise when every homology sheaf is acyclic on covering objects", followed by
  "Derived evaluation of an unbounded complex with locally acyclic homology equals
  evaluated homology". Eight hits in each run: t-structure and homology/localization
  interfaces, not the asserted covering-class comparison.
- Loogle via msearch.py: `CategoryTheory.Sheaf.H, Nonempty`: zero hits.
- Direct rg independently across Mathlib, upstream WeilConjectures, and the project's
  lean/Sheaf, using `0bkz`, `acyclic_covering`, `acyclic_basis`,
  `cohomology.over.U.trivial`, `hypercohomology`, and both orders of
  `acyclic`/`cohomology`. The hits concern affine/Čech acyclicity, bounded-below
  hypercohomology, or other coefficient categories, not this unbounded étale result.
  In particular the bounded-below `TruncationHypercohomology` is proof input,
  not a duplicate of this statement. The exact new declaration name and node id have
  no attachment in upstream, lean/Sheaf, or dag/lean_names_upstream.json.

H5/H6/H8/H9: the module introduces no definitions and has one named theorem, whose
only proof is `sorry`. Its module and theorem docstrings cite Tag 0BKZ and the exact
blueprint id. The theorem docstring carries all seven DAG proof steps, including
bounded-below spectral-sequence collapse and compatibility, derived-limit
reconstruction, preservation by derived sections, Milnor, and the explicit Roos
calculation. There is no claim of unbounded spectral-sequence convergence. No private
notation, local instance, extra hypothesis, unbound variable, or line over 100 characters
was found. The node's lean.statement is verbatim the signature in the module.

Mismatches found: none. Changes: appended this independent second-reading record;
the Lean file and node statement were retained unchanged. The required scompile.py
command compiled the delivered module cleanly, without errors or warnings.
