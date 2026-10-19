## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover` states
`AlgebraicGeometry.Scheme.ProEt.exists_affine_weaklyContractible_covering_family`.
Its only proof is `sorry`; no definition is introduced or duplicated.
The node statement and all dependencies remain unchanged.

Clause-by-clause correspondence:

- A scheme X: `(X : Scheme.{u})`, with arbitrary explicit universe u.
- Its full small pro-etale site: `X.ProEt` and `ProEt.topology X`.
- Every site object U: `(U : X.ProEt)` without affine, qc, or qs assumptions.
- An indexed family of objects and arrows to U:
  `∃ (I : Type (u + 1)) (V : I → X.ProEt) (f : ∀ i : I, V i ⟶ U)`.
  The index lives in the larger universe of the site, with no finiteness or
  nonemptiness hypothesis. Each V i is already a weakly etale scheme over X.
- A covering family: `Presieve.ofArrows V f ∈ precoverage X U`.
  Mathlib's precoverage is the pullback of `Scheme.proetalePrecoverage` along
  the forgetful functor to schemes: exactly fpqc covering families of weakly
  etale arrows, rather than merely a generated-topology covering sieve.
- Each covering object is affine: `∀ i : I, IsAffine (V i).left`.
- Weak contractibility in the FULL site: quantify over
  `(F G : Sheaf (topology X) (Type (u + 1))) (e : F ⟶ G)` and assert
  `Epi e → Function.Surjective (e.hom.app (op (V i)))` for every i.
  This uses categorical epimorphisms of set-valued sheaves; no slice-site
  or affine-subsite replacement occurs.
- Size convention: Scheme.{u}, site objects in Type (u+1), and sheaf values
  in Type (u+1) explicitly encode the two size levels. This agrees with the
  landed sibling ProEtaleAffineAcyclicHypercover. The universe convention is
  metatheoretic and requires no additional Lean object or assumption.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, via the public site dependency.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` records the site notion
  in its declaration docstring and uses the Mathlib `Scheme.ProEt` and
  `Scheme.ProEt.topology`. These exact underlying site definitions, not a
  replacement definition, are used in this statement.
- `def-weil-size-convention` is a convention-only record; explicit universes
  render it as prescribed by that record.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt.precoverage`,
  `Scheme.proetalePrecoverage`, `Scheme.ProEt.topology`.
- Already stated proof dependencies are imported without `public`:
  `Sheaf.RingTheory.IndEtaleStability` (RingHom.indEtale_principalZariski_stability),
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` (Etale and open-immersion instance),
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` (affine qcqs instance).
  Scheme, Spec, open immersions, WeaklyEtale and covering definitions are also
  available through these imports. The ring-extension and affine-splitting
  weak-contractibility nodes have no Lean records yet, so cannot be imported.

Sources checked: local Stacks proetale.tex, lemma-get-many-weakly-contractible
(Tag 098I), and lemma-proetale-enough-w-contractible (Tag 0990). The former
constructs arbitrary affine covering families with the size bound; the latter
explicitly includes the small site. The full six-step DAG proof, including
finite affine-open witnesses for each affine test open, is in the theorem docstring.

Edge cases checked: empty U is allowed with an empty index type; the covering
condition accepts the empty cover of the empty object, and all component
conditions are vacuous. X may itself be empty. No characteristic restrictions,
nonzero-ring assumptions, qcqs assumptions on U, or finite-family restriction
are imposed. Infinite covers of non-quasi-compact U are allowed. Sheaf values
are in the site's size universe, avoiding a smaller, vacuous sheaf test.

Searches for reuse (2026-10-15):

- msearch leanfinder, "Every object of the small pro etale site admits an affine
  weakly contractible covering family": eight hits, on etale topology, affine
  covers and affine transition limits; none is this statement.
- msearch loogle, "Scheme.ProEt, Sheaf, Epi": no hits; service reports unknown
  identifier Scheme.ProEt. This supplied no positive reuse evidence.
- msearch grep, "weaklyContractible|wContractible|enough.*contractible", in
  Mathlib/AlgebraicGeometry: zero hits.
- msearch leansearch, "The small pro etale site has enough affine weakly
  contractible objects": unavailable, Internal Server Error.
- rg of the same contractibility terms in upstream WeilConjectures and the
  side framework: only the ring-theoretic WContractible documentation, not
  a theorem for the small scheme site. Searching the item's id upstream
  returns nothing.
- rg in lean/Sheaf: ProEtaleAffineAcyclicHypercover is a different result,
  requiring qcqs and providing a simplicial hypercover. Its exact full-site
  sheaf-epimorphism formulation was read and reused as the encoding convention.

No statement dispute, correction, new node, or dependency module is needed.

## Second reading by NU

I independently read the node, the sandbox theorem, the three statement-dependency
nodes and their recorded declarations, and the source in proetale.tex
(Tags 098K, 0989, 098H, 098I, 0990) and sites.tex (Tags 090K, 090L).
The source assumes an arbitrary scheme, with the stated size convention;
no omitted global finiteness, separation, or characteristic hypothesis occurs.

The node's objects, hypotheses, and conclusion, matched individually:

1. An arbitrary scheme X [def-pc-scheme]: `(X : Scheme.{u})`.
   Mathlib's `Scheme` is a locally ringed space with locally affine charts;
   its `Scheme.Hom` is a locally ringed space morphism. Exact, pass.
2. The full small pro-etale site [def-weil-pbc-proetale-site]: `X.ProEt`,
   `precoverage X`, and `topology X`. I opened ProEtaleDerivedCategory.lean
   and Mathlib Sites/Proetale.lean. The dependency explicitly identifies
   these as its site. `Scheme.ProEt` is `MorphismProperty.Over @WeaklyEtale
   ⊤ X`: weakly etale maps to X, with all X-morphisms. No restriction to
   affine objects or to a slice over U is introduced. Exact, pass.
3. The size convention [def-weil-size-convention]: the explicit `universe u`,
   `Scheme.{u}`, site objects in Type (u+1), and sheaf sets in Type (u+1).
   The dependency has a convention-only record, not a definition to import.
   This is the project's two-level universe encoding, also used by the landed
   affine-acyclic-hypercover theorem. No independent lower test universe
   makes the quantification vacuous. Pass.
4. Every object U of that site: `(U : X.ProEt)`. No further assumptions
   or instances on U occur. In particular U need not be affine or qcqs. Pass.
5. A covering family of site objects with target U: the existential binders
   `(I : Type (u + 1)) (V : I → X.ProEt) (f : ∀ i : I, V i ⟶ U)` followed by
   `Presieve.ofArrows V f ∈ precoverage X U`. I traced precoverage to the
   comap of `Scheme.proetalePrecoverage`, defined by `propQCPrecoverage
   @WeaklyEtale`, and traced that to `qcPrecoverage ⊓ Scheme.precoverage P`.
   These are jointly surjective weakly etale families with the finite
   quasi-compact-open image witnesses, equivalent to the source's affine-open
   witnesses by finite affine refinement. Thus this asserts an actual
   pro-etale covering family, not just membership in a generated covering
   sieve. No finite or nonempty index requirement is added. Exact, pass.
6. Every member affine: `(∀ i : I, IsAffine (V i).left)`.
   The underlying scheme, not the arrow, is affine. I read `IsAffine` and
   `Scheme.isoSpec`: it means isomorphic to a spectrum. Exact, pass.
7. Every member weakly contractible on the full site: for every i,
   `(F G : Sheaf (topology X) (Type (u + 1))) (e : F ⟶ G)`,
   `Epi e → Function.Surjective (e.hom.app (op (V i)))`.
   This is precisely the node's evaluation of each sheaf epimorphism.
   Sites 090K(2) and 090L identify this with weak contractibility; Mathlib's
   Sites/EpiMono.lean also identifies categorical epis with local
   surjectivity under its sheaf-category hypotheses. The family is chosen
   before quantifying over F, G, e; no dependence of the cover on the sheaf
   morphism is allowed. Exact, pass.

Edge cases: I may be empty (use ULift of an empty type); its presieve is
empty and is covering when U is empty, as follows directly from
`bot_mem_propQCPrecoverage`. The affine and evaluation clauses are then
vacuous. Empty X and empty U are admitted. The zero ring is not excluded
by any instance. There is no numerical n or characteristic parameter;
no characteristic or nontriviality assumption occurs. Non-quasi-compact U
and infinite covers are included. Increasing u gives the same formulation
at every scheme size. No variable or universe is left unbound.

Independent searches, using different wording from the worker:

- msearch leanfinder: "affine covering of weakly etale schemes with projective
  evaluation on sheaves": eight hits on affine covers, etale objects, and
  affine transition limits; no matching covering theorem.
- msearch loogle: `"contractible"`: twelve hits on compiler eta contraction
  and triangulated contractible triangles; no site-theoretic match.
- msearch leansearch: "Each object of the pro etale site admits an affine
  cover by weakly contractible objects": service unavailable (Internal
  Server Error); no claim of a negative search result.
- msearch grep: `projective|contractible`: unrelated hits. I supplemented
  this broad search with direct rg for `weakly.?contractible`,
  `wContractible`, `WContractible`, and `enough.*projective` in Mathlib's
  sites/geometry, slopmaster2 WeilConjectures, the group clone's exact
  pro-etale framework, lean/Sheaf, and dag/lean_names_upstream.json.
  The relevant existing results are ring-theoretic WContractible results,
  a different qcqs affine hypercover theorem, and finite-coproduct evaluation.
  None states this full-site affine covering-family theorem. I opened the
  hypercover signature: its qcqs assumptions and simplicial conclusion
  differ, so it cannot replace the present declaration.

No new definition nodes, dependency modules, or statement_change are present
or needed. The proof-only IndEtaleStability declaration was read; the etale
and affine-qcqs Mathlib dependencies are imported as required. The two
unstated ring-extension/splitting proof nodes have no module to import.
The module and theorem docstrings identify the source and blueprint node,
and their six-step proof plan preserves the affine cover, bounded ring
extension, universe bound, weak-etale composition, finite affine-open
covering witnesses, and full-site splitting argument of the node.
There is one theorem with proof `sorry`, no definitions or other proofs,
no local notation or instances, and no line exceeds 100 characters.
The node's lean.statement was checked verbatim against the file signature.

Mismatches found: none. Changes: appended this independent second reading;
the correct Lean module and node record are unchanged. Server compilation
via scompile.py passed cleanly (module: 1.5 s; nice 19, two threads,
60-second per-file limit); no warnings or errors were emitted.
