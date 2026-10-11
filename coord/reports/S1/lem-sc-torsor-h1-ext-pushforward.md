## Worker report

The module `Sheaf.CategoryTheory.Sites.TorsorExtensionPushforward` states
`CategoryTheory.Sheaf.Torsor.closedImmersion_extension_fibre_pushforward`.
Its only proof is `sorry`. No definitions, additional nodes, dependency replacements or
statement corrections are needed.

Hypotheses and clauses, in the order of the node:

- Schemes Z and X and the closed immersion i are `(Z X : Scheme.{u}) (i : Z ⟶ X)
  [IsClosedImmersion i]`. The structure-sheaf condition is included in the standard
  scheme-morphism predicate; its topological map is `i.base`.
- The abelian sheaf F on the small Zariski site, and the middle abelian sheaf E, are
  `(F E : Z.carrier.Sheaf AddCommGrpCat.{u})`. This is exactly the sheaf category for
  `Opens.grothendieckTopology Z.carrier`.
- The constant integer sheaf is Mathlib's `constantSheaf` applied to
  `AddCommGrpCat.of (ULift.{u} ℤ)`. The lift only puts integers in the coefficient universe.
  Inclusion and projection are `a` and `p`; `w : a ≫ p = 0` and
  `hS : (ShortComplex.mk a p w).ShortExact` give the whole short exact sequence.
- T is upstream `Sheaf.Torsor.lifts isTerminalTop hS` at the global constant section 1.
  The section is the image of `⟨1⟩` under `toSheafify` at `op ⊤`. Upstream's
  `liftsSubfunctor` takes exactly sections of E mapping to its restrictions;
  `lifts.vadd` translates them by `a(g)`. Thus this is the stated fibre sheaf with its action,
  rather than an arbitrary torsor representing the same cohomology class.
- Direct image is Mathlib's `TopCat.Sheaf.pushforward` for `i.base`, for both abelian
  groups and sets. It evaluates on U at `(Opens.map i.base).obj U = i⁻¹(U)`, which is
  the node's U intersect Z after identifying a closed immersion with its closed image.
- The first conjunct is short exactness of the mapped short complex. This states the
  direct-image sequence as a conclusion, without assuming its exactness.
- The existential `r` is the node's u, from the constant integer sheaf on X to the
  pushed-forward integer sheaf on Z. The next clause says for every open U and every
  integer n that it sends the sheafification image of n to that same integer on i⁻¹(U).
  This specifies restriction on all locally constant sections: locally such a section
  is an integer generator, and a morphism of sheaves is determined locally. In particular,
  r(1) is restricted 1. It also handles disconnected opens without replacing the constant
  sheaf by the generally non-sheaf constant presheaf.
- P is literally `pullback ((pushforward ...).map p) r`. The kernel inclusion k has first
  projection equal to the direct image of a and second projection zero (hk).
  These identities uniquely specify the kernel inclusion into the fibre product.
  The existential proof hP states that `ShortComplex.mk k (pullback.snd _ _) hk` is short
  exact, which is the complete pullback sequence with constant integer quotient.
- The source of e is the sheaf of `lifts isTerminalTop hP 1`, so it is precisely the fibre
  of P over 1. Its target is the set-sheaf direct image of T. The type of e is an actual
  sheaf isomorphism, incorporating naturality and inverse bijections on every open.
- The first clause after e specifies its canonical formula: the underlying section of
  its value is `pullback.fst` applied to the underlying lift t. Thus e sends (e,1) to e,
  fixing the requested canonical identification rather than merely asserting existence
  of an unspecified isomorphism.
- The final clause identifies e applied to translation by g with the upstream translation
  action on T over i⁻¹(U). It quantifies over every open, group section and torsor section.
  This is precisely equivariance for i_*F. In particular the target sheaf, with the
  direct-image action, is a torsor, since e transports the lifting-torsor structure to it.
  No separate definition of direct-image torsors is introduced.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`: scheme closed immersion with closed embedding
  underlying map and surjective structure-sheaf stalk maps.
- `Mathlib.CategoryTheory.Sites.Spaces`, `TopologicalSpace.Opens.grothendieckTopology`,
  and `Mathlib.Topology.Sheaves.Sheaf`, `TopCat.Sheaf`: the dependency
  `def-sc-zariski-site` is a Mathlib leaf and has no Lean record.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`, `CategoryTheory.Sheaf.H'`:
  inspected the recorded topological-cohomology declaration. This lemma concerns its
  abelian sheaves and extensions, with no cohomology group in its own conclusion;
  consequently it needs no application of H'.
- `WeilConjectures.CategoryTheory.Sites.Torsor`, `CategoryTheory.Sheaf.Torsor`,
  `CategoryTheory.Sheaf.Torsor.lifts`, and `liftsSubfunctor`: generic torsors, their
  translation action, and the fibre-of-a-short-exact-sequence construction. These apply
  directly to the Zariski site, as the generic clause of `def-sc-gm-torsor` intends.
- `Sheaf.Topology.ClosedImmersionPushforwardExact`,
  `TopCat.Sheaf.shortExact_map_pushforward_closedSubset`: imported the recorded dependency.
  Its exactness assertion is used in the natural-language proof after transporting the
  source space through the homeomorphism onto the closed image. No new exactness predicate
  or assumption is used in the statement.
- Additional Mathlib constructions used directly: `TopCat.Sheaf.pushforward`,
  `CategoryTheory.constantSheaf`, `CategoryTheory.toSheafify`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  `CategoryTheory.ShortComplex.ShortExact`, and `CategoryTheory.Limits.isTerminalTop`.

Edge cases checked: identity immersion gives the original extension and fibre; empty Z
has terminal sheaves of sections and the fibre of the pullback is a singleton; on an open
whose inverse image is empty the two fibres again are singletons. F = 0 gives the unique
lift torsor. Arbitrary disconnected opens are included, since integer sheaves are
sheafifications, and r is prescribed locally on generators. No global splitting or
surjectivity on global sections is assumed. Universe u is explicit and arbitrary, matching
the recorded topological abelian-sheaf dependency's universe convention.

Searches made with the launcher msearch tool:

- LeanSearch: `closed immersion direct image extension fibre over one torsor`:
  service unavailable (Internal Server Error), recorded as unavailable.
- LeanFinder: `direct image of extension pullback constant integer sheaf fibre torsor`:
  eight hits about module pullback/free objects, tilde modules and locally constant module
  presheaves; none states this torsor comparison.
- Loogle: `CategoryTheory.Sheaf.Torsor, pullback`: no hits, unknown identifier
  CategoryTheory.Sheaf.Torsor (the torsor is upstream, not Mathlib).
- Mathlib grep: `torsor.*pushforward|pushforward.*torsor|constantSheaf.*pullback`,
  restricted to CategoryTheory: one comment about commuting constant sheaves with
  pullback/pushforward, no matching torsor theorem.
- `rg` of the source repository and landed Sheaf modules for the item id and
  `torsor.*pushforward|pushforward.*torsor`: no matching declaration.
  Broader torsor/extension searches found the upstream lifts construction and the landed
  étale inverse-image and pushout statements. Those concern different functors and sites
  and do not already state this result.
- Exact-name searches of Mathlib, the source, landed Sheaf modules and
  `dag/lean_names_upstream.json` found no declaration with the new theorem's name.

Sources read: [Stacks 02FQ](https://stacks.math.columbia.edu/tag/02FQ), fibre torsors from
extensions, and [Stacks 02UV](https://stacks.math.columbia.edu/tag/02UV), closed-immersion
cohomology comparison via exact direct image. The local literature checkout contains only
bibliographic files, so these source places were opened on the Stacks website.

Local compilation: clean with `lcompile.py`, no warnings or errors. Server compilation
and the maintainer preflight are checked by the final `deliver2.py --no-push` invocation.
No mathematical node fault or STATEMENT-DISPUTED issue was found.

## Second reading by S1

Independent second reading: opened the node copy, the entire delivered module, all five
statement dependency nodes, and the source declarations listed below. No mathematical or
Lean mismatch was found. The module and node record are left unchanged.

Object/hypothesis/conclusion inventory and comparison (H3):

1. Z and X are arbitrary schemes; i is a closed immersion. Lean: `(Z X : Scheme.{u})
   (i : Z ⟶ X) [IsClosedImmersion i]`. Verdict: exact. Read Mathlib's class extending
   `SurjectiveOnStalks` with `isClosedEmbedding`; this is the dependency's scheme notion,
   not only an injective continuous map. No base field, finiteness, separation or
   Noetherian hypothesis is introduced.
2. F and E are abelian sheaves on the small Zariski site of Z. Lean:
   `(F E : Z.carrier.Sheaf AddCommGrpCat.{u})`. Verdict: exact. Read `TopCat.Sheaf`
   and `Opens.grothendieckTopology`: the objects are opens and covers cover every point.
3. The extension has integer constant sheaf as quotient, inclusion a and projection p.
   Lean: the displayed `constantSheaf ... .obj (AddCommGrpCat.of (ULift.{u} ℤ))`,
   `(a : F ⟶ E)`, `(p : E ⟶ ...)`, `(w : a ≫ p = 0)`, and `hS : ... .ShortExact`.
   Verdict: exact. Read `constantSheaf`: it sheafifies the constant presheaf; ULift changes
   only the carrier universe. w is the short-complex coherence proof, not an extra
   mathematical restriction beyond short exactness.
4. T is specifically the fibre of E over the global section 1, with F acting by
   translation. Lean: `lifts isTerminalTop hS (...toSheafify... ⟨1⟩)`.
   Verdict: exact. Read upstream `Torsor`, `liftsSubfunctor`, and `lifts` in
   `WeilConjectures.CategoryTheory.Sites.Torsor`. The subtype condition is
   `p(e) = restriction(1)` and vadd sends e to e+a(g). The sheaf and the action are
   fully defined upstream; no arbitrary representative of a cohomology class is used.
5. Direct image evaluates on U at U intersect Z. Lean: `TopCat.Sheaf.pushforward`
   for `i.base`, whose definition is sheaf pushforward along `Opens.map i.base`.
   Verdict: exact. Its inverse-image open is U intersect the closed image after the
   homeomorphism supplied by `IsClosedImmersion`; this also covers immersions not written
   literally as subtype inclusions.
6. The direct-image extension is short exact. Lean: the first conjunct
   `(ShortComplex.map ... (TopCat.Sheaf.pushforward ... i.base)).ShortExact`.
   Verdict: exact; this is a conclusion, not an additional assumption. Read the recorded
   dependency module `ClosedImmersionPushforwardExact`, including its short-exactness
   signature for a closed subset. Transport by the homeomorphism onto the closed image
   is the proof route, not a missing hypothesis or a private replacement definition.
7. u restricts locally constant integer sections. Lean: existential r with the equation
   for every open U and every n in ℤ on `toSheafify` images of n. Verdict: exact.
   Every section of the constant integer sheaf is locally such an image, so naturality
   and sheaf uniqueness force restriction on all locally constant sections, including
   disconnected opens. The existential specifies the canonical map uniquely.
8. P is the pullback of i_*E and the integer sheaf over i_*integer sheaf. Lean:
   `pullback ((TopCat.Sheaf.pushforward ...).map p) r`. Verdict: exact, using the existing
   categorical pullback rather than a privately defined fibre product.
9. The pullback extension has kernel i_*F, its natural inclusion, and quotient integer
   sheaf. Lean: existential k, `k ≫ pullback.fst _ _ = pushforward.map a`, existential
   `hk : k ≫ pullback.snd _ _ = 0`, and `hP : ... .ShortExact`.
   Verdict: exact. The two projection equations uniquely specify the natural inclusion;
   hP supplies precisely the displayed short exact sequence.
10. Its fibre over 1 is canonically i_*T. Lean: existential sheaf isomorphism e from
    `lifts isTerminalTop hP (... ⟨1⟩)` to the set-sheaf pushforward of the original
    `lifts ... hS ...`; the next equation says its underlying section is `pullback.fst`
    applied to t.val. Verdict: exact. A sheaf isomorphism incorporates all restriction
    compatibility, and the formula fixes the canonical identification (e,1) ↦ e.
11. The identification is an isomorphism of i_*F-torsors. Lean: the final universal
    equation for U, g and t intertwines `lifts.vadd` on the pullback fibre with
    `lifts.vadd` over `op ((Opens.map i.base).obj U)` on T. Verdict: exact.
    The action on the target is exactly the direct-image action. Local nonemptiness
    and simple transitivity transfer along e from the upstream lifting torsor;
    thus the formulation includes the assertion that i_*T is a torsor, even though
    it does not introduce a second bundled direct-image-torsor construction.

Sources: the local literature checkout has no Stacks .tex files. Independently read
`cohomology.tex` and `modules.tex` from the Stacks project's raw source, at labels
`lemma-torsors-h1`, `lemma-cohomology-and-closed-immersions`, and `lemma-i-star-exact`,
respectively, and checked [02FQ](https://stacks.math.columbia.edu/tag/02FQ),
[02UV](https://stacks.math.columbia.edu/tag/02UV), and
[01AX](https://stacks.math.columbia.edu/tag/01AX). Their hypotheses are arbitrary
spaces and abelian sheaves and, for direct image, a closed embedding; in particular
02UV assumes no Noetherian condition despite its section title. The fibre construction
and direct-image exactness support exactly the node's two proof steps. The cohomology
node's recorded `CategoryTheory.Sheaf.H'` signature was also opened: no H' appears in
this item's conclusion, so no alternative cohomology definition is needed.

Edge cases: Z empty, X empty (forcing Z empty), empty inverse-image opens, and identity
immersion are all admitted. A sheaf of sets has one section over the empty open; the
integer section there is zero, and both lifting fibres are singletons. F = 0 makes p
an isomorphism and both fibres trivial. The formula for r includes n = 0 and all negative
integers. There is no characteristic or index-set restriction. Disconnected opens are
handled by sheafification and locality, without imposing connectedness or global lifts.
The arbitrary explicit universe u and ULift use the same universe convention as the
landed topological abelian-sheaf dependency; there is no independent smaller universe
for quantified test objects. All variables are bound and `autoImplicit` is false.

Independent H4 searches, using different queries from the first reader:

- LeanSearch via msearch: `The fibre over one of a pulled back pushforward extension is
  the pushforward torsor`; service unavailable (Internal Server Error), recorded as
  unavailable, with no claimed negative verdict.
- LeanFinder via msearch: `closed embedding extension of integer sheaf inverse image
  of one`; eight hits (integer closed embeddings, locally constant integer casts,
  structure-sheaf constants, tilde restriction, and a sheaf gluing locus). None states
  this sheaf-extension torsor comparison.
- Loogle via msearch: `ShortComplex.ShortExact, pullback`; zero hits, the unqualified
  identifier is unknown to the service. This is not treated as evidence of absence.
- rg over the entire Mathlib, upstream WeilConjectures, and landed lean/Sheaf trees:
  `torsor.{0,60}(pushforward|direct.image)|pushforward.{0,60}torsor|lifts.{0,60}pullback`.
  Mathlib's algebraic and normed torsor pushforwards are actions along surjective maps,
  not direct image of sheaves along a closed immersion. Other hits concern blowups,
  module pullback, or valuative criteria; none matches. A second search for
  `lifts.*pushforward|pushforward.*lifts|fibre.*extension|fiber.*torsor|torsor.*direct.image`
  found the distinct landed etale inverse-image and pushout results and no duplicate.

H5-H9: no new definitions, hollow data, new nodes or dependency modules; one named theorem
with proof `sorry`. Header, namespace, line lengths, imports and source docstrings follow
the conventions. The docstring supplies both proof steps, including closed-image
transport, direct-image exactness, pullback exactness, and the sectionwise equivariant
identification. No statement correction or disputed statement is present.

Changes: appended this independent reading only. Local `lcompile.py` completed with
exit code 0 and no diagnostics. The delivery dry run and final server compile follow.
