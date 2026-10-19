## Worker report

The module `Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit` states the two
coefficient cases of the node, in `CategoryTheory.abelianSheaf_complex_colimit_homotopyColimit`
and `CategoryTheory.moduleSheaf_complex_colimit_homotopyColimit`. Both proofs are solely
`sorry`; there are no definitions, auxiliary axioms, or private constructions.
The node's natural statement is unchanged.

Hypotheses and clauses, in order:

- A site is `{C : Type u} [SmallCategory C] (J : Precoverage C)` with `J.HasIsos`,
  `J.IsStableUnderComposition`, `J.IsStableUnderBaseChange`, and `J.HasPullbacks`,
  exactly the encoding fixed by def-weil-pbc-sites-and-cohomology. Its topology is
  `J.toGrothendieck`. Abelian coefficients are `Sheaf J.toGrothendieck AddCommGrpCat.{u}`.
- The module case takes `R : Sheaf J.toGrothendieck CommRingCat.{u}` and uses the recorded
  `ringedSiteModules.{u}` on the underlying ring sheaf obtained by `sheafCompose` with
  `forget₂ CommRingCat RingCat`. This is exactly `SheafOfModules`, without changing
  its category or abelian structure. Thus coefficients are a commutative ring sheaf,
  not a scheme-specific replacement category.
- `[HasDerivedCategory.{w} ...]` binds the chosen localization and its morphism universe;
  the functor is Mathlib's `DerivedCategory.Q`. All variables and universes are explicit.
- `E : ℕ ⥤ CochainComplex ... ℤ` is the sequence, with adjacent transition
  `E.map (homOfLE (Nat.le_succ n))`. Functoriality supplies all composite transitions.
  Integers cover all cohomological degrees; there is no boundedness restriction.
- `B : Cofan (fun n ↦ E.obj n)` and `hB : IsColimit B` present the degreewise coproduct
  with its actual injections `B.inj n`. `L : Cocone E` and `hL : IsColimit L` present
  the degreewise sequential colimit with its actual structure maps `L.ι.app n`.
  Mathlib's HomologicalComplexLimits constructs colimits degreewise and evaluations
  preserve these colimits. Quantifying over colimit presentations permits in particular
  the chosen colimits; it imposes no further exactness or coefficient hypothesis.
- `u : B.pt ⟶ B.pt` with `hu` is exactly the unique telescope map:
  `B.inj n ≫ u = B.inj n - E.map (...) ≫ B.inj (n+1)`.
  `q : B.pt ⟶ L.pt` with `hq` is exactly the canonical colimit map, characterized by
  `B.inj n ≫ q = L.ι.app n`. These hypotheses specify the named canonical maps;
  they do not assert monicity, short exactness, or quasi-isomorphisms in advance.
- The existential `p : mappingCone u ⟶ L.pt` is specified by
  `mappingCone.inr u ≫ p = q` and
  `(mappingCone.inl u).comp (Cochain.ofHom p) (add_zero _) = 0`.
  These are precisely its unshifted and shifted summand restrictions; together they
  uniquely specify the canonical chain map. The next conjunct is `QuasiIso p`.
- `Nonempty (IsColimit (Cofan.mk (Q.obj B.pt) (fun n ↦ Q.map (B.inj n))))`
  asserts the coproduct universal property for the actual mapped injections, not
  merely an abstract isomorphism between objects. `Nonempty` only makes this
  data-valued universal-property structure a proposition.
- `e : Q.obj (mappingCone u) ≅ Q.obj L.pt` with `e.hom = Q.map p` states that the
  isomorphism is exactly the localization of the canonical comparison map.
- `Q.mapTriangle.obj (mappingCone.triangle u) ∈ distTriang ...` states the cone
  triangle is distinguished. The following `Triangle.mk` has first arrow `Q.map u`,
  second arrow `Q.map q`, and last arrow `e.inv ≫ coneTriangle.mor₃`: it is precisely
  the cone triangle transported along `Q(p)`, with the actual colimit structure maps.
- The two uses of the recorded `IsSequentialHomotopyColimit` assert respectively
  that `Q.obj (mappingCone u)` and `Q.obj L.pt` are homotopy colimits of the actual
  localized sequence. The existential `h : HasCountableCoproducts ...` supplies the
  ambient structure required by that definition as a conclusion, not an extra
  hypothesis. Both predicates use the same structure and the same transition maps.
- The small etale site and every constant commutative ring, including Z/n, specialize
  the arbitrary site and `R`. No scheme, smoothness, finite generation, monicity,
  or boundedness hypothesis occurs. No separate etale construction is required.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: the site's recorded notions
  `CategoryTheory.Precoverage`, its four site classes, `toGrothendieck`, and `Sheaf`.
  The recorded primary `Sheaf.H'` and its docstring were also read; cohomology of
  sections is not needed to type this particular statement.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib's general-site `SheafOfModules` (recorded dependency).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and the localized cone triangle.
- `Mathlib.CategoryTheory.Limits.HasLimits` and its IsLimit interface:
  `Cocone`, `IsColimit`, `Cofan`; universal-property presentations of the recorded
  colimit notion instead of a second colimit construction.
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`:
  `CategoryTheory.IsSequentialHomotopyColimit`, used twice in each theorem.
- Proof interfaces: `CochainComplex.mappingCone.quasiIso_descShortComplex`
  in `Mathlib.Algebra.Homology.HomotopyCategory.ShortExact`,
  `CategoryTheory.Sheaf.hasExactColimitsOfShape` in
  `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`, and
  `CategoryTheory.moduleSheaves_colimits_forgetful` in
  `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
  The latter two modules are reached by the public dependency imports.
  `lem-kun-derived-countable-sums-exact` has no recorded Lean declaration, so no
  proof-only import can be supplied for it; its role is included in both docstrings.

Source checked: the blueprint's order-1719 unit file and Stacks derived.tex,
`lemma-compute-colimit` (093W) and `lemma-colim-hocolim` (0949). Their exact-sequential-
colimit argument and derived coproduct step match the seven-step proof in the node.

Edge cases checked: the zero sequence gives zero coproduct and colimit and an acyclic
cone; zero transition maps give the identity telescope and zero colimit; identity
transition maps give the constant colimit. Nonmonic transition maps are allowed.
Complexes with arbitrarily nonzero positive and negative degrees are allowed.
The finite telescope proof includes the initial zero sum. The site can be empty.
The zero coefficient ring is permitted, and no characteristic condition is introduced.
The sequence is indexed by ℕ, so an empty sequence is outside this node; empty
coproducts are covered by the ambient countable-coproduct structure.

Searches (2026-10-15):

- msearch.py LeanFinder, “Sequential colimit of unbounded complexes of sheaves is
  represented by the mapping telescope cone and is its derived homotopy colimit”:
  eight hits on HomologicalComplex colimits and sheaf colimits, no full assertion.
- msearch.py Loogle, `"homotopyColimit"`: zero hits.
- msearch.py grep, `telescope|homotopyColimit|colimit.*quasiIso|quasiIso.*colimit`:
  25 hits, unrelated telescope text; no full assertion.
- msearch.py LeanSearch, “The mapping telescope cone of a sequence of complexes of
  sheaves is quasi-isomorphic to the degreewise colimit”: unavailable, Internal Server
  Error; not treated as a negative mathematical search.
- rg on upstream WeilConjectures and lean/Sheaf for
  `homotopyColimit|mapping.telescope|hocolim|lem-kun-complex-colimit-hocolim`:
  no upstream whole statement; existing side `TelescopeColimit` treats only the module
  cone quasi-isomorphism and does not assert derived coproducts or the transported
  homotopy-colimit triangle. Its definitions specialize to module coefficients and
  cannot represent the abelian-sheaf case. They were read and not duplicated as defs.
- rg on dag/lean_names_upstream.json and upstream WeilConjectures for the two proposed
  theorem names and `IsSequentialHomotopyColimit`: no collisions.

Validation: scompile.py compiled the delivered module cleanly, on the server, nice 19,
two threads, 60 seconds per file; side-only dependency overlays compiled cleanly too.
No local compiler or library build was run. No statement dispute, new node, dependency
replacement, or natural-language statement correction is needed.


## Second reading by NM

I independently read the item JSON, its order-1719 blueprint source, Stacks
`derived.tex` definitions/lemmas 090Z, 0A5L, 093W and 0949, all five statement
dependency nodes, and the actual declarations they record. No mathematical
statement correction is necessary. There are no new nodes or dependency modules
in this delivery, and no `statement_change` or citer verdicts to audit.

Object/hypothesis/conclusion checklist, in node order (applies to both theorems
unless a coefficient case is specified):

1. A site: `{C : Type u} [SmallCategory C] (J : Precoverage C)` with the four
   recorded site classes, and topology `J.toGrothendieck`. Verdict: exact recorded
   encoding of def-weil-pbc-sites-and-cohomology. I opened the Precoverage
   structure, its four class signatures and the sheaf interface in Mathlib.
2. Abelian sheaves or modules over a commutative ring sheaf: the first theorem uses
   `Sheaf J.toGrothendieck AddCommGrpCat.{u}`; the second binds
   `R : Sheaf J.toGrothendieck CommRingCat.{u}` and uses `ringedSiteModules.{u}`
   on its underlying ring sheaf. Verdict: both cases present, with no field,
   finiteness, scheme or constant-coefficient restriction. I opened
   RingedSiteModules: its abbreviation is precisely `SheafOfModules`, the recorded
   dependency, including sectionwise linear morphisms and its inherited category.
3. Unbounded cochain complexes and arbitrary transitions: `E : ℕ ⥤ CochainComplex
   ... ℤ`, with `E.map (homOfLE (Nat.le_succ n))` as each adjacent arrow.
   Verdict: exact; composites are supplied by functoriality, no monicity assumed.
4. Localization `Q`: `DerivedCategory.Q`, with `[HasDerivedCategory.{w} ...]`.
   Verdict: the recorded localization at quasi-isomorphisms, not a different
   derived category. I read Basic.lean's HasDerivedCategory, standard, DerivedCategory
   and Q declarations: `w` specifies the chosen morphism universe and can always
   be chosen by the standard construction.
5. Degreewise sum A and colimit L: `(B : Cofan ...) (hB : IsColimit B)` and
   `(L : Cocone E) (hL : IsColimit L)`. Verdict: arbitrary presentations of exactly
   these universal objects. HomologicalComplexLimits.lean constructs the cocone
   degreewise and gives the evaluation-preserves-colimits instances, so these
   are genuinely degreewise sums/colimits, not merely derived colimits.
6. Telescope endomorphism and canonical colimit map: `u`, `hu` say
   `B.inj n ≫ u = B.inj n - E.map (...) ≫ B.inj (n+1)`; `q`, `hq` say
   `B.inj n ≫ q = L.ι.app n`. Verdict: precisely the node's two maps, in Lean's
   composition order. Their universal-property characterizations add no exactness
   or quasi-isomorphism assumption.
7. Canonical chain map p: the existential morphism from `mappingCone u` has
   `mappingCone.inr u ≫ p = q` and zero composite with the degree-minus-one cochain
   `mappingCone.inl u`. Verdict: both summand restrictions are specified, and
   `QuasiIso p` is the required conclusion. I read MappingCone.lean's `inl`, `inr`,
   differential formulas and extensionality; the shifted summand is not mistakenly
   treated as a chain-map inclusion. I also read `descShortComplex` and its two
   restriction formulas in the recorded ShortExact.lean dependency.
8. Actual derived coproduct: `Nonempty (IsColimit (Cofan.mk (Q.obj B.pt)
   (fun n ↦ Q.map (B.inj n))))`. Verdict: universal property for the actual
   localized injections, not only an abstract isomorphism of objects.
9. Cone triangle exhibits the homotopy colimit: membership of
   `Q.mapTriangle.obj (mappingCone.triangle u)` in `distTriang`, together with
   item 8 and `hu`, gives exactly the node's triangle and its 1-minus-shift arrow.
   Verdict: exact. The explicit `IsSequentialHomotopyColimit` conjunct uses the
   dependency's predicate; I opened its definition and checked its existential
   triangle arrows and `Sigma.desc` shift map.
10. Identification via Q(p), and transported triangle for L: `e.hom = Q.map p`
    specifies the isomorphism; `Triangle.mk (Q.map u) (Q.map q)
    (e.inv ≫ coneTriangle.mor₃)` is distinguished. Verdict: the last arrow and
    direction of transport are correct, and the second arrow retains the actual
    colimit map. The second homotopy-colimit predicate is for `Q.obj L.pt`.
11. Ambient countable coproducts: the existential `h : HasCountableCoproducts ...`
    supplies the structure required by the recorded predicate, and is shared by
    the two conjuncts. Verdict: a consequence of exact sequential colimits and
    Stacks 093W/0A5L, not an added hypothesis. No functorial or canonical choice of
    an arbitrary triangulated cone is asserted.
12. Small etale sites and constant coefficients, including Z/n: specializations
    of the arbitrary site and commutative ring sheaf. Verdict: covered without
    any characteristic or boundedness hypotheses.

Edge cases: the index is specifically ℕ, not an arbitrary possibly empty index
category, so excluding an empty sequential index changes nothing. Zero complexes,
zero transitions, identity transitions, empty sites (hence the empty scheme's
site), the zero ring, all characteristics, and Z/0 are allowed. The finite-sum
argument in the docstrings includes its zero initial sum. Integer degrees have
no lower/upper bound. `u` and `w` are explicitly declared universes (the term
binder named `u` is the telescope morphism); the site/coefficient universe `u`
can be enlarged and the derived morphism universe `w` is independently chosen.
No free variable, positive-n restriction or hidden finite-type instance occurs.

Independent searches, with different wording from the worker:

- LeanFinder via msearch: “Exact sequential colimits in a category of sheaves
  identify the cone of one minus successor with the ordinary colimit in the
  unbounded derived category”: eight results, including
  `HomologicalComplex.hasExactColimitsOfShape`, `isColimitOfEval` and
  `CategoryTheory.Sheaf.hasExactColimitsOfShape`; these are component results,
  not the full telescope assertion.
- Loogle via msearch, `"mappingCone", "colimit"`: zero hits. An earlier query
  without the comma was a syntax error and is not counted as negative evidence.
- Grep via msearch, `sequential.*colimit|colimit.*mappingCone|mappingCone.*colimit`:
  two hits on countable-colimit infrastructure, neither the statement.
- Direct rg in Mathlib homology, upstream WeilConjectures and project lean/Sheaf,
  using telescope, homotopy-colimit and colimit/quasiIso variants. I opened
  TelescopeColimit.lean completely: `quasiIso_telescopeColimit` gives the module
  cone comparison, but neither the derived coproduct nor either homotopy-colimit
  triangle; it is not this node's statement. No new definitions are introduced
  here, so there is no competing telescope construction. The existing
  IsSequentialHomotopyColimit dependency is reused. The two proposed theorem names
  do not occur in upstream sources or dag/lean_names_upstream.json.

Mismatches and repair: the worker marked the three proof-support imports
(HomotopyCategory.ShortExact, Grp.FilteredColimits, ModuleCat.Sheaf.Colimits)
`public import`. I changed these to ordinary `import`, as brief-stage2 §3 requires
for proof dependencies. All signatures, conclusions, docstrings and node fields
were retained. The module has two named theorems, both proved only by `sorry`,
no new definitions or axioms, and source/blueprint docstrings carrying all seven
proof steps. The primary `lean.statement` was checked verbatim against the file;
all lines are at most 100 characters.

Second-reader validation: scompile.py compiled both side-only dependency overlays
and the delivered module cleanly on the server (module 5.8 seconds), nice 19,
two threads, 60 seconds per file. No local compiler or library build was run.
