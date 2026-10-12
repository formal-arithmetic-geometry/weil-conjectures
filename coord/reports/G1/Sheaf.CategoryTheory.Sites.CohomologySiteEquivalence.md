## What changed

Repaired both C3/D1 documentation findings of reviewer X-4ca35 (head 4ca359986).
`CohomologySiteEquivalenceCovering.lean` now gives the complete covering-reflection
argument using the two hypotheses, the unit, presieve-family presentation and
`site_covering_isomorphic_family`. Its node describes only that argument and removes
the unrelated site-equivalence-morphism dependency.

`CohomologySiteEquivalenceFixedDegree.lean` now gives the additive sheaf equivalence,
resolution transport, section-complex isomorphism, Ext/derived-section identification,
cohomology and both naturality arguments, with exact source citations. Its node cites
all five substantive dependencies of that argument.

Checking the hypotheses for finding F exposed a further error in the returned new
statement: inverse continuity alone does not imply a sheaf-category equivalence.
Added `hcover_iff` to this NEW split theorem (absent in the repository), synchronized its
node statement and verbatim Lean signature, and supplied the already proved `hiff` at
its sole caller in the target module. No existing library declaration's signature,
visibility, or definition changed; the target signature is unchanged. Updated the
existing target node's proof/dependencies to record the actual three-step reduction.
No modules held by other groups are adapted. Added plain proof imports of SiteEquivalenceMorphismOfSites and CohomologyRightDerivedSections to the open fixed-degree module, matching its recorded proof dependencies.

## Proved and sorry left

Closed original hole: `CategoryTheory.cohomology_site_equivalence`
(node `lem-weil-pbc-etale-cohomology-invariance-under-site-equivalence`).
The target contains no sorry; its Lean proof combines the covering iff, the existing
morphism-of-sites theorem, and the fixed-degree theorem with `hiff`.

The second reader also closed `CategoryTheory.covering_iff_of_equivalence`
(node `cohomology-site-equivalence-covering-iff`) by the existing proved
`site_covering_isomorphic_family`, presieve-family presentation and unit naturality.

Added hole, still left as a named public theorem with whole proof `by sorry`:

- `CategoryTheory.cohomology_presheaf_iso_fixed_degree`
  (node `cohomology-site-equivalence-fixed-degree`).

The original hole is reduced to this strictly smaller cohomology comparison with
covering compatibility and continuity supplied. One original hole closes and one
new hole remains: net zero in the dependency closure, not a sorry-free target proof.
The newly introduced covering theorem is completely proved with standard axioms.

## No longer needed

The covering node no longer needs
`lem-weil-pbc-site-equivalence-is-morphism-of-sites` as a proof dependency. It also
has no injective-resolution or fixed-degree cohomology dependency. Its only substantive
proof dependency is `lem-weil-pbc-site-covering-isomorphic-family`.

The fixed-degree node no longer directly needs
`lem-weil-pbc-site-covering-isomorphic-family`: it receives the covering iff explicitly
and uses the morphism-of-sites theorem for the sheaf equivalence. That covering lemma
remains needed by the covering node and by the morphism-of-sites construction; no
whole module is claimed pruned from the targets' closure. Removed the target module's unused direct proof import
`Sheaf.Paper.SiteCoveringIsomorphicFamily`; the covering module retains it.
Relative to the original target node, `def-weil-pbc-sites-and-cohomology`,
`lem-weil-pbc-equivalence-injective-resolutions` and
`lem-weil-pbc-site-covering-isomorphic-family` are no longer direct proof dependencies.
The first remains in statements/conventions, the second in the fixed-degree plan,
and the third in the proved covering step. No whole module is pruned.

## Where the brief, the DAG or earlier work was wrong

The returned docstrings were summaries rather than complete proofs. Both new nodes
shared a generic mixed covering/cohomology proof and irrelevant dependencies. Their
replacements now distinguish the two arguments and cite the actual required nodes.

The old fixed-degree signature omitted covering compatibility. For an identity
category equivalence with different topologies, inverse continuity can merely embed
sheaves for the finer topology into presheaves for the trivial topology. Such an
embedding need not be an exact equivalence. Concretely, on the category of opens of a
circle, the usual topology and the trivial (isomorphism-only) topology satisfy this
one-directional continuity. Degree-one cohomology of the constant integer sheaf on
the circle is nonzero, whereas cohomology over an object for the trivial topology
vanishes in positive degree because presheaf evaluation is exact. The old statement
would identify these groups. The corrected `hcover_iff` rules out this case and is
already available in the unchanged target. The target was not weakened.

The earlier report also asserted that the target node had been updated, although no
copy was in the sandbox. The target node is now included with the exact dependencies
of the written Lean proof.

## New nodes

`cohomology-site-equivalence-covering-iff`: all small categories C,D and site
precoverages J,K with the four axioms; an equivalence e; both covering-preservation
hypotheses; conclusion the covering iff for every object and presieve. Source:
[00VH](https://stacks.math.columbia.edu/tag/00VH), site axioms, and
[00VU](https://stacks.math.columbia.edu/tag/00VU), tautologically equivalent families,
specialized by the proved isomorphic-family lemma. Its source no longer cites
cohomology lemmas. Existing search records are retained; this repair makes no new
claim of searches or a new formal proof.

`cohomology-site-equivalence-fixed-degree`: the same site context plus abelian-group
sheafification and HasExt on both sides, a covering-compatible equivalence, the inverse
continuity witness, and fixed q. Source:
[03A0](https://stacks.math.columbia.edu/tag/03A0), equivalence of topoi;
[015Z](https://stacks.math.columbia.edu/tag/015Z), preservation of injectives;
[01FT](https://stacks.math.columbia.edu/tag/01FT), equation (the project server);
[03F3](https://stacks.math.columbia.edu/tag/03F3), resolution calculation over objects;
[03YU](https://stacks.math.columbia.edu/tag/03YU), transport and functoriality.
The Ext encoding is handled by the existing derived-sections comparison node rather
than silently treating Mathlib's H' as a definition by resolutions. Existing search
records retained. No change record is required: only the delivery's new intermediate
signature changed, with its sole caller adapted and no existing interface changed.

## Earlier second reading (a previous round; superseded)

Repair recheck of finding F, with both Lean files, both new nodes, the target and its
node open. This expands the prior second-reading record; it does not assert that this
repair worker is an additional independent reader. The dispatcher still arranges the
independent second reader before delivery.

Covering statement, hypothesis-by-hypothesis:

| Lean binder | Node meaning and check |
| --- | --- |
| `universe u; {C D : Type u}` | Both categories inhabit the same arbitrary universe; neither is fixed to a particular site. |
| `[SmallCategory C] [SmallCategory D]` | Both hom universes agree with the object universe; the node says small categories. |
| `(J : Precoverage C) (K : Precoverage D)` | Coverings are presieves at each target, not arbitrary Grothendieck sieves. |
| `[J.HasIsos]` and `[K.HasIsos]` | Singleton isomorphisms are coverings on both sites. |
| `[J.IsStableUnderComposition]` and K counterpart | The composition site axiom is assumed on each side. |
| `[J.IsStableUnderBaseChange]` and K counterpart | Coverings are stable under base change on each side. |
| `[J.HasPullbacks]` and `[K.HasPullbacks]` | Pullbacks along covering members exist; global pullbacks are not assumed. |
| `(e : C ≌ D)` | The data include quasi-inverse functors and unit/counit; no strict inverse equality is required. |
| `hcover` | For EVERY W and presieve R, membership in J implies membership of the e.functor image in K at e(W). |
| `hcover_inv` | For EVERY V and presieve R, membership in K implies membership of the e.inverse image in J at e.inverse(V). |

Covering conclusion: `∀ (W : C) (R : Presieve W), R ∈ J W ↔ R.map e.functor ∈
K (e.functor.obj W)` is exactly the node conclusion, including both implications,
all objects and all presieves. No refinement, generated-topology replacement or
nonempty-family hypothesis occurs. The unit direction is C to e.inverse(e(C)); the
commuting equation is sigma_i followed by g_i = f_i followed by phi, exactly the
signature of `site_covering_isomorphic_family`. Presieve.map_ofArrows and
exists_eq_ofArrows supply the connection from arbitrary presieves to that lemma.

Covering source checks: inspected the current Stacks pages 00VH and 00VU. 00VU is a
DEFINITION of equivalence of families, not itself a theorem about coverings. The
covering assertion is supplied by the proved library lemma and its five-step docstring
(base change, isomorphic pullback, singleton isomorphism covers, composition,
reindexing). The new node's proof[0] and proof_deps cite only that lemma. No injective
resolution step is attributed to these sources.

Covering edge cases: e = identity and J = K makes each image R itself, with the unit
identity; the conclusion is the identity iff. For a non-strict equivalence, unit
components are isomorphisms rather than object equalities, and the specified square
checks their directions. Empty families remain empty under both functors; if such a
family covers, the isomorphic-family lemma transports it with no indices to check.
Repeated arrows or infinite indexing cause no extra hypothesis because membership is
membership of the presieve of arrows, and `exists_eq_ofArrows` does not assume finite
indexing. Singleton isomorphism covers agree with HasIsos. These are mathematical
edge-case checks, not extra formal tests or a proof of the remaining sorry.

Fixed-degree statement, hypothesis-by-hypothesis:

| Lean binder | Node meaning and check |
| --- | --- |
| `{C D : Type u}` and `[SmallCategory C] [SmallCategory D]` | Same arbitrary universe u and small categories as stated in the node. |
| `(J : Precoverage C) (K : Precoverage D)` | Separate precoverages on the corresponding categories. |
| `[J.HasIsos]`, `[J.IsStableUnderComposition]`, `[J.IsStableUnderBaseChange]`, `[J.HasPullbacks]` | Each of the four J axioms is explicitly present. |
| `[K.HasIsos]`, `[K.IsStableUnderComposition]`, `[K.IsStableUnderBaseChange]`, `[K.HasPullbacks]` | Each of the four K axioms is explicitly present. |
| `[HasSheafify J.toGrothendieck AddCommGrpCat.{u}]` | Abelian sheafification on J, in the common universe u. |
| `[HasSheafify K.toGrothendieck AddCommGrpCat.{u}]` | Abelian sheafification on K, separately assumed. |
| `[HasExt.{u} (Sheaf J.toGrothendieck AddCommGrpCat.{u})]` | The source Ext groups exist in universe u. |
| `[HasExt.{u} (Sheaf K.toGrothendieck AddCommGrpCat.{u})]` | The target Ext groups exist in universe u. |
| `(e : C ≌ D)` | Categorical equivalence, not yet a sheaf equivalence without the next hypothesis. |
| `hcover_iff` | For EVERY W and R, R in J iff its e.functor image is in K; corrected explicitly in both Lean and node. |
| `hi : e.inverse.IsContinuous K.toGrothendieck J.toGrothendieck` | Inverse functor continuity with precisely this source/target order; used to define the pushforward from J-sheaves to K-sheaves. |
| `(q : ℕ)` | Fixed arbitrary nonnegative degree; zero included, no positivity assumption. |

Fixed-degree conclusion, factor-by-factor:

| Lean expression | Check |
| --- | --- |
| `Nonempty (... ≅ ...)` | Existence of a natural isomorphism, no arbitrary data-bearing definition chosen from an unproved existence theorem. |
| `Sheaf.cohomologyPresheafFunctor J.toGrothendieck q` | Domain is abelian J-sheaves; values are C-op presheaves of abelian groups with Ext-derived degree-q values. |
| `e.inverse.sheafPushforwardContinuous AddCommGrpCat.{u} K.toGrothendieck J.toGrothendieck` | Sends G on C to G precomposed with e.inverse on D; the functor's contravariant sheaf direction matches the conclusion. |
| `⋙ Sheaf.cohomologyPresheafFunctor K.toGrothendieck q` | Forms degree-q cohomology presheaves on D of those transported sheaves. |
| `⋙ (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{u}).obj e.functor.op` | Restricts those D-op presheaves to C-op; at W evaluates at e(W), on W' to W uses e of that arrow. |
| Outer natural isomorphism | Naturality in G is a natural-isomorphism equation of functors out of the sheaf category. |
| Each presheaf component | Naturality in W is the equation for restrictions inside that component presheaf isomorphism. |

Fixed-degree source checks: 03A0 supplies equivalence of topoi under stronger site
hypotheses; here the explicit library morphism-of-sites theorem specializes the
covering iff to quasi-inverse abelian-sheaf functors. Continuity alone is NOT attributed
to 03A0. 015Z is applied with the exact quasi-inverse as left adjoint, not to an arbitrary
continuous functor. 01FT equation (the project server), 03F3's proof, and 03YU's proof compute by
sections of injective resolutions. They do not directly identify the Ext definition in
Mathlib. That identification is separately provided by
`lem-sc-site-cohomology-right-derived-sections`, whose signature was read: the same
SmallCategory, HasSheafify and HasExt universe u context, arbitrary object U and degree
q, with a natural isomorphism to right-derived evaluation. The existence of resolutions
uses `lem-weil-pbc-site-sheaves-enough-injectives`; their transport uses all clauses of
`lem-weil-pbc-equivalence-injective-resolutions`; lifts and independence use
`lem-weil-pbc-derived-functor-map-via-lift`. These five required nodes are precisely
proof_deps and proof[0].uses. The docstring explains the additional naturality in the
object through the natural free-representable/sections adjunction, rather than deriving
it merely from a fixed-object statement.

Fixed-degree edge cases: for e = identity, J = K and identity unit, E is the identity
and the section-complex map is the identity. In degree q = 0 the map is the inverse
unit restriction identifying G(W) with G(e.inverse(e(W))); no positive-degree argument
is silently used. For injective G, positive-degree cohomology vanishes on both sides
because E preserves injectives. For the zero sheaf every group is zero. For a nontrivial
unit the isomorphism uses inverse unit restrictions in the direction of the theorem;
it does not assert equality of the objects. The different-topologies counterexample
above tests the omitted-hypothesis failure and is now excluded by hcover_iff. Naturality
for identity morphisms follows from the complex identity, and for composites from
functoriality of restrictions and lift-induced maps.

Reduction and route: the two covering hypotheses of the unchanged target produce
hiff; the existing morphism-of-sites theorem gives hi'; the corrected fixed-degree
lemma receives hiff, hi' and q. Each split is strictly below the original theorem:
the first contains no cohomology, the second assumes covering compatibility and
continuity and proves one degree. The sk-prop-cd unit record is unchanged; no unit
statement or step is bypassed. The target node now matches these actual Lean calls.

Validation: `lcompile.py --all` compiled all three modules with exit code 0.
`deliver3.py G1 Sheaf.CategoryTheory.Sites.CohomologySiteEquivalence --no-push`
printed OK (dry run), with compilation and preflight passing, review class CODEX,
and nothing pushed. The only remaining hole in the delivery is the named fixed-degree split theorem above.

## Earlier second reading (a previous round; superseded)

1. Compared the target module with the repository version using diff. Its existing
   theorem signature is byte-for-byte unchanged, and no definition or visibility
   changes. Both intermediate modules are new; their signatures match their nodes.
   Verdict: pass, with no change record required.
2. Compiled all three files through lcompile.py. Independently printed axioms in
   scratch copies: covering_iff_of_equivalence uses only propext, Classical.choice,
   Quot.sound; the fixed-degree theorem and target additionally use sorryAx from
   the single documented fixed-degree hole. No forbidden declarations or hollow
   definitions. Verdict: pass as a partial reduction, not a complete target proof.
3. Read both split statements and complete docstring arguments. Checked identity
   equivalence, empty covering families, non-strict unit, q = 0, zero sheaves and
   injective sheaves. Cover reflection follows from the unit square in the stated
   direction. Fixed-degree transport uses the exact additive sheaf equivalence,
   inverse-unit section map, Ext/derived-sections identification and naturality
   in both variables; continuity alone would be insufficient, but hcover_iff is
   present. Read the cited Stacks 03A0, 015Z, 03F3 and 03YU pages and the library
   comparison declaration. Ran fresh leanfinder, loogle and grep searches with
   alternate queries: coherent-topology sheaf equivalences do not cover arbitrary
   J,K; the cohomology functor search returns its definition, not the comparison.
   Global H.mapFunctor_bijective concerns constant-sheaf cohomology, not H' over
   varying objects. No duplicate exact statement found. Verdict: pass.
4. The target takes cover reflection, the proved morphism-of-sites theorem, then
   fixed-degree comparison. Closed the covering split in a short formal proof.
   Removed its now redundant direct import from the target. Listed every old
   proof dependency displaced by the reduction under No longer needed. Inspected
   sk-prop-cd.realized: none of these nodes realizes a unit statement or step;
   no unit route is bypassed or changed. Verdict: pass.
5. Checked all three node proof plans, dependency unions, sources, creation data
   and Lean records against the code. The target's three calls match its three
   steps. The covering node now has a formal proof using its sole dependency;
   its Lean signature is stored verbatim. The open fixed-degree node records all
   five substantive ingredients of its complete mathematical proof. Verdict: pass.

Changes by this second reader: proved covering_iff_of_equivalence; removed the
unused target import of SiteCoveringIsomorphicFamily; replaced unused destructured
witness names by wildcards; restored docstring indentation; synchronized the
covering node's verbatim signature and proof-origin note; corrected the report's
hole accounting and pruning list. The linter option remains because the unchanged
existential continuity binder is used implicitly in the target's signature.

## Second reading by G1

1. Compared the target module with the repository using diff and extracted its
   signature through the proof delimiter: byte-for-byte unchanged. Both auxiliary
   modules are absent from the repository; no definitions or other existing
   interfaces changed. Verdict: pass.
2. Independently compiled all three modules with lcompile.py --all, exit 0 and
   no warnings. Scratch copies with #print axioms confirm that the covering
   theorem uses only propext, Classical.choice and Quot.sound. The target and
   fixed-degree comparison additionally use sorryAx from the single named
   fixed-degree hole. Inspected every body: no forbidden declarations and no
   definitions, hence no hollow data. Verdict: pass as a decomposition; the
   original theorem is not proved with standard axioms alone.
3. Independently checked the covering unit square and the fixed-degree
   resolution argument, including the Ext/derived-sections bridge. Read the
   library comparison signature and the three Mathlib-backed dependency nodes.
   Tested identity equivalence, empty presieves, non-strict units, q = 0,
   injective sheaves in positive degree and the zero sheaf. Cover compatibility
   excludes the unequal-topology counterexample; no missing hypothesis found.
   Fresh launcher searches used an Ext-cohomology equivalence query (leanfinder),
   the fully qualified cohomologyPresheafFunctor (loogle), and Ext/derived
   equivalence patterns (grep), plus rg on both library roots. Results provide
   building blocks, not this natural comparison. Read Stacks 03A0, 015Z,
   03F3 and 03YU directly. In particular 015Z applies to E because its exact
   quasi-inverse is a left adjoint; arbitrary exact left adjoints do not
   necessarily preserve injectives. Verdict: the remaining statement is true,
   a strictly smaller cohomology-transport step, with a complete word proof.
4. Checked the actual top-down reduction: proved covering reflection, the
   existing proved continuity theorem, then fixed-degree transport. No short
   existing theorem closes the last transport step; objectwise comparisons
   alone do not supply its two naturality conditions. Every removed old direct
   dependency is listed under No longer needed. sk-prop-cd.realized is empty
   for these nodes, and neither its statement nor its steps change. All added
   imports used only for proofs are plain imports. Verdict: pass; no whole
   module is pruned and closure hole reduction is zero.
5. Checked node signatures against the Lean text, existing-node changes against
   the allowed fields, and each proof dependency against its proof steps. The
   target lists its three actual calls; the covering node lists the proved
   isomorphic-family lemma; the open transport node lists the five ingredients
   of its word proof. New nodes have source, blueprint ancestry, searches,
   creation metadata, chapter, unit and complete Lean records. Verdict: pass.

Changes in this reading: corrected the fixed-degree docstring's 015Z description
from “exact left adjoints preserve injectives” to “functors with exact left
adjoints preserve injectives”; corrected a stale report sentence that counted
two remaining holes. No proof, signature, definition or dependency changed.
The covering hole had already been closed before this reader started; the
historical second-reading sections above describe earlier rounds. This delivery
closes the original target hole syntactically and adds one fixed-degree hole:
net zero, a decomposition, with a separately proved covering lemma.
