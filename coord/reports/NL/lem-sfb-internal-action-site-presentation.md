## Worker report

The delivery states `CategoryTheory.InternalActionSite.presentation` in
`Sheaf.CategoryTheory.InternalActionSitePresentation`. This repairs the returned immutable head
`41e7bb27ba35` under §1(C): only the site clause and proof step 3 are corrected,
in addition to the Lean record. No new nodes or dependency modules are added.

The previous worker misclassified the NR landing at ledger line 22944. I read that
landing's node, review and report: it was a stage-1 split, with no Lean declaration.
Stage 2 remains necessary. There is no coord/repair-notes JSON for this item; the supplied return is the
repair instruction. The current node
has the reviewed ten-step proof; its source explicitly describes the result as an
agent-formulated categorical foundation, not a theorem stated in the blueprint.
I read the motivating main-20261015 direct-images proof paragraph (3). The missing
exact external reference is inherited from the node; the module does not falsely
attribute this entire action-site theorem to any single Stacks tag.

All data definitions are explicit. The module never chooses the equivalence or
sheafification from the mere existence theorem. `Presentation` is a specification
structure, and the main theorem asserts its `Nonempty`; its section formulas and
unit diagrams prevent this from asserting an unspecified equivalence. Its notions
are exactly those introduced in the item's own statement, so they are helpers in
the owning module under the human's missing-helper authorization, not independent
new notions. All helpers and named proof obligations are in `lean.declarations`.

Hypotheses and clauses, in the order of the node:

1. The fixed universe V is `universe u`; `C : Type u`, `[SmallCategory C]`,
   `GrpCat.{u}`, `CommRingCat.{u}` and `PresheafOfModules.{u}` are small in this
   bound. The explicit wrapper `Object K` and pairs `Arrow K` also live in u.
   This is a small site, exactly as requested; no new universe equality is imposed
   on a site having independently specified universes. The node fixes one bound.
2. A site with finite limits is `J : Precoverage C`,
   `hJ : J.IsSiteForCoverings`, `[HasFiniteLimits C]`. The exact recorded site
   interface is used. Sheaves are taken on `J.toGrothendieck`, the dependency's
   recorded interpretation of its covering families. The construction retains the
   original covering families, not just their saturation.
3. The sheaf of groups is `K : Cᵒᵖ ⥤ GrpCat.{u}` with
   `hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u})`.
4. The coefficient is `S : Sheaf J.toGrothendieck CommRingCat.{u}`. `baseRing`
   applies Mathlib's forgetful functor to RingCat. This keeps a commutative unital
   ring as input; it does not replace it by an arbitrary noncommutative ring.
   The trivial K-action is encoded by `coefficientPresheaf`, whose maps ignore labels.
5. `LinearAction.act` is a monoid hom from K(X) into `Module.End`, giving the unit,
   product and linearity laws; `LinearAction.naturality` is restriction naturality.
   `EquivariantPresheaf` uses the actual Mathlib module presheaf. `Equivariant`
   describes maps commuting with each action. `EquivariantSheaf` is its full
   subcategory of sheaves; there are no restrictions on morphisms beyond linearity,
   naturality, and equivariance.
6. `Object K` has exactly one base object field. `Arrow K X Y` is the pair
   of a base arrow and a section of K at X. `categoryStruct` gives (1,1) and
   Lean-order composition `(g,b) ≫ (f,a) = (g ≫ f, b * K.map g.op a)`.
   This is the specified conventional `(f,a) circ (g,b)`. `category_laws` is the
   named postponed proof of its equations; `category` contains real structural data.
7. `precoverage` declares a presieve covering exactly when its underlying base
   arrows form an original J-cover, using existential image on labels.
   `hasIsos` asserts singleton isomorphism covers. `covering_pullbacks` renders
   existence of covering pullbacks, with exactly the quantifiers of the base
   dependency's third clause. `labelOneSieve` has arrows `S (Arrow.mk f 1)` and
   actual data; its closure proof is the named `labelOne_downward` theorem.
   `topology` is the generated Grothendieck topology. `topology_mem_iff` says
   `S ∈ topology K J X ↔ labelOneSieve K S ∈ J.toGrothendieck X.base`, exactly
   the corrected site clause. No bind composition assertion remains. Neither
   a terminal object nor finite limits on the twisted category are asserted.
8. `coefficientPresheaf` is `projection.op ⋙ S.obj`. Its objects are R(U),
   and its maps are f-star, independent of a. `coefficient_isSheaf` proves the
   sheaf condition, separately named; `coefficientSheaf` supplies its actual data.
9. `Presentation.sheafEquivalence` is the required equivalence to
   `ringedSiteModules (twistedRing K J hJ S)`, and `sheaf_additive` asserts
   additivity. `presheafEquivalence`, `sections`, `restriction`, `morphisms`,
   and `underlying` specify its section modules, the formula a dot f-star(m),
   the component maps, and its restriction to sheaves. Section identification is
   by linear equivalence, not literal equality of bundled carrier structures.
10. `inverseSections`, `inverse_restriction`, and `inverse_action` specify the
    inverse: restrict to (f,1) and recover a dot m along (1,a). These are formulas
    about the inverse of that same sheaf equivalence.
11. `equivariantSheafification`, `adjunction`, and `baseComparison` say the
    reflection has the ordinary base module sheafification with induced action.
    `siteComparison` identifies twisted-site module sheafification with its
    equivariant counterpart. `base_unit` and `site_unit` make the two natural
    isomorphisms commute with the ordinary units on underlying abelian presheaves.
    These unit characterizations are what the proof's canonical comparison states.
12. `createsKernels` and `createsCokernels` assert creation of limits and colimits
    of `parallelPair f 0` by the actual forgetful functor. Its target is Mathlib's
    ordinary sheaf-module category, whose kernels are sectionwise and whose
    cokernels are module-sheafified presheaf cokernels, as the dependency states.
    Thus this is creation with precisely those underlying objects, not merely
    preservation of an independently supplied equivariant limit.
13. `zero_iff` says a module sheaf on the twisted site is zero exactly when its
    underlying base module sheaf (restriction through the specified inverse) is zero.

Dependency declarations read and used:

- `def-weil-size-convention`: its existing metatheoretic convention record has no
  Lean object; the explicit small universe parameters implement it.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: read full signature/docstring;
  used as hJ on the base, and its isomorphism-cover and existence-of-covering-
  pullbacks clauses are the ones asserted for the action precoverage.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  read full signature/docstring; used for every module-sheaf target.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`,
  `PresheafOfModules.sheafification`, with identity ring map; read the functor,
  its adjunction, and underlying abelian presheaf/unit comparison. Used in both
  comparison fields, on the base and on the twisted site.
- Proof leaf `lem-pc-sites-sheafification-underlying-sets`:
  `Mathlib.CategoryTheory.Sites.PreservesSheafification`,
  `CategoryTheory.sheafifyComposeIso`, `CategoryTheory.sheafComposeIso_hom_fac`;
  read the universal comparison, unit equation and concrete-category instances.
  The returned unused private import of PreservesSheafification has been removed
  (H9); the relevant APIs remain available transitively from the required
  public imports. This proof dependency remains in the DAG.
- Proof leaf `lem-weil-pbc-sheafification-sets-exact`:
  `Mathlib.CategoryTheory.Sites.Sheafification`, `presheafToSheaf` finite-limit
  preservation, and `Mathlib.CategoryTheory.Sites.LeftExact` for its small-site
  instances. Read the full relevant signatures; available for the future proof.

The remaining public imports provide exactly the structures/instances used by the
statement: group filtered-colimit preservation gives abelian sheafification on
small sites, ring limits give sheaf composition with CommRingCat-to-RingCat, and
Limits.Creates supplies creation of kernel/cokernel diagrams.

Edge cases checked: K trivial gives the base arrows, covers and ordinary modules;
R zero admits only zero modules; an empty cover gives the original terminal
matching-family condition on both sides; nonabelian K requires b g-star(a), not
its reversed product; a one-object base with nontrivial K is the group category
with reversed multiplication, whose contravariant modules are left actions.
In particular C_K need not have a terminal object. No representability, enough
points, subcanonicity, nonzero-ring, or global section-lifting assumption appears.

Searches (actual wrapper outputs are retained in searches.jsonl):

- LeanFinder: "Sheaves of modules with an action of a sheaf of groups are equivalent
  to modules on the action site": 8 hits, scalar-sheafification and ordinary module
  sheaf declarations, no action-site presentation.
- Loogle: `"SheafOfModules", "Action"`: 0 hits.
- Mathlib grep in CategoryTheory:
  `actionSite|classifyingSite|equivariantSheaf|internalAction`: 0 hits.
- LeanSearch: "Equivariant sheaves of modules for a sheaf of groups are modules on
  a twisted action site": 8 hits, ordinary module sheaves, scalar sheafification,
  and equivariant functions; none states this theorem.
- Project `rg` in both `lean/Sheaf` and `lean/WeilConjectures` for
  `actionSite|classifyingSite|internalAction|InternalActionSite|twisted.arrow.*site|equivariant.*sheaf.*group`
  and for the exact item tag: no action-site declaration. Earlier broader
  equivariant searches found representation, torsor, and point-action modules,
  which concern fixed external groups rather than a varying sheaf K(U).

Every theorem proof is `sorry`, with a matching blueprint annotation and a
natural-language proof in its docstring. No hollow definition or arbitrary
chosen equivalence is introduced. All theorem statements in this module belong
to this item's construction and its explicitly recorded ten-step proof.
The definite site-statement error has been corrected and recorded below, rather
than leaving the known false assertion with a STATEMENT-DISPUTED flag.

Validation: before editing, the required saved-packet dry run passed at
`8dd07c919a6`, confirming the packet could be reused. That mechanical pass does
not resolve the supplied mathematical counterexample. The repair changes the
actual files, rather than just rebasing or re-pushing the returned version.
The repaired module was compiled only through scompile.py in sandbox mode
(10.8 s) and library-module mode (10.0 s), both clean, with no extra warnings.
The final required dry run and delivery wrapper record the final validation.


## Statement corrected

Return H3 at immutable head `41e7bb27ba35` correctly identifies a false
assertion: the image precoverage need not satisfy `IsSiteForCoverings`, because
its bind clause chooses a refinement independently for distinct twisted arrows,
which can project to the same base arrow.

The old sentence was: “These families make $C_K$ a small site.” The complete
old statement is retained verbatim in `statement_change.old_statement`.
Take the Boolean lattice `{0,a,b,1}` with all singleton presieves covering and
a constant group sheaf with distinct sections x and y. The twisted presieve
`{(id_1,x),(id_1,y)}` projects to a singleton and covers. Refine its two arrows
by the singleton maps from a and b respectively. The bind projects to
`{a→1,b→1}`, which is not a singleton. The same issue allows infinite unions
when one uses finite jointly-surjective profinite covers and infinitely many
labels. Thus it would be wrong to retain the previous theorem.

The corrected sentence states that these families are a precoverage containing
singleton isomorphisms and admitting covering pullbacks for some choice; it
uses the generated Grothendieck topology, whose covering sieves are exactly
those with a base J-covering label-1 sieve. Here J-covering refers to
`J.toGrothendieck`, as everywhere else in the module. The module keeps this
generated topology as before. All other clauses and every field of
`Presentation` are retained.

Source read: `literature/stacks-project/sites.tex`, `definition-site` (00VH),
including the explicit “some choice” clarification after axiom (3), and
`definition-topology` / `definition-topology-associated-site`. I also read the
current main-20261015 direct-images proof paragraph (3); it motivates the
categorical input but does not state this agent-formulated lemma. The correction
therefore changes no blueprint unit statement. Proof step 3 now uses the
isomorphism/pullback clauses and gives the full sieve correspondence and
comparison of generators, instead of the invalid composition argument.

Citer audit: an exact-id search of all `dag/nodes` returned this item and
`lem-sfb-condensed-product-action-inflation`, the sole actual citer. I read its
statement, every proof step and its delivered Lean theorem/docstring.
**holds: true**: its steps 2 and 4 use the unchanged additive equivalence,
kernel/cokernel creation and zero detection. Its step 3 applies the general
ringed-site Grothendieck theorem to the small generated Grothendieck site;
that topology and its sheaf category are unchanged. No use requires bind
closure of the image precoverage. The citer is not edited.

## Repair self-check

Compared the saved node with current main by reading JSON: the sole pre-repair
difference was its `lean` record. The saved report and original Lean statement
were retained except for the corrections identified above. The return's H9
import was removed. The replacement `hasIsos`, `covering_pullbacks`,
`labelOne_downward`, `labelOneSieve`, and `topology_mem_iff` are all listed in
`lean.declarations`; the false `isSiteForCoverings` is removed from that list.
Every proof remains `sorry`, all variables and universes are explicit under
`autoImplicit false`, and the label-1 sieve definition contains actual data.
The new proof obligations each have a source, blueprint tag and proof docstring.

Additional repair search: Mathlib grep via msearch.py,
`labelOneSieve|InternalActionSite|actionSite` in CategoryTheory: 0 hits.
Direct project rg for `labelOneSieve|covering_pullbacks|topology_mem_iff` and the
namespace found no pre-existing version. The previous three-kind search evidence
is retained in the saved searches.jsonl and above; no duplicate notion is added.

Additional edge cases: the Boolean-lattice counterexample explains exactly the
removed clause, while the generated-sieve criterion remains valid; repeated
base arrows with different labels remain allowed. Empty covers give the empty
base sieve; label normalization still works. No finite-group hypothesis was
introduced, so infinite profinite groups remain covered. Pullback stability is
explicitly existence for some choice, avoiding Mathlib's stronger
`Precoverage.IsStableUnderBaseChange`, which quantifies over every choice.
The corrected site theorems do not require K to be a sheaf; the main presentation
continues to require hK for the sheafification comparison.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
