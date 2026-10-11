## Worker report

Following reviewer R-sub-D's H4 finding, `ModuleCohomologyBoundary.lean` now imports
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle` and defines
`moduleCohomologyBoundary` directly using
`CategoryTheory.ShortComplex.ShortExact.singleTrianglePlus`. The body is the right-hand
side of the second conjunct of `CategoryTheory.rightDerived_triangle_connecting` for
`v = Γ(X, -)`, transported through the existing comparison isomorphisms. The previous
hand-built `s`, `i`, `δ`, and `Triangle.mk` expression was removed. The item's theorem,
node statement, and node record are unchanged.

The module `Sheaf.AlgebraicGeometry.BoundaryCechLocalLifts` states
`AlgebraicGeometry.Scheme.Modules.boundary_cech_local_lifts`; its only theorem proof is
`sorry`. A companion definition node supplies the canonical module-cohomology boundary,
whose data is fully written, using the existing derived-global-sections construction.
No repository file was edited directly and no delivery was pushed.

Clause-by-clause correspondence:

- Scheme: `X : Scheme.{u}`. The two explicit `HasDerivedCategory` parameters record the
  localization universes needed for computing the boundary, not geometric hypotheses.
- Algebra sheaves O' and O: `B C : X.CommAlgebraSheaf`. Their map is `p : B ⟶ C`, so
  multiplicativity, preservation of one and compatibility with O_X are built in.
- Kernel I: `I : X.Modules`, with inclusion `j : I ⟶ B.toModule`. The underlying
  quotient map is `(commAlgebraSheafModuleFunctor X.sheaf).map p`, not a freely specified
  module map. `hzero` and `hshort` give the short exact sequence. As in the source,
  I is an ideal/module, not a unital commutative algebra: the phrase 'short exact sequence
  of algebras' is interpreted as exactness of their underlying modules, with ideal kernel.
- Square zero: `hsquare` says the product of every two image sections of I is zero on
  every open W. `@id` merely directs elaboration to B's already existing ring carrier.
- Open covering: `U : ι → X.Opens`, `hcover : iSup U = ⊤`.
- Global section and chosen lifts: universally quantified `f : C.right.obj.obj (op ⊤)`
  and `t : ∀ i, B.right.obj.obj (op (U i))`; the following implication assumes exactly
  `p(t i) = f|U i`. A global section is sent to H⁰ through `toRightDerivedZero.app`.
- I-valued cocycle: the witness `z : K.cycles 1`, where K is the established Čech complex,
  is already a cocycle. Its image under `K.iCycles 1`, projected to each ordered pair x,
  maps under j to the displayed `t(x 0)| - t(x 1)|`. Products in the category of opens
  are intersections, and their `Pi.π` maps are the inclusions into the two opens.
  Thus there is no extra choice of overlap lifts, nor a hypothesis that differences
  already lie in I. Both membership and the cocycle property are conclusions.
- Canonical map and injectivity: the existential `c` satisfies `IsModuleCechComparison
  U I 1 c`, which fixes the canonical map for every injective resolution;
  `Function.Injective c` is its injectivity on underlying groups.
- Image of the class: `K.homologyπ 1 z` is [alpha]; the last equality says its image is
  the canonical `moduleCohomologyBoundary ... 0` evaluated at the degree-zero class of f.
- Simultaneous assertion: c is chosen before the universal quantification over f and t,
  so the same map works for every section and every family of lifts, including two
  sections at once. No multiplication/Leibniz clause is added.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.Paper.PQFCohomology`: `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`;
  its degree functors are `RingedSpace.moduleCohomology` from
  `Sheaf.Topology.RingedSpaceModuleCohomology`, reused here, not abelian-sheaf Ext.
- `Sheaf.CategoryTheory.SiteCechComplex`: `CategoryTheory.SiteCechComplex`, its alternating
  restriction complex and comparison of choices. On opens the finite products exist,
  so this statement uses Mathlib's existing `CategoryTheory.cechComplexFunctor`, exactly
  the representative used by the recorded H¹ comparison dependency. A general site's
  arbitrary chosen fibre products are unnecessary for this specialization.
- `Sheaf.AlgebraicGeometry.CechH1MapNatural`: `Scheme.Modules.cechH1Map_natural` and its
  imported `Scheme.Modules.IsModuleCechComparison` from `ModuleCechComparison`.
- Added already-landed notion dependencies `def-weil-pbc-comm-algebra-sheaf` and
  `def-weil-pbc-ringed-space-algebra-module`: `Scheme.CommAlgebraSheaf`, `.toModule`
  and `CategoryTheory.commAlgebraSheafModuleFunctor` from their recorded modules.
  The two underlying-object definitions are definitionally identical; the latter's
  existing functor supplies the morphism. No algebra or module notion is recreated.

Sources were read online because `literature/stacks-project/cohomology.tex` is absent
on this machine: https://stacks.math.columbia.edu/tag/0B8R and
https://stacks.math.columbia.edu/tag/0B8S. The latter explicitly gives t_i0 - t_i1.

STATEMENT-DISPUTED: the source's displayed t_i0 - t_i1 sign needs independent comparison
with the already-landed `IsModuleCechComparison` total-complex convention and the
canonical derived homology-sequence boundary. Mathlib's alternating coface differential
in degree zero is t_i1 - t_i0, and the unformalized supporting node
`lem-sc-boundary-cech-compatibility` now uses that opposite difference. I have kept the
item's/source's formula exactly and used the canonical boundary, without silently
negating either the comparison or boundary to force agreement. No counterexample is
asserted; this is a sign-convention question for the second reader. The already-landed
citer `lem-sc-boundary-derivation-square-zero` uses a horseshoe snake boundary; the
relation of that convention to this derived boundary likewise needs a sign check.
The derivation identity itself is unchanged by negating all boundary classes.

Edge cases checked: I = 0 gives zero cocycle and zero boundary; a single whole-space
open gives a global lift and zero class; repeated indices give zero diagonal components;
empty opens have zero section modules; an empty covering covers only the empty scheme,
where sections and cohomology vanish. No characteristic, separation, quasi-coherence,
finite-cover or nonempty-index assumption is imposed. Index and module universes match
those of the recorded `cechH1Map_natural`; all universes and variables are explicitly bound.

Searches made (recorded by msearch.py in searches.jsonl):

- LeanFinder, 'Cech cohomology connecting homomorphism represented by differences of
  local lifts': eight hits, including group-cohomology connecting formulas and
  nonabelian cocycle relations; none is this module-sheaf theorem.
- Loogle, `CategoryTheory.cechComplexFunctor`: one exact complex-definition hit, reused.
- Mathlib grep, `cech.*boundary|boundary.*cech|local.lifts`: zero hits.
- rg over WeilConjectures and lean/Sheaf for the item id, declaration names and boundary
  patterns: no existing statement. The citer `BoundaryDerivationSquareZero` was read
  in full; it states the derivation theorem, not this local-lift statement.
- LeanSearch for the canonical module-cohomology connecting morphism: unavailable
  (Internal Server Error), recorded as unavailable, not a negative search result.
- LeanFinder for canonical right-derived boundary: eight hits, including `singleδ`
  (a morphism before deriving Γ) and the snake lemma, but no module-cohomology definition.
- Mathlib grep of `moduleCohomologyBoundary|rightDerived.*δ|boundary.*cohomology` in
  CategoryTheory: zero hits. Source grep finds only `exists_rightDerived_δ_exact`, an
  existential exactness theorem, whose construction was read and reused.
- `blueprint_refs.py search 'module cohomology boundary'` and 'canonical connecting':
  zero matching definition nodes; grep of DAG boundary definitions finds unrelated notions.

Both modules compile together with lcompile.py without errors or warnings.

## New nodes

`def-sc-module-cohomology-boundary` defines the actual connecting morphism on the recorded
module-cohomology functors for a short exact sequence of modules on a ringed space.
It applies derived Γ to the canonical single-complex triangle, takes its homology
boundary, and transports through the existing single/right-derived comparison
isomorphisms. Sources: Stacks 01DZ and the boundary in 0B8S. Searches above show that
neither Mathlib, the project nor the DAG already provides this definition. The source's
`exists_rightDerived_δ_exact` provides only existence of some exactness map, which would
not pin down the boundary required here. The companion module extracts its explicit
canonical construction, with no new theorem and no sorried data. The necessary enough-
injectives proof is the existing named `moduleSheaves_abelian_enoughInjectives` theorem;
no choice of new Abelian structure is made. The new node cites the existing cohomology,
short-exact-sequence and derived-category nodes.

## Earlier second reading (a previous round; superseded)

Independent reading of the item, both delivered modules, every statement dependency
node and its recorded module, and the new definition node. The repository and upstream
checkout were read only. The Stacks TeX was absent locally; I obtained cohomology.tex
from https://raw.githubusercontent.com/stacks/stacks-project/master/cohomology.tex in
this item's scratchpad and read the source around lines 1486 and 5742, together with
the module-cohomology definition at equation cohomology-modules near line 69.
The public pages https://stacks.math.columbia.edu/tag/0B8R,
https://stacks.math.columbia.edu/tag/0B8S and
https://stacks.math.columbia.edu/tag/01DZ were also read.

Objects, hypotheses and conclusions, in the node's order:

1. Scheme X: `(X : Scheme.{u})` is the recorded `AlgebraicGeometry.Scheme` of
   def-pc-scheme. No affine, separated, Noetherian, field, or characteristic assumption.
   Verdict: same object.
2. Commutative O_X-algebra sheaves O' and O: `(B C : X.CommAlgebraSheaf)` and
   `(p : B ⟶ C)` use the recorded under-category construction and its morphisms.
   I opened CommAlgebraSheaf.toModule and commAlgebraSheafModuleFunctor: their
   underlying objects are definitionally the same restriction of the algebra's unit
   module, and the functor's morphism uses exactly p's additive section maps.
   Verdict: same algebra structures and quotient arrow, not arbitrary linear maps.
3. Kernel I and short exactness: `(I : X.Modules)`, `(j : I ⟶ B.toModule)`,
   `hzero`, and `hshort : (ShortComplex.mk j ... hzero).ShortExact` give the mono,
   image-kernel equality, and epi required by def-weil-pbc-exact-sequence. Exactness
   here is sheaf exactness, not surjectivity on all open-section modules. The source
   treats I as an ideal and additive sheaf; it is not a unital algebra. Verdict: correct.
4. Square zero: `hsquare` quantifies over every open W and every pair of I-sections,
   asserting the product of their j-images in B(W) is zero. Since j identifies I
   with the kernel sheaf, this says precisely I² = 0. `@id` just fixes the target
   ring carrier; it adds no condition. Verdict: same hypothesis.
5. Cover: `{ι : Type u}`, `(U : ι → X.Opens)`, `hcover : iSup U = ⊤` give an
   arbitrary covering family in the module/index universe used by the recorded
   cechH1Map_natural. No finite-cover, distinctness, or Nonempty assumption.
   Verdict: correct within the established universe-polymorphic module encoding.
6. Section f and chosen local lifts: the conclusion quantifies over
   `f : C.right.obj.obj (op ⊤)` and `t : ∀ i, B.right.obj.obj (op (U i))`;
   the implication assumes p(t_i) is f restricted along U_i ≤ ⊤. Evaluation at
   top is Γ(X,C), canonically H⁰ via `toRightDerivedZero.app C.toModule`.
   Verdict: same hypotheses, with existence of lifts rendered as arbitrary chosen
   lifts satisfying the lifting equation. No stronger sectionwise-surjectivity premise.
7. Ideal-valued Čech 1-cocycle alpha: `∃ z : K.cycles 1`, for
   `K = (cechComplexFunctor U).obj I.presheafModuleCat`, and the component equality
   after `K.iCycles 1` state both membership in I and the cocycle condition. Each
   `x : Fin 2 → ι` represents an ordered pair. The inner finite product is the
   intersection of the two opens; Pi.π gives its inclusions. Applying j gives
   exactly t_(x 0)| - t_(x 1)|. Verdict: correct formula, all overlaps, no membership
   hypothesis slipped in. The degree-one differential gives the telescoping triple
   identity. Mathlib's complex is the opens specialization of the node's alternating
   complex and is the exact representative used by the landed comparison dependency.
8. Canonical comparison and injectivity: `∃ c : K.homology 1 ⟶ H¹(X,I)`,
   `IsModuleCechComparison U I 1 c`, and `Function.Injective c` impose the canonical
   resolution-independent comparison and its injectivity. I read moduleCechDouble,
   Alpha, Beta, and the predicate: it requires c followed by the resolution
   identification and H(Alpha) to equal H(Beta), for every injective resolution.
   Verdict: canonical map rather than an arbitrary injection; same conclusion.
9. Image of the class: the last equality applies c to `K.homologyπ 1 z` and compares
   it with `moduleCohomologyBoundary ... 0` on the degree-zero class of f.
   The new boundary is actual derived-global-sections data, not an existentially
   chosen map satisfying exactness. Verdict: precisely the node's requested equality;
   its sign compatibility remains disputed below, as already flagged by the writer.
10. Simultaneity: c is selected before `∀ f t`. Thus a single canonical map works
    for any second section and chosen lifts; no second cover or second comparison
    is silently selected. Verdict: same quantifier order and simultaneous assertion.

The localization parameters `[HasDerivedCategory.{wC} ...]` and
`[HasDerivedCategory.{wD} ...]` are choices of localized categories, not geometric
restrictions. I read `HasDerivedCategory.standard` in Mathlib: it supplies the choice
at the standard max universe for every abelian category. The theorem is generic in
both localization choices; it does not require a smaller localization universe.
Every source assumption is already explicit above. In particular 0B8S is stated on
an arbitrary topological space with ring sheaves, so its scheme specialization does
not inherit an unmentioned finiteness or characteristic restriction.

New node def-sc-module-cohomology-boundary: I read its full JSON against 01DZ's
module-valued right-derived cohomology and 0B8S's short exact sequence. Its three
cited notions are the established module cohomology, categorical exact sequence,
and derived category, and stmt_deps lists exactly these. The definition uses the
existing named moduleSheaves_abelian_enoughInjectives proof, singleδ, the fully
faithful Plus inclusion's preimage, derived Γ, HomologySequence.δ, and the existing
single/right-derived comparison isomorphisms. This is the construction written
inside upstream exists_rightDerived_δ_exact, whose declaration I read in full;
that theorem gives only existence of an exactness map and cannot supply this named
canonical morphism by itself. No new data is sorry. The sole inline elementary
cast proof was replaced by the existing `(Nat.cast_add_one q).symm`, so the
boundary definition needs no new proof declaration. I corrected the new node's
source place from the nonexistent label `cohomology-modules` to the actual
`equation cohomology-modules`. Its chapter, unit, created record, empty proof
fields, search fields, and none lean_audit conform to §5. Running blueprint_refs.py
ancestor confirmed lem-sc-pic-proper-ntorsion, matching blueprint.from and its via
chain. No dependency module is delivered and no dependency record is changed.

Edge cases: empty ι is admitted; hcover then forces the underlying space empty.
The empty scheme and empty opens have zero section modules by the sheaf axiom,
so the assertions give zero classes. I = 0 gives zero cocycle and boundary.
A one-open whole-space cover means f lifts globally, so the boundary and Čech class
are zero. Repeated indices give zero diagonal differences. The formula works in
characteristic two as well as other characteristics; there is no coefficient field
assumption. The main theorem concerns only degree one and boundary degree zero;
the new boundary definition admits every q : ℕ, including q = 0. The scheme,
section modules, and index family can all be placed in any larger universe; no
independent smaller test-object universe or nonempty-index premise is used.

Independent searches, recorded by msearch.py in searches.jsonl:

- LeanFinder: `sheaf cohomology connecting class computed using local preimages of a
  section`: eight results concerning nonabelian H1 and Mayer-Vietoris; none states
  this module-cohomology local-lift equality.
- Loogle: `ShortComplex.ShortExact.singleδ`: the service did not recognize that
  identifier (zero results). This is not counted as evidence of absence; I found
  and read the actual declaration in Mathlib's DerivedCategory/SingleTriangle.lean.
- LeanFinder: `right derived functor canonical connecting morphism short exact
  sequence of module sheaves`: eight hits including singleδ and δ_apply, which are
  existing ingredients, not a definition on the recorded moduleCohomology functors.
- LeanSearch: `module sheaf cohomology boundary homomorphism short exact sequence`:
  unavailable with Internal Server Error; recorded as unavailable, not a negative.
- msearch grep `boundary|connecting|local.preimage` is too broad and returned
  unrelated matches; it supplies no absence claim.
- Independent targeted rg on Mathlib, WeilConjectures, and lean/Sheaf for
  `cohomologyboundary|boundary.*local|local.*boundary|cech.*connecting|connecting.*cech`
  found abelian-sheaf cechδ, dimension shifting, other localization boundaries,
  and the already-landed derivation theorem, but no exact statement or canonical
  moduleCohomology boundary. I read the pertinent CechCohomology declarations:
  they concern abelian sheaf Čech functors and componentwise exact sequences,
  and do not give the delivered module boundary/local-lift assertion.
- blueprint_refs.py search `cohomology boundary` found no definition node. The
  supplied dependency nodes were all opened; none defines this boundary.

Mismatches and changes: the statement signature itself matches the node and was
left verbatim. The SiteCechComplex import was unused: the statement uses Mathlib's
cechComplexFunctor through the landed canonical-comparison module, so I removed
that import. An attempted removal of PQFCohomology exposed a missing
HasInjectiveResolutions instance on compilation; I restored that necessary import.
The inline cast proof in the boundary was replaced by a named Mathlib fact, and
the new node's source-label citation was corrected as described above.

Sign review: I independently confirmed that Stacks 0B8S explicitly prints the
first-minus-second local-lift difference, while the alternating Čech differential
from degree zero is second-minus-first. I also read mappingCone.triangle (third
arrow induced by -fst), triangleOfSESδ, singleδ, HomologySequence.δ, and the
upstream single/right-derived identification, rather than assuming that a cone's
visible minus sign settles the transport. In fact a degreewise split triangle
uses the positive splitting-differential-projection cocycle, so the cone minus
alone is not a resolution of this issue. The delivered boundary is exactly the
upstream canonical triangle construction; no sign was inserted to force agreement.
I cannot certify the final transported sign from these signatures alone. The
writer's STATEMENT-DISPUTED remains active for mathematical review under H6: the
source agrees with the node, and no concrete counterexample was established.
The supporting compatibility node's opposite sign and the derivation theorem's
horseshoe convention deserve a common comparison in stage 3. This review does
not silently change the node, its dependencies, the comparison, or the boundary.

Validation: both delivered modules were compiled together with lcompile.py. The
final declaration signatures were checked against lean.statement after whitespace
normalization; every variable and universe is explicitly bound and every Lean
line is at most 100 characters. The only theorem proof is the required sorry;
there are no hollow definitions, private copies, new file-local notation, or new
instances. Server compilation and preflight are delegated to deliver2.py's final
checks as required by the dispatcher brief.

## Second reading by H1

I reread the node, its Stacks sources (Cohomology Lemmas 0B8R and 0B8S), all
statement dependencies, and both delivered modules. The node introduces, in order:

1. A scheme `X`; Lean uses `(X : Scheme.{u})`, with no geometric, finiteness,
   characteristic, or field hypotheses. Verdict: exact.
2. Commutative `O_X`-algebra sheaves `O'` and `O` and their map; Lean uses
   `(B C : X.CommAlgebraSheaf)` and `p : B ⟶ C`. Verdict: the recorded notion,
   including its algebra and structure-sheaf compatibility.
3. A kernel `I` and short exact sequence; Lean uses `I : X.Modules`,
   `j : I ⟶ B.toModule`, `hzero`, and `hshort` for the underlying module sequence.
   Verdict: correct: the source only requires the kernel ideal as an additive
   `O_X`-module, while `p` supplies the quotient algebra map.
4. The square-zero condition; `hsquare` states that products of all pairs of
   image sections on every open are zero. Verdict: exact, with no extra condition.
5. An open cover; `{ι : Type u}`, `U : ι → X.Opens`, and `hcover : iSup U = ⊤`.
   Verdict: arbitrary covers, including empty-index covers of the empty scheme.
6. A global section and chosen local lifts; Lean quantifies `f` and `t` and assumes
   the restriction equation for every index. Verdict: equivalent to the source's
   existence-and-choice wording and has the same quantifier order.
7. The ideal-valued Cech cocycle; Lean existentially supplies `z : K.cycles 1`
   and requires each pair component, after `j`, to equal the displayed first-minus-
   second restricted lift. Verdict: includes both membership and the cocycle law;
   no overlap lift or extra hypothesis is assumed.
8. The canonical comparison and injectivity; Lean requires
   `IsModuleCechComparison U I 1 c` and `Function.Injective c`. Verdict: canonical
   comparison, not an arbitrary map, with the source's injectivity clause.
9. The image identity; Lean identifies `c (K.homologyπ 1 z)` with
   `moduleCohomologyBoundary ... 0` applied to the canonical degree-zero class of
   `f`. Verdict: the connecting class is explicit and uses the added canonical
   boundary definition.
10. Simultaneity; `c` is chosen before `∀ f t`, so one comparison serves every
    section and every choice of lifts. Verdict: exact.

The added definition node `def-sc-module-cohomology-boundary` was read against
Stacks 01DZ/0B8S. Its Lean definition applies derived global sections to the
canonical short-exact triangle, takes `HomologySequence.δ`, and transports through
the existing single/right-derived comparison isomorphisms. It has no hollow data;
the only proof in the delivery is the item's required theorem `sorry`. Its record
was added to `stmt_deps`, and the item's `lean.statement` is verbatim the theorem
signature.

Edge cases checked: `I = 0`, a one-open cover (including `⊤`), repeated indices,
empty opens, empty index type, empty scheme, characteristic two, and degree zero
of the boundary definition. No nonempty, finite, Noetherian, separated, or
characteristic assumption is present; universes of `X`, modules, and the cover
match the dependency declarations.

Searches were repeated with targeted `rg` over Mathlib, `WeilConjectures`, and
`lean/Sheaf`, plus the recorded LeanFinder/Loogle searches. No existing theorem or
definition gives this module-level Cech local-lift statement or the canonical
`moduleCohomologyBoundary`; the reused Cech comparison and module-cohomology
notions are the recorded declarations. Both delivery modules compile together with
`lcompile.py`. No mismatch requiring a Lean repair was found in this reading; the
only delivery metadata repair was ensuring the new boundary node appears in
`stmt_deps`. The previously reported first-minus-second versus alternating
-differential sign remains a convention question for stage 3 and is not silently
changed here.
