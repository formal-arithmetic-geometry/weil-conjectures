## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtale.RepleteOnContractible` states
`AlgebraicGeometry.Scheme.proetale_surjective_sections_of_epi_tower`. Its sole theorem
has proof `sorry`; there are no new definitions, auxiliary theorems, or node corrections.
The module and theorem docstrings cite the current main-20261015 blueprint and include
all four proof steps of the DAG: surjectivity at W, chosen preimages and recursion above
m, finite descending extension below m, and the sectionwise inverse-limit formula.

Clause-by-clause correspondence:

- The scheme X is `(X : Scheme.{u})`, with no finiteness or separation hypothesis.
- The site X_proet is the exact Mathlib `X.ProEt` and `ProEt.topology X`, whose definition
  uses all weakly etale X-schemes and the fpqc finite-refinement covering condition.
- An inverse sequence of sheaves of sets is
  `F : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) (Type (max (u + 1) w))`.
  Its adjacent map from n+1 to n is `F.map (homOfLE (Nat.le_succ n)).op`.
- Epimorphic transitions are exactly
  `hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)`.
  This is categorical epimorphism, not a sectionwise-surjectivity assumption.
- An arbitrary site object is `(W : X.ProEt)`; weak contractibility is
  `(hW : (ProEt.topology X).IsWeaklyContractible.{max (u + 1) w} W)`.
  This is the existing definition, using locally surjective sheaf morphisms, equivalent
  to epimorphisms for sheaves of sets. It imposes no affineness or connectedness on W.
- The first conclusion is the first conjunct:
  `∀ n : ℕ, Function.Surjective
    ((F.map (homOfLE (Nat.le_succ n)).op).hom.app (op W))`.
- The second conclusion is the second conjunct:
  `∀ m : ℕ, Function.Surjective ((limit.π F (op m)).hom.app (op W))`.
  This is evaluation of the actual sheaf-limit projection at every m, not merely
  its epimorphism or its degree-zero specialization. Sheaf limits are sectionwise.

Dependencies read and used:

- `sk-def-pe-site`: Mathlib `AlgebraicGeometry.Scheme.ProEt` and
  `AlgebraicGeometry.Scheme.ProEt.topology`, in
  `Mathlib.AlgebraicGeometry.Sites.Proetale`. Read the full definitions and docstrings
  (objects at line 100 and topology at line 156) and the node's full match record.
- `det-pe-weak-contractible-equivalences`:
  `AlgebraicGeometry.Scheme.proetale_weakContractible_equivalences`, in
  `Sheaf.AlgebraicGeometry.ProEtale.WeakContractibleEquivalences`. Read the entire
  signature and proof docstring. Its equivalence with condition 3 is the proof input;
  its module is imported without `public` because it is needed only for the proof.
- `det-pe-replete-definition`: `CategoryTheory.GrothendieckTopology.IsReplete`, in
  `Sheaf.CategoryTheory.RepleteSheafTopos`. Read the definition and full docstring.
  The theorem uses precisely its inverse-sequence and projection expressions;
  `limit` and `limit.π` are Mathlib constructions, exported by that module. Read
  `Sheaf.createsLimitsOfShape` in `Mathlib.CategoryTheory.Sites.Limits` as well.
- Added the already landed definition node `sk-def-pe-weak-contractible` to stmt_deps
  so that use of its recorded declaration is explicit:
  `CategoryTheory.GrothendieckTopology.IsWeaklyContractible`, module
  `WeilConjectures.CategoryTheory.Sites.WeaklyContractible`. Read the entire definition
  and its Stacks 090M docstring in the side framework. No duplicate definition is made
  and this node's own record is not changed.

Universes: u and w are explicitly declared, and autoImplicit is false. The small site
has object universe u+1 and morphism universe u. Section sets have universe
max (u+1) w, exactly the size range permitted by the generic repleteness definition.
The existing weak-contractibility definition is polymorphic in this value universe.
The equivalence theorem is stated at the base universe u+1; the proof at a larger value
universe uses the same condition directly through the existing polymorphic definition
and the epi/local-surjectivity criterion. No equality of site universes or extra
HasSheafify hypothesis is imposed.

Edge cases checked before writing: m=0 needs no descending extension; m=1 has one
backward transition; any m is included. If F_m(W) is empty, surjectivity onto it is
vacuous, and the recursive argument starts only after a section is prescribed.
No nonemptiness of sheaves or of W is assumed. Empty scheme and disconnected W are
allowed. There is no finite-tower restriction, stabilization hypothesis, characteristic
restriction, quasi-compactness, or affineness. The natural-number index includes zero.
The tuple construction in the docstring chooses sections of sets only, never splittings
of epimorphisms as sheaf morphisms.

Searches for an existing exact statement:

- `msearch.py ... leanfinder` query: "On a weakly contractible object of the pro etale
  site, the transition maps and all limit projections of a countable tower of
  epimorphisms of sheaves of sets are surjective". Eight hits: LightProfinite
  transition-map surjectivity; coherent-topology sequential-limit local-surjectivity
  and epimorphism theorems; LightCondensed epimorphism theorem; the epi/local-surjectivity
  criterion. None states both conclusions of this item at an arbitrary W.
- `msearch.py ... loogle` query:
  `CategoryTheory.Limits.Types.surjective_π_app_zero_of_surjective_map`.
  One exact-name hit. Read its signature and docstring in
  `Mathlib/CategoryTheory/Limits/Types/Images.lean`: it handles only the zeroth projection
  of an already surjective set-valued tower and does not give the pro-etale assertion.
- `msearch.py ... grep` query:
  `IsWeaklyContractible|surjective_π_app_zero_of_surjective_map`, subdirectory
  `CategoryTheory`. Five hits in Types/Images and ConcreteCategory/Basic, only the
  generic zeroth-projection theorem and its auxiliary construction.
- `rg` over upstream `WeilConjectures/` for the item id and new declaration name:
  no matches. Searches for weak contractibility and surjective towers in its
  CategoryTheory and AlgebraicGeometry/ProEtale directories found no exact statement.
- `rg` over `lean/Sheaf/` found the generic repleteness definition, the already landed
  weak-contractibility equivalence and downstream repleteness theorem, plus results
  about module-valued evaluation. None gives this pair of conclusions for set-valued
  towers at arbitrary weakly contractible W.
- Read the side framework's
  `WeilConjectures.AlgebraicGeometry.ProEtale.Replete`: its affine-site local-surjectivity
  and pro-etale module-valued epimorphism results do not state this item.
  Read its `CategoryTheory.Sites.WeaklyContractible`: it supplies the notion used here,
  not a sequential-limit statement. Read Mathlib coherent-topology sequential-limit
  declarations: they assume a different site and give local surjectivity at zero.

No STATEMENT-DISPUTED issue or node fault was found. The natural-language statement,
proof, and proof dependencies are unchanged. Only lean and the addition of an existing
landed definition to stmt_deps differ from the repository node.

Validation: prescribed `scompile.py N8 det-pe-replete-on-contractible` compiled the
module in its sandbox form and library-module form, with no warnings or errors
(1.6 s and 1.7 s respectively). Delivery dry-run validation is recorded below.

## Second reading by N8

Independent reading on 2026-10-17. I opened the sandbox node and Lean module,
compared the node with the repository version, and read its blueprint statement,
proof and parent unit. The source is the main-20261015 blueprint node, not an
unmentioned theorem with extra ambient hypotheses. The parent unit concerns every
scheme. For the meaning of weak contractibility I also read Stacks `sites.tex`,
Lemma `lemma-w-contractible` and Definition `definition-w-contractible` (090M):
these concern an arbitrary site and object and impose no affine or connectedness
hypothesis. Their lifting is into the sheaf coproduct of the whole covering,
not necessarily into one member.

Objects, hypotheses and conclusions, listed independently from the node:

1. A scheme X and its small pro-etale site. Lean: `(X : Scheme.{u})`,
   `ProEt.topology X`, with site objects `X.ProEt`. Verdict: exact. I read
   Mathlib `AlgebraicGeometry/Sites/Proetale.lean`: `Scheme.ProEt` is the full
   category of weakly etale X-schemes, `ProEt.precoverage` is the pullback of
   `proetalePrecoverage`, and `ProEt.topology` is its generated topology. This
   uses the recorded `sk-def-pe-site` Mathlib match, not an affine subsite.
2. An inverse sequence of sheaves of sets. Lean:
   `F : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) (Type (max (u + 1) w))`.
   Its adjacent arrow is `F.map (homOfLE (Nat.le_succ n)).op`, with source
   index n+1 and target n. Verdict: exact; functoriality supplies all composites.
3. Every transition is epimorphic. Lean:
   `hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)`.
   Verdict: exact categorical epimorphisms; no assumption of surjectivity on
   every object's sections. I read `Sheaf.isLocallySurjective_iff_epi` in
   Mathlib `Sites/LocallySurjective.lean`, including its `HasSheafify` premise.
   The value universe is at least the object and morphism universes, the usual
   range for set-valued sheafification; no extra instance is a theorem binder.
4. An arbitrary weakly contractible object W. Lean: `(W : X.ProEt)` and
   `hW : (ProEt.topology X).IsWeaklyContractible.{max (u + 1) w} W`.
   Verdict: exact. I opened the recorded side-framework module
   `WeilConjectures.CategoryTheory.Sites.WeaklyContractible` and read the body:
   every locally surjective morphism of set-valued sheaves is surjective at W.
   By the epi criterion this is precisely condition 3 of the node's equivalences.
   It requires neither affineness, a w-contractible coordinate ring, nor a
   section into a single covering member. `sk-def-pe-weak-contractible` is an
   already landed definition node, explicitly added to stmt_deps by the author;
   its existing declaration is used without a private replacement.
5. For every n, the transition evaluated at W is surjective. Lean: the first
   conjunct `∀ n : ℕ, Function.Surjective
   ((F.map (homOfLE (Nat.le_succ n)).op).hom.app (op W))`.
   Verdict: exact, with the prescribed transition and quantifier.
6. For every m, the limit projection evaluated at W is surjective. Lean:
   the second conjunct `∀ m : ℕ, Function.Surjective
   ((limit.π F (op m)).hom.app (op W))`.
   Verdict: exact, using the actual sheaf limit and its coordinate projection,
   including every m rather than only zero or an epimorphism conclusion.
   I read `Sheaf.createsLimitsOfShape` in Mathlib `Sites/Limits.lean`; forgetting
   to presheaves and evaluating preserves this limit, giving exactly the
   source's compatible tuples and coordinate maps.

Dependency interfaces were read, not inferred from names. In particular,
`proetale_weakContractible_equivalences` quantifies over Type (u+1) sheaves and
states the splitting/projectivity/evaluation equivalences plus the affine-ring
assertion. It is imported as the proof dependency. It is not silently applied
at a larger value universe: at that universe the existing polymorphic
`IsWeaklyContractible` definition supplies the evaluation condition itself,
using epi = local surjectivity. `GrothendieckTopology.IsReplete` in
`Sheaf.CategoryTheory.RepleteSheafTopos` uses the same adjacent maps and every
`limit.π F (op m)`, with value universe `max u v w`. Substituting site object
universe u+1 and morphism universe u yields exactly the present value universe.
I also read `coord/pefw-upstream-framework.md` and used the group clone's
framework sources, not the older checkout for absent pro-etale framework files.

Edge cases: n=0 is present and m=0 has no backward extension; m>0 includes all
finitely many earlier stages. The index is specifically ℕ, so an empty indexing
category is outside this node rather than excluded by a hidden hypothesis.
Empty section sets are permitted: a prescribed target section is required only
inside a surjectivity test. Constant empty and singleton towers both fit.
No zero object is assumed for set-valued sheaves. Empty schemes, empty site
objects and disconnected weakly contractible objects are permitted. The empty
object has singleton sections by the sheaf condition for the empty cover.
There are no characteristic, field, finiteness, separation or Noetherian
assumptions. Universes u and w are declared; autoImplicit is false; the site
retains object universe u+1 and morphism universe u, with arbitrary larger
section universe `max (u+1) w`. I found no unbound variable or universe.

Independent searches (recorded with the prescribed msearch wrapper):

- LeanFinder: "Evaluation at a projective representable sends an inverse
  sequence of sheaf epimorphisms to surjections, including every projection
  of its limit". The eight results were coherent-topology and light-condensed
  sequential-limit theorems, projective or profinite projections, and the
  concrete-category zeroth-projection theorem; none states this pair of
  conclusions at arbitrary weakly contractible W.
- LeanSearch: "Surjectivity of sections of inverse limits of sheaves on a
  weakly contractible object". Eight results: topological-space stalk lemmas,
  `Types.limitEquivSections`, and global-section limit formulas. No exact match.
- Loogle: `"IsWeaklyContractible"`. No hits; I used the local definition source
  rather than treating this service's index as evidence that it is absent.
- Prescribed grep: `surjective.*π|π.*surjective|EpiπAppZeroOfEpi` in
  Mathlib/CategoryTheory, plus direct rg in Mathlib Sites and Limits,
  the entire upstream WeilConjectures tree, and the project's Sheaf tree.
  I read the signatures of `Types.surjective_π_app_zero_of_surjective_map`
  and its concrete variant: already-surjective set/concrete towers, index zero.
  Neither includes the sheaf evaluation assertion or every projection.
- I opened the side-framework `ProEtale/Replete.lean`: the affine-site
  local-surjectivity theorem concerns a different site and local lifts at zero;
  `Scheme.ProEt.epi_π_app_zero_of_epi` is module-valued and concludes epi at zero.
  `Sites/WeaklyContractibleProducts.lean` treats module-valued exactness and
  one-minus-transition on products, not this statement. The project's
  `isReplete_proEtale` concludes categorical epimorphism and cites this item;
  it does not replace it. No existing exact declaration was found. The new
  declaration name is absent from upstream, Mathlib and the upstream-name index.

H5/H6/H8/H9 checks: there are no new definitions, auxiliary declarations, new
nodes, dependency-module repairs or corrected statements in this delivery.
The sole theorem body is `by sorry`. Its module and declaration docstrings name
the precise source and blueprint id; the theorem docstring includes all four
node proof steps: transition surjectivity, chosen preimages and forward recursion,
finite backward extension, and the sectionwise-limit identification. Imports
serve statement or proof dependencies, with the equivalence module non-public.
Every Lean line is at most 100 characters. I mechanically compared whitespace-
normalized file signature and lean.statement: identical.

Mismatches and changes: none found in the statement, definitions, source mapping,
proof docstring, or dependency records. I preserved the Lean module and node copy
and appended this independent reading only. No STATEMENT-DISPUTED issue arose.
The required scompile.py invocation compiled the sole delivered file in both
sandbox and library-module forms cleanly (2.2 s and 2.0 s), without warnings.
