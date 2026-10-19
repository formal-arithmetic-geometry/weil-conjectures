## Worker report

The module defines `etale_section_zero_open`, stating the zero locus theorem for a section of an abelian sheaf on the small étale site. The scheme `T`, sheaf `F`, étale object `V`, and section `s` render the hypotheses exactly. The existential `W` and inclusion `i` render the largest open subset; `IsOpenImmersion i.left` says it is Zariski open. The restriction clause uses `F.1.map h.op s = 0` and characterizes vanishing by `Set.range h.left ⊆ Set.range i.left`. The geometric-stalk clause quantifies separably closed fields and geometric points `v`, uses `pointSmallEtale` and `toPresheafFiber` for the germ, and characterizes membership in the open by factorization through `i`.

Dependencies are Mathlib declarations: `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.smallEtaleTopology`, `CategoryTheory.Sheaf`, and `CategoryTheory.GrothendieckTopology.Point.sheafFiber`/`AlgebraicGeometry.Scheme.pointSmallEtale`; all are imported from Mathlib modules. No project dependency module was needed.

Edge cases checked include the empty open (represented by an étale object with open immersion), the zero section (the whole object satisfies the restriction equivalence), arbitrary and empty covering behavior through the sheaf object, and geometric points over any separably closed field.

Searches for an existing declaration: `msearch.py ... leanfinder` for “zero locus of section of etale abelian sheaf is open” returned only structure-sheaf and general stalk results; `loogle` for `stalk, zero` returned unrelated stalk-rank/is-zero lemmas; Mathlib grep for open-map and zero-locus signatures found no theorem for arbitrary abelian étale sheaves; `rg` over WeilConjectures and `lean/Sheaf` found no matching declaration. Therefore a new statement module is required.

## Earlier second reading (a previous round; superseded)

Read the node and module independently. The three hypotheses and all three conclusion clauses match: openness is `IsOpenImmersion`, restriction is the iff with image containment, and the germ criterion is the iff with factorization through the open immersion. No mismatch was found.


## Second reading by NB

I read the node, Stacks `etale-cohomology.tex`, lemma `lemma-zero-over-image`
(Tag 04FR), and the actual Mathlib declarations independently. The surrounding
section assumes only schemes and abelian étale sheaves, with no finiteness,
Noetherian, separation, or characteristic hypothesis. The node agrees with the
source; no statement correction is needed.

Object/hypothesis/conclusion checklist:

1. Scheme T: `(T : Scheme.{u})`, using `AlgebraicGeometry.Scheme` from
   `def-pc-scheme`. I opened its locally ringed space/local-affineness definition
   and scheme morphisms in `Mathlib.AlgebraicGeometry.Scheme`. Verdict: exact.
2. Small étale site: `T.smallEtaleTopology`, with objects `T.Etale`. I opened
   `Scheme.Etale` in `Mathlib.AlgebraicGeometry.Morphisms.Etale`: its objects
   are étale scheme maps to T and its morphisms are T-morphisms; the instance
   makes each such arrow étale. I opened `smallEtaleTopology` and
   `ofArrows_mem_smallEtaleTopology_iff` in `Mathlib.AlgebraicGeometry.Sites.Etale`:
   covers are jointly surjective families. These are precisely the declarations
   recorded by `def-weil-pbc-etale-site`. Verdict: exact.
3. Abelian sheaf F: `(F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})`.
   I opened `CategoryTheory.Sheaf` in `Mathlib.CategoryTheory.Sites.Sheaf`, the
   full subcategory of presheaves satisfying the sheaf condition. This uses the
   coefficient convention explicitly recorded by `def-weil-pbc-abelian-etale-sheaves`.
   No local constancy, constructibility, or torsion hypothesis. Verdict: exact.
4. Étale object p:V→T: `(V : T.Etale)`, with the structure map `V.hom`.
   Section s: `(s : (F.1.obj (Opposite.op V) : AddCommGrpCat.{u + 1}).carrier)`.
   Thus s is an element of this sheaf at this very object, rather than a section
   of a structure sheaf. Verdict: exact.
5. Largest Zariski open W⊆V with zero restriction: `∃ (W : T.Etale) (i : W ⟶ V),
   IsOpenImmersion i.left ∧ ...`. Its underlying open is `Set.range i.left`.
   The restriction iff with `V' = W`, `h = i` forces `s|W = 0`; with an arbitrary
   open subscheme of V it forces every other vanishing open to be contained in
   this one. Conversely every literal open of V gives such an étale T-object.
   This is equivalent to clause (1), without an extra uniqueness-of-presentation
   assertion. Verdict: exact.
6. Every site morphism h:V'→V, restriction iff image containment:
   `∀ (V' : T.Etale) (h : V' ⟶ V),
   (F.1.map h.op) s = 0 ↔ Set.range h.left ⊆ Set.range i.left`.
   Arrows are all T-morphisms, not just open immersions or covers. Quantifiers
   follow the existential W, so the same open works for all arrows. Verdict: exact.
7. Every geometric point of V: `∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
   (v : Spec (.of Ω) ⟶ V.left), ...`. I opened `Scheme.pointSmallEtale` in
   `Mathlib.AlgebraicGeometry.Sites.EtalePoint`: its fiber at an étale object is
   exactly the set of lifts of this geometric point. `v ≫ V.hom` is p v.
   Verdict: exact, including separably closed rather than algebraically closed fields.
8. Germ zero in F at p v iff v belongs to W:
   `(pointSmallEtale (v ≫ V.hom)).toPresheafFiber V (Over.homMk v) F.1 s = 0 ↔
   ∃ (y : Spec (.of Ω) ⟶ W.left), y ≫ i.left = v`.
   I opened `Point.presheafFiber`, `Point.toPresheafFiber` (the coprojection at
   this pointed object), and `Point.sheafFiber` (the underlying-presheaf fiber)
   in `Mathlib.CategoryTheory.Sites.Point.Basic`. This is the recorded notion
   of `def-weil-pbc-geometric-stalks`, definitionally the stalk of F, not a
   Zariski stalk. Factorization through an open immersion is equivalent to
   membership of the geometric point's underlying point in its image; Spec Ω
   has one point. Verdict: exact; no choice of residue-field closure is fixed.

Edge cases: no inhabitance assumptions on T, V, W, or a cover. The empty scheme
and empty vanishing open are permitted, and the empty cover forces zero sections
on the empty object. For s=0 the universal criterion forces the open image to
be all of V (take h the identity); the zero sheaf is permitted. All field
characteristics are admitted; no coefficient integer n or restriction n≠0 is
present. The only universe binder is explicitly `u`; scheme and geometric-field
universes follow `pointSmallEtale` exactly, and coefficients are explicitly
`AddCommGrpCat.{u + 1}` as the dependency requires. No free universe or variable
is left to auto-implicit elaboration.

Independent searches (2026-10-15), using words other than the worker's:

- LeanFinder via msearch: “vanishing germ of an abelian sheaf section on the
  etale site is an open condition”. Eight results, including
  `RingedSpace.exists_res_eq_zero_of_germ_eq_zero`, `Scheme.zero_of_zero_cover`,
  and `RingedSpace.basicOpen`; these concern the structure sheaf, not arbitrary
  étale abelian sheaves with all three conclusion clauses.
- Loogle via msearch: `"toPresheafFiber"`. Twelve results in
  `CategoryTheory.GrothendieckTopology.Point.Basic`, including coprojection
  naturality and equality detection. These are usable general stalk tools,
  not the largest open/image/geometric-germ theorem.
- LeanSearch via msearch: “For an abelian sheaf on the small etale site, a local
  section vanishes precisely on a largest open subscheme”. Service returned
  Internal Server Error; unavailable, no mathematical verdict inferred.
- Direct rg across all pinned Mathlib, WeilConjectures, project lean/Sheaf, and
  upstream-name records for `etale_section_zero_open`, `zero.over.image`,
  vanishing sections, zero loci, and open germ/zero signatures. No exact
  declaration or name collision. I opened the candidate
  `TopCat.Sheaf.isClopen_setOf_germ_eq_zero_of_locallyConstant`: it is about a
  topological sheaf with an extra local-constancy hypothesis, so cannot replace
  this statement. Upstream `stalkZeroLocus` concerns vanishing of whole sheaves,
  whereas the present node concerns an individual section.

Mismatches and repairs: the mathematical clauses were correct. The file lacked
its module/public-section header and public statement imports; I restored the
project conventions, removed redundant imports, and put the declaration in
`AlgebraicGeometry.Scheme`. I made the coefficient universe explicit in F and s,
following the dependency record. The earlier compressed proof docstring omitted
the explicit small affine cofinal indexing and integer-module zero-detection
steps: I expanded it to the node's five numbered steps, naming their dependencies,
and imported the corresponding Mathlib proof modules. The node lean record now
has the qualified declaration and the signature verbatim from the file.

No new nodes, dependency modules, private notions, hollow definitions, or proof
work were needed. The only theorem still has proof `sorry`. Server compilation
through scompile.py passed in 1.4 seconds, nice 19, two threads, 60-second limit,
with no errors or warnings.
