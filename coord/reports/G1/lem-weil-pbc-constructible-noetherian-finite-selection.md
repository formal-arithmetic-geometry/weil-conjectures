## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleFiniteSelection` states
`AlgebraicGeometry.Scheme.exists_mono_biproduct_of_constructible_stalk_detection`
and the explicit “in particular” corollary
`AlgebraicGeometry.Scheme.exists_mono_biproduct_of_constructible_stalk_injective`.
Both proofs are `sorry`; no definition or auxiliary theorem was added.

Clause-by-clause correspondence:

- “X Noetherian” is `(X : Scheme.{u}) [IsNoetherian X]`.
- “F a constructible abelian etale sheaf” is
  `F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}` and
  `hF : IsConstructibleEtaleSheafOfSets
  ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F)`.
  Constructibility here means constructibility of its underlying sheaf of sets, hence
  finite geometric stalks, exactly as in the dependency node. The source's abelian-valued
  `IsConstructibleSheaf` uses finitely generated groups instead of finite groups, so it
  is deliberately not used as the finiteness hypothesis.
- The arbitrary index set, target sheaves, and family are `(L : Type w)`,
  `G : L → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`, and `φ : ∀ l : L, F ⟶ G l`.
  No constructibility, finiteness, or torsion condition is imposed on G.
- Every geometric point is quantified as `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`
  and `s : Spec (.of Ω) ⟶ X`, following the dependency's geometric-point convention.
- Every nonzero stalk element is the binder
  `v : ((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F`
  and the premise `v ≠ 0`.
- Some family member detects that element is
  `∃ l : L, (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map (φ l)) v ≠ 0`.
- The finite subset is `∃ L₀ : Finset L`. Its finite direct-sum map is
  `biproduct.lift (fun l : L₀ => φ l.val)`, with target the biproduct of `G l.val`
  indexed by the subtype of selected indices. Its components are exactly the original
  maps, by `biproduct.lift_π`; `Mono` renders monomorphism.
- The “in particular” clause is a second theorem with the same X, F, L, G, φ and conclusion;
  its hypothesis is, for each geometric point, `∃ l : L, Function.Injective` of the
  corresponding stalk map. There is no assertion that a single index works for all points.

Dependencies read and used:

- `def-weil-pbc-etale-sheaves`: `Sheaf.AlgebraicGeometry.EtaleSheaves`, declaration
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleSheafOfSets`; its full definition uses
  `Stratification`, sheafified inverse image, and finite locally constant restrictions.
  Underlying abelian sheaves use the dependency's recorded Mathlib `CategoryTheory.Sheaf`.
- `def-weil-pbc-geometric-stalks`: `Mathlib.CategoryTheory.Sites.Point.Basic`,
  `CategoryTheory.GrothendieckTopology.Point.sheafFiber`, specialized using
  `AlgebraicGeometry.Scheme.pointSmallEtale` from
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`. Its definition is the colimit over the
  opposite category of pointed etale neighbourhoods; applying its functor to φ gives
  the stalk homomorphism.
- Mathlib's `biproduct.lift` and `HasFiniteBiproducts.of_hasFiniteProducts` are used.
  The latter is enabled as a local instance, supplying a structural consequence of the
  sheaf category's existing finite products and preadditivity, without a new hypothesis.

Edge cases checked before writing: empty X (geometric-point conditions vacuous), zero F
(the detection condition vacuous), empty L (the detection hypothesis then forces zero
stalks), empty chosen L₀ (the empty biproduct is the zero object), arbitrary size w of L,
nonzero stalk elements with varying detecting indices, and arbitrary target sheaves.
There is no field-characteristic restriction. The “in particular” hypothesis is sufficient
because each stalk morphism is an additive homomorphism and sends zero to zero.

Searches for an existing statement:

- msearch leanfinder, query “finite selection of stalk detecting maps from a constructible
  etale sheaf is monomorphic”: eight hits, including topological stalk-mono criteria and
  `Sheaf.mono_of_isLocallyInjective`; none selects a finite subfamily on the etale site.
- msearch loogle, query `"IsConstructibleSheaf"`: zero hits.
- msearch grep, query `constructible.*finite.*selection|finite.*stalk.*mono`: zero hits.
- msearch leansearch, query “finite selection of morphisms from constructible etale sheaf
  detects every geometric stalk”: service unavailable (Internal Server Error).
- rg on WeilConjectures and lean/Sheaf for constructible sheaves, finite selection,
  stalk detection, and finite-subfamily mono names found constructibility definitions
  and finite-pushforward embedding results, but no matching declaration. The upstream
  `ConstructibleSheaf/FinitePushforward.lean` theorem constructs finite pushforwards and
  does not select indices from an arbitrary given family.
- grep of the item id in WeilConjectures found no tagged declaration. rg of the chosen
  declaration names in Mathlib, WeilConjectures, lean/Sheaf, and
  dag/lean_names_upstream.json found no collision.

The local literature payload is not present on this remote machine. The dependency and
item node records were read in full; the cited partition argument was checked against
https://stacks.math.columbia.edu/tag/09Z6 (Lemma 59.74.3, proof of (1), partition alternative;
proof of (2) follows the same argument). The source's actual lemma is a finite-pushforward
embedding, and the node explicitly adapts its partition method to a given detecting family.
The module docstrings reproduce all four DAG proof steps and their dependency ids.
No statement correction or disputed statement is needed.

Validation: server compilation type-checked both declarations. The initial long-line
warning was repaired. The final delivery dry run is recorded by the tool output.


## Second reading by G1

Independent reading of the item JSON and both declarations in
`lean/Sheaf/AlgebraicGeometry/ConstructibleFiniteSelection.lean`, followed by the
complete statement dependencies and their source definitions. Verdict: the Lean says
exactly what the node says; no mathematical or signature repair is necessary.

Object/hypothesis/conclusion checklist (written from the node before matching):

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| A scheme X, Noetherian | `(X : Scheme.{u}) [IsNoetherian X]` | Exact. Mathlib's class includes local Noetherianity and quasi-compactness, not an extra separatedness assumption. |
| An abelian sheaf F on the small etale site | `F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}` | Exact category, using the dependency's existing Mathlib sheaf construction. |
| F constructible | `hF : IsConstructibleEtaleSheafOfSets ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F)` | Exact finite constructibility of the underlying sets, as stipulated by the dependency and the node's finite-stalk proof. |
| An arbitrary indexing set L | `(L : Type w)` | Exact; independent universe w, no Fintype or Nonempty hypothesis. |
| Arbitrary abelian target sheaves indexed by L | `G : L → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}` | Exact; no additional property of G. |
| Given maps from F to these targets | `φ : ∀ l : L, F ⟶ G l` | Exact; the selected maps are these same morphisms. |
| Every geometric point | `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)` | Exact dependency convention, no chosen base field or characteristic. |
| Every nonzero element of its stalk | `v : ((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F`, followed by `v ≠ 0 →` | Exact additive stalk and nonzero premise. |
| Some family member detects this element | `∃ l : L, (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map (φ l)) v ≠ 0` | Exact quantifier order: l may depend on both s and v. |
| There is a finite subset of the original L | `∃ L₀ : Finset L` | Exact, permitting the empty finite subset. |
| Its component map to the finite direct sum is a monomorphism | `Mono (biproduct.lift (fun l : L₀ => φ l.val))` | Exact. The subtype indexes precisely the selected elements, and `biproduct.lift_π` identifies its components with φ. |
| In particular, at each geometric point some single map is injective | The second theorem has `hφ : ∀ Ω [Field Ω] [IsAlgClosed Ω] s, ∃ l : L, Function.Injective (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map (φ l))` and the same finite-subset conclusion | Exact; no requirement that one l work at all points. Both clauses are recorded in `lean.declarations`. |

Dependency inspection: opened `def-weil-pbc-etale-sheaves` in full and
`Sheaf.AlgebraicGeometry.EtaleSheaves`. Its `IsConstructibleEtaleSheafOfSets`
is an existential `Stratification` followed by finite locally constant set-sheaf
pullback on every stratum. Read `etaleSetPullback`,
`IsLocallyConstantEtaleSheafOfSets`, and `IsFiniteLocallyConstantEtaleSheafOfSets`:
the inverse image is sheafified left Kan extension along base change; local
constancy is restriction over an etale cover; finiteness means `Finite` at each
geometric stalk. Read the source's `Scheme.Stratification` in
`WeilConjectures/ConstructibleSheaf/Defs.lean`: finite partition, constructible
locally closed strata, immersed schemes with the prescribed images. These are
precisely the dependency's notions, without a private definition here.

Opened `def-weil-pbc-geometric-stalks` and both of its recorded declarations.
`pointSmallEtale` in Mathlib's `AlgebraicGeometry/Sites/EtalePoint.lean` uses lifts
of s to etale neighbourhoods; `presheafFiber` and `sheafFiber` in
`CategoryTheory/Sites/Point/Basic.lean` take the opposite-category-of-elements
colimit and restrict it to sheaves. Thus `.map (φ l)` is the required stalk map.
The local `HasFiniteBiproducts.of_hasFiniteProducts` attribute provides an existing
structural consequence, not a hypothesis on the node's objects.

Source reading: local literature payloads are absent. Independently retrieved
`https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex`
and read `lemma-constructible-maps-into-constant` through the end of its proof;
also checked https://stacks.math.columbia.edu/tag/09Z6. Its assumption is a
Noetherian scheme, and its abelian case has finite abelian stalk values. The ring
assumption belongs only to the separate module case, so none belongs here.
The node adapts the partition alternative in proof (1), with the same argument
for (2), to an arbitrary given detecting family; it does not claim to state the
source's finite-pushforward conclusion. The Lean docstring carries the node's
four steps: irreducible lisse stratification; one index per nonzero generic
stalk element; generic-kernel propagation and finite union; exact and
conservative geometric stalks. The corollary docstring explains nonzero
detection from injectivity and invokes that same argument. All cited proof
nodes are named. No source hypothesis was lost.

Edge cases: empty X is allowed (geometric-point premises vacuous); zero F is
allowed (nonzero-element premise vacuous). Empty L is allowed: detection then
forces zero stalks and the empty selection suffices. For the corollary, empty L
on nonempty X does not satisfy its existential premise, as the node requires.
Empty L₀ gives the zero biproduct. There is no integer n or characteristic
parameter to restrict. Universes u and w are explicitly bound. The sheaf-value
universe u+1 and geometric-field universe u agree with the dependency/site
conventions; enlarging u covers larger schemes, fields and sheaf values, while
w remains independent. Geometric points given over larger algebraically closed
fields give the same etale stalk tests after field extension; algebraic closures
of residue fields in u already test every point. No extra cardinality or
finiteness restriction on L or the targets is present.

Independent searches with different wording:

- msearch leanfinder: “A finite subfamily of homomorphisms separates elements of
  every stalk of a finite locally constant sheaf”. Eight results, mainly
  `Profinite.exists_locallyConstant_finite_aux` and locally constant functions;
  none states this etale sheaf selection theorem.
- msearch loogle: `"biproduct.lift"`. Ten results; checked the lift signature
  and projection identity. These implement the finite-sum map, not this theorem.
- msearch leansearch: “Noetherian constructible sheaf monomorphism into finite
  product of a given separating family”. Service unavailable, Internal Server
  Error; recorded as unavailable, not as a negative mathematical result.
- msearch grep: `stalk_detection|stalk_injective|finite_subfamily.*sheaf|sheaf.*finite_subfamily`.
  Zero hits.
- Direct rg over Mathlib, WeilConjectures, project lean/Sheaf and
  dag/lean_names_upstream.json for finite subfamilies, separation, stalk detection,
  constructible injections and the proposed declaration names. No matching
  theorem or name collision. Opened the nearby
  `Etale.exists_mono_biproduct_lowerStar_of_isNoetherian` in
  `ConstructibleSheaf/FinitePushforward.lean`: it existentially constructs finite
  pushforward targets and a new map, rather than selecting from the given φ.
  It therefore cannot replace this statement. Also read the source's
  `IsConstructibleSheaf` and `IsFiniteSheaf`: their abelian finiteness is finite
  generation, which is not the finite underlying-set notion specified here.

No new definition nodes or dependency modules were delivered; both dependencies
are usable as recorded. No `statement_change` is present or necessary. No hollow
definition or proved lemma was introduced: the module has no definitions and
exactly the two named `sorry` theorem proofs. All imports serve the sheaf
predicates, Noetherian scheme condition or biproduct construction. No variable
or universe is unbound. Both declaration docstrings and the module header have
the source and blueprint tag; all lines are at most 100 characters.

Mismatch/repair log: none. Kept the correct module and node record unchanged;
appended this independent second reading and its source/search evidence. Checked
by script that `lean.statement` is verbatim the main theorem signature, excluding
`:= by`. Server scompile compiled the complete delivered module cleanly in 1.9 s
(exit 0, no warnings).
