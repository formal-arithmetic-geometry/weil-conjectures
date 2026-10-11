## Worker report

The module `Sheaf.Topology.SheafCokernelLocalImage` states
`SheafOfModules.sheafified_cokernel_local_image`, with its sole proof `sorry`.
It defines no new notion and changes only the item's `lean` record.

Clause-by-clause correspondence:

- A ringed space is the unbundled pair `{X : Type (max u v)} [TopologicalSpace X]`
  and `R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}`. The topology is the
  ordinary opens topology. The ambient universe `max u v` simultaneously accommodates
  the opens and module sections; `v` is the ring universe. No finite-dimensional,
  nonempty, commutative-ring, or scheme condition is imposed.
- The two sheaves of modules and their morphism are
  `{F G : SheafOfModules.{max u v} R}` and `(φ : F ⟶ G)`.
  `SheafOfModules` is exactly the recorded Mathlib declaration of
  `def-weil-sheaf-of-modules-category`.
- The sectionwise quotient presheaf `P` is `cokernel φ.val` in the category of
  presheaves of `R.obj`-modules. This is a categorical choice of the quotient,
  rather than a second quotient definition: evaluation preserves cokernels by
  `PresheafOfModules.Finite.evaluation_preservesFiniteColimits`. In `ModuleCat`,
  `ModuleCat.cokernelCocone` uses `G(V) ⧸ LinearMap.range (φ_V).hom` and its `mkQ`.
  Its universal-property isomorphism identifies the categorical choice with exactly
  that quotient, preserving the quotient map. No arbitrary substitute presheaf is used.
- `P^#` is `(PresheafOfModules.sheafification (𝟙 R.obj)).obj (cokernel φ.val)`.
  This is the existing module-sheafification construction from
  `def-weil-presheaf-modules-sheafification`, already a proof dependency of the item.
  Its underlying sheaf of abelian groups is definitionally
  `(presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj P.presheaf`,
  the recorded sheafification of `def-weil-pbc-sheafification`. There is no
  specialized replacement of either dependency.
- The binder `q` has precisely the required source `G` and target `P^#`.
  `hq` fixes its underlying abelian-presheaf map to the quotient projection
  followed by `toSheafify`. It spells out the node's instruction “let q be the
  composite”; it does not assume exactness, local lifting, or any constraint on φ.
  Such a map always exists: use the inverse sheafification counit at `G` followed
  by the sheafification of `cokernel.π φ.val`. Restriction of scalars along the
  identity is the identity functor, and the counit is an isomorphism.
- The kernel subsheaf is described by its sections: for every open `V` and section
  `s`, the first conjunct asserts `q.val.app (op V) s = 0 ↔ ...`.
  Kernels of sheaves of modules are computed sectionwise, so this describes the
  entire kernel as a subsheaf of `G`, including its inherited module structure,
  rather than merely its global sections or stalks.
- “Locally in the image” is
  `∀ x : X, x ∈ V → ∃ (W : Opens X) (hWV : W ≤ V), x ∈ W ∧ ∃ t, ...`.
  The last equality is exactly
  `φ.val.app (op W) t = G.val.map (homOfLE hWV).op s`.
  Neighborhoods at every point are equivalent to an open covering of `V`.
  Conversely every member of an open covering is such a neighborhood for the
  points it contains. Thus this has the same local meaning as the node.
- The two consequent clauses are the remaining conjuncts `Epi q` and `φ ≫ q = 0`.
  Lean's composition order is first φ, then q, hence the node's `q ∘ φ`.

Dependency signatures and source inspection:

- `Mathlib.Algebra.Category.ModuleCat.Sheaf`, `SheafOfModules` and its `Hom`:
  a presheaf of modules with its underlying abelian presheaf a sheaf, and linear
  component maps commuting with restriction.
- `Mathlib.CategoryTheory.Sites.Sheafification`,
  `CategoryTheory.presheafToSheaf`, `sheafificationAdjunction`, `toSheafify`:
  the left adjoint to inclusion and its unit, as the recorded dependency states.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`,
  `PresheafOfModules.sheafification`, `sheafificationCompToSheaf`,
  `sheafificationAdjunction`: inspected their full signatures/docstrings; at
  `𝟙 R.obj` these supply the existing module sheafification, whose underlying
  abelian sheafification is the previous dependency's functor.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits`,
  `PresheafOfModules.Finite.evaluation_preservesFiniteColimits`, and
  `Mathlib.Algebra.Category.ModuleCat.Kernels`, `ModuleCat.cokernelCocone`:
  the pointwise cokernel identification above. These are Mathlib infrastructure,
  not missing definitions.

The local literature checkout has no Stacks `.tex` files. I read the source at
[Stacks 01AH](https://stacks.math.columbia.edu/tag/01AH) and
[Stacks 00WK](https://stacks.math.columbia.edu/tag/00WK): the former specifies
sheafified presheaf colimits and sectionwise limits; the latter supplies local
representatives in sheafification. The four-step proof in the docstring follows
all four steps of the existing DAG proof, including its references to 00WB/00WK.
No statement correction or disputed clause was needed.

Edge cases checked before writing:

- `V = ⊥`: the local predicate has no points to quantify over; by the sheaf axiom
  the section module on the empty open is zero, so the kernel criterion still holds.
  This also covers the empty space and an empty covering.
- `F = 0` or `φ = 0`: local-image sections are locally zero and hence zero; the
  sheafification of the presheaf quotient recovers `G` and q is an isomorphism.
- `G = 0`: all clauses hold with the zero quotient and zero morphism.
- An isomorphism φ gives zero quotient and every section lifts, as required.
- There are no restrictions on the characteristic, nonzero ring, or size of an
  open cover. The pointwise neighborhood formulation avoids an independent cover
  index universe. All Lean universes and variables are explicitly bound.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leansearch "The kernel of the sheafification of the quotient of
  sheaves of modules consists of sections locally in the image"`: service
  unavailable (Internal Server Error), recorded as unavailable, with no verdict.
- `msearch.py ... leanfinder "kernel of sheafified quotient consists of sections
  locally in the image and quotient map is epi"`: eight hits, all set-valued
  `Sheaf.image`, `imageι`, `toImage`, their local-injectivity/epi statements, and
  `imageFactorization`; none states this module quotient/kernel theorem.
- `msearch.py ... loogle "PresheafOfModules.sheafification, SheafOfModules,
  cokernel.π"`: zero hits; Loogle did not recognize the unqualified `cokernel.π`.
  The subsequent direct source reading found its standard categorical definition.
- `msearch.py ... grep "cokernel|locally.*image|toRangeSheafify"
  Algebra/Category/ModuleCat`: 25 hits, including module quotient cocones and
  finite presentations, but no local-image theorem for sheafified quotients.
- `rg -n "cokernel.*local|local.*image|lem-weil-pbc-sheaf-cokernel-local-image"`
  in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project's
  `lean/Sheaf`: scheme-specific local-image results in `Modules/GeneratingLocus`
  and `Modules/QuasicoherentKernel`, constructible-sheaf results, and a citation
  of this item in `Modules/QuasiCoherentCokernelImage`; none is the ringed-space
  statement. The project's quasi-coherent cokernel/image theorem imposes a scheme
  and quasi-coherence and therefore cannot supply this item.
- Direct `rg` for `sheafified_cokernel_local_image` in Mathlib, `WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no name collision.

Validation: server compilation of the final module succeeded in 1.9 seconds,
with no warnings or errors. The only proof is the required theorem's `sorry`.

## Second reading by K1

I read the sandbox node and theorem independently, then the recorded dependency
signatures in Mathlib. There is no `statement_change`, new node, or dependency
module in this delivery. The node's statement and its Lean signature need no repair.

Source checked: the local repository has no Stacks checkout, so I fetched the
upstream `modules.tex` and `sites.tex` into this item's `scratchpad/` and read the
source TeX, including the surrounding assumptions. In `modules.tex`, section
`section-kernels` assumes only a ringed space; its preceding `section-pathology`
explicitly permits the zero ring sheaf. The sectionwise kernel and sheafified
quotient construction precedes `lemma-limits-colimits` (01AH, lines 204–243).
In `sites.tex` I read `theorem-plus` (00WB) with its proof and
`lemma-sections-sheafification` (00WK). Neither adds geometric, finiteness,
nonemptiness, characteristic, or local-ring hypotheses. Source links:
[01AH](https://stacks.math.columbia.edu/tag/01AH),
[00WB](https://stacks.math.columbia.edu/tag/00WB), and
[00WK](https://stacks.math.columbia.edu/tag/00WK).

The list of objects, hypotheses, and conclusions, with their Lean renderings:

1. A topological space X and a sheaf of rings O_X: `{X : Type (max u v)}`,
   `[TopologicalSpace X]`, and `R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}`.
   This is the unbundled ringed space, with exactly the opens topology. Verdict:
   matches; no scheme, separation, commutativity, or nonzero hypothesis added.
2. Two sheaves of O_X-modules and a linear sheaf morphism: the binders
   `{F G : SheafOfModules.{max u v} R}` and `(φ : F ⟶ G)`.
   I opened `SheafOfModules` and `SheafOfModules.Hom` in
   `Mathlib/Algebra/Category/ModuleCat/Sheaf.lean`: the underlying module
   presheaf is an abelian sheaf and the maps are presheaf-module morphisms.
   This is precisely `def-weil-sheaf-of-modules-category`'s recorded match.
   Verdict: matches the dependency, without another definition.
3. P(V) = G(V)/φ_V(F(V)), with induced restrictions: `cokernel φ.val`.
   I opened `PresheafOfModules.Finite.evaluation_preservesFiniteColimits`
   in `Presheaf/Colimits.lean` and `ModuleCat.cokernelCocone`,
   `cokernelIsoRangeQuotient`, and `cokernel_π_cokernelIsoRangeQuotient_hom`
   in `ModuleCat/Kernels.lean`. They identify evaluation of this chosen
   cokernel with the quotient by the linear range, including the quotient map.
   Verdict: the same presheaf up to its canonical quotient isomorphism.
4. P^# and the canonical composite q: the target of `q` is
   `(PresheafOfModules.sheafification (𝟙 R.obj)).obj (cokernel φ.val)`.
   I opened `presheafToSheaf`, `sheafificationAdjunction`, and `toSheafify`
   in `Sites/Sheafification.lean`, and module `sheafification`,
   `sheafificationCompToSheaf`, and `sheafificationAdjunction` in
   `Presheaf/Sheafification.lean`. They are the recorded matches of
   `def-weil-pbc-sheafification` and `def-weil-presheaf-modules-sheafification`.
   The module functor has precisely the ordinary abelian sheafification as
   underlying sheaf. `hq` identifies the underlying q with the quotient
   projection followed by the unit; it constrains construction data only.
   A compatible module map always exists because the unit is linear and
   forgetting module sheaves is full. Verdict: the canonical composite,
   with no extra assumption on φ or F or G and no missing definition.
5. Kernel equals the subsheaf of locally image sections: the first conjunct
   quantifies over every `V : Opens X` and `s : G.val.obj (op V)` and asserts
   `q.val.app (op V) s = 0 ↔ ...`. The right side chooses for each `x ∈ V`
   an open `W ≤ V` containing x and `t : F.val.obj (op W)` with
   `φ.val.app (op W) t = G.val.map (homOfLE hWV).op s`.
   These neighborhoods cover V; any covering with lifts gives these
   neighborhoods. Sectionwise equality of these subsets of G gives the
   claimed equality of subsheaves, including the induced module operations.
   Verdict: all sections, both directions, and the same quantifier order.
6. q is an epimorphism: the second conjunct `Epi q` is categorical epicness
   in the same module-sheaf category. Verdict: matches; no sectionwise
   surjectivity substituted.
7. q ∘ φ = 0: the final conjunct is `φ ≫ q = 0`. Verdict: exactly the
   claimed composite in Lean's diagrammatic order.

Edge cases: on the empty open (and the empty space), the neighborhood predicate
is vacuous, while the sheaf axiom makes its section module zero, so the iff is
correct. No nonempty cover/index binder excludes the empty cover. For φ = 0 or
F = 0 the local-image subsheaf is zero by separatedness and q identifies G with
its sheafification. For G = 0 all the conclusions remain valid; for invertible φ
the quotient is zero and every section lifts. The zero ring sheaf is allowed.
There is no integer n or characteristic condition in this node. The universes
u and v are explicitly bound; the opens site and module carriers have universe
`max u v`, providing the required small-site sheafification instances for every
ambient size (smaller carriers can be lifted). There is no independent covering
index universe or assumed `HasSheafify` instance which could exclude spaces.

Independent searches, using different wording from the first worker:

- LeanSearch: `Sheaf of modules quotient projection has kernel the local range
  of a linear morphism` returned Internal Server Error; recorded unavailable,
  not as evidence of absence.
- LeanFinder: `A section is killed in the cokernel sheaf if and only if it locally
  lifts through the morphism of module sheaves` returned eight free-presentation
  helpers (`generatorsOfIsCokernelFree`, `relationsOfIsCokernelFree` and their
  projections) in `Sheaf/Quasicoherent`, not this arbitrary morphism theorem.
- Loogle: `PresheafOfModules.toPresheaf, CategoryTheory.Limits.cokernel`
  returned zero hits.
- Direct rg in Mathlib's module categories, Sites, and topological sheaves, and
  in `WeilConjectures` and the project's `lean/Sheaf`, using local/range/image,
  kernel/sheafification, and cokernel/local variants. The ModuleCat range
  quotient lemmas are infrastructure; Sites locally injective/surjective unit
  lemmas do not state this module quotient/kernel theorem. I opened the source's
  `Scheme.Modules.epi_of_forall_exists_app_eq` in `QuasicoherentKernel.lean`:
  it is scheme-specific, assumes local lifting, and has no kernel criterion.
  The project's `quasiCoherent_cokernel_image` in `QuasiCoherentCokernelImage.lean`
  assumes a scheme and quasi-coherence and cites this item. Neither is a match.
  No existing declaration supplies the whole node; the new theorem is retained.

Mismatch and repair: the signature, node record, dependencies, and mathematical
clauses were right and are unchanged. The theorem docstring's fourth proof step
omitted the node's explicit observation that φ factors through the local-image
subsheaf. I added that sentence, explaining that its sections are images.
The four proof steps now carry the quotient construction, local vanishing,
subsheaf/kernel identification, factorization, and epimorphism argument.
There are no definitions or auxiliary proofs; the sole theorem remains `sorry`.
All imports provide the module sheafification, opens-site interpretation, or its
concrete sheafification/filtered-colimit instances. Names, docstring source/id,
100-character width, and explicitly bound variables/universes were checked.

Validation of the repaired module: `scompile.py` compiled it on the server in
1.9 seconds with exit code 0 and no warnings or errors. A direct comparison
confirmed that `lean.statement` is verbatim the theorem signature. The delivery
dry run passed compilation and all stage-2 preflight checks.
