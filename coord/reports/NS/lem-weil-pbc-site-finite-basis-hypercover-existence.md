## Worker report

The module `Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence` states
`CategoryTheory.exists_site_finite_basis_hypercover`, with `sorry` as its entire proof.
No new definition, dependency repair, or statement correction is needed.

Hypothesis and conclusion correspondence:

- Small site: `{C : Type u} [SmallCategory C]` and `J : Precoverage C`, with
  `J.HasIsos`, `J.IsStableUnderComposition`, `J.IsStableUnderBaseChange`, use the exact
  site encoding recorded by `def-weil-pbc-sites-and-cohomology`. The globally assumed
  `[HasPullbacks C]` supplies fibre products (and hence pullbacks along covering arrows);
  a redundant additional `J.HasPullbacks` hypothesis is unnecessary.
- Chosen set of objects: `(B : Set C)`.
- Every object has a finite basis cover: `hcover` quantifies over every `T`, with
  witnesses `I : Type u`, `U : I → C`, and `f : ∀ i, U i ⟶ T`, asserting `Finite I`,
  `∀ i, U i ∈ B`, and `Presieve.ofArrows U f ∈ J T`.
- Adjoining a basis arrow to any finite basis cover: `hadjoin` quantifies over
  every finite `I`, family `U`, and `f`, with precisely the basis and covering premises,
  then every `V ∈ B` and `g : V ⟶ T`. Its conclusion is membership of
  `Presieve.ofArrows U f ⊔ Presieve.singleton g` in `J T`.
- For each `T`: the last binder `(T : C)` is arbitrary, followed by existential `K`.
- Augmented simplicial formal family: `K : SimplicialObject (FormalCoproduct.{u} (Over T))`.
  Each component is an object of `Over T`, hence has its displayed arrow to `T`;
  every component of every simplicial operator is an over-morphism. This provides the
  canonical augmentation to the singleton terminal family, commuting with all operators.
  The functor laws encode all face, degeneracy, and mixed simplicial identities.
- Finite terms: `∀ n, Finite (K _⦋n⦌).I`.
- Basis members: `∀ n i, ((K _⦋n⦌).obj i).left ∈ B`.
- Proper-face matching objects: `M n : Cone (K.properFaceDiagram n)` and
  `∀ n, Nonempty (IsLimit (M n))` give precisely the compatible proper-face limit.
  The matching map `μ n` is characterized by its composite with every cone projection
  being `K.map a.obj.hom.op`. Its uniqueness follows from the limit property; it is
  not an arbitrary unconstrained map.
- Degree zero: `(M 0).pt = (FormalCoproduct.incl (Over T)).obj (Over.mk (𝟙 T))`.
  The proper-face category is empty here, so the cone is terminal and `μ 0` is the
  canonical augmentation. This equality chooses the specified representative, without
  requiring any extra structure on `C`.
- Componentwise covering: for each `n` and `j : (M n).pt.I`, the source index type
  is `{i : (K _⦋n⦌).I // (μ n).f i = j}`. `Presieve.ofArrows` lists exactly the
  underlying component arrows, transported along the index equality by `eqToHom`.
  Membership in `J ((M n).pt.obj j).left` is precisely the given site's covering
  condition, rather than merely covering in its associated Grothendieck topology.

Dependency declarations used:

- `Mathlib.CategoryTheory.Sites.Precoverage`: `CategoryTheory.Precoverage`,
  `Precoverage.HasIsos`, `Precoverage.IsStableUnderComposition`, and
  `Precoverage.IsStableUnderBaseChange`, as recorded for the site dependency.
  Their signatures and docstrings were read, including the pullback and composition axioms.
- `Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic`:
  `CategoryTheory.Limits.FormalCoproduct`, its `Hom` fields `f` and `φ`, category instance,
  and `FormalCoproduct.incl`. The full source signatures and docstrings were read.
- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`: `CategoryTheory.SimplicialObject`,
  the functor category `SimplexCategoryᵒᵖ ⥤ C`, with faces and degeneracies supplied by
  functoriality (read the full definitions of `δ` and `σ`). This is imported transitively
  through the proper-face module, which already imports the recorded matching module.
- `Sheaf.CategoryTheory.ProperFaceMatchingObject`:
  `CategoryTheory.SimplicialObject.ProperFaceCategory` and `properFaceDiagram`.
  Their full source definitions were read. This already-landed node is added to
  `stmt_deps` under brief-stage2 §5's permission to add landed dependencies; no new
  copy of the proper-face category or diagram is introduced.
- Proof-only import `Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers`
  supplies `hasFiniteLimits_of_hasTerminal_and_pullbacks` from the proof dependency
  `lem-weil-pbc-finite-limits-from-terminal-pullbacks`; its full signature was read.
  `lem-weil-pbc-site-hypercover-finite-extension` has no recorded Lean declaration,
  so it contributes the documented proof step but no import. It is a proof prerequisite,
  not an object needed to type this statement.

Source checked: the local `hypercovering.tex`, Tag 0DAV, complete statement and split
extension construction, and the definition of hypercovering at Tag 01G5. The finite
version uses finite matching diagrams, finite component covers, and finitely many
surjections between finite ordered sets, exactly as the node's proof explains.

Edge cases checked: degree zero has the empty proper-face diagram and singleton
`id_T` matching object; degree one has two vertices, giving the product over `T`.
Empty source index sets and empty chosen covers remain permitted. An empty target
matching family has no component covering conditions. Empty `B` is not ruled out:
when the site admits empty covers everywhere the empty simplicial family works.
An empty category has no `T` and the statement is vacuous. Finite indices in `Type u`
lose no finite families, and the formal-coproduct index universe is `u` as recorded
by the formal-coproduct dependency. No nonemptiness or splitting requirement is added.

Searches made:

- `msearch.py leanfinder`: “A site with finite covering families from a basis admits a
  hypercover finite in every simplicial degree” returned eight zero/one-hypercover
  and finite-precoverage hits, including `GrothendieckTopology.OneHypercover`; no
  all-degree finite-basis existence theorem.
- `msearch.py loogle`: `Hypercover, matchingObject` returned zero hits (unknown
  identifier `Hypercover`).
- `msearch.py grep`: `matchingObject|Hypercover` in `CategoryTheory` returned 25 hits
  concerning zero/one hypercovers and their site APIs; no exact match.
- Direct `rg` of Mathlib site and formal-coproduct sources located the exact presieve,
  precoverage, and formal-family interfaces used above.
- Direct `rg` of the upstream `WeilConjectures/CategoryTheory` for matching/hypercover
  names found the zero/one-hypercover pro-category APIs, not this statement.
- Direct `rg` of the full upstream `WeilConjectures` for the item id and proposed
  theorem name found no declaration. Direct `rg` of project `lean/Sheaf` found only
  the item's proof citation in `ProEtaleAffineAcyclicHypercover`, not its statement.
- Searched DAG node statements/titles for matching objects, semi-representable
  objects, and hypercovers. The existing proper-face diagram is reused. The existing
  scheme-specific `IsSemiRepresentableHypercover` concerns `X.Etale`, not an arbitrary
  small site, and is not substituted for the node's general site.

Validation: `scompile.py` compiled the delivered module cleanly on the server
(nice 19, two threads, 60 seconds per file; reported compile time 0.8 seconds).
The declaration uses only explicitly bound variables and universe `u`. No local
compiler or library build was run. No STATEMENT-DISPUTED issue was found.

## Second reading by NS

I independently read the repository node, sandbox node and Lean file together with
`hypercovering.tex`, lemma-w-contractible (Tag 094K), lemma-hypercovering-object
(Tag 0DAV), definition-hypercovering (Tag 01G5), and definition-covering-SR.
Tag 094K states precisely the finite version here; no additional hypothesis is
assumed in its surrounding text. No statement correction or new node is needed.

Object/hypothesis/conclusion checklist, in the order of the node:

1. A small site with fibre products: `{C : Type u} [SmallCategory C]
   [HasPullbacks C]`, `J : Precoverage C`, and the three instances `J.HasIsos`,
   `J.IsStableUnderComposition`, `J.IsStableUnderBaseChange`. PASS. I opened the
   dependency node and Mathlib `Sites/Precoverage.lean`: these are exactly its
   recorded site convention, and global pullbacks supply covering pullbacks.
   No terminal object or global finite-limit assumption is added on C.
2. A chosen set of objects: `B : Set C`. PASS; it need not be nonempty,
   isomorphism-closed, or stable under limits.
3. Each object has a finite B-cover: `hcover` quantifies over every `T : C`,
   then `I : Type u`, `U : I → C`, `f : ∀ i, U i ⟶ T`, and requires `Finite I`,
   `∀ i, U i ∈ B`, and `Presieve.ofArrows U f ∈ J T`. PASS; every clause is present.
4. Adjoining a B-arrow to any finite B-cover preserves covering: `hadjoin`
   quantifies over the target, index, finiteness instance, family, arrows,
   basis-membership and covering hypotheses, then `V ∈ B` and `g : V ⟶ T`.
   `Presieve.ofArrows U f ⊔ Presieve.singleton g ∈ J T` is the appended family.
   PASS under the dependency's presieve convention; no upward-closure hypothesis
   or demand that the appended singleton already covers is substituted.
5. For each T there exists an augmented simplicial formal family: final binder
   `(T : C)` precedes `∃ K : SimplicialObject (FormalCoproduct.{u} (Over T))`.
   PASS. Every component has its arrow to T and every component operator commutes
   with that arrow by `Over.Hom.w`. The singleton `id_T` is terminal in this
   formal-family category, so the unique augmentation exists and is natural.
   This is also the source's SR(C,T) = SR(C/T) interpretation.
6. Every degree is finite: `∀ n, Finite (K _⦋n⦌).I`. PASS; this is degreewise
   finiteness, not the stronger condition of finitely many nondegenerate simplices.
7. Every component lies in B: `∀ n i, ((K _⦋n⦌).obj i).left ∈ B`. PASS.
8. Matching objects are compatible proper-face limits: `M n : Cone
   (K.properFaceDiagram n)` and `∀ n, Nonempty (IsLimit (M n))`. PASS.
   I opened the matching dependency node and `ProperFaceMatchingObject.lean`:
   `properFaceProperty n` selects injective maps with source length strictly
   less than n, and `properFaceDiagram` is the opposite of the forgetful
   diagram composed with K. It gives precisely all compatible proper faces.
9. Degree-zero matching object is the specified singleton: `(M 0).pt =
   (FormalCoproduct.incl (Over T)).obj (Over.mk (𝟙 T))`. PASS. There are no
   proper faces in degree zero. The equality selects this representative of
   the terminal object; it imposes no additional condition on T or C.
10. The maps are canonical matching arrows: `μ n ≫ (M n).π.app (op a) =
    K.map a.obj.hom.op` for every proper face a. PASS. These equations and
    `IsLimit` determine μ uniquely; in degree zero terminality determines it.
11. Matching arrows cover componentwise in every degree: for every `n` and
    target index `j`, the final `Presieve.ofArrows` uses exactly the subtype
    `{i // (μ n).f i = j}`. Its map is `((μ n).φ i.val).left` followed by
    `eqToHom` for that equality. PASS; the transport has the correct direction,
    from target index `(μ n).f i` to j, and membership is in the original
    `J ((M n).pt.obj j).left`, not its generated Grothendieck topology.
12. All simplicial identities: `K` is a functor on `SimplexCategoryᵒᵖ`.
    PASS; identity and composition laws give face-face, degeneracy-degeneracy,
    and mixed identities. There is no separate unsupported list of operators.

I read the exact `FormalCoproduct`/`Hom`/category/`incl` declarations in Mathlib
`Limits/FormalCoproducts/Basic.lean`, and `SimplicialObject`, `δ`, `σ` in
`AlgebraicTopology/SimplicialObject/Basic.lean`, against their dependency nodes.
They are the required notions, not merely similarly named declarations.
I also read `SimplicialMatchingObject.lean` and the full signatures of the finite
limit tools in `LimitsOfProductsAndEqualizers.lean`. The proof docstring includes
all five DAG steps: slice and initial cover, finite formal-family matching limits,
split extension, finite repeated adjoining, and stabilization with augmentation.
The split-extension node has no recorded module; it is needed for the future
proof, not for typing this statement. There are no delivery dependency modules
or new definition nodes to review under H12/H13.

Edge cases: I=empty remains allowed in both hypotheses and the output. The
covering condition for an empty target family is vacuous, while an empty source
fibre over an existing target must actually be an empty covering in J. Empty B
is allowed when the cover hypothesis permits it. An empty C has no T, so the
conclusion is vacuous. Degree zero is checked above; degree one is the two-vertex
product in SR(C/T), and higher degrees impose compatible proper faces. There
are no ring, characteristic, zero-object, scheme, or nonemptiness restrictions.
The only universe u is explicitly bound. SmallCategory is the dependency's small
site convention, not an additional restriction on the node. Finite families can
always be reindexed in Type u, so the index-universe choice loses no case.

Independent searches, using different descriptive wording from the worker:

- `msearch.py leanfinder`: "A simplicial family over an object with finitely
  many basis objects in every degree and covering boundary maps exists" gave
  eight hits about simplicial splitting index sets, finite simplicial sets,
  standard simplices and truncated simplex categories. No matching theorem.
- `msearch.py loogle`: `"hypercover"` gave twelve zero-hypercover declarations;
  none is an all-degree finite-basis existence statement.
- `msearch.py grep`: `semi.?representable|basis.*hypercover|hypercover.*basis`
  gave one affine-basis-cover calculation, not this theorem.
- Direct `rg` with basis/hypercover, semi-representable, and existence wording
  on Mathlib sites, upstream WeilConjectures, project lean/Sheaf, and
  dag/lean_names_upstream.json found no exact declaration. I opened the nearby
  `exists_finite_split_hypercover` in `FiniteSplitHypercoverExistence.lean`:
  it is specific to qcqs schemes and the etale site, so cannot replace the
  arbitrary-small-site theorem here. The previously recorded proper-face
  diagram is already reused rather than copied.

Mismatch/repair: no mathematical mismatch found. The docstrings cited only
0DAV and 01G5 although Tag 094K is the exact finite theorem. I added 094K and
its label to the module source citation and added 094K to the theorem citation.
No Lean signature, hypothesis, conclusion, or dependency was changed. The
worker report remains above. There is one named theorem with its entire proof
`sorry`, no new definitions, no hollow data, and no local notation or instances.

Final validation: server scompile.py passed cleanly in 0.9 s, nice 19, two
threads, 60-second limit. The initial invocation used the repository directory
and found no sandbox file; rerunning from the sandbox fixed the path. No Lean
error or warning was reported. A literal comparison confirms lean.statement is
the complete verbatim theorem signature; all Lean lines are at most 100
characters, and all variables and universes are explicitly bound.
