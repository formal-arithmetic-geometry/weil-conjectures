## Worker report

The module `Sheaf.CategoryTheory.SiteHypercoverFreeResolution` states
`CategoryTheory.siteHypercover_free_resolution`. Its sole theorem has proof `sorry`.
There are no definitions, auxiliary theorems, new nodes, dependency repairs, or
statement corrections. The mathematical node, including its proof and split report,
is preserved. The canonical augmented alternating free abelian sheaf complex is
expressed by Mathlib's existing `AlternatingFaceMapComplex.ε`; the conclusion is
that this particular chain map to the single complex on the free sheaf of `W` is
a quasi-isomorphism.

### Returned-delivery repair

The immutable returned head `2f78c2ff32b0` was rejected for an unauthorized
`split_report` change and a missing/non-record `lean`. The sandbox supplied for
this retry contained only dispatcher brief marker files, so there was no retained
Lean module or node copy to reuse. I reconstructed the delivery from the current
shared node. A JSON comparison with that node reports exactly one changed key,
`lean`: in particular, `split_report`, `statement`, `stmt_deps`, `proof`,
`proof_deps`, and review/creation metadata are unchanged. The complete `lean`
record specifies the module, declaration, file, verbatim source signature,
`branch: newtargets-dag`, `by: N3`, the UTC date, and `existing: false`.
The required delivery wrapper constructs the repair on current `newtargets-dag`,
without carrying the stale returned node metadata forward.

### Hypotheses and clauses

- A small site with finite limits is `{C : Type u} [Category.{v} C]
  [HasFiniteLimits C]`, `(J : Precoverage C)` and
  `(hsite : J.IsSiteForCoverings)`. The latter is precisely the dependency's
  recorded site axiom predicate, including existence of covering pullbacks and
  bind composition. Objects and arrows form sets in the explicit universes.
- The object `W` is `(W : C)`. The augmented simplicial object is
  `(U : SimplicialObject C)` and
  `(e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W)`. Naturality of `e`
  enforces compatibility of every simplicial operator with the augmentation.
- For every `n`, the finite matching object in `C/W` is rendered by its functor
  of sections. A test object is `(T : C)` with `(w : T ⟶ W)`. Its matching family
  is `p Δ h θ : T ⟶ U.obj (op Δ)` for each lower simplex `Δ.len < n` and
  operator `θ : Δ ⟶ SimplexCategory.mk n`. The first quantified equation says
  every face has augmentation `w`; the second is compatibility under every
  operator between lower simplices. A noninjective `θ` factors through its
  proper image, so its entry is determined by proper faces and degeneracies;
  this adds no extra input to the proper-face finite matching limit.
- The covering matching-map assumption is `hcover`: each such section has a
  covering sieve `S ∈ J.toGrothendieck T`, and for every `f : V ⟶ T` in `S`
  there is `t : V ⟶ U _⦋n⦌` over `f ≫ w` realizing all pulled-back faces.
  Pulling back the node's covering family of the matching object gives this
  condition. Conversely apply it to that matching object's universal family;
  its covering sieve of lifts is contained in the matching map's generated
  sieve. On a site in the recorded convention a covering sieve contains a
  covering family, giving exactly the node's stated factorizations. This is
  the same matching-cover formulation already used by the landed
  `CategoryTheory.siteHypercover_injective_sections_exact` consumer.
- At `n = 0`, there are no lower simplices; the matching object is `W`, so this
  says exactly that `U₀ → W` generates a covering sieve. At `n = 1`, a matching
  family is two vertices with the same map to `W`, hence its object is
  `U₀ ×[W] U₀`. For larger `n` the equations encode the compatible proper faces
  in the slice, rather than ordinary degree-zero coskeleton products.
- The free abelian presheaf on a representable is the composite of
  `uliftYoneda.{max u v}` and
  `(Functor.whiskeringRight Cᵒᵖ (Type (max u v)) AddCommGrpCat.{max u v}).obj
  AddCommGrpCat.free`. `uliftYoneda` changes only the universe of hom-sets.
  Composing with `presheafToSheaf J.toGrothendieck AddCommGrpCat.{max u v}`
  gives precisely the node's sheafification `ℤ[V]`. These are existing Mathlib
  constructions, with no second free-sheaf definition introduced.
- `SimplicialObject.Augmented.whiskeringObj` applies that composite to
  `{ left := U, right := W, hom := e }`, preserving the actual augmentation.
  `AlgebraicTopology.AlternatingFaceMapComplex.ε.app` then constructs the
  canonical augmentation of the alternating-face complex. Its source has
  degree-`p` term `ℤ[Uₚ]` and differential `Σᵢ (-1)^i ℤ[dᵢ]`; its target is
  `ChainComplex.single₀` on `ℤ[W]`.
- `QuasiIso` asserts that the induced map on every homology sheaf is an
  isomorphism. The target has positive homology zero and zeroth homology
  `ℤ[W]`; the degree-zero map is induced by the original augmentation. This
  is equivalent to exactness of the entire displayed augmented sequence,
  including surjectivity onto `ℤ[W]`, with no arbitrary zeroth-homology iso.
- The size convention is implemented by the explicitly bound `u v`. Values
  live in `max u v`, containing both site universes, so every needed limit,
  free group, and sheafification exists. The site's object and arrow universes
  remain independent. No extra sheafification-existence hypothesis is added.

### Dependency declarations and sources inspected

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, read with its full definition
  and 00VH docstring; used directly as `hsite`.
- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`:
  `CategoryTheory.SimplicialObject`, its `δ` and `σ`, and the comma-category
  definition of `Augmented` with `Augmented.whiskeringObj`; read their full
  signatures and docstrings. This module is publicly re-exported through
  `AlternatingFaceMapComplex`.
- `Mathlib.CategoryTheory.Sites.Sheafification`:
  `CategoryTheory.presheafToSheaf`, `toSheafify`, and `sheafificationAdjunction`;
  read the definitions and their surrounding typeclass parameters.
  `presheafToSheaf` is used directly; the others explain its universal property.
- `def-weil-size-convention` is the dependency's recorded metatheoretic
  convention, with no declaration: universes are bound explicitly.
- `Mathlib.CategoryTheory.Yoneda`: `CategoryTheory.uliftYoneda`.
  `Mathlib.Algebra.Category.Grp.Adjunctions`: `AddCommGrpCat.free`, whose
  generators are exactly elements of the represented hom-set.
- `Mathlib.AlgebraicTopology.AlternatingFaceMapComplex`:
  `AlgebraicTopology.AlternatingFaceMapComplex.ε`; read its chain-map definition,
  including its degree-zero component and alternating-face differential.
  `Mathlib.Algebra.Homology.QuasiIso`: `QuasiIso` and its definition in terms
  of the homology maps. These supply the full conclusion without custom data.
- Proof imports retain the recorded modules
  `Sheaf.Paper.CechNerveFreeHomology`,
  `Sheaf.CategoryTheory.TruncatedCoskeletonFiniteLimits`,
  `Sheaf.AlgebraicTopology.CoskeletonFreeHomologyComparison`, and
  `Sheaf.CategoryTheory.MatchingObjectCoskeleton`. The proof-only dependencies
  `lem-trf-cech-nerve-one-coskeletal` and
  `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective` have no recorded module
  in the current node files; no nonexistent import is invented for them. The
  coskeleton definition is already in Mathlib's simplicial-object module.

The natural-language theorem docstring carries all seven proof steps of the
node, including the relative Čech nerve base case, its separate `n = 1`
transition, the slice/ordinary matching comparison only for `n ≥ 2`, and
augmentation-compatible fixed-degree stabilization. The Stacks source was read
at `hypercovering.tex`, lemma-acyclic-hypercover-sheaves (Tag 01GE), together with
the indicated 01GC--01GD references.

### Edge cases checked

For `n = 0` the family is empty, yet `hcover` still demands local lifting of
`T → W`; so the augmentation-cover assumption is retained. For `n = 1` both
vertices share their augmentation, excluding the incorrect absolute-product
matching condition. Empty representables and empty coverings are allowed: when
an object is covered by the empty family, all relevant sheaf sections are forced
and the covering-sieve formulation still applies. The identity constant
hypercover satisfies the hypotheses and gives the standard augmented alternating
constant complex. No splitness, terminality of `W` in `C`, subcanonicality,
nonempty index set, scheme hypothesis, or coefficient-ring hypothesis is used.
The coefficient universe `max u v` includes cases with distinct object and
morphism universes. No statement fault or STATEMENT-DISPUTED flag remains.

### Searches for an existing statement

- `msearch.py`, LeanFinder, query: "augmented alternating free abelian sheaf
  complex of a hypercover is exact on a small site". Eight hits: Mayer--Vietoris
  square exactness, one-hypercover sheaf tests, and alternating constant complex
  exactness. None states this all-degree augmented hypercover result.
- `msearch.py`, Loogle, query:
  "AlgebraicTopology.alternatingFaceMapComplex, QuasiIso". Zero hits.
- `msearch.py`, LeanSearch, query: "The canonical augmentation of the free
  abelian sheaf chain complex of a hypercover is a quasi-isomorphism". Eight
  hits, including `ChainComplex.augment`, truncation/augmentation isomorphisms,
  and quasi-isomorphism localization infrastructure; no matching theorem.
- `msearch.py`, Mathlib grep, query `hypercover|Hypercover` in
  `AlgebraicTopology`: zero hits. The query
  `free.*[Aa]belian.*[Hh]ypercover|[Hh]ypercover.*free|siteHypercover_free_resolution`
  in `CategoryTheory` also gave zero hits.
- `rg` in Mathlib's `CategoryTheory/Sites` and `AlgebraicTopology` found the
  existing zero/one-hypercover machinery and alternating-face constructors,
  but no theorem about all matching degrees and free abelian sheaf resolution.
- `rg` of the upstream `WeilConjectures` tree for hypercover/free-resolution
  combinations and the item id gave no matching declaration.
- `rg` of `lean/Sheaf` found
  `AlgebraicGeometry.SplitEtaleHypercover.freeAbelian_augmentation_quasiIso_sheaf`
  in `Sheaf.Paper.HypercoverFreeResolution`. Its full signature was read: it
  assumes a split étale hypercover of a quasi-compact quasi-separated scheme,
  so it is a special case and does not state the arbitrary-site result. The
  Čech free-resolution declarations cover relative Čech nerves only. The landed
  injective-sections consumer concerns the dual complex, not this theorem.
- `dag/lean_names_upstream.json` and the upstream item-id search contain no
  existing declaration for this node.

### Validation

The prescribed `scompile.py N3 lem-trf-site-hypercover-free-resolution` compiled
both its sandbox probe and the final library-path module successfully, each
within the 60-second per-file limit and without warnings. Initial attempts with
an unnecessary independent larger coefficient universe exposed Mathlib's
filtered-colimit size inference issue; the final module uses the natural common
bound `max u v`, and requires no additional mathematical assumption or local
instance. All lines are at most 100 characters, every variable and universe is
explicitly bound, and the node's stored signature matches the file verbatim.
The required delivery dry run and final push are run after this report.

## Second reading by N3

Independent maintainer reading of immutable delivery
`c6878cbdf688184b4131082d23a17cd40a227a3a`, performed on 2026-10-18 by the
reviewer assigned to this delivery, who did not write it. This section replaces
the delivered placeholder; it does not claim that the worker performed a second
reading. The Worker report above is retained in full.

I opened the item JSON, all four immutable statement-dependency JSON files, the
128-line delivered Lean module and its docstrings, and the actual declarations
below. I compared the item with Stacks `hypercovering.tex` 01GC--01GE
(lines 590--782) and 01GW (lines 885--937), and the relative nerve and higher
coskeleton arguments with `simplicial.tex` 018I (line 2814 onwards) and 018B
(line 2602 onwards). The statement agrees with the representable case of 01GE;
no subcanonicality assumption is needed.

Hypothesis and conclusion comparison:

1. The small category with finite limits is `{C : Type u} [Category.{v} C]
   [HasFiniteLimits C]`. The covering system is `J : Precoverage C` and the
   actual recorded site predicate is `hsite : J.IsSiteForCoverings`. I read
   `Sheaf.CategoryTheory.SiteCoveringAxioms`, including its bind-composition
   and chosen-covering-pullback clauses and 00VH docstring. This uses the
   dependency's public notion, with no second site definition. The global
   finite-limit instance is exactly the item's hypothesis.
2. `W : C`, `U : SimplicialObject C`, and the natural transformation `e` to
   the constant object on `W` give precisely an augmented simplicial object.
   Mathlib `SimplicialObject.Basic` defines the former as a functor from
   `SimplexCategory` opposite, with the recorded faces and degeneracies.
   Naturality supplies all augmentation compatibilities.
3. For fixed `n,T,w`, `p` specifies every lower-dimensional simplex over a
   map to `[n]`. Its first equation puts each simplex over `w`; its second
   equation is the cone compatibility, with contravariance correctly expressed
   by `U.map α.op` and `α ≫ θ`. Every noninjective map factors as a surjection
   followed by an injective proper face. The compatibility equation forces
   its entry from that proper face, so quantifying over all lower operators
   imposes exactly the proper-face matching limit, not extra boundary data.
4. `hcover` asks for a covering sieve whose every arrow has a lift realizing
   this entire matching family and its augmentation. Pullback of the given
   covering of the matching object proves this condition. Conversely apply
   it to the matching object's universal cone: the sieve of such lifts is
   contained in the sieve generated by the matching map. Upward closure makes
   that generated sieve covering. Under the recorded site axioms the topology
   generated by `J` has the covering families as a basis up to refinement,
   giving the node's factorizing covering family. Thus neither direction adds
   a hypothesis. Existence of the finite matching limits is already supplied.
5. `uliftYoneda.{max u v}` is the represented hom-set with a universe lift.
   Mathlib `AddCommGrpCat.free` has object `FreeAbelianGroup` and maps induced
   by maps of generators. Whiskering it and then `presheafToSheaf` gives
   exactly the sheafified free abelian presheaf on each representable.
   I read `presheafToSheaf`, `toSheafify`, `sheafificationAdjunction`, and the
   concrete sheafification and abelian-sheaf instance context. These are the
   recorded sheafification notion, not new data assumed in the theorem.
6. `Augmented.whiskeringObj` applies this same functor to `U`, `W`, and `e`.
   I read `AlternatingFaceMapComplex.objD` (the signed sum of faces), and `ε`:
   its target is `ChainComplex.single₀` of the augmentation object, and its
   degree-zero component is the given augmentation. I read `QuasiIsoAt` and
   `QuasiIso`; the latter requires homology isomorphisms in every degree.
   Consequently the conclusion includes both positive homology vanishing and
   the original augmentation's isomorphism on degree-zero homology, hence
   exactness and surjectivity at `ℤ[W]`. It is not an arbitrary homology iso.
7. Universes `u,v` are explicitly bound and independent; `max u v` contains
   both site sizes and makes concrete abelian sheafification available.
   This realizes `def-weil-size-convention` without imposing `u = v` or
   restricting the coefficient ring (the coefficients here are exactly ℤ).

Edge cases: at `n=0` the matching family is empty, but `w` is still quantified
and local lifting is still required, giving the cover of `W`. At `n=1` there
are two vertices over the same `w`, giving `U₀ ×[W] U₀`, not the absolute
product. For `n=2` the edge compatibilities identify vertex augmentations;
the slice-to-ordinary matching comparison is used only for `n≥2`. Empty
covering families and empty represented section sets are permitted; no
nonemptiness instance occurs. The identity constant hypercover gives the
usual alternating constant complex (successive differentials zero and
identity) with its identity augmentation. Zero free sheaves are included.
There is no field, characteristic, scheme, qcqs, splitness, terminal-object,
or subcanonicality restriction.

I checked each of the seven proof-docstring steps against the immutable node:
local lifts; relative Čech base stage; finite-limit coskeleta; the separate
1-coskeletal first transition; the matching comparison only in degree at
least two; inductive homology comparison; and fixed-degree stabilization
preserving augmentation. None is replaced by an absolute zero-coskeleton.
I also opened the four imported project proof modules. Their free-module
formulations require the usual coefficient/category comparisons at stage 3;
they are not extra assumptions on this statement. Proof-only nodes without
recorded modules do not prevent stating this theorem, and no missing
statement-level helper or DAG prerequisite is being hidden.

Independent duplicate searches used `rg` on Mathlib's sites and algebraic
topology directories, upstream `WeilConjectures`, the project `lean/Sheaf`,
and `dag/lean_names_upstream.json`, with hypercover/free-resolution terms
and the exact declaration name. The worker also records LeanFinder, Loogle,
and LeanSearch searches above. The relevant existing project theorem is
`AlgebraicGeometry.SplitEtaleHypercover.freeAbelian_augmentation_quasiIso_sheaf`;
I opened its signature: it assumes a split étale hypercover of a qcqs scheme,
so cannot replace this arbitrary-site result. Relative Čech results are also
special cases. There is no duplicate construction in the delivered module.

The source and blueprint markers occur on both module and theorem docstrings.
The only local declaration is the theorem, whose proof is exactly `by sorry`;
there are no hollow definitions, arbitrary canonical-map substitutes or local
proofs. `autoImplicit false` is set, all binders and universes are bound,
and no line exceeds 100 characters. A direct extraction of the signature
before `:= by` agrees byte-for-byte with `lean.statement`. The commit's JSON
diff only adds `lean`, preserving all mathematical and split metadata.
No statement correction or new/dependency module is needed.

Route pivot: I read `origin/newtargets-dag:coord/route-pivot-dropped.txt` in
the shared clone. Its intersection with this item's statement and proof
dependencies is empty. There is no repair-note file for this item at that
ref. The seven steps use ordinary simplicial objects and abelian sheaves;
they introduce no enhanced localization, Quillen rectification, coherent
sections, straightening or operads, and no pro-étale substitute.

Reproducibility: I ran the prescribed wrapper on the immutable snapshot file:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py N3 \
  lem-trf-site-hypercover-free-resolution \
  snapshot/lean/Sheaf/CategoryTheory/SiteHypercoverFreeResolution.lean
```

It exited 0, compiling `Sheaf/Stage2/Sandbox0.lean` in 2.3 seconds and
`Sheaf/CategoryTheory/SiteHypercoverFreeResolution.lean` in 2.4 seconds,
each under the 60-second file limit, with no Lean errors or warnings. The
installed wrapper actually uses the server side overlay, despite the brief's
older local-overlay wording; these timings are its returned compiler evidence.
An initial SSH multiplexing diagnostic did not prevent the successful checks.
No direct SSH command, global build, delivery operation, project-clone edit,
or Git mutation was performed by the reviewer.

Finding and correction: H1/H11, the original second-reading heading contained
only a disclaimer, not an actual reading. This complete report replacement
supplies the independent clause-by-clause reading required for landing. No
Lean or JSON change is required; the mathematical delivery is accepted.
