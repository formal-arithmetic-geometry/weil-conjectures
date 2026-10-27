## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentHyperplaneRestrictionSequence` states
`AlgebraicGeometry.ProjectiveSpace.HyperplaneRestriction.exists_coherentHyperplaneRestrictionSequence`.
Its sole theorem has proof `sorry`. The fourteen helper definitions have real data and specify
exactly the zero scheme, twisted pullback, multiplication, restriction and connecting maps in
this theorem. All are listed in `lean.declarations` and have source/blueprint docstrings.
The natural-language statement, proof and proof dependencies of the item are unchanged.

The earlier NQ delivery was the Stage 1 split, with no Lean record or module for this item.
The retained sandbox initially contained only dispatcher brief markers. This delivery supplies
the missing Stage 2 statement; it does not resubmit that unchanged Stage 1 split.
The current repair responds to the reachability return on immutable head 14179854cc6d.

Clause-by-clause reading (all names below are in the namespace
`AlgebraicGeometry.ProjectiveSpace.HyperplaneRestriction` unless qualified):

- Infinite field: `(k : Type u) [Field k] [Infinite k]`. Characteristic is unrestricted.
- Positive projective dimension: `(n : ℕ) (hn : 1 ≤ n)`. The homogeneous coordinate index is
  `ULift.{u} (Fin (n + 1))`, so the relative projective space over `Spec (.of k)` is exactly
  projective n-space in the existing projective-space/twist encoding. The ULift handles any
  universe of the coefficient field without changing the finite coordinate set.
- Coherent module: `F` is a module on that projective space, and `hF` is precisely
  `RingedSpace.IsCoherent P.toRingedSpace F`, the literal Tag 01BV predicate. The item
  lean.note records this rendering; the landed Q25 dependency record stays unchanged.
- Nonzero linear section: the first existential is
  `s : Γ(twist ... 1, ⊤)` with conjunct `s ≠ 0`.
- Its zero scheme and closed immersion: `hyperplane s` and `inclusion s` are the subscheme
  and subscheme inclusion of `(homOfGlobalSection (twist ... 1) s).zeroLocus`.
  Thus H is the actual Z(s), with its defining ideal and canonical closed immersion;
  neither H nor the immersion is arbitrarily quantified. The invertible module O(1) and
  the structure module are the domain and codomain required by the zero-locus definition.
- Projective hyperplane: `e : hyperplane s ≅ ℙ(ULift (Fin ((n - 1) + 1)); Spec (.of k))`.
  This is projective space of dimension n-1, including dimension zero when n=1.
- All integer twist comparisons: `θ` quantifies over `d : ℤ` and identifies
  `twistOn s d = i^*O_P(d)` with `e^*O_{P^(n-1)}(d)`. This is the pullback formulation of
  carrying the twists across the isomorphism H ≅ P^(n-1).
- Multiplicativity of these same comparisons: the first conjunct says for every pair
  `d a : ℤ` that `pulledMultiplication i d a ≫ θ(d+a).hom` equals
  `(θ(d).hom ⊗ₘ θ(a).hom) ≫ pulledMultiplication e.hom d a`.
  `pulledMultiplication` pulls back the canonical `ProjectiveSpace.twistTensorIso` through
  the section-normalized comparison of `module_pullback_tensor`. This includes negative
  and zero degrees; the comparisons are not independent arbitrary twist identifications.
- Coherence of G=i^*F: the second conjunct is exactly
  `RingedSpace.IsCoherent (hyperplane s).toRingedSpace ((tensorPullback i).obj F)`.
  `moduleOn s F d` is G ⊗ O_H(d), with O_H(d) defined as i^*O_P(d), as in Tag 0EGK.
- Every twisted short exact sequence: for every `d : ℤ`, `multiply s F d` is
  `F ◁ twistMulHom (1 + (d-1) = d) s`; `restriction s F d` is the normalized pullback
  adjunction unit on F(d), followed by the pushforward of `restrictionIso s F d`.
  The existential proof `hz` states their composite is zero, and `hs` says that this
  actual `ShortComplex` is short exact. Hence its terms and arrows are precisely
  F(d-1) --s--> F(d) --> i_*G(d), with monic first and epic second arrows.
- The initial zero in the cohomology sequence: `Function.Injective` of the degree-zero
  `RingedSpace.moduleCohomology` map induced by `multiply`. These are the recorded module
  right-derived global sections, including in degree zero.
- Every consecutive cohomology segment: for every `q : ℕ`, the three `Function.Exact`
  clauses assert exactness at H^q(P,F(d)), H^q(H,G(d)), and H^(q+1)(P,F(d-1)), respectively.
  The first/next arrows are the cohomology maps of multiplication by s.
  `cohomologyRestriction` is `moduleCohomologyFMap i (restriction s F d) q`, so it is the
  restriction induced by the actual pullback unit, not an arbitrarily supplied map.
  `he` states the canonical `moduleCohomologyEdgeMap i (moduleOn s F d) q` is invertible.
  This is the closed-immersion identification in Tag 0EGK used to express the sequence
  on H. `boundary` is its inverse followed by `sequenceBoundary`, which is exactly the
  canonical `RingedSpace.moduleCohomologyBoundary` of the given short exact sequence.
  Standard derived-category instances are passed explicitly inside this construction;
  no extra derived-category existence hypothesis is imposed on the theorem.
- Surjectivity of linear-section restriction: `Function.Surjective (globalRestriction i
  (twist ... 1))`. The target is Γ(i^*O_P(1),top)=Γ(O_H(1),top), as above; the degree-one
  component of θ identifies this with the lower-dimensional projective-space twist.
- Restriction commutes with products: the final quantification is over every integer d,
  every `u : Γ(F ⊗ O_P(d),top)` and every `v : Γ(O_P(1),top)`. Its equality is the
  restriction of `(F ◁ twistMulHom (1+d=d+1) v).app top u` versus the product of the
  two restricted sections under `moduleMultiplication`. The latter is the associator
  followed by `i^*F ◁ pulledMultiplication i d 1`. Thus it is exactly (uv)|H=(u|H)(v|H).

The canonical maps are constructions, not hypotheses. Choosing the tensor comparison from
`module_pullback_tensor` is legitimate: its theorem is already proved, and its pure-section
formula determines the map since these sections locally generate tensor pullback. The
normalized adjunction is the recorded `tensorPullbackSectionAdjunction`, fixed uniquely by
sending m to 1 tensor m. Cohomology restriction uses the existing resolution construction,
and the boundary uses the existing derived-triangle construction, without another choice.

Dependency declarations read and used:

- `Field` from Mathlib.Algebra.Field.Defs (`def-weil-field`).
- `AlgebraicGeometry.ProjectiveSpace.twist` from
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`.
- `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent` (literal Tag 01BV rendering in item lean.note).
- `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus` from
  `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`.
- `tensorPullback`, `tensorPullbackSectionAdjunction`, and its normalized unit from
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` and its public upstream import.
- `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` from
  `WeilConjectures.AlgebraicGeometry.PQFCohomology`, together with its degree functors
  `AlgebraicGeometry.RingedSpace.moduleCohomology`.
- `AlgebraicGeometry.ProjectiveSpace.twistTensorIso` and `twistMulHom` from the public
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistMul` / TwistTensor modules.
- `AlgebraicGeometry.Scheme.Modules.module_pullback_tensor` from
  `WeilConjectures.AlgebraicGeometry.ModulePullbackTensor`.
- `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap` and `moduleCohomologyEdgeMap`
  from `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap`.
- `AlgebraicGeometry.RingedSpace.moduleCohomologyBoundary` from
  `WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary`.

The pullback-tensor, boundary and cohomology-map nodes are cited because their constructions
occur explicitly in the signature and its canonical arrows. The existing def-pc-projective-space-twist dependency carries the twist family;
its upstream twistTensorIso and twistMulHom definitions supply the multiplication.
The Nonempty twist-tensor theorem remains in proof_deps, whose content is unchanged.
Stated proof dependencies are imported: Serre, CoherentFiniteTypeLocallyNoetherian,
Mathlib.RingTheory.FiniteType and Mathlib.AlgebraicGeometry.Noetherian; the twist, invertible,
Proj and pullback material is also available through the public statement imports.
`lem-sfb-coherent-regular-hyperplane-restriction` is a proof-only dependency. It now has
the landed module `Sheaf.AlgebraicGeometry.CoherentRegularHyperplaneRestriction`; this
repair imports it for Stage 3. The six-step theorem docstring preserves its role.

Edge cases checked before finalizing:

- n=1 gives P^0 as hyperplane; negative twists and zero twists are still quantified over ℤ.
  Linear-section restriction remains surjective on P^0, and H^1(P^1,O)=0 proves it.
- n=0 is excluded by the node's explicit positive-dimensional hypothesis only.
- F=0 is allowed: both module sequences and all cohomology maps have zero terms, while
  the nonzero section and linear-section surjectivity still concern the ambient geometry.
- For a skyscraper module, the chosen hyperplane avoids its associated support; the
  restriction may be zero, which none of the conclusions excludes.
- Positive characteristic is allowed; infinitude, not characteristic zero, is required.
- The field may be small or live in any universe u; ULift of the coordinate index imposes
  no independent small-universe quantification and loses no such field.
- Only canonical zero-scheme inclusions and actual tensor pullbacks appear. No arbitrary
  comparison, exactness assumption, Noetherian assumption, or chosen hyperplane is added
  as a theorem hypothesis.

Searches for an existing statement:

- msearch.py leanfinder query: "A coherent sheaf on projective space over an infinite field
  admits a regular hyperplane restriction short exact sequence and long exact cohomology
  sequence". Eight hits, including unrelated Profinite exactness and abstract derived
  categories; no coherent hyperplane theorem.
- msearch.py loogle query: `"hyperplane"`. Eight hits on convex/proper-cone separation,
  measure-theoretic hyperplanes and a sphere homeomorphism; no algebraic-geometry match.
- msearch.py grep query: `hyperplane|hyperplaneRestriction|regularHyperplane`, restricted
  to Mathlib/AlgebraicGeometry. Zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for hyperplane and coherent/restriction sequence
  names found coordinate-hyperplane geometry, projective-bundle constructions, and
  proof-docstring references in FreeQuotientKernelRegularityBound, but no theorem for this
  item. Searching the exact node id in upstream Lean gave no hit.
- The DAG search finds the separate finite-family common-hyperplane node, already cited
  in the item's proof; that node now has the landed declaration exists_coherent_regular_hyperplane. It does not include this item's
  linear-section surjectivity and multiplication-compatible all-degree comparisons.
- Source/API searches found actual TwistTensor/TwistMul, ModulePullbackTensor,
  ModuleCohomologyFMap, ModuleCohomologyBoundary and Coherent implementations; these are
  reused rather than redeclared.

Sources checked: the full lemma-hyperplane proof (089Z), lemma-exact-sequence-induction
(08A0), finite-family remark, and remark-exact-sequence-induction-cohomology (0EGK) in
literature/stacks-project/varieties.tex, together with the recorded dependency docstrings.
There is no statement dispute and no natural-language statement correction.

## Reachability repair of 14179854cc6d

The saved-packet dry run passed as 6ed2aa83ba6, but this does not resolve the independent
incremental DAG finding. Applied correction (1) explicitly authorized by the return:
removed the sandbox node def-sfb-projective-space-twist-multiplication and removed only
that id from the item's stmt_deps. Kept lem-pc-twist-tensor in proof_deps. Updated lean.note
to identify twistTensorIso and twistMulHom as upstream definitions of the existing
def-pc-projective-space-twist family, as for the landed NR sibling. There are no new nodes
or dependency modules in this packet. The module is unchanged; no import_flags or
unrelated reachability edits are attempted. Other current-base metadata was retained.
The return's alternative (2), waiting for a global re-link, is unnecessary for this repair.

Read the current base node, saved node and module, the repair note, and the public upstream
Twist/TwistTensor/TwistMul definitions. The repair note concerns Stage 1 re-splitting;
this Stage 2 packet preserves the base's statement and proof, and does not perform that
separate re-split. The current return accepts the mathematical statement and requests
only the ownership/reachability repair above.

## Second reading by Q38

Self-check without a second agent, as explicitly required by the dispatch brief.
Re-read the node and the full retained module. The arbitrary infinite field, n>=1 and
coherent module binders match exactly. A single nonzero linear section fixes its actual
zero scheme, the isomorphism with P^(n-1), and every integer-degree twist comparison.
The same comparisons satisfy the multiplicativity equation. The pullback is coherent.
For each integer d, multiply and normalized-unit restriction form the stated ShortExact
complex. The H^0 injectivity and three exactness clauses for every natural q express the
entire long exact sequence, using canonical moduleCohomologyFMap restriction and the
triangle boundary transported along moduleCohomologyEdgeMap. The final two clauses are
surjectivity of linear-section restriction and the product rule for arbitrary global
sections. No characteristic, negative degree or zero-module case is excluded.

The upstream twistTensorIso maps tensor products of the standard frames to the sum-degree
frame; twistMulHom is its section-composite, so the unchanged helpers use the intended
multiplication. The definitions contain real data. Classical.choose(module_pullback_tensor)
is retained as the canonical comparison fixed by the theorem's section formula. There is
one postponed theorem with its six-step proof docstring. All fourteen helper declarations
and the theorem remain listed in lean.declarations. The only mismatch found in this
repair was the unnecessary new owner and dependency edge; both have been removed.

Validation: scompile.py compiled the retained module as both sandbox (13.3 s) and
library module (9.9 s), with no errors or non-sorry warnings. The stored signature
was checked byte-for-byte against the file; autoImplicit and relaxedAutoImplicit
are disabled, the only sorry is the named theorem, and all lines have at most
100 characters. The repaired-packet deliver2.py --no-push passed preflight and compilation as
2a7273e96ee. It staged only the item node, unchanged Lean module and report;
the removed definition node was absent. Final self-check verified that the item
differs from current base only in lean and stmt_deps, that proof_deps is unchanged,
and that the module SHA256 remains
b348b76c0646168c4007640abbe332380b9258c2730edcbbe74f001d62d57194.
