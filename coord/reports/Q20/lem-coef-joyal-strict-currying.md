## Worker report

Stage 2 statement of `lem-coef-joyal-strict-currying`, in
`Sheaf.AlgebraicTopology.JoyalStrictCurrying`. The only theorem is
`SSet.joyal_strict_currying`, with proof `sorry`. Its docstring gives all four
proof steps, including the all-sharp specialization of the already stated marked
internal-Hom theorem. The repair changes the source/proof-origin citations and Lean docstrings as required by
returned review; the theorem statement, proof text, dependencies, and no new node are
unchanged. No dependency repair or statement correction is needed.

The previous worker's ending concerned the already reviewed stage-1 split by
Q63. This delivery does not split or re-review that split: it supplies the
previously absent stage-2 statement.

Hypotheses and clauses, checked against the entire node statement:

- The fixed small universe is the explicit `universe u`, and every one of
  `X K Q : SSet.{u}` is arbitrary. All extra variables and universes are bound;
  `set_option autoImplicit false` enforces this. The larger ambient universe is
  supplied by Lean's universe hierarchy; the degree types and hom-sets remain
  small in `u`.
- Simplicial sets and their maps are Mathlib's `SSet` and natural transformations.
  Products are the existing cartesian tensor `⊗`, which has degree set
  `X.obj n × K.obj n` and coordinatewise operators. Standard simplices are
  `SSet.stdSimplex.obj n`; `stdSimplex.objEquiv.symm a` encodes a monotone map
  `a : m.unop ⟶ n.unop` as its corresponding simplex.
- The functor simplicial set is exactly the existing `(ihom K).obj Q` used in
  `def-cbc-enhanced-diagrams-cones`. The helper `SSet.functorSimplexEquiv K Q n`
  is a real, choice-free equivalence from its n-simplices to
  `(K ⊗ stdSimplex.obj n ⟶ Q)`, constructed by composing
  `SSet.yonedaEquiv.symm` with
  `CategoryTheory.FunctorToTypes.functorHomEquiv K (stdSimplex.obj n) Q`.
  It names a conversion between two existing presentations, not another
  internal-Hom simplicial set. Unfolding the existing maps sends `h` to the
  simplicial map with value `h.app m a.op k` at `(k,a)`. The first conjunct of
  the theorem explicitly identifies restriction by `a.op` with precomposition
  by `(K ◁ SSet.stdSimplex.map a)`, so this is the node's specified
  Hom(K times Delta[n],Q) model with its specified operators.
- The displayed bijection is the quantified family
  `E : ∀ X K Q : SSet.{u}, (X ⟶ (ihom K).obj Q) ≃ (X ⊗ K ⟶ Q)`.
  Lean's `Equiv` includes both inverse identities, hence actual bijectivity.
- The forward map is the second conjunct:
  `E X K Q f = (f ▷ K) ≫ (β_ ((ihom K).obj Q) K).hom ≫ (ihom.ev K).app Q`.
  Here the last two maps are the existing evaluation with its factors swapped
  to the order Fun(K,Q) times K. Thus the right-hand side is exactly
  evaluation after `f × id_K`.
- The third conjunct states in every degree that this evaluation is
  `(functorSimplexEquiv K Q n.unop (f.app n x)).app n
  (k, stdSimplex.objEquiv.symm (𝟙 n.unop))`. In particular taking X to be the
  functor simplicial set and f to be its identity gives precisely
  `ev_n(h,k) = h_n(k,id_[n])` for arbitrary h and k.
- The fourth conjunct states the inverse formula for every degree n, degree m,
  x in X_n, k in K_m, and monotone map `a : m.unop ⟶ n.unop`:
  the mapping-simplex interpretation of `((E X K Q).symm g).app n x`, evaluated
  at `(k,stdSimplex.objEquiv.symm a)`, is
  `g.app m (X.map a.op x, k)`. This is the specified transpose, with the order
  of its two product coordinates unchanged.
- The final conjunct simultaneously treats every `c : X' ⟶ X`, `a : K' ⟶ K`
  and `b : Q ⟶ Q'`. The functor-side map is
  `c ≫ f ≫ (MonoidalClosed.pre a).app Q ≫ (ihom K').map b` and its image is
  `(c ⊗ₘ a) ≫ E X K Q f ≫ b`. Setting two of these maps to identities gives
  each naturality separately: contravariant in X and K, covariant in Q.
- There are no quasicategory, Kan, fibrancy, nonemptiness or size restrictions
  in the binders. Nothing requires an enhanced-category structure on Q.

Dependency declarations and source inspection:

- Statement dependency `def-cbc-enhanced-diagrams-cones`: read its full
  statement, lean record, and the full module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, including the docstrings and
  signatures of the recorded `SSet.Enhanced.coneCategory`, `constantDiagrams`,
  `diagramVertex` and `evaluation`. Its internal functor category is directly
  Mathlib's `(ihom K).obj Q`; cones are not needed by this item. The module is
  imported publicly to use that same presentation and its primitives.
- Proof dependency `lem-coef-marked-internal-hom`: read its module
  `Sheaf.AlgebraicTopology.MarkedInternalHom`, including the complete
  `SSet.Marked.marked_internal_hom` signature and seven-step proof docstring.
  Its all-sharp specialization gives the node's proof plan. It is imported
  without `public`, as prescribed for a proof dependency. Also inspected the
  real `mapFlat` and `internalHom` definitions in MarkedPointCartesianModel.
- Read Mathlib `CategoryTheory/Functor/FunctorHom.lean`: `HomObj`,
  `homObjEquiv`, `functorHom`, `functorHomEquiv` and `natTransEquiv`;
  `CategoryTheory/Monoidal/Closed/FunctorToTypes.lean`: full equivalence and
  closed-structure definitions; `Monoidal/Closed/Basic.lean`: `ihom.ev`,
  `MonoidalClosed.curry`, `uncurry` and `pre`; and
  `AlgebraicTopology/SimplicialSet/StdSimplex.lean`: `stdSimplex`, `objEquiv`,
  `yonedaEquiv` and their coordinate formulas. These verify the orientation
  and data of the conversion helper and the evaluation map.

Source read: Goerss--Jardine, *Simplicial Homotopy Theory*,
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Goerss-Jardine2.pdf,
Chapter I, Section 5, printed pp.20--21. The function-complex definition gives
`Hom(X,Y)_n = Hom_sSet(X × Δ^n,Y)` and restriction by precomposition on the
simplex factor. Proposition 5.1 (Exponential Law) states the evaluation map,
the natural bijection `Hom(K,Hom(X,Y)) ≅ Hom(X × K,Y)`, its explicit inverse,
and naturality in K, X and Y. Its proof is exactly the degreewise identity-
simplex and transpose calculation used here. The all-sharp marked specialization
and the comparison with the existing project internal-hom presentation are the
application supplied by this node and its marked internal-Hom dependency.
Edge cases checked before drafting and again against the signature:

- X empty: both hom-sets are singletons, since X times K is empty; the formulas
  contain no unbound choice of a simplex.
- K empty: Fun(K,Q) is terminal and X times K is empty, including when Q is
  empty; the equivalence is still between singleton hom-sets.
- Q empty: maps on either side exist exactly when X times K is empty, with the
  empty-X and empty-K cases retained. No point of Q is selected.
- K = Delta[0]: currying reduces to maps X to Q through the canonical terminal
  factor identifications.
- n=m=0, identity operators, repeated/degenerate vertices, and non-injective
  simplex maps: `stdSimplex.objEquiv` accepts every monotone map, and the formula
  uses contravariance `X.map a.op` with the correct variance.
- Nonfibrant Q and even empty simplicial sets are allowed; every construction
  is an ordinary simplicial map and the theorem has no filler assumptions.

Searches actually run for this item (2026-10-17):

- `msearch.py ... leanfinder` query: "Simplicial sets maps X to the internal hom
  Fun K Q are naturally bijective to maps X times K to Q with explicit degreewise
  evaluation and transpose formulas". Eight hits included
  `SSet.instMonoidalClosed`, `SSet.yonedaEquiv`,
  `CategoryTheory.SimplicialCategory.homEquiv'` and `SSet.stdSimplex.objEquiv`.
  These supply primitives, not the full statement with the explicit model,
  forward/inverse formulas and simultaneous naturalities.
- `msearch.py ... loogle` query:
  `CategoryTheory.FunctorToTypes.functorHomEquiv`. Three hits: that equivalence
  and its `apply_app` and `symm_apply_app` lemmas. Their source was read; the
  equivalence uses K times X in place of X times K and the structured HomObj
  presentation. It is reused in the canonical degreewise conversion.
- `msearch.py ... grep` query:
  `def functorHomEquiv|functorHomEquiv_apply_app|functorHomEquiv_symm_apply_app`.
  Three results: Functor/FunctorHom.lean:118,
  Enriched/FunctorCategory.lean:455 and Monoidal/Closed/FunctorToTypes.lean:37.
  No exact full statement is present.
- `msearch.py ... leansearch` query: "Simplicial set exponential adjunction with
  explicit evaluation and currying in each simplicial degree". Eight results
  included `SSet.instMonoidalClosed`, `CategoryTheory.CartesianClosed.curry`,
  `CategoryTheory.exp.ev`, and generic comparison maps. Again these are the
  reused general closed structure, not the node's full explicit statement.
- `rg` in WeilConjectures and lean/Sheaf for Joyal, strict currying, Hom/ihom,
  evaluation, natTransEquiv and stdSimplex.objEquiv: found the existing enhanced
  internal hom and marked generalization described above; no ordinary strict
  currying statement with the node's full clauses. Search by the node id in
  WeilConjectures had no hits. `rg` of the proposed declaration names in
  Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json had no
  collisions. The DAG's node-id search found only this node and its consumers.

## Source correction for returned review

The retained packet cited HTT Proposition 1.2.7.3 (printed p.94), which concerns a later homotopy-exponential application and does not state the strict function-complex formulas used here. I replaced every item source, proof-step source, proof-origin citation, and Lean module source citation with Goerss--Jardine, *Simplicial Homotopy Theory*, Chapter I §5, pp.20--21, especially Proposition 5.1 (Exponential Law). That proposition explicitly gives the evaluation map, inverse construction, and naturality in all three variables. The theorem statement is unchanged, so the §1(C) `statement_change` record and citer audit are not required; no citer is broken.

Validation: `scompile.py Q20 lem-coef-joyal-strict-currying` compiled the sandbox
file and the library-path file cleanly, with no errors or warnings. The first
attempt required qualifying `SSet.stdSimplex.map` to avoid the topological
standard-simplex map namespace. All theorem proofs remain `sorry`; the helper has actual equivalence data and no
postponed proof. No mathematical statement is disputed. The delivery wrapper treats the DAG `source`, `proof`, and `proof_origin` fields as maintainer-owned; the corrected source is therefore carried in the module docstring, this report, and the delivered `lean.note` for maintainer metadata update.

## Second reading by Q20

(Supplied at review by the maintainer's second reader, replacing a one-line placeholder.)

Clauses of the node against `SSet.joyal_strict_currying`:

- Universe U, arbitrary U-small X, K, Q: `universe u`, `X K Q : SSet.{u}`, all bound, no
  extra instance, fibrancy or nonemptiness hypotheses. Verdict: matches.
- Fun(K,Q)_n = Hom(K x Delta^n, Q) with operators by precomposition on the simplex factor: the
  dependency's `(ihom K).obj Q` with the choice-free `functorSimplexEquiv` (Yoneda then
  `FunctorToTypes.functorHomEquiv`), and conjunct 1 states that restriction by `a.op` is
  precomposition with `K ◁ stdSimplex.map a`. Verdict: matches.
- Bijection Hom(X,Fun(K,Q)) = Hom(X x K,Q): the `Equiv` family `E`. Verdict: matches.
- Forward map ev o (f x 1_K): conjunct 2 (braiding orders the factors as Fun(K,Q) x K);
  ev_n(h,k) = h_n(k,1_[n]): conjunct 3 at all degrees. Verdict: matches.
- Inverse g -> (x -> ((k,alpha) -> g_m(X(alpha)x,k))): conjunct 4, for all n, m, x, k and
  every monotone alpha (including degenerate ones). Verdict: matches.
- Naturality in X (contravariant), K (contravariant) and Q (covariant): conjunct 5, which
  combines all three; identities recover each one separately. Verdict: matches.
- Together, conjuncts 3 and 4 fix E in every degree, so the existential is not weaker than the node.

Edge cases: X, K or Q empty and K = Delta[0] (both hom-sets are singletons or empty
together); n = m = 0; degenerate alpha. Nothing excludes any of these.

Satisfiability check (scratch file, not delivered): with
E = (ihom.adjunction K).homEquiv.symm followed by the braiding `homCongr`, conjuncts 1, 2, 3
and 5 hold by `rfl` / `ext; rfl`. Conjunct 4 follows from conjuncts 1 and 3 and the
naturality of `E.symm g`. Everything compiles with nt_compile.

Source: Goerss--Jardine I.5, function complex and Prop. 5.1 (Exponential Law), states exactly
this. The module docstrings cite it; HTT Prop. 1.2.7.3 does not. The node's maintainer-owned
`source`/`proof_origin`/proof-step source fields still cite HTT, and stage 2 cannot change them;
the correction is recorded in `lean.note` for the maintainer. The statement is unchanged, so
no statement_change.

The Lean statement equals the already-landed Q24 statement of this item word for word. Only
the author line and `lean.note` differ.
