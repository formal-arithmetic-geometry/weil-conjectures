## Worker report

The theorem `Algebra.isSmoothAtPrime_iff_exists_jacobian_minor` states exactly the fixed-presentation Jacobian criterion. Nothing is proved: its proof is `by sorry`. The dependency module adds the fixed-presentation clause of the already existing complete-intersection definition node, with full data and no sorry. No item statement correction or new node is needed.

Source read: https://stacks.math.columbia.edu/tag/00TE (Lemma 10.137.15), including its proof, and https://stacks.math.columbia.edu/tag/00SP (Definition 10.136.5). The local literature checkout does not contain algebra.tex, so the actual Stacks pages were opened. In particular 00SP explicitly distinguishes the existential ring-map condition from saying that the displayed presentation is a relative global complete intersection.

Hypothesis and clause correspondence:

- Commutative ring R: `(R : Type v) [CommRing R]`, arbitrary universe, no field or Noetherian assumption.
- Integers n,c >= 0: `(n c : ℕ)`; Fin indices shift the paper's 1-based enumeration to 0-based enumeration without changing any objects.
- The c equations in n variables: `f : Fin c → MvPolynomial (Fin n) R`.
- S equals the displayed quotient: `MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)` is used directly everywhere. Its standard quotient R-algebra is used; no arbitrary unrelated S or algebra structure occurs.
- This presentation is a relative global complete intersection: `hci : IsRelativeGlobalCompleteIntersectionPresentation R f`. It quantifies over every prime `p : Ideal R` with `[p.IsPrime]`, and for every nonzero fibre requires `c ≤ n` and `topologicalKrullDim (PrimeSpectrum (p.Fiber S)) = (n-c : ℕ)`. `p.Fiber S` is Mathlib's κ(p) ⊗[R] S, canonically the fibre ring. The inequality is required only for nonempty fibres, correctly encoding signed n-c; it is not a new global assumption.
- Prime q of S: `q : PrimeSpectrum S`, carrying primality and properness.
- Smoothness at q: the dependency's `Algebra.IsSmoothAtPrime R q`, exactly existence of g outside q with smooth S_g. Mathlib `IsSmoothAt` is deliberately not substituted, since it defines formal smoothness of the local ring.
- Subset I of n indices with size c: `∃ i : Fin c → Fin n, StrictMono i ∧ ...`. The range of i is a c-element subset. Conversely every such subset has its unique increasing enumeration, so no subset is excluded and no ordering/sign ambiguity is introduced.
- Matrix rows j=1,...,c and columns the increasingly ordered elements of I: `fun j k : Fin c ↦ MvPolynomial.pderiv (i k) (f j)`.
- Formal partial derivatives: `MvPolynomial.pderiv`, the recorded Mathlib match of def-weil-pbc-polynomial-partial-derivative.
- Determinant g_I in the polynomial ring: `Matrix.det` of this matrix, not of its transpose.
- Image bar g_I in S: `Ideal.Quotient.mk (Ideal.span (Set.range f))` applied to that polynomial determinant.
- The image lies outside q: `... ∉ q.asIdeal`.
- Both directions, with no extra conclusion: `IsSmoothAtPrime R q ↔ ∃ ...`.

Dependency declarations read in full with docstrings and used:

- def-weil-pbc-mv-polynomial-ring: Mathlib.Algebra.MvPolynomial.Basic, `MvPolynomial`; also read its universal-property declarations `MvPolynomial.algHom_ext` and Mathlib.Algebra.MvPolynomial.Eval, `MvPolynomial.aeval`. Only the carrier is needed by this statement.
- def-weil-pbc-relative-global-complete-intersection: Sheaf.Paper.RelativeGlobalCompleteIntersection, `Algebra.IsRelativeGlobalCompleteIntersection`, read in full. The delivered Sheaf.RingTheory.RelativeGlobalCompleteIntersectionPresentation imports it and supplies `Algebra.IsRelativeGlobalCompleteIntersectionPresentation`, the missing first clause of the same node. It reuses `Ideal.Fiber`, `PrimeSpectrum`, and `topologicalKrullDim` through the dependency's imports.
- def-weil-pbc-polynomial-partial-derivative: Mathlib.Algebra.MvPolynomial.PDeriv, `MvPolynomial.pderiv`; read the derivation signature, pderiv_monomial and pderiv_X.
- def-weil-pbc-singular-ideal: Sheaf.RingTheory.SingularIdeal, `Algebra.IsSmoothAtPrime`; read the recorded singularIdeal and all auxiliary declaration signatures/docstrings, including its definition of smoothness at a prime. Only IsSmoothAtPrime is needed here.
- def-weil-pbc-matrix-determinant: Mathlib.LinearAlgebra.Matrix.Determinant.Basic, `Matrix.det`; read det_apply, whose Leibniz formula has exactly the node's orientation.

Edge cases checked before writing:

- c=0: the unique empty increasing map exists and det of the empty matrix is 1. It avoids every prime, giving smoothness of the polynomial ring, including n=0.
- c>n: there is no strictly increasing map. The fixed-presentation condition forces all fibres empty, hence S=0; no prime q can then be supplied. This case is not ruled out by an added global c≤n binder.
- Zero R or zero quotient: no prime q exists; the theorem does not impose Nontrivial R or Nontrivial S.
- n=c: the only c-element subset is all variables and the condition is the full Jacobian determinant, with the expected orientation.
- Arbitrary characteristic: pderiv has the integer exponent coefficient reduced in R; no characteristic restriction is introduced.
- Why the existential predicate alone is insufficient: over a nonzero field k, take n=1,c=2 and f=(x,0). The quotient k is a relative global complete intersection as a ring map and is smooth, but no two-column minor exists. Thus it is essential to use the given presentation's dimension condition, exactly as 00SP and the node prescribe.

Searches performed (actual tool results):

- msearch.py leansearch: `relative global complete intersection smooth at prime iff a maximal Jacobian minor is outside the prime`; service unavailable (Internal Server Error), recorded in searches.jsonl, no absence conclusion drawn.
- msearch.py leanfinder: `quotient polynomial algebra smooth at prime if and only if some maximal Jacobian minor is not in prime for complete intersection`; eight results, including SubmersivePresentation.isStandardSmooth, IsStandardSmooth, Smooth.exists_span_eq_top_isStandardSmooth, IsSmoothAt.exists_notMem_isStandardSmooth. None asserts this fixed-presentation equivalence.
- msearch.py loogle: `Algebra.PreSubmersivePresentation.jacobian`; twelve results concerning submersive presentation Jacobians and their unit property, no complete-intersection-at-prime equivalence.
- msearch.py grep: `00TE|jacobian.*smooth|smooth.*jacobian`, RingTheory; two docstring hits in Smooth/Local.lean, no exact statement.
- rg of `jacobian|Jacobian|complete.intersection` in WeilConjectures and lean/Sheaf: existing square Jacobian and standard smooth material, existing existential complete-intersection definition and equation-count localization's explicitly inline fixed-presentation condition. No named fixed-presentation predicate or this theorem.
- rg for the item id in WeilConjectures and dag/lean_names_upstream.json: no matching declaration.
- rg for the two proposed declaration names in Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no collision.

## Dependency modules

`def-weil-pbc-relative-global-complete-intersection`: its old record names only `Algebra.IsRelativeGlobalCompleteIntersection`, which existentially quantifies n,c and relations. The node also defines the condition for specified n,c,f, and that is what this lemma needs. Sheaf.RingTheory.RelativeGlobalCompleteIntersectionPresentation supplies this previously unrecorded clause as `Algebra.IsRelativeGlobalCompleteIntersectionPresentation`; it imports and retains the original ring-map predicate without redefining it. The expression is the same fibre condition used inside the original definition and inline in the landed equation-count localization module. Only the dependency node's lean record changes, with a note explaining this mismatch. No dependency statement is changed and no new definition node is required.

Compilation and dry-run results are recorded below after validation.

Validation: scompile.py compiled both modules together cleanly on the server (exit 0,
1.6 seconds, no warnings). deliver2.py --no-push printed OK: all applicable preflight
checks and server compilation passed; only the independent second reading remains for
its assigned reader. Nothing was pushed, and no second-reading section was authored here.


## Second reading by M1

Read independently: the item node and both delivered modules, every statement-dependency
node and its recorded declaration, the existing ring-map complete-intersection module,
and Stacks [00TE](https://stacks.math.columbia.edu/tag/00TE) and
[00SP](https://stacks.math.columbia.edu/tag/00SP). The local Stacks .tex checkout is absent;
the official pages supply the source statement and proof. No standing field,
Noetherian, nontriviality, or characteristic hypothesis is assumed by these sources.

Object/hypothesis/conclusion checklist (all verdicts PASS):

1. Arbitrary commutative R: `(R : Type v) [CommRing R]`. Explicit `universe v`;
   no restriction to fields or Noetherian rings.
2. Nonnegative counts n,c and c equations in n variables: `(n c : ℕ)` and
   `(f : Fin c → MvPolynomial (Fin n) R)`. Fin indexing shifts 1-based names
   without changing the finite families. `MvPolynomial` is the dependency's
   finitely supported monomial algebra; its `aeval` and `algHom_ext` signatures
   confirm the stated universal property.
3. The displayed quotient S and its R-algebra structure: every occurrence is
   `MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)`, with the canonical quotient
   algebra. There is no second S or unrelated structure map.
4. This particular presentation is a relative global complete intersection:
   `hci : IsRelativeGlobalCompleteIntersectionPresentation R f`. Opening its
   definition shows precisely `∀ (p : Ideal R) [p.IsPrime], Nontrivial (p.Fiber S) →
   c ≤ n ∧ topologicalKrullDim (PrimeSpectrum (p.Fiber S)) = (n-c : ℕ)`.
   `Ideal.Fiber` is κ(p) ⊗[R] S; commutativity identifies it with the node's
   tensor order. The dimension is that of the fibre spectrum, not a local ring.
   `c ≤ n` only on nonempty fibres correctly encodes signed n-c.
5. A prime q of S: `q : PrimeSpectrum S`, whose `asIdeal` is prime and proper.
6. Smoothness at that prime: `IsSmoothAtPrime R q`. The imported definition
   is `∃ g : S, g ∉ q.asIdeal ∧ Smooth R (Localization.Away g)`;
   it matches the recorded dependency and does not replace it with local formal
   smoothness `IsSmoothAt`.
7. A subset I of cardinality c, increasingly ordered: `∃ i : Fin c → Fin n,
   StrictMono i ∧ ...`. Such a map is injective and enumerates its c-element
   range; every c-element subset of Fin n admits exactly this enumeration.
8. The c-by-c matrix has equations as rows and selected variables as columns:
   `fun j k : Fin c ↦ MvPolynomial.pderiv (i k) (f j)`. I opened `pderiv`,
   `pderiv_monomial`, and `pderiv_X`: these are formal derivatives over R in
   arbitrary characteristic, not analytic differentiation.
9. Polynomial determinant g_I: `Matrix.det` on that matrix. `det_apply` has
   the node's Leibniz formula and orientation; empty matrices have determinant 1.
10. Its image in S: `Ideal.Quotient.mk (Ideal.span (Set.range f))` applied to
    the determinant. This is the quotient map, not evaluation in another algebra.
11. Avoiding q: that image `∉ q.asIdeal`. The outer `↔` gives both directions,
    and the existential subset is inside its right side, just as in the node.

Dependency-module review (H13): the existing
`Algebra.IsRelativeGlobalCompleteIntersection` quantifies existentially over
presentations. The node separately specifies what it means for a given
presentation, so the old record is unusable for hypothesis 4. The delivered
`IsRelativeGlobalCompleteIntersectionPresentation` supplies that clause, imports
and retains the ring-map definition, and contains full predicate data, no sorry.
Its note explains the mismatch and both clauses of the definition. No new definition
node is introduced, and no dependency statement is changed. The predicate is
not hollow: for example over a nonzero field the presentation (x,0) with n=1,c=2
fails it even though its quotient is a smooth complete-intersection ring map.

Edge cases: c=0 uses the empty increasing map and determinant 1; n=c=0 is
included. With n=0<c or c>n there is no increasing map, and the complete-
intersection hypothesis forces every fibre empty and hence S=0, so no q exists.
For zero R or zero S there is likewise no q; no Nontrivial assumption was added.
For n=c the only subset is all variables. Characteristic is unrestricted.
All variables and universes are explicitly bound; the quotient's universe is
inherited from R, so no independent algebra universe or test-object restriction
occurs. There is no separate scheme hypothesis; an empty affine spectrum is
covered by the zero-ring case.

Independent searches with different wording:

- msearch leanfinder: "smooth locus of a quotient with expected fibre dimension
  detected by determinants of derivatives of its given equations": eight hits,
  including `IsStandardSmooth`, `SubmersivePresentation.isStandardSmooth`, and
  `Smooth.exists_span_eq_top_isStandardSmooth`; none states this fixed-presentation
  equivalence at a prime.
- msearch loogle: `MvPolynomial.pderiv, Matrix.det`: zero hits.
- rg of `complete intersection|CompleteIntersection|jacobian|Jacobian` in Mathlib
  RingTheory/Smooth and RingTheory/Extension/Presentation, the source
  WeilConjectures tree, and project lean/Sheaf: local cotangent injectivity
  criteria, submersive-presentation Jacobians, square Jacobian presentations,
  and the existing existential complete-intersection predicate, but no exact
  statement or named fixed-presentation condition. I opened
  `FormallySmooth.iff_injective_lTensor_residueField`; it has a local algebra,
  formal smoothness, and cotangent injectivity, rather than this conclusion.
  The project's equation-count module uses the same condition inline, not
  as a reusable predicate. Source occurrences concerning Jacobian varieties
  are unrelated.

Conventions and proof review: both module/declaration source docstrings carry
exact blueprint ids. The theorem docstring follows all eight node proof steps:
conormal basis and differential; smooth localization and left inverse;
nonzero localization and c≤n; maximal minors generating 1;
principal-localization presentation; variable renaming; triangular Jacobian
with determinant g_I²; standard smooth implies smooth. The sole theorem proof
is `by sorry`, and the predicate contains no proof hole. Imports are used and
no universe or variable is unbound. Both node records retain the verbatim
Lean signatures.

Mismatches found: none. Changes: appended this independent review only;
Lean statements, definitions, node statements, and worker report retained.

Second-reader validation: scompile.py compiled both modules together in dependency
order, exit 0, 1.6 seconds, with no warnings.
