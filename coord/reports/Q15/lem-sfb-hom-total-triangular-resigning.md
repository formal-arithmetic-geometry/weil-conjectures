## Worker report

Stage 2 statement for `lem-sfb-hom-total-triangular-resigning`, in
`Sheaf.Algebra.Homology.HomTotalTriangularResigning`.
The main declaration is `CochainComplex.hom_total_triangular_resigning`.
It is the only theorem and its proof is `sorry`. The six auxiliary definitions have
real data; none chooses an object from a postponed existence theorem.
No statement correction, dependency repair or new node is needed. The accepted
Q150 stage-1 statement, dependencies and seven-step proof remain unchanged.

The inherited BLOCKED message concerned an attempted stage-1 re-split. I checked
the live node (reviewed PASS, no lean record), queue (stage 2), and repair-notes
(no note). The stage-handoff paragraph of brief-stage2 §0 specifically authorizes
recording this accepted split's Lean statement. Nothing reopens stage 1 here.

Hypotheses and every statement clause:

- Abelian category in a fixed morphism universe: `{E : Type u}`,
  `[Category.{v} E] [Abelian E]`. `u` and `v` are independent explicit universes.
  The Hom groups and both complexes of groups are in `AddCommGrpCat.{v}`.
  `[HasDerivedCategory.{w} AddCommGrpCat.{v}]` records the localization choice
  in the node's chosen universe; it imposes no mathematical extra condition,
  since `HasDerivedCategory.standard` always supplies the standard larger choice.
- Cochain complexes and bounds: `(P I : CochainComplex E ℤ)`,
  `hP : ∀ i, 0 < i → IsZero (P.X i)` and
  `hI : ∀ r, r < 0 → IsZero (I.X r)`.
- `P_p = P^{-p}` and `∂_{p+1} = d_P^{-p-1}`: the constructed
  `homTotalBicomplex P I` has object `AddCommGrpCat.of (P.X (-p) ⟶ I.X r)`;
  its horizontal map precomposes by `P.d (-p') (-p)`, with `p'=p+1` when
  nonzero. Its vertical map postcomposes by `I.d r r'`. The structure equations
  are supplied by the actual two complex equations and associativity.
- The product-defined complex `C` is the existing `CochainComplex.HomComplex P I`.
  Mathlib uses all integer source degrees rather than only nonpositive ones.
  `homTotalRestriction P I n` explicitly restricts to the node's exact product
  `∀ p : ℕ, P.X (-↑p) ⟶ I.X (n-p)`; the first conjunct asserts this canonical
  restriction is an isomorphism. The omitted positive-source factors are zero.
  Thus this encoding changes no objects up to the stated canonical identification.
- Its differential is Mathlib's `HomComplex.δ n (n+1)`; by its read signature
  and component formula `δ_v`, it is postcomposition by `d_I` plus
  `(n+1).negOnePow` times precomposition by `d_P`, exactly `d_Ix-(-1)^n x∂`.
- Only `0 ≤ p ≤ n` contribute: the fourth conjunct says every coordinate with
  natural `p` and `n < p` is zero; the comparison formula sums only over
  `Finset.Icc (0 : ℤ) n`. The second conjunct states `C^n=0` for `n<0`.
- First-quadrant commuting double complex: `homTotalBicomplex` is Mathlib's
  `HomologicalComplex₂`, and the third conjunct states its vanishing for
  `p<0 ∨ r<0`. The horizontal and vertical formulas are literal constructor
  data, not hypotheses requiring an externally supplied bicomplex.
- The total is `(homTotalBicomplex P I).total (ComplexShape.up ℤ)`, the dependency's
  existing construction. Mathlib's convention here is `d_h+(-1)^p d_I`.
  Its degreewise diagonal coproduct exists in abelian groups without any new
  assumption; first-quadrant vanishing makes that diagonal finite in support.
- The bidegree multiplier is the explicit integer unit
  `homTotalTriangularSign p r = (p*r+p*(p+1)/2).negOnePow`.
  Although the formula is extended to integer indices, its sign recurrence
  conjuncts and inverse formula quantify exactly over `p,r ≥ 0` as the node does.
- The specified cochain isomorphism is the existential `T : HomComplex P I ≅ ...`.
  Its hom is characterized on every cochain by the finite sum of diagonal
  inclusions of precisely the signed coordinates. This specifies the actual
  morphism uniquely, rather than merely postulating an unspecified isomorphism
  or an isomorphism on cohomology.
- Its inverse uses the same multipliers: the next clause computes every
  nonnegative `(p,r)` coordinate of `T.inv` as the same sign times
  `homTotalProjection P I (p+r) p r`. The projection is explicitly constructed by
  `totalDesc`, with identity at that summand and zero at all others.
  Coordinates outside that quadrant have zero source or target by the bounds.
- `δ²=0` is explicitly the fifth conjunct. `Tδ=dTot T` is explicitly the clause
  quantified over integer `n` and every Hom cochain, including negative degrees.
- The derived isomorphism is explicitly an `e` in `DerivedCategory AddCommGrpCat`.
  Its hom is `DerivedCategory.Q.map T.hom` and its inverse is
  `DerivedCategory.Q.map T.inv`. This is precisely the specified `Q(T)`, not a
  cohomology-only comparison.
- Both multiplier recurrences are the sixth conjunct, with the factors written
  as integer units `p.negOnePow` and `(p+r+1).negOnePow`.
- For every `n≥0`, being `δ`-closed is equivalent to being the same family as
  a morphism `f : P ⟶ I⟦n⟧`. The penultimate clause states this equivalence;
  `homTotalMapFamily` is `Cochain.ofHom f` followed by `rightUnshift`, which
  removes only the shifted target identification, with no multiplier.
- For maps `f,g` and `H : Homotopy f g`, the final clause gives both
  `family f-family g = n.negOnePow • δ (family H)` and the corresponding total
  boundary equation after applying `T.hom`. `homTotalHomotopyFamily` uses
  `Cochain.ofHomotopy` and `rightUnshift (n-1)`, so the underlying family is
  unchanged. Mathlib's `δ_ofHomotopy` and shift convention are exactly
  `f-g=d_{I[n]}H+Hd_P`. All degrees `n≥0`, including zero, are quantified.
- There are no injectivity, projectivity or Hom-exactness assumptions.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`. Its finite-product definition is
  equivalent to the node's finite-biproduct formulation.
- `def-weil-preadditive-category`: `CategoryTheory.Preadditive`,
  `Mathlib.CategoryTheory.Preadditive.Basic`, including its abelian Hom groups,
  bilinear composition, and `Preadditive.leftComp` / `rightComp`.
- `def-weil-size-convention`: the recorded metatheoretic convention, implemented
  by explicit independent `u v w`, not an invented definition or an extra axiom.
- `def-weil-abstract-derived-category`: `CochainComplex`,
  `HomologicalComplex`, `DerivedCategory`, `HasDerivedCategory`, and
  `DerivedCategory.Q`, from `Mathlib.Algebra.Homology.DerivedCategory.Basic` and
  its imports. `HomComplexShift` supplies the existing shift and family APIs.
- `def-sp-double-complex-total`: recorded
  `WeilConjectures.CategoryTheory.DoubleComplexTotal` is publicly imported;
  its public Mathlib `HomologicalComplex₂`, `ofGradedObject`, `total`,
  `ιTotalOrZero` and `totalDesc` construct exactly the node's commuting total.
  No new filtration or total notion is introduced.

All statement dependencies are public imports or their transitive imports.
The only additional proof dependency, Preadditive, is already publicly exposed
because the statement's Hom groups and canonical maps themselves use it.

Edge cases checked before writing and again against the signature:

- `n<0`: the finite interval is empty, all product factors vanish, and `T` is
  between zero groups. The signature explicitly includes negative `n`.
- `n=0`: the sole nonzero diagonal coordinate is `(0,0)`, multiplier one.
  A degree -1 homotopy has target `I^{-p-1}=0` on every nonpositive source;
  positive source objects vanish. Thus the final equation says `f=g`, as required.
- The new edge outputs `(0,n+1)` and `(n+1,0)` have the correct missing horizontal
  and vertical contributions, respectively; the two recurrences match them.
- Small signs: `t(0,0)=1`, `t(1,0)=-1`, `t(0,1)=1`, `t(1,1)=1`.
  The differences of the exponent are `p` vertically and `p+r+1` horizontally.
- Zero input complexes, zero Hom groups and groups killed by 2: negation and the
  identity coincide where appropriate; no division by 2 in a coefficient group
  occurs, only integer division of the always-even integer `p(p+1)`.
- No boundedness stronger than the stated one-sided bounds, no finiteness of
  Hom groups and no equality of object/morphism universes is imposed.

Searches for existing declarations (2026-10-23):

- `msearch.py ... leanfinder` query: “The Hom complex of a nonpositive complex and
  a nonnegative complex is isomorphic to the finite total of the commuting Hom
  bicomplex by triangular signs”. Eight results, including
  `HomologicalComplex₂.ι_totalShift₂Iso_inv_f`, `ι_totalShift₁Iso_inv_f` and
  `totalShift₁Iso_hom_totalShift₂Iso_hom`; these concern shifts of an existing
  bicomplex, not this Hom/total comparison with homotopy normalization.
- `msearch.py ... loogle` query `CochainComplex.HomComplex, HomologicalComplex₂.total`:
  successful, zero hits.
- `msearch.py ... grep 'HomComplex|triangular|resign' Algebra/Homology`:
  existing Hom-complex, homotopy and shift files, no matching triangular comparison.
- `msearch.py ... leansearch` query: “The Hom complex differential is conjugate to
  the commuting double complex total differential by triangular signs”. Eight
  results, including `HomComplex.δ_hom`, `δ`, `Cochain.diff`,
  `HomComplex_d_hom_apply` and `HomologicalComplex₂.totalAux.d₁_eq`;
  they give the reused ingredients, not the full statement.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `triangular|resign|hom-total-triangular|homDouble|HomDouble|homBicomplex|HomBicomplex`:
  the closest source is `HomComplexDualTotalComparison`, for internal Hom of
  module sheaves into an opposite total at degree `-n`. I read its signature;
  it concerns different objects and hypotheses and is not this statement.
- Exact item-id search over `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no declaration carrying this node.
- Exact names of all seven new declarations searched in Mathlib, both project
  roots and `dag/lean_names_upstream.json`: no collisions.

Source read: `literature/blueprint/latest/.../sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3). It gives the route; the actual sign computation is correctly
recorded by the accepted node as an agent-extracted argument, with an internal
category reference WANTED. This delivery preserves that provenance, does not
attribute the triangular comparison itself to a nonexistent Stacks theorem,
and uses Stacks only for the complex, total, shift and localization conventions.

Validation: `scompile.py Q15 lem-sfb-hom-total-triangular-resigning` compiled the
sandbox and final named module cleanly (4.2 and 1.9 seconds), with no errors or
non-sorry warnings. Every variable and universe is explicitly bound, no local
notation/instance/private interface is used, and no line exceeds 100 characters.

## Second reading by Q15

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
