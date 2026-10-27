## Worker report

The module `Sheaf.AlgebraicGeometry.AffineGroupoidRankwiseMonicGluing` states
`AlgebraicGeometry.affineGroupoid_rankwise_monic_gluing`, with one postponed proof
and no new definitions. The natural-language statement and all other node fields
are unchanged. No new nodes, dependency repairs, or statement correction are needed.

Sources read: `literature/stacks-project/groupoids.tex`,
`lemma-finite-locally-free-disjoint-free` (Tag 03BI), and
`lemma-integral-over-invariants` (Tag 03BJ), especially its first proof paragraph;
`literature/stacks-project/schemes.tex`, `lemma-disjoint-union-affines` (Tag 01I5),
whose proof identifies the section ring with the product by the sheaf property.
The node makes the reduction/recombination in 03BJ explicit; the theorem does
not assert existence of the rankwise annihilators.

Hypotheses, with no additional mathematical assumptions:

- The commutative rings are `A B : CommRingCat.{u}`; their affine schemes are
  `Spec A` and `Spec B`. The universe is arbitrary and includes the zero ring.
- The maps `s t`, `e`, `i`, and `c : pullback s t ⟶ Spec B` have precisely the
  node's domains and codomains and its composition convention.
- `hG : Scheme.IsGroupoid s t e i c` is the recorded definition of all groupoid
  laws on every test scheme. No freeness, equivalence-relation, or extra base
  condition is assumed.
- `[s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree]` are the two finite locally
  free assumptions, using the dependency's existing classes.

Every conclusion and conditional clause is rendered as follows:

- `I : Finset ℕ` and `∀ r : I, 0 < r.1` give a finite set of positive integers.
  `U : I → (Spec A).Opens` supplies the open pieces. Nonemptiness, closedness,
  and affineness are exactly `Nonempty (U r).toScheme`, `IsClosed ...`, and
  `IsAffine (U r).toScheme`. `Pairwise ... Disjoint` and `iSup U = ⊤` express
  their disjoint union decomposition.
- `V : I → (Spec B).Opens` satisfies both `V r = s ⁻¹ᵁ U r` and
  `V r = t ⁻¹ᵁ U r`, with `IsAffine (V r).toScheme`. Thus it is the node's
  invariant arrow piece, not a separately chosen unrelated affine scheme.
- Families `s' t' e' i' c'` have the restricted domains. The groupoid predicate,
  the two `IsFiniteLocallyFreeOfDegree r.1` conclusions, and the four equations
  with the open inclusions assert the groupoid structure and restriction of
  source, target, identity, and inverse. The family `k` has both pullback
  projection equations; hence it is the canonical induced map on composable
  pairs. `c' r ≫ (V r).ι = k r ≫ c` asserts restriction of composition.
- The invariant subring `C` is constrained by equality to
  `(Spec.preimage s).hom.eqLocus (Spec.preimage t).hom`; `Spec.preimage` is the
  inverse of `Spec.map` and is exactly the affine coordinate homomorphism.
  `Cᵣ r` is constrained by equality to the equalizer of `(s' r).appTop.hom` and
  `(t' r).appTop.hom`. Consequently all three rings are the specified rings,
  rather than arbitrary subrings chosen to make the statement true.
- The rings of pieces are literally `Γ((U r).toScheme, ⊤)` and
  `Γ((V r).toScheme, ⊤)`. The witnesses `ρA`, `ρB`, and `ρC` are ring
  equivalences onto their dependent product rings. Each component of `ρA`
  and `ρB` is required to equal the open-inclusion map on global sections,
  composed with `(Scheme.ΓSpecIso A).inv` or `(Scheme.ΓSpecIso B).inv`.
  These equations fix the canonical restriction maps.
- The two equations for `ρB ((Spec.preimage s).hom a) r` and the analogous
  target term are precisely the required source and target compatibility.
  Coercing `ρC a r` to the section ring gives `ρA (a : A) r`, specifying that
  `ρC` is the restriction of `ρA`.
- The conditional polynomial clause universally quantifies `a : A` and
  `P : ∀ r : I, Polynomial (Cᵣ r)`, then assumes `I.Nonempty` and the
  rankwise conditions. On a nonempty affine piece its section ring, and
  therefore its unital subring `Cᵣ r`, are nonzero. Thus `(P r).Monic` and
  `(P r).natDegree = r.1` say exactly that `P r` has the displayed expansion
  `X^r + sum of coefficients in lower degrees`. They introduce neither an
  extra hypothesis nor a restriction on the permitted coefficient choices.
  `(P r).eval₂ (Cᵣ r).subtype (ρA a r) = 0` is exactly `P_r(a_r)=0`.
- `d = I.sup id` specifies the maximum rank: the supremum of a nonempty
  finite set of natural numbers is its maximum. The formula for `Q` is
  `X^d + ∑ j ∈ Finset.range d, C(q_j) * X^j`, where `q_j` is exactly
  `ρC.symm (fun r ↦ (X^(d-r.1) * P r).coeff j)`. This explicitly gives the
  padded coefficient tuples `q_{r,j}` and their recombination; the statement
  does not merely assert existence of some annihilator.
- `Q.Monic` is the monicity assertion. Its `map` along
  `(Pi.evalRingHom ... r).comp ρC.toRingHom` is explicitly
  `X^(d-r.1) * P r`, the coefficientwise restriction equation.
- For each `r`, the statement gives both
  `ρA (Q.eval₂ C.subtype a) r = (ρA a r)^(d-r.1) * P_r(a_r)` and the
  vanishing of that right-hand side. The final equality is
  `Q.eval₂ C.subtype a = 0`, exactly the global annihilation equation.
- The final implication handles `IsEmpty (Spec A)` without invoking the
  nonempty-polynomial clause: `I = ∅`, `Subsingleton A`, monicity of
  `(Polynomial.X : Polynomial C)`, and its evaluation at every `a : A`
  equal to zero. This expresses the unique element and its specified
  monic annihilator. The three product equivalences are outside the
  conditional and therefore also hold in this case.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Spec`, `Spec.map`, `Scheme.Hom.appTop`, and
  `Scheme.ΓSpecIso`; these give schemes, morphisms, spectra, section maps,
  and the canonical identification of the coordinate ring.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Spec.preimage` and
  `Spec.homEquiv`; the latter's forward map is the former.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, and `pullback.snd`, available through the
  recorded groupoid module's public pullback import.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidLaws`: `Scheme.IsGroupoid`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFree` and `IsFiniteLocallyFreeOfDegree`.
- `Mathlib.Algebra.Polynomial.Basic`, `Eval.Defs`, `Monic`, and
  `Degree.Defs`: `Polynomial`, `eval₂`, `map`, `coeff`, `natDegree`,
  `Monic`, `X`, and `C`.
- `Mathlib.Algebra.Ring.Subring.Basic`: `RingHom.eqLocus` and
  `Subring.subtype`; `Mathlib.Algebra.Ring.Pi`: `Pi.evalRingHom`.

Proof dependencies are imported without `public`:
`Sheaf.AlgebraicGeometry.AffineGroupoidInvariantRankStrata`, containing
`affineGroupoid_exists_invariant_rank_strata`, and the two Mathlib sheaf
modules containing `TopCat.Sheaf.isProductOfDisjoint` and
`TopCat.Sheaf.objSupIsoProdEqLocus`. Their full declarations and docstrings
were read. The existing rank-strata theorem uses `IsGroupoidScheme`, whereas
this node's recorded definition is `Scheme.IsGroupoid`. Both express exactly
the same test-scheme groupoid laws, the former with chosen pullback lifts and
the latter with universally quantified pullback points. Conversion follows
from the pullback universal property; no new notion or stronger assumption
is needed. The proof docstring records this translation.

Edge cases checked before finalizing the statement:

- Empty spectrum / zero ring: no `Nontrivial A` or nonempty-piece index
  assumption occurs outside the conditional polynomial clause. Products
  over an empty index set are the zero ring; the invariant subring is a
  zero ring too. Mathlib defines `Monic` as leading coefficient equal to
  one, so `X` is indeed monic over that zero ring.
- A singleton rank set gives `d=r`, padding exponent zero, and precisely
  the original polynomial.
- Ranks one and unequal positive ranks are allowed. For example ranks
  one and three pad a degree-one polynomial by `X^2`, inserting zero
  coefficients in degrees zero and one. The formula uses the padded
  coefficients directly and matches the node's coefficient recipe.
- Rank zero is excluded only for nonempty pieces by positivity, as
  required by the identity section. No characteristic or reducedness
  assumption is present.
- All equalizer subrings and maps use the same arbitrary universe as
  their ambient rings. The finite rank index is a subtype of `ℕ`, so it
  creates no extra universe or finiteness restriction.
- Failure to supply rankwise polynomials gives no annihilator assertion:
  the main polynomial result is genuinely conditional.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder` with query “Affine finite locally free scheme
  groupoid invariant rank decomposition product invariant rings glue monic
  annihilating polynomials”: eight unrelated/partial hits, including
  `instIsIsoSchemeSigmaSpecOfFinite`; no theorem combining all clauses.
- `msearch.py ... loogle` with query `Polynomial.map, RingHom.eqLocus`:
  zero hits.
- `msearch.py ... grep` with query `rank.*strat|monic.*glu|eqLocus`:
  25 hits, including Mathlib's ring/subring equalizer definitions; these
  supply the standard notion, not this gluing theorem.
- `rg -n` over `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry` with
  `rankwise|monic.*glu|invariant.*[Rr]ank|eqLocus|affine-groupoid-rankwise`:
  existing invariant-ring, integrality, norm, and rank-strata declarations;
  none gives the product equivalences and the specified coefficient formula.
- `grep -rn` for this node id in `lean/WeilConjectures`: no hit.
- `rg -n` for the proposed full theorem name in `lean/Sheaf`,
  `lean/WeilConjectures`, Mathlib, and `dag/lean_names_upstream.json`:
  no existing declaration.

Validation: the prescribed `scompile.py` compiled both its sandbox module
and the library module without errors or warnings. The file explicitly
sets `autoImplicit false`, binds universe `u`, contains one theorem with
proof `sorry`, and has no line exceeding 100 characters. The delivery dry
run recompiled the final file and passed the server preflight (commit
`8370b39df22`; nothing pushed by that check).

No `STATEMENT-DISPUTED` issue was found. The node's old example module
`CompactObject.lean` has been withdrawn in the current checkout; the
current public-module header and visibility convention were followed.

## Second reading by Q93

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
