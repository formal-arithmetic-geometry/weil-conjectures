## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothCurveHighDegreeHilbertStability` states
`AlgebraicGeometry.exists_uniform_smooth_curve_high_degree_hilbert_stability`.
Its only theorem has proof `sorry`. It introduces no definitions, axioms, new nodes,
or dependency repairs, and changes only the item's `lean` field.

Source checked: Morrison, *GIT Constructions of Moduli Spaces of Stable Curves and
Maps*, arXiv:0810.2340, Section 2.4, Theorem 5, printed pp.10--11, at
https://arxiv.org/pdf/0810.2340 (online PDF read, pages 10--12). The theorem gives
asymptotic Hilbert stability uniformly over high-degree complete series. The
preceding Lemma 4(3) gives the uniform criterion; the accepted DAG proof already
corrects the source's endpoint gap and the factor two in its polygon estimate.
The inherited proof is retained in full, with its six steps rendered in the Lean
docstring. The paper is not copied or changed in the read-only repository.

Hypotheses and clauses, in the order of the node:

* Integers `g >= 2`, `d >= 2g+1`: `(g d : ℕ)`, `(hg : 2 ≤ g)`,
  `(hd : 2 * g + 1 ≤ d)`. Every integer allowed by these inequalities is
  nonnegative, so these binders exclude no case. Degree is compared in `ℤ`.
* Put `r=d+1-g`: the coordinate type is `HilbertPlucker.Coordinates n`, whose
  definition is `ULift (Fin (n+2))`, and `n + 2 + g = d + 1` fixes its size.
  Since the numerical hypotheses give `r >= 4`, parametrizing `r` by `n+2`
  covers every allowed case without truncating integer subtraction.
* There is an integer bound depending only on `g,d`: `∃ M : ℕ` occurs before
  **all** binders for `k,C,L,n,i,e,m` and their hypotheses. A natural bound is
  equivalent to an integer bound on nonnegative Hilbert degrees by increasing
  an integer bound to its maximum with zero.
* Every algebraically closed field: `∀ (k : Type u) [Field k] [IsAlgClosed k]`.
  The universe `u` is explicit; field and schemes use the same arbitrary universe.
  No characteristic, perfectness, or characteristic-zero hypothesis is imposed.
* A curve over `k`: `(C : Scheme.{u}) [C.Over (Spec (.of k))]` supplies its
  structure map. `[IsConnectedCurve (C ↘ Spec (.of k))]` uses the existing
  connected-curve class, including nonemptiness, connectedness, dimension one,
  separatedness and finite type. In particular the weaker bare `IsCurve` class
  alone is not mistaken for a connected curve.
* Smooth projective: `[Smooth (C ↘ Spec (.of k))]` and
  `[IsHProjective (C ↘ Spec (.of k))]` use the dependency conventions.
* Genus `g=dim H¹(O_C)`: `C.arithmeticGenus k = g` uses exactly the recorded
  cohomological arithmetic genus, not a different genus or an abstract parameter.
* Invertible module of degree `d`: `(L : C.Modules) [L.IsInvertible]` and
  `L.degree k = (d : ℤ)` use the recorded invertibility and Euler-characteristic
  degree. No ampleness condition is added: the assumed embedding supplies it.
* The given embedding: `(i : C ⟶ ℙ(HilbertPlucker.Coordinates n; Spec (.of k)))`,
  `IsClosedImmersion i`, and the equality of its composite with the projective
  structural projection to `C ↘ Spec k`. This is an embedding over the given
  field structure, rather than a scheme embedding with an unrelated scalar action.
* Complete linear system of `L`, with chosen coordinate identification and evaluation:
  `e : (Scheme.Modules.tensorPullback i).obj (ProjectiveSpace.twist ... 1) ≅ L`
  identifies the hyperplane pullback with the specified line. The displayed function
  sums the canonical pulled-back coordinate sections, carried to `L` by `e`,
  against coefficients `a j : k`. Scalars enter by
  `(C ↘ Spec k).appTop.hom ((Scheme.ΓSpecIso (.of k)).inv (a j))`.
  This function is automatically k-linear for the canonical scalar restriction.
  Its `Function.Bijective` hypothesis is precisely the chosen identification
  `k^r ≃ H⁰(C,L)` (equivalently, the coordinate sections form a basis).
  Because these are the sections pulled back from the actual map `i`, their
  evaluation defines that same `i`; an arbitrary chosen association to a map is
  never used. This is the same coordinate-evaluation encoding used in the published
  `GiesekerPotentialStabilityConclusion.complete_nondegenerate`, which was read for
  interface guidance but is not imported or copied as a second notion.
* Every `m >= M(g,d)`: `∀ m : ℕ, M ≤ m → ...`.
* Hilbert polynomial `dm+1-g`: the conclusion supplies a
  `P : NumericalHilbertPolynomial` with the exact equation
  `P.1 = Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C (1 - (g : ℚ))`.
  The subtraction is in `ℚ`, not truncated natural subtraction. The polynomial is
  a conclusion, not an extra assumption about the curve or its embedding.
* Hilbert point **of this embedding**: the conclusion supplies a Hilbert
  representative `D`, its degree-`m` presentation `E`, and
  `x : PGLLinearization.fieldTest k k ⟶ D.H`, with
  `D.ideal.comap (ProjectiveSpace.map ... x.left) = i.ker`.
  This equality is equality of ideal sheaves on the original projective space;
  it retains the full closed subscheme structure. By the component and universal
  ideal fields of `HilbertPlucker.Hilbert`, this is the point of that polynomial
  component classifying the given embedding. No arbitrary map or merely nonempty
  choice of linearization enters the hypotheses or a definition.
* Stable for the specified Hilbert--Plücker linearization:
  `E.pgl_line.IsStable k x`. Here `E` is exactly the recorded
  `HilbertPlucker.Presentation`, which fixes the coordinate action, determinant
  action and descent normalization. Its `pgl_line` linearizes the `r`th tensor
  power of the actual Hilbert determinant, as required by the dependency, and its
  stability uses invariant sections, closed orbit in the semistable locus and
  dimension-zero scheme-theoretic stabilizer. The SL/PGL comparison in that
  presentation ensures this is the intended Hilbert stability in all characteristics.
* Independence of the curve, line and characteristic follows from the displayed
  quantifier order; there is one `M` for all those objects, all coordinate choices,
  and every subsequent degree. The existential presentation is simply an explicit
  representative of the Hilbert point and its prescribed canonical linearization,
  whose representability and existence are given by the dependency. It does not
  replace geometric stability by a numerical criterion or a sufficient condition.

Dependency declarations read and used:

* `Mathlib.Algebra.Field.Defs`: `Field` (the `mathlib_match` of `def-weil-field`).
* `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`:
  `AlgebraicGeometry.Scheme.arithmeticGenus`,
  `AlgebraicGeometry.Scheme.Modules.degree`; full defining signatures and docstrings
  were read, including `C.Over (Spec k)` ambient parameters.
* `Sheaf.AlgebraicGeometry.HilbertPluckerPGLLinearization`:
  `AlgebraicGeometry.HilbertPlucker.Coordinates`, `.Hilbert`, `.Hilbert.H`,
  `.Presentation`, and `AlgebraicGeometry.exists_hilbert_plucker_pgl_linearization`.
  The whole source was read, including coordinate and determinant normalization,
  PGL descent, common stable loci and field extension clauses. The statement uses
  its presentation directly and the proof invokes its theorem.
* `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective` (finite projective-space embedding convention).
* `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
* `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`, read for the presentation's ample lines.
* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
* `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve` and
  `AlgebraicGeometry.IsConnectedCurve`, both signatures and docstrings read.
* Proof-only import `Sheaf.Paper.StrictCodegreePolygonGap`:
  `Gieseker.exists_uniform_strict_codegree_polygon_gap`, whose codegree hypotheses
  and uniform quantifier were checked against proof step 4.
* The proof dependencies `lem-sfb-linear-series-degree-dimension-bound` and
  `lem-sfb-uniform-gieseker-codegree-criterion` have no Lean record or Mathlib
  match in the read repository. They supply no available proof-only module to
  import. They are not needed to type this statement and are not restated here.
  Each is still named in its appropriate step of the theorem's docstring.

Edge cases checked before writing: `g=2,d=5` gives `r=4,n=2`, hence is included;
all larger allowed integers have `n=r-2`; the empty scheme, zero-dimensional
connected schemes and disconnected curves are excluded by exactly the node's
connected-curve hypothesis; `g=0,1` and `d<2g+1` are outside the node; `m=0`
is handled by its same `M ≤ m` implication; no extra `m>0` is assumed. Negative
constant coefficient `1-g` is preserved in the polynomial. Positive characteristic,
including characteristic dividing `r`, remains included. The use of full ideal
sheaves and the dependency's scheme-theoretic stabilizer preserves nilpotents.

Searches performed with the prescribed `msearch.py NE <item>` wrapper:

* LeanFinder: `Uniform Hilbert stability of smooth projective curves embedded by
  complete high degree linear series`: eight unrelated results (Weierstrass
  projective curves and projective-spectrum properness); no stability theorem.
* Loogle: `HilbertPlucker, IsStable`: zero hits, unknown identifier `HilbertPlucker`
  in the search index. Its actual project declaration was read directly instead.
* Mathlib grep: `Hilbert.*[Ss]tab|[Ss]tab.*Hilbert|Gieseker`: one unrelated hit in
  `Mathlib/RingTheory/Nullstellensatz.lean` (the English word establishes).
* LeanSearch: `A complete line bundle of degree at least 2g plus 1 on a smooth
  projective genus g curve is asymptotically Hilbert stable`: eight unrelated
  analytic Hilbert-sum/smooth-structure hits; no GIT stability result.
* Direct `rg -n` on both `lean/WeilConjectures` and `lean/Sheaf`, for
  `Hilbert.*[Ss]tab|[Ss]tab.*Hilbert|[Cc]omplete[Ll]inear|complete.*[Ss]eries`
  and the item's exact id: found the recorded Hilbert--Plücker interface,
  `BoundedHilbertWeightPolynomials.IsHilbertSemistable`, potential stability,
  complete-system closed immersion and ten-canonical parameter constructions.
  None states uniform high-degree **smooth-curve stability**. The semistability
  predicate is different from the stability needed here and is not copied.
  No exact item-id hit was found upstream or in existing project modules.

The full theorem compiles cleanly with the required `scompile.py`, in sandbox
and library module modes (1.9 s and 1.8 s respectively). Both auto-implicit options
are disabled. No `#check`, file-local notation/instance, or temporary probe remains.
No statement dispute or node correction was needed.

## Second reading by NE

This section replaces the delivered self-check of the statement worker ("no second agent was
started"), which is not an independent second reading (H11). It was written by the
maintainer's independent reviewer from the immutable delivery 7a5c063e; the Lean module and
the node record are unchanged.

Node clauses and their Lean rendering, each checked against the dependency declarations:

* g ≥ 2, d ≥ 2g+1 integers: `(g d : ℕ) (hg : 2 ≤ g) (hd : 2 * g + 1 ≤ d)`. Every integer
  satisfying the inequalities is nonnegative. Correct.
* r = d+1-g: `∀ n, n + 2 + g = d + 1`, `Coordinates n = Index (n+2)`. n is determined by
  g,d; r ≥ 4 > 2 so nothing is lost. Correct.
* One integer M(g,d) for every algebraically closed field: `∃ M : ℕ` precedes `k`, `C`,
  `L`, `n`, `i`, `e`, `m`. Uniform in the curve, the line and the characteristic. Correct.
* k algebraically closed: `(k : Type u) [Field k] [IsAlgClosed k]`. No characteristic
  hypothesis. Correct.
* C smooth projective connected curve: `IsConnectedCurve` (= `IsCurve` (separated, locally
  of finite type, quasi-compact, dim ≤ 1) + `ConnectedSpace` + dim = 1), `Smooth`,
  `IsHProjective`, all on `C ↘ Spec k`. These are the def-sc-curves, def-sbc-smooth-morphisms
  and def-kun-projective owners. Correct.
* genus g = dim H¹(C,O_C): `C.arithmeticGenus k = g`, where `arithmeticGenus : ℕ` is
  `finrankH k 𝒪 1` (def-pc-genus). Correct.
* L invertible of degree d: `[L.IsInvertible]`, `L.degree k = (d : ℤ)` (χ(L) − χ(O),
  def-pc-degree-line-bundle). No ampleness added. Correct.
* Embedding by the complete linear system, with chosen k^r ≃ H⁰(C,L): closed immersion
  `i` over Spec k, `e : i^*O(1) ≅ L`, and bijectivity of a ↦ Σ_j a_j · e(i^* x_j). This says
  the pulled-back coordinates form a k-basis of H⁰(C,L), i.e. i is the evaluation map of a
  chosen basis of the complete series. Conversely every such embedding arises (d ≥ 2g+1
  gives very ampleness, so `IsClosedImmersion i` is not an extra restriction). Correct.
* m ≥ M: `∀ m, M ≤ m`. Correct.
* Hilbert point with polynomial dm+1-g: `∃ P, P.1 = C d * X + C (1 - g)` (subtraction in
  ℚ), `D : Hilbert k n P`, `x : fieldTest k k ⟶ D.H` with
  `D.ideal.comap (ProjectiveSpace.map _ x.left) = i.ker`: the k-point of the P-component
  whose pulled-back universal ideal is the full ideal sheaf of i. Correct.
* Stable for the Hilbert–Plücker linearization: `E.pgl_line.IsStable k x` for a
  `Presentation D m`. The existential over D and E is not weaker. `Presentation` pins
  `sl_line` on the wedge generators of the determinant (`determinant_formula`, which
  generate since `surjective`). Its field `stable_points` gives
  `sl_line.IsStable Ω x ↔ pgl_line.IsStable Ω x`. So the stability predicate does not
  depend on the choice of E (or of the group G and its cover). The existence of E for
  m ≥ M(P,r) is the dependency theorem, and M absorbs that threshold. `IsStable` is the
  def-sfb-group-scheme-linearization predicate (invariant sections, closed orbit in the
  semistable locus, 0-dimensional scheme-theoretic stabilizer). Correct.

Edge cases: g=2, d=5 (n=2) included; characteristic dividing r included; empty and
disconnected C excluded exactly as the node does; m=0 handled by `M ≤ m`.

Records: the item node differs from the live node only in `lean`. `lean.statement` is a
verbatim substring of the file. Single theorem with `sorry`, no definitions. Module and
theorem docstrings carry the source place, `(blueprint: …)` and the six proof steps. The
private import `Sheaf.Paper.StrictCodegreePolygonGap` is the landed (2026-10-23) proof
dependency module. Universe u is shared by k and C. No pro-étale substitute.

Searches: rg `IsHilbertStable|HilbertStab|Gieseker|high.degree` on lean/Sheaf and
lean/WeilConjectures found no competing statement. The only related declaration is
`IsHilbertSemistable` (semistability, a different notion).

No mismatch was found in the Lean. The only change is this section.
