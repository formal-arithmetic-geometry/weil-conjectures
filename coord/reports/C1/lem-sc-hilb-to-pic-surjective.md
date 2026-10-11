## Worker report

The module `Sheaf/AlgebraicGeometry/HilbertToPicardSurjective.lean` states
`AlgebraicGeometry.exists_surjective_hilbertToPicardMorphism`. It uses the recorded
Hilbert-to-Picard construction and adds `Surjective γ.left` for the resulting morphism.
The source's integer degree is corrected to a natural number `d : ℕ`, since the Hilbert
functor and the dependency morphism are indexed by `ℕ`; the hypothesis `f.genus ≤ d`
expresses `d ≥ g`.

The Lean statement renders the hypotheses as follows: `k` is a separably closed field;
`f : C ⟶ Spec k` has `[f.IsSmoothProjectiveCurve]` and
`[GeometricallyIntegral f]`; `d : ℕ` satisfies `f.genus ≤ d`; `H` represents
`hilbertPresheaf f d`; and `P` represents `picardFunctorDegree f d`. The universal
Hilbert object is `D := (eH.homEquiv (𝟙 H)).1`. Its relative effective Cartier and
invertibility clauses are retained, as are the existence of the universal Picard class
`L`, its isomorphism to `D.toModulesᵛ`, and its fibrewise degree `d`. The classifying
morphism `γ : H ⟶ P` is required to have the recorded representing equality and
`Surjective γ.left`, which is the underlying scheme morphism's surjectivity.

Dependencies used: `Sheaf.AlgebraicGeometry.HilbertToPicardMorphism`,
`WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`, and Mathlib's
`AlgebraicGeometry.Surjective` from `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.

Edge cases checked: `d = 0` is allowed when the genus is zero; the Nat index prevents
negative Hilbert degrees; arbitrary separably closed fields and geometrically integral
curves remain permitted.

Searches: `msearch.py leanfinder` for a Hilbert-to-Picard surjectivity theorem (no match);
`msearch.py loogle` for Picard/Hilbert morphism names (only generic surjectivity); grep of
Mathlib AlgebraicGeometry (no Picard/Hilbert functors); `rg` of WeilConjectures found only
the preceding construction and unrelated Hilbert domination results.

## Statement corrected

The original statement used `d ∈ ℤ` while `Hilb^d` and the recorded morphism node use
`d : ℕ`, so it could not be represented by the available functors. It was corrected to
`d ∈ ℤ_{≥0}` in the prose and `d : ℕ` in Lean, with `d ≥ g` as `f.genus ≤ d`.
Citers checked: `lem-pc-nonzero-section-integral-cartier`,
`lem-pc-zero-scheme-divisor-iso`, `thm-sc-theorem-of-the-base`, and
`lem-sc-picg-geometrically-integral`; each still uses the surjectivity conclusion.

## Second reading by C1

Read the corrected node against Stacks pic.tex, lemma-picard-pieces (Tag 0BA0),
lines 1196–1282, using the local literature copy /home/ubuntu/c1-stacks-review/pic.tex.
Clause (4) introduces gamma_d for nonnegative d; clause (5) and paragraph four
prove its surjectivity for d ≥ g. The first paragraph uses a rational point to
identify Picard classes with invertible modules. Since g = dim H¹(O) is a natural
number, d ≥ g already excludes negative d. The Nat correction loses no case.
I restored the original explicit definition of Pic^d in the prose, changing only
the degree domain to nonnegative integers.

Object/hypothesis/conclusion checklist (all verdicts: matches after repair):

- Separably closed field k: `{k : Type u} [Field k] [IsSepClosed k]`.
- Curve C over k with its structure morphism: `{C : Scheme.{u}}`
  and `(f : C ⟶ Spec (.of k))`.
- Smooth projective curve: `[f.IsSmoothProjectiveCurve]`. Opened its declaration
  in SmoothProjectiveCurve and its parents in Variety: integral, separated,
  finite type, dimension exactly one, smooth, projective. No added assumptions.
- Geometrically integral: `[GeometricallyIntegral f]`, opened Mathlib Integral;
  geometric integrality is imposed on every field fibre, as the dependency says.
- Genus g = dim_k H¹(C,O): `@Scheme.arithmeticGenus k _ C ⟨f⟩`, the recorded
  def-pc-genus declaration in EulerChar, with the explicit Over structure from f.
  The worker used `f.genus`, which Curve defines using differential forms.
  RiemannRoch.genus_eq_arithmeticGenus bridges them, but the signature now uses
  the node's recorded definition directly.
- Nonnegative d and d ≥ g: `(d : ℕ)` and `(hd : ...arithmeticGenus... ≤ d)`.
- H_d representing Hilb^d: `(H : Over (Spec (.of k)))` and
  `(eH : (hilbertPresheaf f d).RepresentableBy H)`. Opened Hilbert/Defs:
  closed subschemes finite, flat, locally finitely presented, constant rank d.
- P_d representing the degree-d Picard functor: corresponding Over object P and
  `(eP : (picardFunctorDegree f d).obj.RepresentableBy P)`. Opened Picard/Defs,
  Degree and Jacobian: this is the fppf sheafification of the fibre-degree-d
  subpresheaf of the recorded Picard presheaf, the accepted dependency encoding.
- The specified gamma_d, D ↦ O(D): `(γ : H ⟶ P)` with `hγ` the representing
  equality for the sheafified universal divisor class. Universal D is exactly
  `(eH.homEquiv (𝟙 H)).1`. The auxiliary Picard class L, membership hL and
  isomorphism hD specify that class of the actual dual ideal module. They are
  the data of lem-sc-hilb-to-pic-morphism, whose full module and node were read;
  they impose no new geometric hypothesis. Invertibility is contained in Pic,
  and degree d is contained in membership in picardSubfunctorDegree.
- Conclusion: exactly `Surjective γ.left`. Opened Mathlib UnderlyingMap:
  this means Function.Surjective on underlying points. The worker instead
  existentially selected a surjective gamma and repeated construction clauses.
  Now the given canonical morphism is the subject of the conclusion.

Edge cases: d = 0, g = 0 and the empty effective divisor are allowed; neither
positive degree nor positive genus is required. Empty C is excluded by the
node's integral one-dimensional curve hypothesis itself. Empty test schemes
are allowed by the functors; hL is legitimately vacuous there and creates no
extra hypothesis on the theorem's field points. There is no characteristic
restriction, and separably closed is not replaced by algebraically closed.
The shared arbitrary universe u matches the recorded scheme/field functors;
there is no smaller independent universe for test fields, no finite index set,
and no added Noetherian, rational-point or finiteness binder.

Independent searches: msearch leanfinder query "Abel map symmetric power onto
degree component of Picard variety" found only Weierstrass point-to-class-group,
linear symmetric powers and class-group surjectivity, not this statement.
msearch loogle `"hilbertToPicard"` returned zero matches. msearch leansearch
"effective divisors degree at least arithmetic genus surject onto Picard scheme"
was unavailable (Internal Server Error), recorded without a no-match verdict.
rg for Abel-Jacobi, hilbertToPicard and Hilbert/surjectivity in Mathlib,
WeilConjectures and lean/Sheaf found only the landed construction and
Hilbert/Curve.exists_surjective_of_representableBy_hilbertPresheaf_curve.
Opened the latter: its map is from an auxiliary scheme onto Hilb, not from
Hilb onto Pic. Upstream names have no collision with the new theorem name.
No existing declaration matches; no new notion or dependency module is needed.

Repairs: changed the existential construction theorem to
AlgebraicGeometry.surjective_hilbertToPicardMorphism for the given classifying
map; replaced differential genus with recorded arithmeticGenus; expanded the
proof docstring through all seven node steps and their dependencies; added the
standard copyright header; kept only the two actual dependency citers in
statement_change, changing `what_was_wrong` to `what` and citer `node` to `id`;
added the missing lean.branch and recorded the complete signature including
its conclusion. The only theorem proof remains `sorry`; no definitions added.
The corrected module compiled on the server with exit 0 and no warnings.

Correction citer audit: opened thm-sc-theorem-of-the-base and
lem-sc-picg-geometrically-integral and their citing proof steps: both use d = g
and the surjectivity of the canonical gamma_g, so both holds:true.
lem-pc-nonzero-section-integral-cartier and lem-pc-zero-scheme-divisor-iso were
incorrectly called citers in the worker's correction: their blueprint ancestry
mentions this item, but neither stmt_deps nor proof_deps cites it. They are
proof dependencies of this item instead and are removed from the record.
There are no new nodes or dependency modules to review in this delivery.

The Worker report describes the first version; the repairs above supersede its
existential conclusion, genus choice and four-citer description.

## Reviewer note (R-hps1204, FIX)

The statement correction is reverted (`--revert-statement`): the sheaf-dag statement already
takes d ≥ g with g = dim H¹(O) ≥ 0, so `d : ℕ` with `arithmeticGenus ≤ d` states it exactly;
Hilb^d is only used for that d, and the definition sentence of Pic^d for d ∈ ℤ is the same as
in the sibling lem-sc-hilb-to-pic-morphism. The "Statement corrected" section above is therefore
superseded; the Lean statement is unchanged.
