## Worker report

Repair of the returned stage-1 head 82e84af212fa: this delivery is now a stage-2 statement,
not a split. The sandbox initially retained only launcher marker files, with no Lean module,
node copy or report. I reconstructed the packet from the current shared node. Its reviewed
Q06 `split_report.summary` and the complete `split_report.tool_uses`, including all reasons,
are preserved verbatim. No field other than `lean` is changed. There are no new DAG nodes,
no dependency-record repairs, and no statement correction.

The module is `Sheaf.AlgebraicGeometry.VectorProjectiveCompletion`; its main theorem is
`AlgebraicGeometry.VectorProjectiveCompletion.exists_projective_completion`. Its proof is
exactly `by sorry`. All helper definitions have real data. `Presentation` records the
canonical affine-basis presentation of the existing symmetric algebra notion, using
Mathlib's `SymmetricAlgebra` and the recorded `Scheme.GradedAlgebraData`, rather than a new
construction of relative Proj. The theorem asserts existence of all required data; it never
chooses a scheme, algebra, map or chart from a bare existence assertion.

The source was read in `literature/stacks-project/constructions.tex`, section
`section-projective-bundle` (Tag 01OA) and `definition-projective-bundle` (Tag 01OB), along
with the current blueprint first proof paragraph of `thm-amb-vector-bundle-purity` in
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/`. This paragraph
asserts compactifiability by projective completion. The module docstring cites these sources,
and the theorem docstring gives the complete six-step node proof, combining the final
compactification and rank-zero steps into step 5. Each helper carries the same blueprint id.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Scheme S, Noetherian | `(S : Scheme.{u}) [IsNoetherian S]` |
| Constant finite rank d ≥ 0, including zero | `(d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]`; no positivity binder |
| The specified vector bundle Spec_S Sym(F) with projection pi | `VectorBundleZeroSection.scheme S d F`, `VectorBundleZeroSection.π S d F`, and its recorded `affineChart` |
| Sym(O_S ⊕ F) with symmetric grading | `P : Presentation S F`; `P.equiv V` identifies the affine algebra with `SymmetricAlgebra Γ(S,V) (Γ(S,V) × F(V))`; finite direct-sum sections are this product module; `grade_eq` is the image of the nth power of the degree-one image |
| The sheaf's actual restrictions, including the distinguished first summand | `Presentation.restriction` sends `(a,m)` to the restrictions of a and m; `GradedAlgebraData.res_algebraMap` supplies scalars; this fixes the full algebra restriction by its generators |
| Ebar is relative Proj, and r its structural map | `P.algebra.relProj` and `P.algebra.relProjHom`, from the recorded upstream construction |
| Ebar Noetherian, r proper | `IsNoetherian P.algebra.relProj ∧ IsProper P.algebra.relProjHom` |
| t induced by 1 in the first summand, degree one | `t P V := P.equiv V (SymmetricAlgebra.ι _ _ (1,0))` and the existential `ht`; restrictions agree by `Presentation.restriction` |
| D_+(t) globally | `chartOpen P`, the union of the actual basic opens under `relProjι` over all affine base opens |
| Canonical j, an open immersion, with rj=pi | `c : Compactification (VectorBundleZeroSection.π S d F)` supplies the open immersion `c.i` and factorization `c.comm`; `hZ` identifies its ambient scheme with the specified relative Proj and the displayed equation identifies `c.g` with r; j is `c.i ≫ eqToHom hZ` |
| j identifies E with D_+(t) | Its `opensRange` equals `chartOpen P`; since j is an open immersion this is the asserted isomorphism onto that open subscheme |
| Canonical choice of j | The affine-chart equation fixes j on every affine inverse image, and the following universal clause asserts uniqueness among all morphisms satisfying exactly those equations |
| Every affine open V with a module frame | Universal binders `V : S.affineOpens` and `e : VectorBundleZeroSection.Trivialization S d F V.1`, using the recorded sheaf-frame notion |
| Local model Proj R[t,x_1,...,x_d] | `q` is an R-algebra equivalence from `MvPolynomial (Fin (d+1)) R` to `P.algebra.obj V`, sends X_0 to t and X_(i+1) to the frame coordinate, and preserves homogeneous components in both directions |
| This model is the recorded relative projective space P^d_V | `g` is a bijective graded ring homomorphism from its affine-top section algebra to `P.algebra.obj V`, fixes base coefficients through `V.1.topIso`, and sends each recorded coordinate to `q (X i)`; `b` is explicitly its `Proj.map` followed by the canonical `projectiveChart`, with the over-V equation |
| The same local open is its standard projective chart | `b.hom ⁻¹ᵁ RelativeProjectiveSpace.standardOpen ... 0 = Proj.basicOpen ... (t P V)`; the recorded `RelativeProjectiveSpace.localChart` is the underlying homogeneous-localization chart of `projectiveChart` |
| Coordinate-ring map x_i ↦ x_i/t | `a V` is a ring equivalence from `Sym(F(V))` to `HomogeneousLocalization.Away ... t`; for every m its value at `ι m`, in the ordinary localization, is `x(m) * invSelf t`, and the following equation fixes every base coefficient; applying this to `frameSection ... i` gives exactly x_i/t |
| The local isomorphism is the restriction of j | `affineChart ... V ≫ chartMap P ht a V = E_V.ι ≫ c.i ≫ eqToHom hZ`; `chartMap` uses `Spec.map (a V).symm`, then the existing `Proj.awayι` and `relProjι` |
| Compatibility with restriction | For every inclusion U ≤ V, the spectrum of the recorded symmetric-algebra restriction composed with `chartMap V` equals `chartMap U` |
| Compatibility with a linear frame change | The universal matrix clause takes any relation e'_j = Σ_i G_ij e_i and gives the identical relation between their dehomogenized coordinates, with coefficients mapped through `a V`; this covers every frame change, and the recorded bundle `transition_spec` supplies its invertible matrices |
| pi separated and of finite type | `IsSeparated pi ∧ LocallyOfFiniteType pi ∧ QuasiCompact pi`; the last two are precisely the project's finite-type convention |
| E Noetherian | `IsNoetherian (VectorBundleZeroSection.scheme S d F)` |
| (j,r) a compactification | The same witness `c : Compactification pi`, not an unrelated compactifiability assertion |
| At d=0 the identity compactification of S | For `d = 0`, `eE : E ≅ S` and `eP : Ebar ≅ S` have homs equal to pi and r, and `j = eE.hom ≫ eP.inv`; therefore both structural morphisms and j become identities under these canonical structural identifications |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`: `scheme`, `π`, `affineChart`,
  `Trivialization`, `frameSection`, and the restriction/frame-change interfaces.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`: `Scheme.GradedAlgebraData`,
  `relProj`, `relProjHom`, `relProjι`, `toOpen`, and affine restriction compatibility.
  This and the graded-input source were read with `scompile.py --source` because the
  older source checkout does not contain these modules.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`:
  `exists_quasiCoherentSymmetricAlgebra`, used by the proof plan.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper` and `IsSeparated`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, carried by `c`.
- `Sheaf.AlgebraicGeometry.RelativeProjectiveSpace`: `scheme`, `π`, `algebra`,
  `construction.restrictionIso`, `coordinate`, `standardOpen` and its `localChart`
  interpretation. The current server source was read with `scompile.py --source`.
- `def-weil-scheme-morphism-properties` has a convention-only record; its finite-type
  notion is the existing `LocallyOfFiniteType` plus `QuasiCompact`, its separatedness
  is the existing `IsSeparated`. No replacement definition is made.
- `WeilConjectures.Compactification.Refinement`: the imported `Compactification`
  type, including its proper, open-immersion and factorization fields; the recorded
  refinement/category interface is preserved and no alternate compactification is defined.

The stated proof prerequisites are imported, including upstream symmetric-algebra grading,
relative-Proj functoriality and universality, and Mathlib's symmetric-algebra basis theorem,
finite-type and gluing modules. `lem-pur-projective-bundle-tautological-geometry` currently
has no Lean record, so there is no module to import for that future proof step; no part of
its conclusion is made a hypothesis of the statement.

Edge cases checked: rank zero uses `Fin 0` (empty coordinates and matrix sums), with only
the distinguished t remaining in `Fin (0+1)`; Proj R[t] is entirely D_+(t), including over
the zero ring. The empty scheme is permitted; there is no nonemptiness, nontrivial-ring or
positive-rank hypothesis. Affine opens may be empty. Overlaps of affine opens are handled
by all affine refinements, never assumed affine. All schemes, affine section rings and
module sections have the same source universe u, and the universal `Scheme.{u}` binder
places no additional universe equality on an input site. Every variable and universe is
explicitly bound; `autoImplicit` is false. The symmetric-algebra convention is that of the
node, Sym(F), without dualizing F. No statement dispute or node fault was found.

Stage-2 searches performed using `msearch.py Q145 lem-amb-vector-projective-completion`:

- LeanFinder: "A finite rank vector bundle has projective completion Proj Sym of O direct
  sum E with canonical open chart and proper projection". Eight hits on projectivization
  over fields and topological vector bundles; none gives this scheme-theoretic statement.
- LeanSearch: "Vector bundle embeds in projective bundle O plus E as affine chart".
  Eight hits on topological/manifold vector-bundle charts; no algebraic completion.
- Loogle: `AlgebraicGeometry.Proj.awayι`. Twelve hits, including the absolute Proj chart,
  its open immersion and restriction formulas. These are used as the local chart API;
  none states the global relative symmetric-algebra completion.
- Mathlib grep: `projectiveCompletion|SymmetricAlgebra|ProjectiveBundle` in
  `AlgebraicGeometry`: zero hits.
- Source and project rg: projective/completion combinations, symmetric graded algebra
  combinations, and then `VectorProjectiveCompletion|exists_projective_completion` in
  `WeilConjectures/` and `lean/Sheaf/`: no existing declaration for this statement;
  unrelated curve completion modules and the existing relative-projective-space
  construction were inspected. An exact item-id search in the source and a completion
  search in `dag/lean_names_upstream.json` returned no match.

Compile evidence: all compilation uses the prescribed `scompile.py` wrapper for this
single module. The initial rank-zero inverse elaboration was repaired by explicit
structural isomorphisms. A later check requested a public import for the graded-hom
irrelevant-ideal lemma; that exact import was added. No global build or direct Lean
compilation is used. The final compile and dry-run results are recorded below.

## Second reading by Q145

I reopened the current node and the full module for a separate clause-by-clause second
pass. This is a second pass by the delivery author; the independent review remains the
maintainer's review, as required by this dispatcher brief, which forbids starting agents.

This pass found two concrete interface issues and repaired them. First, merely asserting
an isomorphism to relative projective space carrying D_+(t) to the standard open did not
connect that isomorphism to the displayed frame coordinates. The theorem now supplies the
bijective graded map `g`, fixes its coefficients and every generator, and requires `b.hom`
to be exactly the induced `Proj.map` followed by the recorded projective-space chart.
Thus the polynomial equivalence, relative projective comparison and x_i/t calculation
refer to the same coordinates. Second, a bare inverse of r in the rank-zero conclusion
required an unavailable instance while elaborating that conjunction. Explicit structural
isomorphisms `eE` and `eP`, whose homs are pi and r, now state the canonical identity
normalization without any added input hypothesis.

Rechecked the remaining clauses against the node: S is Noetherian, F has exactly constant
rank d, the vector bundle is the recorded one, and d=0 is included. `Presentation` fixes
Sym(O⊕F), not Sym(F), and uses its symmetric-degree grading and actual restrictions.
The relative Proj and its structural map are the recorded upstream construction. Both
Noetherian assertions, properness of r, the image D_+(t), factorization rj=pi, and the
compactification are present. The dehomogenization equivalences fix scalars and all
module generators, which determines them uniquely; the chart equations then determine j
uniquely. The standard-open comparison uses the recorded relative-projective-space API.
Restriction ranges over every nested affine pair, and the matrix equation applies to
all frame changes. Finite type includes quasi-compactness, and separatedness is explicit.
The rank-zero clause identifies this very compactification with the identity, rather than
just asserting an unrelated compactification exists. Empty bases and zero rings remain
admissible. No mismatch remains and the natural statement is unchanged.

Finally rechecked the JSON against the current shared node: all pre-existing fields,
including the reviewed split summary and complete tool-use reasons, are preserved. The
`lean.statement` is the theorem signature verbatim from its keyword up to `:=`; the
record lists every helper and the main theorem. Every declaration has a source/blueprint
docstring, the sole theorem has the complete natural-language proof, and no definition
contains a `sorry` or selects data from the theorem. There are no new nodes or dependency
modules to review.

Final validation, 2026-10-17 UTC: the last standalone `scompile.py Q145
lem-amb-vector-projective-completion` completed both wrapper checks without errors or
warnings: sandbox check 8.9 seconds and module check 9.6 seconds. The prescribed
`deliver2.py Q145 lem-amb-vector-projective-completion --no-push` then printed
`OK (dry run): commit 259df92baa passes the preflight and compiles; nothing pushed`.
The staged set was exactly this module, its node JSON, and this report. This validation
paragraph is the only change after that dry run; the full final packet is checked again
before pushing.
