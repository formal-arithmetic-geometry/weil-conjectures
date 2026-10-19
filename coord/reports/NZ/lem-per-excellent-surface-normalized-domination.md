## Worker report

States `AlgebraicGeometry.exists_normalized_point_blowup_domination` in
`Sheaf.AlgebraicGeometry.ExcellentSurfaceNormalizedDomination`, with `sorry` as the entire
proof. No new notions, dependency modules, or statement corrections are required.
The Q34 delivery de5027a456 was stage 1: the current node has no Lean record. Thus the
previous worker's duplicate-delivery refusal did not complete this stage-2 item. The preserved
sandbox contained only dispatch markers, not a packet or a successful interrupted delivery.

Source read: Stacks `resolve.tex`, Tag 0BBT, the statement and proof beginning at
`lemma-dominate-by-normalized-blowing-up`; properness is Tag 0BFT. The source allows a
Noetherian Nagata base, whereas this node deliberately specializes to a normal excellent
integral base. Its initial normalization is consequently the identity. The stage-1 proof's
correction to take the dominating component of the graph, and correction of the printed
O_X,C subscript to O_Y,C, are retained in the proof docstring.

Hypotheses, individually:

- `S : Scheme.{u}` with `[IsIntegral S]`: an integral base, including nonemptiness.
- `[IsNoetherian S]`: the base is Noetherian.
- `hNormal`: every stalk is an integrally closed domain, the normal-scheme condition using
  the dependency's inline normal-domain convention.
- `hExcellent : ∀ U : S.affineOpens, IsExcellent Γ(S, U)`: excellence of every affine
  coordinate ring, exactly as specified by the node.
- `hDim : topologicalKrullDim S = 2`: dimension two, the scheme counterpart of the recorded
  ring Krull dimension; no affine base or local base is imposed.
- `Y : Scheme.{u}` with `[IsIntegral Y]`: integral source, with no normality assumed.
- `f : Y ⟶ S` with `[IsProper f]`: the stated proper map.
- `hη` and `hBir`: the generic point maps to the generic point and the canonical induced
  map `f.functionFieldMap hη : S.functionField ⟶ Y.functionField` is an isomorphism.
  These express inducing an isomorphism of function fields, not an unrelated field isomorphism.

Conclusion, clause by clause:

- `∃ n : ℕ`: a finite nonnegative length, including zero.
- `X : Fin (n+1) → Scheme.{u}`: the levels S_0 through S_n.
- `hIntegral : ∀ i, IsIntegral (X i)`: each level is integral.
- `hzero : X 0 = S` and `p 0 = eqToHom hzero`: bottom level is S with its identity structure
  map, transported along that identification, not merely some unrelated isomorphic object.
- `p : ∀ i, X i ⟶ S`, `arrow : ∀ j : Fin n, X j.succ ⟶ X j.castSucc`, and
  `arrow j ≫ p j.castSucc = p j.succ`: the specified tower and its composites to S.
- The stalk-domain and integrally-closed conjunction at every point of each `X i`: all levels
  are normal.
- `∀ j, IsProper (arrow j)`: each tower arrow is proper.
- The `hgen`/`IsIso (@Scheme.Hom.functionFieldMap ...)` clause: each arrow induces an
  isomorphism of the actual function fields of its two integral levels. Integral instances
  are passed explicitly, with their corresponding irreducibility instances at generic points.
- For each j, `x` with `hx : IsClosed {x}` and
  `I = Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩`: the reduced closed-point ideal.
- `∃ (_ : IsIntegral I.blowup) (e : X j.succ ≅ I.blowup.normalization)` with
  `e.hom ≫ I.blowup.fromNormalization ≫ I.blowupMap = arrow j`: the arrow is the ordinary
  blowup followed by normalization in that integral blowup's function field, up to an
  isomorphism over the preceding level. The integral blowup witness is the domain of
  definition of this existing normalization, not an extra input hypothesis.
- `∃ l : X (Fin.last n) ⟶ Y, l ≫ f = p (Fin.last n)`: the required S-morphism factoring
  the composite. There is no regularity assertion about the endpoint, and no finite-normalization
  requirement is silently inserted into the conclusion.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`, through scheme Noetherianity
  (`Mathlib.AlgebraicGeometry.Noetherian`).
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsDomain`, `IsIntegrallyClosed`:
  the recorded inline normal-domain predicates on local rings.
- `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`; the scheme dimension is
  `topologicalKrullDim` from `Mathlib.Topology.KrullDimension`.
- `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `Sheaf.AlgebraicGeometry.FunctionField`, `Scheme.functionFieldOfComponents`: its docstring
  explicitly directs the arbitrary integral-scheme clause of def-sc-function-field to the
  existing `Scheme.functionField` (the generic stalk), which is used here.
- `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`, `Scheme.Hom.functionFieldMap`:
  the canonical generic-stalk map; its signature and docstring were read via scompile --source.
- `Sheaf.RingTheory.ExcellentRing`, `IsExcellent`: exact recorded excellence predicate.
- `WeilConjectures.Blowup.Gluing`, `Scheme.IdealSheafData.blowup` and `blowupMap`:
  the ordinary glued blowup and canonical structural morphism; current source read via wrapper.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`, `Scheme.normalization` and
  `Scheme.fromNormalization`: the normalization in the integral scheme's function field;
  current source read via wrapper. The canonical vanishing ideal is the existing ideal-sheaf API.

The already stated proof dependencies are imported without `public`: discrete valuation rings,
`Sheaf.AlgebraicGeometry.ExcellentNormalizedBlowupTower`,
`Sheaf.TraceFormula.ProjectiveBundleProper`, and `WeilConjectures.Blowup.Principalization`.
The three other geometric proof nodes currently lack recorded Lean modules; their full
natural-language arguments remain in the docstring plan and no proof is attempted here.

Edge cases checked: n = 0 gives a singleton level, no arrows or centers, and the inverse of an
isomorphism when f is already an isomorphism. A nonnormal Y is permitted; its normalization
belongs to the proof only. Empty S and Y are excluded precisely by the node's integrality.
No characteristic assumption, chosen base field, affineness, localness, regularity, or extra
separatedness on S is introduced. All schemes may be placed in the same arbitrary universe u.
The dimensions are topological dimensions, so non-affine surfaces are included. Each point
center is reduced by vanishingIdeal, not an arbitrary subscheme supported at the point.

Searches (2026-10-19):

- msearch leanfinder: `Every proper birational morphism to a normal excellent Noetherian surface
  is dominated by a finite tower of normalized blowups at reduced closed points`: 8 results,
  only relative-normalization morphisms and properties, no finite-tower existence theorem.
- msearch leansearch: `A proper birational morphism of normal excellent surfaces is dominated
  by normalized point blowups`: 8 results, properness/dominance and relative normalization;
  none says this theorem.
- msearch loogle: `"blow", "normal"`: 0 hits.
- msearch grep: `normalized.*blow|blow.*normali`: 0 Mathlib hits.
- rg in the upstream WeilConjectures tree and side `lean/Sheaf/AlgebraicGeometry` for
  `normalized.*blow|blow.*normali|lem-per-excellent-surface-normalized-domination`: upstream
  has no match; the side has normalized-blowup calculus, geometry of an already supplied tower,
  local refinement and completion descent. Read their signatures: none is this existence
  and domination statement for an arbitrary proper birational Y over excellent S.

No STATEMENT-DISPUTED issue found. The declaration has all variables and universes explicitly
bound and only a theorem proof is postponed. Compilation and preflight results follow below.

Validation: scompile.py compiled the delivered module cleanly as both sandbox and library
(3.4 seconds each), including the required side-only excellent-tower overlay. No compiler
errors or additional warnings. Only this single module is delivered.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
