## Worker report

The module `Sheaf.AlgebraicGeometry.InvertibleProperNoetherianModels` states
`AlgebraicGeometry.invertible_proper_noetherian_models`. Its only theorem proof is
`sorry`, as required in stage 2. It defines no new notions, adds no nodes, repairs
no dependency interfaces, and changes only the item's `lean` field. The signature
in that record is copied verbatim from the theorem, up to `:=`.

Source read: `literature/stacks-project/more-morphisms.tex`,
`lemma-ample-in-neighbourhood`, Tag 0D2S, from the affine reduction through the
compatible invertible modules and the sentence `Let y_i`. The node is the
approximation input of that proof, not its ampleness conclusion. The source
uses arbitrary proper morphisms; the statement introduces no finite-presentation
assumption on the given morphism. The six proof steps in the node are reproduced
in the theorem's docstring, including affine projections and the cofinal-tail
limit check.

The Lean translation, hypothesis by hypothesis and clause by clause:

| Node text | Lean rendering |
| --- | --- |
| Schemes Y, X and morphism f:Y→X | `{X Y : Scheme.{u}} (f : Y ⟶ X)` |
| f proper | `[IsProper f]` |
| X affine | `[IsAffine X]` |
| M an invertible O_Y-module | `(M : Y.Modules) [M.IsInvertible]` |
| A small partially ordered index set I | `∃ (I : Type u) (_ : PartialOrder I)`; the index universe is the scheme carrier universe |
| Nonempty with a least element 0 | `(_ : OrderBot I)`; `⊥ : I` is the index called 0 and witnesses nonemptiness |
| I directed | `(_ : IsDirected I (· ≤ ·))` |
| Inverse systems Y_i and X_i | `Ys Xs : Iᵒᵖ ⥤ Scheme.{u}`; functor laws supply identity and composite transitions |
| Proper f_i and commuting transition squares | `fs : Ys ⟶ Xs` and `∀ i, IsProper (fs.app i)`; `fs.naturality` is exactly `q_ji ≫ f_i = f_j ≫ r_ji` |
| Projections a_i and b_i | Natural transformations `a : (Functor.const Iᵒᵖ).obj Y ⟶ Ys` and similarly `b`; their naturality gives compatibility with transitions |
| Every transition affine | `∀ i j h, IsAffineHom (Ys.map h) ∧ IsAffineHom (Xs.map h)` |
| Every projection affine | `∀ i, IsAffineHom (a.app i) ∧ IsAffineHom (b.app i)` |
| f_i a_i = b_i f | `∀ i, a.app i ≫ fs.app i = f ≫ b.app i` |
| Both displayed cones are limits | `Nonempty (IsLimit (Cone.mk Y a)) ∧ Nonempty (IsLimit (Cone.mk X b))`; `IsLimit` includes the factorization and uniqueness for every scheme cone |
| Each X_i affine | `∀ i, IsAffine (Xs.obj i) ∧ ...` |
| Each X_i finite type over Spec Z | `LocallyOfFiniteType (specULiftZIsTerminal.from (Xs.obj i)) ∧ QuasiCompact (...)`; this is the recorded finite-type definition, using Spec of the universe lift of Z |
| Each X_i and Y_i Noetherian | `IsNoetherian (Xs.obj i) ∧ IsNoetherian (Ys.obj i)`; the Mathlib class extends `IsLocallyNoetherian` and `CompactSpace` |
| Y_i quasi-separated | `QuasiSeparatedSpace (Ys.obj i)`, equivalent to quasi-separatedness of its structure morphism |
| An invertible M_0 on Y_0 | `∃ (M₀ : (Ys.obj (op (⊥ : I))).Modules), M₀.IsInvertible ∧ ...` |
| An isomorphism a_0^*M_0 ≅ M | The witness `e₀ : (Scheme.Modules.tensorPullback (a.app (op ⊥))).obj M₀ ≅ M` |
| M_i is defined to be q_i0^*M_0 | Every occurrence uses `(Scheme.Modules.tensorPullback (Ys.map (homOfLE (bot_le : ⊥ ≤ i)).op)).obj M₀` directly; no arbitrary family replaces this expression |
| Every M_i invertible | The final conjunction's first clause: `∀ i, (...).IsInvertible` |
| q_ji^*M_i ≅ M_j | The existential family `e : ∀ i j (hij : i ≤ j), ... ≅ ...` |
| a_i^*M_i ≅ M | The existential family `d : ∀ i, ... ≅ M` |
| Isomorphisms induced by pullback composition | The final two clauses specify `e i j hij` and `d i` as the inverse `tensorPullbackSectionComp`, followed by `eqToIso` of `Ys.map_comp` or the cone equation; `d i` finally composes with `e₀` |

The equalities specifying `e` and `d` fix the canonical comparisons; they do not
require unrelated extra isomorphism choices or extra geometric hypotheses.
At i = ⊥ the expression for M_i is the pullback along the identity transition,
identified with M₀ by the recorded identity-pullback comparison. Thus M₀ is the
chosen descended object, while the uniform family retains the literal formula
M_i = q_i0^* M₀ also at the least stage.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  `AlgebraicGeometry.Spec` and `Spec.map` (available through the public imports).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`; its instance
  `Scheme.Modules.IsInvertible.pullback` is a proof-plan dependency, already in
  the same public module.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`:
  `AlgebraicGeometry.IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; quasi-compactness of a morphism is
  `AlgebraicGeometry.QuasiCompact` from `Morphisms.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Noetherian`:
  `AlgebraicGeometry.IsLocallyNoetherian`, `AlgebraicGeometry.IsNoetherian`;
  proof facts `LocallyOfFiniteType.isLocallyNoetherian` and
  `IsLocallyNoetherian.quasiSeparatedSpace`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, the underlying scheme's
  quasi-compactness; the proof also uses
  `AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`, its scheme form `QuasiSeparatedSpace`,
  and `quasiSeparatedSpace_iff_quasiSeparated`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`, publicly imported from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`, and
  `tensorPullbackSectionComp`, the section-normalized comparison explicitly
  supplied by the recorded pullback dependency. `tensorPullbackSectionId`
  gives the identity normalization used in the natural-language explanation.
- `Mathlib.AlgebraicGeometry.Limits`: `specULiftZIsTerminal`, which keeps the
  scheme and integer spectrum universes compatible without restricting u.
- Proof imports, without public visibility:
  `WeilConjectures.AlgebraicGeometry.ProperLimitNoetherian`
  (`AlgebraicGeometry.exists_proper_limit_noetherian`),
  `Sheaf.AlgebraicGeometry.InvertibleAffineLimitDescent`
  (`AlgebraicGeometry.invertible_affine_limit_descent`),
  `Mathlib.AlgebraicGeometry.AffineTransitionLimit`
  (`AlgebraicGeometry.isAffineHom_π_app`, `isLimitOpensCone`), and
  `Mathlib.AlgebraicGeometry.AffineScheme`
  (`AlgebraicGeometry.Scheme.compactSpace_of_isAffine`). The affine
  quasi-separatedness instance is in the already public QuasiSeparated module.

Edge cases checked before writing: an empty source or empty affine base is
allowed; no nonempty scheme, nonzero module, surjectivity, flatness, ampleness,
or finite-presentation assumption was added. The zero sheaf can be invertible
on the empty scheme, which the statement permits. A one-element index system
is allowed. Every identity transition, including q_00, is included in the
canonical formulas. `OrderBot` prevents an empty indexing set. Index type
`Type u` avoids an independent smaller universe for approximation. Limit cones
retain their actual vertices Y and X, so there is no unstated identification
of a chosen abstract limit. No statement fault or disputed clause was found.

Searches made (2026-10-24):

- `msearch.py ... leanfinder`: “A proper morphism over an affine scheme and an
  invertible module admit compatible proper Noetherian models with affine
  transition maps and a least indexing element”. Eight hits, including
  affine-transition-limit factorization results and
  `IsFinite.iff_isProper_and_isAffineHom`; none state this theorem.
- `msearch.py ... loogle`: `IsProper, IsInvertible`. No hits; the service did
  not resolve the unqualified `IsProper`. Retried the qualified
  `AlgebraicGeometry.IsProper`: twelve properness-class and stability hits,
  none giving compatible models with an invertible module.
- `msearch.py ... grep`:
  `invertible.*(limit|noetherian)|proper.*noetherian` in AlgebraicGeometry.
  Zero Mathlib hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`:
  `lem-trf-invertible-proper-noetherian-models|invertible_proper_noetherian_models|[Ii]nvertible.*[Nn]oetherian.*[Mm]odel`.
  No existing theorem or module for this item. A broader model search found
  `ProperLimitNoetherian` and `NoetherianApproximation.Model`; the former is
  already a proof dependency, and the latter treats proper flat families and
  is not this statement. Existing affine-limit tensor comparisons were read;
  this delivery introduces no duplicate comparison definition.

Validation: `scompile.py Q44 lem-trf-invertible-proper-noetherian-models`
compiled the delivered file in sandbox and library module positions cleanly
(6.6 s and 2.2 s). Both auto-implicit options are disabled. No helper theorem,
extra definition, `#check`, file-local instance, notation, or hidden hypothesis
is present. The required `deliver2.py --no-push` passed preflight and compilation
with dry-run commit `8c401450cbe`. The final delivery is then pushed by the
prescribed wrapper for the maintainer's independent review.

## Second reading by Q44

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
