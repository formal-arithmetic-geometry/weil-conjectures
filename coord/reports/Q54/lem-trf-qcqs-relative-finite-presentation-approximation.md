## Worker report

The module `Sheaf.AlgebraicGeometry.QcqsRelativeFinitePresentationApproximation`
states `AlgebraicGeometry.exists_qcqs_relative_finitePresentation_approximation`.
It has one theorem, with proof `sorry`, and introduces no definitions. The node
is unchanged except for its `lean` field. No statement correction or disputed
statement was needed. Source read: `literature/stacks-project/limits.tex`,
`lemma-relative-approximation` (Tag 09MV), including its proof. The node explicitly
requests the special case with quasi-compact base, which is also the case used
in the source proof after shrinking the base.

Hypothesis and clause correspondence:

- Schemes and their morphism: `{Z S : Scheme.{u}}` and `(f : Z ⟶ S)`.
- Both schemes quasi-compact: `[CompactSpace Z]` and `[CompactSpace S]`.
- Both schemes quasi-separated: `[QuasiSeparatedSpace Z]` and
  `[QuasiSeparatedSpace S]`. No condition is imposed on `f` itself.
- Small nonempty directed set: existential `I : Type u`, `Preorder I`,
  `IsDirected I (· ≤ ·)`, `Nonempty I`. This uses the project's Stacks 00D3
  directed-set convention. The index universe is the schemes' universe.
- System of schemes: `D : Iᵒᵖ ⥤ Scheme.{u}`. A relation `i ≤ j` in `I`
  corresponds to a map from stage `j` to stage `i`. `D.map_id` and
  `D.map_comp` impose the identity and composition laws.
- System over `S`: `q : D ⟶ (Functor.const Iᵒᵖ).obj S`. Its components
  are the structural maps, and naturality says all transitions are over `S`.
- Each structural map has finite presentation: the first conjunct states
  `LocallyOfFinitePresentation (q.app i) ∧ QuasiCompact (q.app i) ∧
  QuasiSeparated (q.app i)` for every stage. All three conditions are retained,
  as required by Stacks 01TP and the convention node, even though Mathlib's
  finite-presentation module's introductory prose mentions only two.
- Affine transitions: `∀ (i j : Iᵒᵖ) (h : i ⟶ j), IsAffineHom (D.map h)`.
- Compatible projections: `π : (Functor.const Iᵒᵖ).obj Z ⟶ D`.
  Naturality gives compatibility with every transition.
- Projections over `S` and the specified factorization of `f`: the third
  conjunct is `∀ i, π.app i ≫ q.app i = f`.
- Every stage qcqs: the fourth conjunct is
  `∀ i, CompactSpace (D.obj i) ∧ QuasiSeparatedSpace (D.obj i)`.
- Limit in schemes, including unique factorization for every compatible
  family from any scheme: `Nonempty (IsLimit (Cone.mk Z π))`. The apex
  is exactly `Z`; `IsLimit.lift`, `fac`, and `uniq` give precisely the
  requested universal property. This is a limit in `Scheme`, not only in
  `Over S`. No arbitrary test map to `S` is imposed on the universal property.

Dependencies used (their source declarations and docstrings were read):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-pbc-scheme-conventions`: a convention-only record, no module or
  declaration. Its qcqs meanings use `CompactSpace`, `QuasiSeparatedSpace`,
  and its finite-presentation meaning uses the three conditions above.
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` is publicly imported
  for `AlgebraicGeometry.QuasiSeparated`.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `pqf-def-affine-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
  `AlgebraicGeometry.IsAffineHom`.
- Standard categorical interfaces: `Mathlib.CategoryTheory.Limits.IsLimit`
  (`CategoryTheory.Limits.IsLimit`, `Cone.mk`) and
  `Mathlib.CategoryTheory.Category.Preorder` (preorder category).

Proof-dependency imports are plain imports: `Mathlib.AlgebraicGeometry.Noetherian`
for lem-weil-pbc-finite-type-over-noetherian and pqf-lem-lft-fp-locnoeth;
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` for def-pc-fibre-product;
`WeilConjectures.AlgebraicGeometry.LimitFibreProducts` for
lem-weil-pbc-limit-fibre-products. The remaining proof-only nodes
lem-trf-qcqs-arrow-absolute-approximation and
lem-a1-map-over-base-finite-presentation have neither a usable Lean record nor a
Mathlib match in the supplied DAG; there is therefore no recorded module to
import for them. They are not required to type this stage-2 statement. The
four-step proof docstring preserves their planned uses.

Edge cases checked before writing: empty `Z` is allowed (the constant empty
scheme over `S` is a possible system); empty `S` forces empty `Z` and is also
allowed. A singleton index and identity transitions are allowed, while empty
index types are explicitly excluded. For `f = 𝟙 S`, a constant system is possible
for every qcqs `S`, without Noetherian or finite-type assumptions on `S`.
Nonseparated schemes, non-Noetherian schemes, nonaffine stages, and all
characteristics remain allowed. No independent smaller test universe is used.
All variables and universes are explicit, with `autoImplicit false` enabled.
No hidden `let` or `show` occurs in the signature.

Searches performed with the prescribed `msearch.py Q54 <item>`:

- LeanFinder: "A morphism of quasi compact quasi separated schemes is an inverse
  limit of finitely presented schemes over its target with affine transition
  maps". Eight hits, including `Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`
  and `Scheme.exists_isQuasiAffine_of_isLimit`; none constructs this system.
- Loogle: `AlgebraicGeometry.LocallyOfFinitePresentation, AlgebraicGeometry.IsAffineHom`.
  Two hits: `Scheme.preservesColimit_yoneda` and
  `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`. Both require an
  already supplied inverse system; neither states approximation existence.
- Grep in Mathlib AlgebraicGeometry:
  `relative.*approximation|approximation.*relative|exists.*[Ff]inite[Pp]resentation`.
  Five hits in AffineTransitionLimit, all the preceding factorization theorem
  or its proof, and no matching existence theorem.
- LeanSearch: "Every quasi compact quasi separated scheme over a quasi compact
  quasi separated base is a directed inverse limit of schemes of finite
  presentation over that base with affine transitions". Eight hits, including
  `Scheme.compactSpace_of_isLimit` and `Scheme.isAffine_of_isLimit`; these give
  properties of supplied limits, not existence of finite-presentation models.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for relative approximation
  and the item id found only different statements (Noetherian approximation
  for complete intersections, relative completion/étale approximation,
  finite integral approximation) and a downstream proof citation.
- Exact declaration-name search in both source roots and
  `dag/lean_names_upstream.json` found no collision. The upstream
  `NoetherianApproximation` theorem inspected is an affine absolute
  approximation, not the arbitrary relative qcqs statement here.

Validation: the first server compile passed in both sandbox and library modes
with no errors or unexpected warnings. Delivery preflight and the final compile
are recorded by the prescribed delivery wrapper.

## Second reading by Q54

A separate rereading by this same dispatched worker was performed; the brief
forbids starting other agents and reserves independent review for the maintainer.
I reread the node beside the signature: both qcqs hypotheses, nonempty directed
index, finite presentation including quasi-separatedness, affine transitions,
all functor laws, compatibility over the base, the factorization of `f`, qcqs
stages, and the scheme-level unique-factorization property are each present as
listed above. The cone apex is `Z` itself and the direction is `Iᵒᵖ`, so no
isomorphism choice or reversal of transition direction is concealed. I found no
mathematical mismatch. `autoImplicit false` was added after the first compile
to make explicit-variable checking enforceable; no signature change was needed.
