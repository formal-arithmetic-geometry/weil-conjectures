## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianPicardInfinitesimalLift` states
`AlgebraicGeometry.AlgebraicSpace.exists_etale_rigidifiedLine_infinitesimalLift`
with a single `sorry`. Its two fully constructed helper definitions give the
actual parameter family and its canonical map under a parameter morphism.
They belong to this node's restriction maps; they introduce no replacement
notion of algebraic space, line, rigidification, or algebraic equivalence.

The node's mathematical statement and accepted proof are unchanged. Its
`stmt_deps` gains two already landed definition nodes:
`def-sfb-abelian-space-poincare-data` and `def-sfb-rigidified-space-lines`.
The first supplies the existing abelian-family and fibrewise-trivial predicates;
the second supplies the existing groupoid in which the conclusion is stated.
A traversal of their statement/proof dependencies found no path back to this item.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Locally Noetherian scheme S | `{S : Scheme.{u}} [IsLocallyNoetherian S]`. |
| Commutative group algebraic space A over S | `A : AlgebraicSpace S`, `g : CommutativeSpaceGroup A`; the latter is the existing natural commutative group law on its functor of points. |
| Proper, smooth, finite presentation, abelian geometric fibres | `hA : IsAbelianFamily (groupSpaceProjection A)`. The read definition conjoins `MapIsProper`, chartwise `Smooth`, local finite presentation and `HasAbelianFibres`. Proper includes separatedness and finite type, so the local-finite-presentation clause is finite presentation here. The geometric scheme models are proper smooth connected over algebraically closed fields, with the inherited group law. |
| The assertion after any locally Noetherian base change | `∀ (B : Over S) [IsLocallyNoetherian B.left]`. For a parameter T over B, `picardInfinitesimalFamily` is literally A times_S T, with its pulled-back identity. This is canonically the family (A times_S B) times_B T. The identity object `Over.mk (𝟙 S)` includes the original assertion, and every B to S includes the stated base-change assertion. No Noetherian condition is imposed on T or T₀. |
| Affine S-schemes T₀ and T and a closed immersion | `T₀ T : Over B.left`, `[IsAffine T₀.left] [IsAffine T.left]`, `i : T₀ ⟶ T`, `[IsClosedImmersion i.left]`. An arrow in this over-category is exactly a morphism over B, hence also over S. |
| Quasi-coherent defining ideal I, I squared zero | `i.left.ker ^ 2 = ⊥`. The Mathlib `Scheme.Hom.ker` is an `IdealSheafData`, a quasi-coherent ideal sheaf. For a closed immersion it is its actual defining ideal; it is not an independently chosen ideal or an arbitrary module. |
| Line M₀ on the small etale site | `M₀ : RigidifiedLines (picardInfinitesimalFamily A g B T₀).e`. The existing groupoid requires the underlying module to satisfy `IsLineModule`, defined by local structure-module trivializations on the actual small etale site. |
| Specified identity rigidification r₀ | The same `RigidifiedLines` object carries its actual invertible map from identity pullback to the structure module. It is data, not merely existence of a trivialization. |
| Algebraically trivial on every geometric fibre, with the given parameter-family meaning | `FibrewiseTrivial ...` on `smallModuleRestriction.obj ((rigidifiedLineForget ...).obj M₀)`. The read predicate tests all geometric scheme models using the existing `AreAlgebraicallyEquivalent`, whose generating pairs are isomorphic lines and fibres of a line family over a smooth connected separated finite-type parameter variety. The small-model restriction is the fixed module equivalence, not a new algebraic-equivalence relation. |
| Etale covering {U_j to T} | Existential `J : Type u`, `U : J → Over B.left`, `p : ∀ j, U j ⟶ T`, followed by etaleness of every `p j` and joint surjectivity on scheme points. This is the usual scheme etale covering condition. No affineness or finiteness of the cover is imposed. |
| Rigidified line M_j on A_U_j, fibrewise algebraically trivial | For each j, an existential `M : RigidifiedLines ...` and the same `FibrewiseTrivial` predicate on its underlying small-model module. |
| Restriction isomorphism on A_(U_j times_T T₀) | The overlap is `CategoryTheory.Limits.pullback i (p j)` in `Over B.left`, whose underlying scheme is the scheme fibre product. Its second projection maps to U_j and its first to T₀. `picardInfinitesimalFamilyMap` is the identity on A paired with each of these actual projection maps. |
| Isomorphism preserves rigidification | The conclusion is `Nonempty` of an isomorphism between the two objects obtained by the existing `rigidifiedLinePullback` functors. Arrows of this groupoid are exactly the module isomorphisms commuting with the specified rigidifications. The existential `wU` and `w₀` are the section-square equalities needed as inputs of those functors; they introduce neither freely chosen comparison maps nor an additional mathematical assumption. |
| No uniqueness asserted | The conclusion uses existential choices and `Nonempty`, with no `∃!` or uniqueness condition. |

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its scheme-morphism category.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian` (the every-affine-open Noetherian-ring formulation).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`, its `Modules`, and `IsLineModule`. Read their signatures and docstrings, including the actual etale-site construction.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`, the existing locally trivial rank-one predicate underlying the geometric algebraic-equivalence definition.
- `Sheaf.AlgebraicGeometry.AbelianSpacePoincareData`: `Poincare.Pointed`, `Pointed.baseChange`, `pointedGroup`, `product`, `fst`, `snd`, `pair`, `baseMap_eq`, `IsAbelianFamily`, `HasAbelianFibres`, `FibrewiseTrivial`. Read their data and docstrings. These use the existing small-module restriction equivalence and scheme restriction; neither dual existence nor any Poincare representability theorem is used.
- `Sheaf.AlgebraicGeometry.RigidifiedLines`: `RigidifiedModule`, `IsRigidifiedLine`, `RigidifiedLines`, `rigidifiedLineForget`, `rigidifiedLinePullback`, including its actual tensor-composition/unit formula. Thus the conclusion is the existing normalized pullback, not an arbitrary restriction operation.
- Read `RegularGroupSpace.CommutativeSpaceGroup`, `groupSchemeMap`, `groupSpaceProjection`, `LineAlgebraicEquivalence.AreAlgebraicallyEquivalent`, `AlgebraicSpaceMorphismProperties.MapIsProper`, and `Mathlib.IdealSheaf.Basic`'s `Scheme.Hom.ker` for the definitions used transitively.
- Plain proof imports are the already stated `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus` and `Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality`. The three other proof prerequisites (`lem-sfb-space-picard-obstruction-natural`, `lem-sfb-algebraically-trivial-line-multiplicativity`, `lem-sfb-abelian-h2-reduced-coproduct-injective`) currently have no Lean record and are named in the proof docstring, without an invented declaration or import.

Sources read: Milne AV I Section 8, printed pp.36--37 (PDF pages 42--43),
including Proposition 8.4, the normalized universal family, and Remark 8.7;
Stacks `spaces-more-morphisms.tex`, label
`lemma-picard-group-first-order-thickening` (Tag 0DNM), its statement and
units-sequence proof. The module accurately identifies the relative lifting
assertion as the agent-stated extension in the node. The node's MFK GIT
Proposition 6.7 reference remains WANTED; neither the report nor the module
claims to have read it. The five accepted proof steps are all transcribed in
the theorem docstring, including arbitrary coefficient modules at non-Noetherian
affine parameters and the explicit evaluation calculation for normalization.

Edge cases checked by reading the definitions and the full type:

- The identity base change B = S is admitted, as are arbitrary locally Noetherian
  base changes; no restriction to geometric or flat base changes occurs.
- T and T₀ may be non-Noetherian affine schemes. There is no finite-generation
  hypothesis on the square-zero ideal.
- I = 0 and the identity immersion are admitted. The pullback/groupoid formulation
  retains the supplied rigidification in this case.
- Empty affine schemes and the empty base are admitted. No `Nonempty J` is imposed;
  joint surjectivity forces a nonempty covering only when T has points.
- Zero-dimensional abelian fibres, trivial groups, arbitrary fibre characteristic,
  and nonreduced parameters remain included. No torsion integer is inverted.
- Universe u is explicit throughout; the cover index and scheme-test universes are
  the same u as the schemes. No independent smaller test universe is introduced.
- On the overlap, the first projection goes to T₀ and the second to U_j. The
  section-square equalities have the orientation required by `rigidifiedLinePullback`.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder "Algebraically trivial rigidified line bundles on abelian schemes lift across square zero thickenings"`: 8 hits, headed by `AlgebraicGeometry.FormallyUnramified`, `retractionOfSectionOfKerSqZero` and ring formal smoothness. None is the line-module lifting assertion.
- `msearch.py ... loogle '"Picard", "FormallySmooth"'`: 0 hits.
- `msearch.py ... leansearch "Algebraically trivial rigidified invertible sheaves on abelian schemes lift through square zero thickenings"`: 8 hits, headed by `liftOfDerivationToSquareZero` and trivial square-zero extension maps, not this assertion.
- `msearch.py ... grep 'Picard|AbelianScheme|AbelianVariety'`: 23 hits; ring Picard groups, elliptic curves and Picard-Lindelof material, no match.
- `rg` of `lean/WeilConjectures` for the node id gave no declaration. Searches in both `lean/WeilConjectures/AlgebraicGeometry` and `lean/Sheaf` for abelian-space, rigidification, algebraic-equivalence and infinitesimal-lift names found the reusable definitions above, not an existing theorem with this conclusion. `dag/lean_names_upstream.json` likewise gave no binding for this item.
- `tools/blueprint_refs.py search infinitesimal` returned 0 blueprint matches. No new node was necessary; the existing Poincare-data and rigidified-line nodes give every needed notion.

Verification: compilation is exclusively through the prescribed `scompile.py`.
The first check diagnosed a name collision with `AlgebraicSpace.pullback`; all
scheme fibre-product references are now explicitly `Limits.pullback`. The next
check type-checked both sandbox and library module names and reported only one
long line, which was shortened before the final clean check. No statements are
proved; the single theorem proof is `sorry`, and both helper definitions have
fully specified data. No disputed statement or source correction is asserted.

## Second reading by Q134

This is a separate self-reading under the dispatcher's explicit instruction not
to start other agents; it is not represented as an independent worker review.
The maintainer's independent reading remains part of the normal delivery process.

Reopened the node, the delivered module, and the definitions of
`IsAbelianFamily`, `FibrewiseTrivial`, `RigidifiedLines` and
`rigidifiedLinePullback`. Compared every hypothesis and conclusion in the table
above. The original S case is included by B = `Over.mk (𝟙 S)`; arbitrary B over S
makes the final base-change clause explicit without assuming the parameters
Noetherian. Checked that `i.left.ker` is the quasi-coherent defining ideal of
the closed immersion. Checked that lines are required for both M₀ and each M,
and algebraic triviality is required on both sides. The restriction isomorphism
lives in the common rigidified-line groupoid on the actual overlap, so it cannot
forget r₀. Checked both overlap projections and section-square orientations.
No mathematical mismatch was found; the qualified fibre-product name and line
break were the only corrections needed by the compiler. There are no new nodes,
dependency-module repairs, hollow definitions, uniqueness conclusions, or changes
to the natural-language statement.
