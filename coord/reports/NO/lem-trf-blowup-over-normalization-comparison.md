## Worker report

The module `Sheaf.AlgebraicGeometry.BlowupOverNormalizationComparison` states
`AlgebraicGeometry.Scheme.IdealSheafData.normalizedBlowup_over_normalization_comparison`.
Its sole theorem proof is `sorry`; no new definition or auxiliary theorem is introduced.
The node changes only in `lean`. No statement correction or new node is needed.

Hypothesis-by-hypothesis correspondence:

- The reduced scheme S is `(S : Scheme.{u}) [IsReduced S]`.
- Its finite-type structure over Q is `(a : S ⟶ Spec (.of (ULift.{u} ℚ)))`
  with `[LocallyOfFiniteType a] [QuasiCompact a]`. The explicit structural morphism
  follows the interface of the recorded proof dependency `normalizedBlowup_finality`.
  The ring ULift Q is the canonical universe lift of Q, retaining arbitrary u.
- The quasi-coherent ideal is `(J : S.IdealSheafData)`. Coherence is rendered as
  `hJ : ∀ U : S.affineOpens, (J.ideal U).FG`, exactly as in finality. A finite-type
  Q-scheme is Noetherian, so quasi-coherent finite-type ideals are precisely coherent
  ideals (Stacks 01XZ, the recorded coherence criterion). On affine opens finite type
  is exactly finite generation of the corresponding ideal. Thus this is equivalent
  to the node's hypothesis, including on nonaffine S, and is not a restriction to
  principal or invertible ideals.
- The nowhere dense zero set is `hcentre : Dense (J.support.compl : Set S)`.
  Mathlib's `IdealSheafData.support` is the closed zero locus, not the support of J
  as a module. For a closed set, nowhere dense means its complement is dense.
- The componentwise normalization and its map are `S.reducedNormalization` and
  `S.fromReducedNormalization`, with their recorded coproduct-of-components meanings.
- X and p are exactly `J.normalizedBlowup` and `J.normalizedBlowupMap`.
- The extended ideal is `J.comap S.fromReducedNormalization`; Y and q are that
  ideal's `normalizedBlowup` and `normalizedBlowupMap`. The `comap` definition is the
  kernel of the first projection from the pullback of the closed subscheme.

Conclusion-by-conclusion correspondence:

- The first conjunct states `Dense` for the complement of the extended ideal's
  closed support on `S.reducedNormalization`.
- The second conjunct is `∃! n : J.normalizedBlowup ⟶ S.reducedNormalization,
  n ≫ S.fromReducedNormalization = J.normalizedBlowupMap`, giving precisely the
  unique lift p = nu composed with n.
- For every such n, the third conjunct first asserts `∃! e : X ≅ Y,
  e.hom ≫ q = n`. It does not assume an arbitrary comparison map or an isomorphism.
- For every isomorphism e satisfying that equation, the next clause states that
  `e.inv ≫ p = q ≫ nu`; its inverse is therefore an S-morphism.
- The following universal quantifier ranges over every morphism `r : Y ⟶ X`, with
  only `r ≫ p = q ≫ nu` as its premise, and concludes `r = e.inv`. This is uniqueness
  among all S-morphisms, not merely among invertible ones.
- The last two clauses are `e.hom ≫ e.inv = 𝟙 X` and `e.inv ≫ e.hom = 𝟙 Y`.
  They explicitly render the node's two inverse identities.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`, with its
  sectionwise definition and stalk equivalence; exposed transitively by normalization.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`. Its body is the
  conjunction of Mathlib quasi-coherence and finite type, not a replacement definition
  of coherent sheaves. Here quasi-coherence is supplied by IdealSheafData and finite
  type is expressed by affine finite generation, as in the existing finality interface.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and `blowupMap`,
  used through the normalized-blowup definitions.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalization`
  and `Scheme.fromReducedNormalization`, whose full construction and signatures were read.
- `Sheaf.AlgebraicGeometry.NormalizedBlowup`: `Scheme.IdealSheafData.normalizedBlowup`
  and `normalizedBlowupMap`, whose full bodies were read; exposed through the
  public finality import, which publicly imports the definition-only module in the
  current source. A single public path avoids a duplicate declaration in the published
  finality build, whose older dependency closure still imports the calculus copy.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`: `Scheme.IdealSheafData.comap`.
- `Sheaf.AlgebraicGeometry.NormalizedBlowupFinality` is public because it also exposes
  the statement definitions as described above; its theorem `normalizedBlowup_finality`
  is a proof dependency. The remaining plain proof imports are
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`
  (`IsFinite`, with integral morphisms exposed there), and
  `WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
  (`Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType`). Finite-type
  composition and base change are already in the public finite-type import.
- The other proof dependencies `lem-sfb-component-dominant-normalization-lift`,
  `lem-sfb-componentwise-normalization-generic-properties`, and
  `lem-trf-normalization-affine-stalk-closure` have no recorded Lean declarations
  in the current read clone, so there is no module of those nodes to import.

Sources read: the DAG statement and all six proof steps, each statement dependency
and its declaration/docstring, ILO Expose VIII 2.2.1--2.2.4 on printed p.90 (PDF
text extracted into sandbox), and the current `literature/blueprint/latest` locality
statement/proof. This item is an auxiliary comparison, not the unit's own statement.

Edge cases checked before writing:

- Empty S: its componentwise normalization and both blowups are empty. The ideal
  finite-generation condition and all morphism uniqueness conclusions retain their
  empty cases. No Nonempty, integral, irreducible, or positive-dimension binder appears.
- Reducible S: componentwise normalization is a coproduct; no function field of
  the whole S is assumed, and all morphisms are between the recorded schemes.
- Unit ideal: its zero locus is empty; both normalized blowups identify with the
  normalization and the comparison/inverse conclusions remain valid.
- Zero ideal on nonempty S: its zero locus is all S and fails the stated density
  hypothesis. On empty S the zero and unit ideals coincide and are allowed.
- Disconnected schemes and dimension-zero components require no additional hypothesis.
- Arbitrary u is retained by the standard ULift Q convention used in finality.

Searches for an existing statement (2026-10-23 UTC):

- msearch leansearch: `Normalized blowup commutes with normalization of a reduced
  scheme`; eight results about relative morphism normalization, including
  `Scheme.Hom.normalizationDesc` and `Scheme.Hom.toNormalization`. No match for the
  absolute componentwise normalized-blowup assertion.
- msearch leanfinder: `The normalized blowup of a reduced scheme is canonically
  isomorphic to the normalized blowup of the extended ideal on its normalization`;
  eight results on relative normalization and coproduct maps; no exact match.
- msearch loogle: `"normalization", "blowup"`; zero results.
- msearch grep: `blow.*normali[sz]|normali[sz].*blow` in `AlgebraicGeometry`;
  zero Mathlib hits.
- rg of that pattern in `lean/WeilConjectures` and `lean/Sheaf`: the existing
  `NormalizedBlowupCalculus` contains a private `normalization_comparison` and
  public `normalizedBlowup_calculus`. The private lemma assumes n and only concludes
  uniqueness of an isomorphism. The public theorem bundles many other assertions;
  neither declaration has the full statement of this node (the extended-centre
  density and uniqueness of all reverse S-morphisms are not its comparison clauses).
  No exact declaration is restated here.
- rg for `lem-trf-blowup-over-normalization-comparison` in upstream and Sheaf,
  and for the proposed declaration in `dag/lean_names_upstream.json`, upstream and
  Sheaf: no existing declaration found.

No STATEMENT-DISPUTED flag: the source universal properties support every clause.

## Second reading by NO

Self-review after writing, with the node and module open; the maintainer supplies
the independent delivery review as specified in the dispatcher brief. No other
agent was started. Checked the three hypotheses (reduced finite-type Q-scheme,
coherent quasi-coherent centre, nowhere dense zero set), the precise componentwise
normalization and normalized-blowup constructions, unique n, unique isomorphism
for that n, and uniqueness of the inverse among *all* S-morphisms. In particular,
the reverse-map uniqueness premise is only the over-S equation; it does not assume
an over-normalization equation. Checked both inverse equations and extended-centre
density. No statement correction was needed and no extra assumption was added.

Validation: scompile.py passed both the isolated sandbox compile and the proper
library-module compile (8.6 s and 5.0 s respectively), with no errors or warnings.
The initial duplicate-definition error was repaired by using the single public
finality import path rather than directly loading both versions of the definitions.
