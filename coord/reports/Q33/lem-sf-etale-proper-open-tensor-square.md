## Worker report

Item: `lem-sf-etale-proper-open-tensor-square`, group Q33, stage 2.
The delivery adds `Sheaf.AlgebraicGeometry.EtaleProperOpenTensorSquare`, with one theorem
`AlgebraicGeometry.Etale.etaleProperOpenTensorSquare`, whose proof is `sorry`.
No definition, dependency replacement, new node or statement correction is needed.
The source is Stacks `more-etale.tex`, lemma-shriek-proper-and-open (0F7B), case (b),
specialized to a Cartesian open square. The tensor part is the node's agent mate
calculation from `sites-cohomology.tex` 0GL1/0B56; 0E48 supplies related normalization,
not a claim that Stacks directly states this additional equation. I also read the current
blueprint `latest/blueprint/sec-six-functors-basics/sk-prop-cohsm/thm-asd-smooth-tensor.proof.md`,
especially the paragraph on transposing the projection and composite counit.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Finite commutative ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`. This includes
  the zero ring and makes no choice of a nonzero characteristic or invertible integer.
- Four arbitrary schemes and the four arrows: `{U V W Z : Scheme.{u}}`,
  `{r : U ⟶ W} {k : U ⟶ V} {i : W ⟶ Z} {p : V ⟶ Z}`.
- The square is Cartesian: `sq : IsPullback r k i p`. This includes commutativity and
  the universal property, without choosing `U` to be the literal selected pullback.
- Proper `p` and open `i`: `[IsProper p] [IsOpenImmersion i]`.
  `[IsOpenImmersion k]` exposes the stated base-change consequence for the existing
  extension-by-zero API; it is not an extra mathematical restriction on the square.
  Properness of `r` is likewise a consequence, and is not separately assumed.
- Ordinary unbounded module categories: `DerivedCategoryModule A U` and
  `DerivedCategoryModule A Z`, expanding to the recorded constant-coefficient
  `DerivedCategory (Sheaf _.smallEtaleTopology (ModuleCat.{u + 1} A))`.
  These are not bounded, completed, constructible, or structure-sheaf categories.
- `P_a` in the exchange is the exact termwise `D((a)^*[ModuleCat A])`.
  In the tensor formula it is the canonical left-derived presentation `L((a)^*[...])`.
  `leftDerivedUpperStarIsoMapDerivedCategory` is the canonical identification of these
  presentations, explicitly used by the published base-change and projection APIs.
- `R_a` is `R((a)_*[ModuleCat A])`; `J_j` is `D((j)_!open[ModuleCat A])`.
- The specified beta is the inverse of
  `mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso (ModuleCat A) sq`.
  Its source is `J_i ⋙ P_p`, and target `P_r ⋙ J_k`. The isomorphism is obtained
  degreewise from the open base-change sheaf mate, with the required inside/outside
  description. It is not an arbitrarily supplied comparison.
- The specified Gamma is the existing
  `openImmersionLowerShriekLowerStarExchange (ModuleCat A) sq`. I read its definition,
  docstring and component lemma `openImmersionLowerShriekLowerStarExchange_app`:
  its component is precisely the unit of the termwise `P_p ⊣ R_p`, then
  `R_p(beta_{R_r M})`, then `R_p(J_k(counit_r M))`. No second mate or map is defined.
- “Gamma is a natural isomorphism” is the first conjunct `IsIso (openImmersion... sq)`;
  the underlying object is already a natural transformation of the required functors.
- Every unbounded `M,N`: the second conjunct quantifies
  `∀ (M : DerivedCategoryModule A U) (N : DerivedCategoryModule A Z)`.
- `Gamma_M tensor 1_N`: the first left-hand factor is
  `((-⊗ᴸ-(Z)[ModuleCat A]).map (Gamma.app M)).app N`.
- `pi_{p;J_k M,N}`: the second left-hand factor is the double component of
  `rightDerivedLowerStarProjectionMap (ModuleCat A) p` at `J_k M,N`.
- `R_p(delta_{k;M,P_p N})`: the third left-hand factor applies `R_p.map` to the
  inverse double component of `derivedOpenImmersionLowerShriekProjectionIso` for `k`.
- The fourth left-hand factor is the explicit identification allowed by the node:
  `R_p.map (J_k.map ((tensor.obj M).map (derivedSquareUpperStarIso ...).hom.app N))`.
  Here the hom goes from `P_k P_p N` to `P_r P_i N`; its inverse is the node's
  displayed `P_r P_i N ≅ P_k P_p N`. Thus both sides land in
  `R_p J_k (M tensor P_r P_i N)`, and no equality of objects is assumed.
- `delta_{i;R_r M,N}`: the first right-hand factor is the inverse open projection
  component at `R_r M,N`.
- `J_i(pi_{r;M,P_i N})`: the next right-hand factor is `J_i.map` of the recorded
  counit-defined projection component for `r` at `M,P_i N`.
- `Gamma_{M tensor P_r P_i N}`: the last right-hand factor is exactly that component
  of the existing exchange natural transformation.
- Composition in Lean is left to right with `≫`; the resulting equation is the node's
  displayed equation, whose mathematical compositions are read right to left.
- No qc-open, Noetherian, boundedness, constructibility, Tor-amplitude, or invertibility
  of the projection morphisms appears in the signature. The components remain those of
  canonical natural transformations, so their naturality is inherited.

Recorded statement dependencies used, after reading their statements and source signatures:

- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`; `IsPullback` is
  the universal-property version appropriate to a given Cartesian square.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` (separated, universally closed, locally finite type;
  universal closedness supplies quasi-compactness as in its record).
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  re-exporting `AlgebraicGeometry.Etale.DerivedCategoryModule` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `def-kun-projection-formula-map`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`,
  `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap` and its component/
  transpose lemmas. They define the actual counit-transpose, not a chosen map.
- `lem-weil-pbc-extension-by-zero-exact`:
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`,
  `AlgebraicGeometry.Etale.preservesFiniteLimits_openImmersionLowerShriek` and the
  already supplied additive/left-adjoint instances defining exact termwise extension.
- `lem-pur-etale-open-derived-tensor`:
  `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`,
  `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso`, inverse components.
- `lem-sfb-ringed-derived-monoidal-comparisons`:
  `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`,
  `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`, publicly
  imported as the node's general comparison theorem. In this constant-coefficient
  specialization the explicit canonical pullback comparison is the existing
  `derivedSquareUpperStarIso`, defined from the two `leftDerivedUpperStarComp` maps
  in `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`.

The canonical exchange API is publicly imported from
`WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange`.
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat` supplies the existing
flat-preservation instances for these coefficients; it adds no hypothesis. Every recorded
proof dependency is imported, privately unless already a statement dependency: localized
exact adjunction, exact derived normalization, extension stalks, module stalk/cohomology
test, arbitrary open base change, torsion-ring proper base change, stalk as pullback,
fully-faithful mate image, `mateEquiv`, ordinary open projection exchange, and mixed-action
mate transfer. The theorem docstring includes all six natural-language proof steps.

Edge cases checked before writing and again against the elaborated signature:

- Empty `W` (and hence `U`): extension from the empty open is zero, so Gamma and both
  composites have the required zero behavior; there is no nonempty-scheme hypothesis.
- `i = id`: base change makes `k` an isomorphism, and the equation reduces to the same
  proper projection under the canonical unit/composition identifications.
- `p = id`: base change identifies `r` with an isomorphism; the equation reduces to
  the open tensor identity. No invertibility of an arbitrary proper projection is used.
- Zero coefficient ring: allowed by `CommRing` and `Finite`; its module categories
  are trivial and finite implies torsion also here (annihilator 1 suffices).
- Zero and genuinely unbounded complexes are admitted by the unrestricted derived
  object binders, and no common cohomological bound occurs.
- The universe convention is the recorded one: schemes at `u`, coefficient modules
  at `u+1`. No independent smaller universe of test schemes or coefficients is introduced.
- Non-quasi-compact opens and non-Noetherian bases are unrestricted.

Searches (2026-10-23 UTC, using the prescribed msearch wrapper):

- LeanFinder, “Proper open interchange of unbounded etale derived module sheaves is
  compatible with projection formula tensor maps”: 8 unrelated results, including
  `SheafOfModules.Presentation.map_π_eq`, `ModuleCat.Tilde.toOpen_res`, and étale tensor
  algebra results; no matching statement.
- LeanSearch, “Proper open interchange for etale sheaves commutes with derived tensor
  projection maps”: 8 unrelated sheaf restriction, algebraic étale base-change and Proj
  results; no matching statement.
- Loogle, `"mateEquiv"`: 12 generic mates/pasting results; useful machinery, no matching
  proper/open tensor theorem.
- Mathlib grep, `properOpen|openImmersionLowerShriekLowerStarExchange`: 0 hits.
- Source/project `rg` for `openImmersionLowerShriek`, `properOpen`, exchange/tensor patterns,
  and the exact node id: found the canonical exchange definition, its torsion invertibility
  theorem, open projection/base-change coherence, and downstream citations. None is the
  combined public statement of this item. The exact-id search in `WeilConjectures` is empty.
- In `lean/Sheaf`, `CompactificationProjectionComposition.lean` has a **private** helper
  `mixed_projection`, with file-local `let` abbreviations and generic coefficient binders.
  I read its entire statement and normalization. It confirms the direction of the explicit
  last comparison, but is not an accessible declaration that can carry this node's public
  combined assertion. I do not copy its proof or introduce its definitions.
- `rg etaleProperOpenTensorSquare` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no existing declaration with the delivered name.

No STATEMENT-DISPUTED flag or mathematical node fault was found. The requested example
`lean/Sheaf/CategoryTheory/CompactObject.lean` is now a withdrawn empty module; I read it
and its node, and follow the active `module`/public-import conventions from the standing
brief and the other landed statement modules.

Validation: prescribed `scompile.py Q33 lem-sf-etale-proper-open-tensor-square <file>`
passed in sandbox mode (22.2 s) and library mode (19.8 s), with no errors or unexpected
warnings. Only the node's `lean` field is changed; its signature is extracted verbatim
from the delivered theorem, and all pre-existing JSON fields are preserved.

## Second reading by Q33

I reopened the node and Lean file and reread them side by side. This is the worker's
second pass; the dispatcher explicitly prohibits spawning another agent and the delivery
receives an independent maintainer review. No independent second reader is claimed here.

The finite ring and arbitrary scheme hypotheses match; `IsOpenImmersion k` only exposes
the stated base-change consequence. I checked the first conjunct refers to the whole
natural transformation, not just one component. I traced Gamma's existing definition to
the termwise adjunctions and beta inverse, and traced the projections to the published
counit-transpose definition. The inverse of the open projection iso has precisely the
direction of delta in the node. I checked the four factors of the left-hand composite
and the three factors of the right-hand composite and their common target; the fourth
left factor is necessary because `derivedSquareUpperStarIso.hom` points from `P_k P_p`
to `P_r P_i`. The node expressly permits that identification. The equality quantifies
over both arbitrary derived objects and does not assume projection invertibility.
No statement mismatch was found and no correction was made. The only proof is `sorry`,
and all universes/variables are bound with `autoImplicit false`.
