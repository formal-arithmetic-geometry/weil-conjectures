## Worker report

The module `Sheaf.AlgebraicGeometry.TraitPrimitiveSectionSpecialization` states
`AlgebraicGeometry.Scheme.Modules.exists_trait_primitive_section`, with its entire proof
postponed by `sorry`. It introduces no definitions, axioms, auxiliary statements, new nodes,
or dependency repairs. Only the item's `lean` record changes.

Hypothesis and conclusion correspondence:

| Node text | Lean rendering |
| --- | --- |
| A discrete valuation ring R | `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]` |
| Fraction field K | `(K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]` |
| Residue field k | The canonical `IsLocalRing.ResidueField R`, with quotient map `IsLocalRing.residue R`; this is exactly R modulo its maximal ideal, not an arbitrary field or map. |
| Uniformizer pi | `(π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})` |
| A morphism X to Spec R | `(X : Scheme.{u}) (f : X ⟶ Spec (.of R))` |
| Smooth | `[Smooth f]`, the dependency's affine-local smoothness definition |
| Separated, meaning closed-immersion diagonal | `[IsSeparated f]`, whose field is `IsClosedImmersion (pullback.diagonal f)` |
| Of finite presentation | `[QuasiCompact f]` together with smoothness, which implies local finite presentation, and separatedness, which implies quasi-separatedness. These are exactly the three components of the node's finite-presentation convention. Redundant local-finite-presentation and quasi-separated binders are omitted. |
| Nonempty geometrically connected fibres | `[GeometricallyConnected f]`: Mathlib requires `ConnectedSpace` after every field-valued base change, and `ConnectedSpace` includes `Nonempty`. Its fibrewise equivalence matches the node's residue-field formulation. Testing an algebraic closure is equivalent by faithfully flat descent of connectedness and nonemptiness; no geometric integrality or rational point is assumed. |
| X_K and X_k | `pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))` and `pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))` |
| Projections to X | The respective `pullback.fst` maps |
| Invertible module C | `(C : X.Modules) [C.IsInvertible]`, exactly the recorded upstream class |
| Restrictions C_K, C_k by tensor inverse image | `(tensorPullback (pullback.fst f ...)).obj C` |
| Every nonzero global generic section | `(sK : Γ((tensorPullback ...).obj C, ⊤)) (hsK : sK ≠ 0)` |
| An integer m and global section s exist | `∃ (m : ℤ) (s : Γ(C, ⊤)), ...` |
| s restricts to pi^m s_K | First conjunct. The normalized tensor-pullback adjunction unit at C, evaluated on the top open, is the canonical pullback of s. The coefficient is `(algebraMap R K π) ^ m` in K, transported to the structure sheaf by `(Scheme.ΓSpecIso (.of K)).inv` and then by the generic-fibre structural map `(pullback.snd f ...).appTop`. The resulting global regular function acts by the existing section-module scalar action. |
| s restricts nontrivially to X_k | Second conjunct: the same normalized unit for the canonical residue-field fibre, evaluated at s, is unequal to zero. |
| No properness or completeness | Neither is a binder or a premise. The proof-only import of Proper reflects the inherited proof-dependency record, not an assumption on f. |

Dependency declarations read and reused:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`.
- `def-sc-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`,
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`,
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`.
  Read its real section construction and uniquely normalized unit, not merely a
  freely chosen adjunction. No alternative pullback or restriction map is introduced.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`; supplied by smoothness here.
- `def-sc-discrete-valuation-ring`: the `mathlib_match` in
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, `IsDiscreteValuationRing` and
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  with scheme pullbacks from `Mathlib.AlgebraicGeometry.Pullbacks`.

Also read the existing `GeometricallyConnected`, `ConnectedSpace`, local residue field,
fraction-ring predicate, `IsSeparated`, and `Scheme.ΓSpecIso` source declarations.
Proof dependencies with recorded modules or Mathlib matches are imported without `public`
unless already public statement dependencies. The docstring reproduces all seven proof
steps: localization at pi, integrality, finite affine denominators and gluing, stalkwise
Krull intersection, maximal global divisibility, and division-and-gluing contradiction.

Source check: opened `literature/stacks-project/algebra.tex` at
`lemma-normal-domain-intersection-localizations-height-1` (Tag 031T, specifically (2)),
and `literature/stacks-project/descent.tex` at `lemma-regular-local-smooth` (Tag 036D).
As the node expressly says, this geometric lemma is agent-extracted rather than a verbatim
Stacks assertion; the supplied alternative denominator proof is retained in the docstring.

Edge cases checked:

- An empty X or empty special fibre is excluded by the stated nonempty geometric-fibre
  hypothesis itself: Mathlib's connectedness includes nonemptiness. No extra nonempty
  assumption is added, and an open generic-only scheme cannot satisfy the hypothesis.
- A zero s_K is explicitly excluded; on a scheme where there are no nonzero generic
  sections the statement is correctly vacuous, with no section-existence assumption.
- Negative, zero, and positive m are all permitted by `ℤ` and field `zpow`.
  A uniformizer is nonzero, so its image in the fraction field is nonzero and negative
  powers mean the required inverses, not truncated natural powers.
- Any residue characteristic is permitted. R is not a field by the DVR class itself.
- The trivial line on Spec R gives the usual normalization of a nonzero fraction by
  its valuation, illustrating both signs of m. Nonproper examples such as affine space
  over R are not excluded. There is no completeness, henselianity, dimension, group,
  ampleness, global-triviality, or generic-section-generation assumption.
- All variables and universes are explicit; all schemes, rings and field-valued tests
  use the common arbitrary universe u required by the existing Scheme APIs. No smaller
  independently quantified test universe makes the fibre hypothesis vacuous.

Searches for an existing statement, all performed before writing:

- `msearch.py ... leanfinder`: "A nonzero generic fibre section of an invertible module
  on a smooth scheme over a discrete valuation ring can be rescaled by a uniformizer
  to extend with nonzero reduction". Eight hits, including
  `PowerSeries.weierstrassDistinguished_smul`, `Valuation.exists_pow_Uniformizer`,
  `StructureSheaf.normalize_finite_fraction_representation`, and
  `ModuleCat.Tilde.exists_const`. None states this line-section specialization theorem.
- `msearch.py ... loogle`: `"IsDiscreteValuationRing", "section"`: zero hits.
- `msearch.py ... grep`: `uniformizer.*section|section.*uniformizer|primitive.*section`
  in Mathlib/AlgebraicGeometry: zero hits.
- `msearch.py ... leansearch`: "Primitive specialization of a generic line bundle
  section over a discrete valuation ring". Eight hits, about DVR classes, localizations,
  power series, or structure-sheaf evaluation. No theorem matching the item.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`:
  `primitive.*[sS]ection|[sS]ection.*[uU]niformizer|trait_primitive`.
  Hits concern Cech primitives, roots of unity, adic coefficients, or local traits;
  none gives this statement.
- `rg` for the exact item id in `lean/WeilConjectures`: zero hits.
- Searched geometric connectedness and canonical tensor-pullback section usages in
  both source trees; reused the established Mathlib class and recorded normalized unit.

One inherited proof-plan citation fault is worth recording for stage 3:
step 2 cites `lem-pc-proper-base-change` for preservation of smoothness, but that node's
current declaration states stability of properness. Smooth base-change stability is
already in the imported Smooth module. The mathematical step is valid and requires no
change to this item's statement; no proof plan or dependency records were edited.
No statement dispute or missing notion was found.

Validation: `scompile.py Q146 lem-sfb-trait-primitive-section-specialization` compiled the
file in sandbox and library module modes on the server (1.8 seconds each), without errors
or unexpected warnings. The only postponed declaration is the named main theorem.

## Second reading by Q146

Author's second pass, under the dispatcher's direct-delivery instruction; the maintainer
supplies the independent review. Reopened the node and final module and checked the table
above clause by clause. The DVR generator condition is exact; the fraction map and residue
quotient are canonical; the generic and special fibres use the correct first projections
to X, while the generic coefficient uses the second projection to Spec K. In particular,
the integer power is taken in K before transport, so negative exponents are preserved.
Both restrictions use the recorded normalized tensor adjunction unit. The nonzero special
restriction is an inequality of global sections, not a pointwise-generating condition.
The finite-presentation condition is fully present as smooth plus quasi-compact plus
separated, and Mathlib's `ConnectedSpace` supplies exactly the node's fibre nonemptiness.
No properness or completeness premise appeared. No mismatch requiring a statement change,
additional node, or dependency repair was found. No proofs were supplied.
