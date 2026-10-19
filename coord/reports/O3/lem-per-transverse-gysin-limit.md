## Worker report

The module `Sheaf.AlgebraicGeometry.TransverseGysinLimit` states
`AlgebraicGeometry.Etale.transverse_gysin_limit`. All definitions have actual data;
the item theorem alone has `sorry`. The node statement and proof are unchanged.

The encoding follows the ordinary small-etale module-sheaf categories used by the
recorded dependencies. `regularClassCoefficients ℓ 1` is `ULift (ZMod (ℓ^1))`, the
coefficient-universe lift of F_ell. `transverseTateObject` embeds the recorded signed
finite Tate sheaf into degree zero. Ordinary cohomology is derived Hom from the
constant rank-one sheaf, and supported cohomology is derived Hom from its exact
closed direct image. This is the presentation of `closedSupportHom`; its restriction
cone is the derived kernel section functor `derivedSupportedEtaleSections`.
The inclusion of that dependency and the normalized support triangle keeps the
support convention explicit. There is no pro-etale category or abstract cohomology model.

Hypotheses, clause by clause:

- The prime is `(ℓ : ℕ) (hℓ : ℓ.Prime)`. The coefficient exponent is fixed to one.
- The small directed index is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] (a₀ : I)`. The chosen stage only witnesses nonemptiness
  and supplies invertibility at the limit. The conclusion holds for every choice
  of that stage; it imposes no condition on the system. The index universe equals
  the schemes' universe, as required for the affine-limit continuity convention.
- `Z V : Iᵒᵖ ⥤ Scheme` are the inverse systems. `i : Z ⟶ V` gives the closed
  immersions and commuting transition squares. Both families are affine and
  Noetherian by the four pointwise typeclass binders. A morphism between affine
  schemes is affine, so separate affine-transition assumptions would be redundant.
- `[∀ a, IsClosedImmersion (i.app (op a))]` is precisely the recorded closed-immersion
  definition. `z`, `v`, `_hz`, `_hv` are the two cones and their limit proofs.
  Their apexes are Noetherian. The closed immersion `j` and `hj` specify the
  compatible limiting pair; the limits determine its map uniquely.
- `c : ℕ` includes codimension zero. `t a` and `tLimit` are the ordered lists of
  global regular generators. `_hlen`, `_hlenLimit` give their common length `c`.
  `_hreg`, `_hregLimit` use Mathlib `RingTheory.Sequence.IsRegular`, including
  its nonzero final-quotient condition, exactly as the recorded dependency does.
- `_hcut` and `_hcutLimit` identify the generated ideals with the kernels of
  the global-section maps of the closed immersions. On affine schemes these say
  exactly that the sequences cut out the specified closed subschemes. The limit
  schemes are affine because they are limits of affine schemes.
- `_ht` asserts entrywise preservation by every transition; `_htLimit` asserts
  preservation by the limit projections. These are list-map equalities, so the
  order and every generator are retained. There is no flatness binder.
- `hV a` is invertibility of `ℓ^1` on every ambient stage, equivalently of `ℓ`.
  `transverseUnitPullback` derives all closed-stage and limit invertibility
  certificates using the actual global-section ring maps. They are not extra
  hypotheses, nor data selected from an existence assertion.

Conclusions, clause by clause:

- The first conjunct quantifies `q m : ℤ` and gives `TransverseContinuity` for
  both supported groups and ordinary groups on `Z`. It means every limit class
  descends to a stage and every stage class killed at the limit vanishes at a
  later stage. For these canonical additive compatible pullbacks this is exactly
  bijectivity of the canonical directed-colimit comparison, in the same
  elementwise format as `cohomology_continuity_of_isLimit`.
- `transverseHomPullback` is an explicit composite: exact inverse image on
  derived categories, its degree-zero realization and shift isomorphisms, and
  the normalized source and target Tate comparisons. Ordinary pullback uses
  `regularClassTwistPullback`; supported pullback additionally inverts the
  canonical `regularClassExchange` along the natural square. Finite base change
  makes it invertible for all the Cartesian pairs here. Its zero extension is
  only a total definition outside that domain; it is never an arbitrary map.
- `transverseClassFamily` selects the uniquely specified family in the existing
  `regular_immersion_class_calculus` theorem. `transverseGysin` is actual exact
  closed direct image of a cohomology morphism followed by the shifted specified
  supported class, with the canonical addition-of-shifts comparison. It uses
  the positive Cartier normalization of that dependency, not a new class family.
  Its zero extension outside stalk regular immersions is irrelevant here:
  localization of the globally regular sequence makes each stated immersion
  stalk regular. In particular it does not replace regularity by an assumption.
- The second conjunct is the equation for every transition `a ≤ b`: pull back
  `G_a(x)` equals `G_b` applied to the ordinary pullback of `x`. Its target degree
  is `q + 2 * (c : ℤ)` and its twist is `c`.
- The third conjunct is that same equation for every projection to the limit.
  Together with the first conjunct it says exactly that the colimit of the
  compatible Gysin maps is the Gysin map of `j`. Every colimit class has a stage
  representative, so this is equality of the specified maps under both canonical
  continuity identifications, not just existence of group isomorphisms.

Dependencies read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, the ordinary module-sheaf
  derived category. Its existing module is imported through the class calculus.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`:
  `Scheme.finiteEtaleTateTwist`; the signed extension is the already published
  `Scheme.finiteEtaleTateSheaf`, used through `regularClassTwist`.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.EtaleSupportedSections`:
  `supportedEtaleSections`, `derivedSupportedEtaleSections`.
- `Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus`:
  `regular_immersion_class_calculus`, `RegularImmersionClassFamily`,
  `regularClassCoefficients`, `regularClassTwist`, `regularClassTwistPullback`,
  and `regularClassExchange`; `IsStalkRegularClosedImmersion` is its existing
  support-local regularity interface.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `Scheme.etaleFiniteTwistPullback` and its normalized structured witness
  `Scheme.finiteEtaleTwistPullbackData`.
- Proof imports: `ClosedSupportHom.closedSupportHom` (in the Etale namespace),
  `EtaleCohomologyContinuity.cohomology_continuity_of_isLimit`,
  `NormalizedSupportTriangle.normalizedSupportTriangle_distinguished`, and
  Mathlib filtered colimits of abelian groups. The recorded supported-product
  theorem has no published Lean declaration, so no speculative proof import is added.

Edge cases checked against the statement and definitions:

- `c = 0`: the list is empty, its ideal is zero, each closed immersion is an
  isomorphism on its affine scheme, and the class-calculus normalization is the
  identity. The complementary open is empty. No positivity assumption is imposed.
- `q < 0`: the two cohomology groups of degree-zero sheaves vanish, while Gysin
  targets still have the stated signed degree. No conversion from `q` to a natural
  number occurs. Negative `m` uses the existing dual Tate line.
- Empty schemes: the regular-sequence dependency requires a nonzero final
  quotient, so globally empty closed schemes are already excluded by the node's
  regular-sequence hypothesis; this is not an extra nonemptiness restriction.
  The empty complementary open for `c = 0` remains included.
- A singleton directed index gives identity continuity and identity transition
  compatibility. No linear order or injective transition map is required.
- A nonflat transition such as k[t,x] to k[t] preserving the regular generator t
  is allowed. A map sending t to zero fails the required regularity/preservation,
  as it should. Thus flat base change has not silently replaced the assertion.

Searches retained from the interrupted attempt (`searches.jsonl`) and checked:

- msearch grep, `supported.*[Cc]ohomology|[Cc]ohomology.*[Cc]ontinuity|Gysin`,
  AlgebraicGeometry: zero Mathlib hits.
- msearch loogle, `"Kummer"`: eight algebraic Kummer/Dedekind hits, none ordinary
  etale supported cohomology.
- msearch leanfinder, `Supported etale cohomology continuity for affine inverse
  limits of regular closed pairs and compatibility of Kummer Gysin maps`:
  eight hits about affine scheme limits and approximation, no exact statement.
- msearch leanfinder, `Etale cohomology with supports continuity inverse limits
  preserved regular sequence Kummer Gysin maps`: affine-limit/algebraic etaleness
  hits only, no supported Kummer continuity statement.
- msearch leansearch, `Etale cohomology with closed supports commutes with inverse
  limits of affine schemes preserving a regular sequence`: eight hits about
  scheme limits, affine opens and structure sheaves, not this statement.
- `rg` of the upstream WeilConjectures tree, the project's `lean/Sheaf`, and the
  upstream name index for transverse/Gysin/continuity names: no duplicate item
  or occupied new helper names. The existing ordinary continuity and class
  calculus are used, not restated.

Source reading: Stacks `etale-cohomology.tex`,
`lemma-directed-colimit-cohomology` (03Q6), including its affine base-change
formulation and proof; ILO Expose XVI printed pp. 233--234, Proposition the project server
(arbitrary base change of generalized classes), Definition 2.3.1 (the conormal
class and codimension-zero normalization), and Theorem 2.3.2 (composition).
The node's six proof steps supply the supported localization and regular-flag
argument. No statement correction was needed.

The existing class-calculus theorem carries a `STATEMENT-DISPUTED` note about
uniqueness from its displayed laws. This delivery neither changes that assertion
nor claims to resolve it; it uses precisely the recorded unique class family.
The continuity and Cartier-preserving naturality assertions themselves agree
with the cited source argument.

## Dependency modules

`lem-per-regular-immersion-class-calculus`: the republished module retains its
complete canonical class family and laws. Its recorded `.c` and `.p` consumer
interface was unusable against the stale compiled finite-Tate dependency.

`lem-asd-etale-finite-twist-pullback`: the republished module retains the
normalized structured comparisons and every law of the original theorem. It
supplies those missing projections to the class-calculus consumer.

The compile exposed a publication/interface mismatch: the recorded class-calculus
module calls `Scheme.finiteEtaleTwistPullbackData`, but resolving its dependency
without explicitly supplying the current finite-Tate module gives “Unknown constant”
at its two `.c` and `.p` calls. The saved repair by nested `Classical.choose_spec`
projections timed out after 60 seconds, both in the private overlay and on server
confirmation. That repair was discarded. The current dependency sources are
republished together, with a module-docstring clarification, without changing the comparisons, normalizations, laws,
or theorem statements. The structured source retains every original clause and
compiles within the required limit; no arbitrary Tate isomorphism is supplied.
The dependency-node copies change only `lean` and explain this mismatch in `lean.note`.

The added statement dependency `lem-asd-etale-finite-twist-pullback` is an already
landed node used directly for the canonical twist comparisons, not a new definition.

## Self-check

Re-read the item and the module clause by clause after completion. The saved file
had no theorem and used invalid line breaks after field-notation dots; these were
repaired. Its Gysin shift comparison originally inferred natural-number shifts;
it now explicitly uses integers. All variables and universes are explicitly bound.
The selected canonical family is the recorded unique family; no hollow definition
or additional flatness assumption has been introduced. The final delivery is
subject to the maintainer's independent reading, as required by the dispatch brief.

The first dry run compiled every module cleanly through server confirmation. Its
sole preflight failure was that this dependency section did not explicitly spell
out `lem-per-regular-immersion-class-calculus`; that report defect is repaired.
The preflight also notes the added already-landed Tate comparison theorem node:
it owns the exact canonical structured comparisons used to state these maps,
so this is an interface dependency, not an additional mathematical assumption.

Resumption self-check (2026-10-18 UTC): the saved packet passed the prescribed dry
run, including all three per-file compilations and server preflight. Re-read the
current item against the saved theorem and its canonical maps: the hypotheses,
signed continuity clauses, transition equation and limit projection equation match.
The two dependency signature records now retain the source line breaks verbatim;
no Lean declaration or mathematical statement changed during this resumption.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
