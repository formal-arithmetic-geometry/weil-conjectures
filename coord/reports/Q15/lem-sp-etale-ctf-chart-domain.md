## Worker report

Item: `lem-sp-etale-ctf-chart-domain`, Q15, stage 2, 2026-10-22.
Module: `Sheaf.Paper.EtaleCtfChartDomain`.

The delivery states the node in the ordinary constant-ring module-sheaf presentation
used by its recorded adjunction-transfer dependency. There are two postponed named
theorems, each with `sorry` as its entire proof and a source/proof-plan docstring.
The other four declarations have real data: two composites of the already published
functors and two canonical natural isomorphisms. There is no arbitrary comparison
map, new derived category, new constructibility predicate, or extra Tor assumption.
No definition node or dependency repair is necessary.

The node's assertions for R=A and R=B are rendered by specializing the universally
quantified single-coefficient theorem `etaleCtfChartDomain` twice, using the SAME n.
The separate `etaleCtfChartScalarDomain` has A, B, their unital ring map and that
common n. This is a decomposition of the universally quantified node into its
single-ring assertions and its coefficient-map assertion, without a statement change.

Hypothesis-by-hypothesis correspondence:

| Node | Lean |
| --- | --- |
| Field k, characteristic p>0 | `(k : Type u) [Field k] [Fact (ringChar k).Prime]`; positive characteristic of a field is prime |
| Prime ell different from p | `(ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]` |
| Finite commutative coefficients | `(R : Type (u+1)) [CommRing R] [Finite R]`, and A,B analogously in the scalar theorem |
| N=ell^n >= 1 annihilates the rings | `n : ℕ`, `hR : ((ℓ ^ n : ℕ) : R) = 0`; scalar theorem has `_hA` and `_hB` for the same n. Primality of ell implies N>0, including n=0 |
| Unital A -> B | `φ : A →+* B`, without flatness, projectivity or an algebra chosen independently of φ |
| All schemes are k-schemes | `[U.Over (Spec (.of k))]`, etc., for U,V,T,T' |
| Separated and finite type over k | `[IsSeparated (T ↘ Spec (.of k))]`, `[LocallyOfFiniteType (T ↘ Spec (.of k))]`, `[QuasiCompact (T ↘ Spec (.of k))]`, repeated for each named scheme |
| h is a separated finite-type k-morphism | `(h : U ⟶ V) [h.IsOver (Spec (.of k))] [LocallyOfFiniteType h] [QuasiCompact h] [IsSeparated h]` |
| Chosen compactification in the setting | `c : Compactification h`; its canonical `Compactification.overZ` structure and proper structure map supply `locallyOfFiniteType_over`, `quasiCompact_over`, `isSeparated_over`; `isOver_i` and `isOver_g` retain k-linearity. Thus no independent assumption on the middle scheme is lost |
| An arbitrary standing inverse-image map | `(u : T' ⟶ T) [u.IsOver (Spec (.of k))]`, without an etale or smooth assumption |
| Small ordinary etale derived categories | `Etale.DerivedCategoryModule R T`, i.e. `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u+1} R))` |
| Ordinary pro-etale category | `DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u+1} R))` |
| Dctf | The dependency's `AdjunctionTransfer.etaleProperty` and `proEtaleProperty`, used literally, with finite-value constructibility and actual Tor tests against every degree-zero module sheaf |
| Constant-ring derived scalar extension | `Etale.scalarExtension φ T` and `pbcFixedScalarExtension (Scheme.ProEt.topology T) φ`, the existing left adjoints of actual derived restriction, with K-flat counits in the published interface |
| Finite Tate powers | `Scheme.finiteEtaleTateTwist T' N R hR a`, placed in degree zero by `DerivedCategory.singleFunctor`; a ranges over ℕ |

Clause-by-clause correspondence:

1. The first conjunct of `etaleCtfChartDomain` says that
   `Etale.rightDerivedLowerShriekOfCompactification (ModuleCat R) c` sends every
   `etaleProperty R U` object to `etaleProperty R V`. The imported definition is
   exactly exact derived open extension followed by total right-derived proper
   direct image, on the unbounded ordinary categories. Specialize R separately
   to A and B.
2. The second conjunct supplies preservation `hc` and states
   `(comparison R T hc).IsEquivalence`. That dependency functor is the actual
   restriction of `(comparisonUpperStar (ModuleCat R) T).mapDerivedCategory`
   on objects AND morphisms; its equivalence cannot be an unrelated equivalence.
   `Functor.asEquivalence` supplies the usual equivalence data if needed.
3. The third conjunct quantifies over all bounded constructible K and all ordered
   integer intervals a<=b, and states the equivalence of the two existing
   `DerivedCategory.torAmplitudeIn` predicates. These use the derived tensor
   against EVERY module sheaf on each site. It is stronger than merely preserving
   existence of some bound only in exactly the way the node explicitly requests.
4. The last two conjuncts state preservation of the etale and pro-etale Dctf
   domains by `etaleChartOperation` and `proEtaleChartOperation`, for every natural
   twist and integer shift. The operation is exact scheme inverse image, derived
   tensor with the finite Tate object, then the shift. The line is tensored on the
   left, the symmetric convention for K(a).
5. `chartOperationComparison` provides the actual canonical natural isomorphism
   `nu_T^* ⋙ proEtaleChartOperation ≅ etaleChartOperation ⋙ nu_T'^*`.
   Its term uses `comparisonUpperStarCompUpperStarIso`, its exact derived descent,
   `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`, and
   `CommShift.commShiftIso`. The two preservation conclusions put its endpoints
   in the full finite-Tor subcategories; naturality and invertibility survive
   restriction to those full subcategories. For a=0 this includes bare inverse
   image followed by shift, and b=0 includes the finite Tate tensor comparison.
   The individual inverse-image, tensor and shift comparisons are also reexported
   by their published names; none is selected from existence of an equivalence.
6. The pro-etale Tate object in this canonical formula is
   `D(nu^*) (finiteEtaleTateTwist[0])`. Exactness identifies this with the comparison
   pullback sheaf placed in degree zero. The imported
   `Scheme.finiteRootSiteComparison` supplies its root-normalized first-power
   identification with `finiteRootProTensor = mu_N tensor_(Z/N) R`, with the same
   units on sections and compatible scheme pullback. The monoidal comparison
   iterates that identification for every finite power. This is the canonical
   ordinary finite-coefficient presentation of the pro-etale Tate object, also
   used by existing `geoP1Twist`; it introduces no choice of a local basis.
7. `etaleCtfChartScalarDomain` states preservation by arbitrary coefficient
   extension on both sites. `chartScalarComparison` is the restriction of the
   already published canonical B-linear `pbcComparisonReduction`, formed by the
   scalar-adjunction mate of exact scalar restriction and comparison. Its term
   is `Functor.isoWhiskerLeft` of that specified comparison, so there is no
   unconstrained natural isomorphism. Together with scalar preservation and
   the finite-Tor comparison equivalence, both its endpoints lie in Dctf.

Statement dependencies read and used:

- `sk-def-sfb-dc-setting`: the recorded module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
  is publicly imported. Its setting is rendered by explicit binders, as its
  record instructs. The companion `WeilConjectures.Compactification.Over`
  declarations listed above ensure every compactification stays in that setting.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`
  and its public `Etale.DerivedCategoryModule`, Mathlib `DerivedCategory`, its
  homology and single functors. This is the recorded six-functor presentation.
- `lem-pur-derived-change-of-rings`:
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem.
  The already published companion `Sheaf.Paper.EtaleDerivedScalarTensor` supplies
  `Etale.scalarExtension` in the required ordinary module-valued-sheaf presentation;
  `Sheaf.Paper.WitnessCompatibility` supplies `pbcFixedScalarExtension` and the
  specified `pbcComparisonReduction`. Their constructions are the canonical
  derived scalar adjunction, not an arbitrary functor or coefficient map.
- `det-sp-et-proet-adjunction-transfer`: `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`,
  `AdjunctionTransfer.etaleProperty`, `proEtaleProperty`, and `comparison`. The
  theorem about transferred adjoints is not assumed to obtain this node's domain
  results; only its already constructed predicates and restricted comparison are used.
- `lem-asd-finite-etale-twist-line`:
  `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`,
  `Scheme.finite_etale_torsion_twist_line`, and the publicly imported construction
  `Scheme.finiteEtaleTateTwist` from `FiniteEtaleTateTwist`.
- `def-amb-etale-compact-support`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `Etale.rightDerivedLowerShriekOfCompactification`. Its complete signature and
  body were read: `D(openLowerShriek) ⋙ R(lowerStar)`.
- `det-pe-finite-tor-comparison-noetherian`:
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`,
  `ProEtale.finiteTorComparisonNoetherian`. Its small coefficient-site model
  theorem supplies exact Tor preservation/reflection and the finite-Tor equivalence.
  The new theorem states the corresponding ordinary presentation needed by the
  recorded chart adjunctions, without imposing equality of unrelated universes.

Every recorded proof-dependency module is imported without `public` unless already
used in the public interface. The Mathlib leaf for finite type over Noetherian is
`Mathlib.AlgebraicGeometry.Noetherian`. The proof plans reproduce the node's ten
steps: bounded flat models; exact constructible flat open extension; proper fibre
bound and finite-Tor pushforward; arbitrary scalar extension; exact inverse image;
finite twists and signed shifts; comparison equivalence/interval reflection; and
canonical scalar, pullback, root/tensor and shift comparisons.

Edge cases checked before and after writing:

- Empty schemes and zero complexes: no nonemptiness condition is imposed; exact
  functors and extension by zero preserve zero. The compactification need not have
  dense image, which is not required by the given definition.
- Zero coefficient rings are retained: no `Nontrivial` binder. When n=0, N=1 and
  annihilation forces the coefficient ring to be zero, which remains included.
- a=0 uses the actual constant sheaf in `finiteEtaleTateTwist`; no positive-twist
  restriction or chosen trivialization is hidden in the operation.
- Arbitrary b in ℤ includes negative and zero shifts, with actual signed shift
  functors. The proof changes [alpha,beta] to [alpha-b,beta-b].
- Identity u is admitted; canonical inverse-image, tensor and shift comparisons
  are used, including their inherited identity normalization.
- Nonflat coefficient maps, e.g. Z/ell^2 -> Z/ell, are admitted. Finite Tor amplitude
  is tested over B after extension, with a bounded flat B-model; finite projective
  dimension of B over A is neither required nor asserted.
- A single Tor interval for all inputs is never required. The preservation claims
  quantify input by input, and interval comparison quantifies every given [a,b].
- Coefficients inhabit Type (u+1), schemes are `Scheme.{u}`, with the standard small etale and
  small pro-etale sites and their full module categories. No additional equality
  of site object/morphism or localization universes was introduced.

Searches for existing material (2026-10-22):

- `msearch.py ... leanfinder "Etale compact support preserves bounded constructible
  complexes of finite Tor amplitude and etale proetale comparison commutes with
  scalar extension and Tate twists"`: eight hits on etale ring maps, scheme
  morphisms and condensed solidification; no match for the whole node.
- `msearch.py ... loogle "DerivedCategory.torAmplitudeIn, Etale.upperStar,
  ModuleCat.extendScalars"`: zero hits, unknown identifier
  `DerivedCategory.torAmplitudeIn` in Mathlib's search index. The project has its
  own Tor predicate; it was read and reused.
- `msearch.py ... grep "constructibleFiniteTor|torAmplitudeIn|comparison.*Tensor"
  AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch "Etale compact support preserves constructible
  complexes with finite Tor amplitude and coefficient extension commutes with
  proetale comparison"`: eight unrelated ring/scheme etale hits, no full match.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item ID, chart/ctf
  names, `constructibleFiniteTor`, Tor intervals, scalar extension and comparison
  tensor/pullback/shift names found the partial native stability/comparison APIs
  and the recorded adjunction-transfer predicates. They do not state this full
  node. The canonical APIs were reused in the real comparison definitions.
- Exact-name searches for all six new declaration names over both library roots
  found no declaration. No existing notion was copied.

Initial compiler feedback found the distinction between the ring power and the
natural-number power cast, and the finite-ring binder needed by the canonical
flat-preserving comparison API. Both were repaired. The final module was checked
with `scompile.py` in module mode as sandbox and intended library module: clean,
15.9 and 9.0 seconds respectively before the final Mathlib proof import. The dry
run performs the final compile and preflight after that import.

No STATEMENT-DISPUTED issue, statement correction, or defective node was found.

## Second reading by Q15

I reread the node and completed file as a separate clause audit after compilation;
no second agent was started, as required by the dispatch brief. The maintainer's
independent review remains the external review.

This rereading checked the full hypotheses and conclusions listed above against
both signatures. It checked the exact Dctf predicates in the dependency source,
the literal restricted comparison functor, all-module Tor tests on each site,
common N and zero-ring case, the chosen compactification's induced middle setting,
and the order and signs of inverse image, finite Tate tensor and shift.

The canonical comparison body was read again: its three stages descend the actual
scheme pullback comparison, invert the tensor comparison in the required direction,
and invert `commShiftIso` to move comparison across the final shift. The scalar
comparison is exactly the published mate restricted along the finite-Tor inclusion.
Thus the term data fixes the maps and their naturality. The pro-etale Tate
presentation was cross-checked with finite-root site comparison and the existing
comparison-pullback convention for finite pro-etale Tate objects. No remaining
hypothesis or conclusion mismatch was found. Only the cast and finite-ring API
binder corrections described above were needed.
