## Worker report

The module `Sheaf.RingTheory.PseudoCoherentNormalizedAlgebraTower` states
`DerivedCategory.pseudoCoherent_normalizedAlgebraTower`, with its entire proof `sorry`.
It introduces no definitions, new nodes, dependency replacements, or statement correction.
The module docstring identifies the source, and the declaration docstring carries all six
steps of the node's proof, with the same ingredient nodes.

Source read: `literature/stacks-project/more-algebra.tex`,
`lemma-Rlim-pseudo-coherent-gives-complete-pseudo-coherent` (09AV, lines 28378ff.),
including its hypotheses, conclusion and proof; `lemma-Noetherian-pseudo-coherent`
(066E, lines 16517ff.), particularly assertion (2). Also read the preceding 0CQF proof's
identification of the finite-free termwise limit and its reductions. These support the
statement as written: Noetherian finite cohomology replaces pseudo-coherence at the first
level, and no perfectness assumption is present.

Hypotheses and conclusions matched individually:

| Node clause | Lean rendering |
| --- | --- |
| Commutative Noetherian ring C | `{C : Type u} [CommRing C] [IsNoetherianRing C]` |
| Ideal J and C canonically isomorphic to its J-adic completion | `(J : Ideal C) [IsAdicComplete J C]`; Mathlib's predicate includes Hausdorffness, not only precompleteness |
| E_n in D(C/J^n), n positive | `K : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (C ⧸ J ^ (n + 1)))`; `K 0` is the node's E_1 |
| Supplied transition in D(C/J^(n+1)) | `t n : K (n + 1) ⟶ ...mapDerivedCategory.obj (K n)`, where the functor is restriction along `Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1)))` |
| The transition induces a derived reduction isomorphism | `hnorm`: for every target N over the smaller quotient, `a ↦ t n ≫ Res.map a` is bijective |
| Regard the tower as one in D(C) | `f` and `hf`: `f n` is exactly the image of `t n` under restriction to C, followed by the canonical restriction-composition comparisons |
| E is the specified derived limit with its projections | `E`, `p`, `δ`, `hE : IsDerivedLimitTriangle f E p δ`; the level projection is `p ≫ Pi.π _ n` |
| E_1 bounded above | `hbounded`: some integer b satisfies `IsZero (H^i(K 0))` for every i>b |
| Every cohomology module of E_1 finitely generated | `hfinite : ∀ i : ℤ, Module.Finite ... (H^i(K 0))` |
| E pseudo-coherent | First conjunct `IsPseudoCoherent E`, using the dependency's finite-free bounded-above predicate unchanged |
| Projections induce E tensor^L C/J^n ≅ E_n | For any family `L n` left adjoint to exact derived restriction, `∃ e : ∀ n, (L n).obj E ≅ K n`, with `(e n).hom` equal to the adjunct of `p ≫ Pi.π _ n` |
| Compatible with supplied transitions and quotient cocycles | The equation quantified over every `m n` and `h : n ≤ m` compares the units followed by `Res(e m)` and the composite transition `(Functor.ofOpSequence f).map (homOfLE h).op` with the unit followed by `Res(e n)`. `Functor.ofOpSequence` supplies identity and composition laws, including equal indices and all triple-level cocycles |
| Derived J-completeness | The last two conjuncts give `HasProduct` for the restricted reductions and, for every choice of that product, `IsDerivedLimit` of the reduction tower with transition `Res(e(n+1).hom) ≫ f n ≫ Res(e n).inv`, with limit E itself |
| No perfectness assumption | No `IsPerfect`, finite projective dimension, bounded-below, or cohomological-freeness hypothesis occurs |

The universal property in `hnorm` is a logical expansion, not a new definition or a
replacement derived-category object. If T is the left adjoint of exact derived restriction,
and a : T(X) → Y is the adjunct of the transition X → Res(Y), the displayed bijection is
precomposition by a under the adjunction. For every N it is bijective exactly when a is an
isomorphism (Yoneda). Thus it says precisely that this supplied transition exhibits Y as
the derived reduction of X; it is not an arbitrary levelwise isomorphism.

Similarly, the `L` and `adj` quantifiers are INSIDE the conclusion. No existence of a tensor
functor or an adjunction is added as a hypothesis. They name any choice of the actual derived
scalar extension, characterized as the left adjoint of exact derived restriction. Its
existence and identification with derived tensor are the usual derived change-of-rings and
derived-adjunction results cited by this node. There is no independent choice of comparison
maps: the equality to the adjunct fixes them. All targets N and all modules live in
`max u v`, so the normalization test does not become vacuous in a smaller universe.

The cocycle clause is written after restricting to C, but it also determines the required
compatibility before restriction. In detail, put η_n = `(adj n).unit.app E`. The canonical
map from `L m E` to the restriction to C/J^(m+1) of `L n E` is the UNIQUE adjunct of η_n
under `adj m`, using the canonical scalar-restriction comparison. The displayed all-level
equation says that composing this map with the restricted `e n` has the same adjunct as
`e m` followed by the supplied composite transition. The adjunction bijection therefore
gives equality in D(C/J^(m+1)), not merely equality of its restriction to D(C). This does
not assume restriction is faithful on derived morphisms. These canonical maps satisfy the
quotient cocycles by the same uniqueness. The last derived-limit clause uses precisely their
restricted maps, transported through e, rather than an unrelated reduction tower.

Choice and size bookkeeping: the explicit `HasDerivedCategory.{w}` instances are the
localizations required by `def-weil-abstract-derived-category`, for the base ring and every
positive quotient. The hypothesis `HasProduct` is the product in the given Roos triangle;
no finite-product or perfectness restriction is imposed. `f` with its defining equation
only names the supplied restricted transitions; it is not extra mathematical input. The
last product is asserted to exist in the conclusion, so completeness has no additional
product-existence hypothesis. Every variable and universe is bound explicitly, with
`set_option autoImplicit false`; there are no local instances, notation or abbreviations.

Dependency declarations read and used:

- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` (lines 44–56) and its
  interpretation by `AdicCompletion.of_bijective_iff`; this is the exact recorded notion.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (lines 194ff.) and the immediately
  following `isNoetherianRing_iff_ideal_fg`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  and the homology functor API exported by the recorded pseudo-coherence module.
- `Sheaf.CategoryTheory.Triangulated.DerivedLimit`: `CategoryTheory.IsDerivedLimitTriangle`
  and `CategoryTheory.IsDerivedLimit`, both read in full with their docstrings.
- `Sheaf.RingTheory.RingPseudoCoherent`: `DerivedCategory.IsPseudoCoherent`, read in full;
  its witness is a bounded-above finite-free complex, not a perfect complex.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, lines 116–119.
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`: `SheafOfModules.derivedChangeOfRings`;
  the recorded general-site theorem is imported as the node's proof ingredient. It is not
  applied to ModuleCat by pretending the two categories are definitionally equal.
- `Sheaf.RingTheory.PseudoCoherentNilpotentInvariance`:
  `DerivedCategory.isPseudoCoherent_iff_of_surjective_nilpotent_kernel`, including its
  explicit total-left-derived-functor signature and docstring, is imported as a proof
  ingredient, without restating it.

Additional recorded proof modules imported, without `public`:
`Sheaf.Algebra.Category.ModuleCat.RingScalarExtension` (`ModuleCat.ringExtendScalars` and
its adjunction), `Sheaf.Algebra.Homology.KFlatTelescopeClosure`
(`CochainComplex.kFlat_closure`), `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
(`CategoryTheory.preDerivedAdjunctionGeneral`), and
`Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
(`CategoryTheory.Functor.exactFunctor_derivedFunctor`). The levelwise-isomorphism Mathlib
leaf is already imported through pretriangulated categories. The remaining proof nodes
(marked lifting, cohomology criterion, strict tower limit, and derived-limit morphism) have
no recorded Lean module on this base, so no invented imports were added for them.

The canonical scalar-restriction comparison uses the actual declarations
`ModuleCat.restrictScalarsComp'`, `Ideal.Quotient.factor_comp_mk`, and
`Functor.mapDerivedCategoryCompIso` / `Functor.mapDerivedCategoryNatIso` from
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, whose signatures
and docstrings were read. The inverses in `hf` go from successive restriction to direct
restriction. This prevents unconstrained comparison isomorphisms from twisting the tower.

Edge cases checked before writing:

- `J = 0`: all positive quotients are C and normalization makes a constant tower up to the
  supplied isomorphisms. No positive-exponent level is lost by using n+1.
- `J = ⊤`: Hausdorff completeness forces C to be the zero ring; no `Nontrivial` hypothesis
  excludes it. The zero tower and zero object remain admitted.
- A zero first reduction and zero finite-free ranks are allowed.
- Cohomology may extend indefinitely to negative degrees; the bound is only above, and
  `hfinite` is degreewise. No uniform bound on resolution length is imposed.
- For example take a singular Noetherian ring C = k[ε]/(ε²), J = 0, and constant tower k
  in degree zero. Its first level need not be perfect, but all hypotheses still apply.
- Arbitrary integer upper cutoffs, all coefficient characteristics, and equal/triple-level
  quotient indices are included.

Searches actually run for this item:

- `msearch.py ... leanfinder "A normalized derived tower over an adically complete
  Noetherian ring with bounded above finite cohomology is effective and pseudo coherent"`:
  eight hits, all ordinary adic-completion flatness/exactness and related completion facts;
  no matching derived-tower reconstruction theorem.
- `msearch.py ... leansearch "A normalized derived tower over an adically complete
  Noetherian ring reconstructs a pseudo coherent complex"`: UNAVAILABLE, HTTP Internal
  Server Error. This is not recorded as a negative mathematical search result.
- `msearch.py ... loogle "IsAdicComplete, DerivedCategory"`: zero hits.
- `msearch.py ... grep "pseudo.?coherent|[Rr]lim.*[Cc]omplete"`: zero Mathlib hits.
- `rg` for the node id, pseudo-coherent/tower combinations, and derived scalar-extension
  names in the upstream `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no theorem matching this node. The searches found the recorded nilpotent-invariance
  module and upstream small-étale normalized DVR towers; the latter concern a different
  coefficient category and do not state algebraic pseudo-coherent reconstruction.
- Focused `rg` for `restrictScalarsComp`, `mapDerivedCategoryCompIso`,
  `mapDerivedCategoryNatIso`, and quotient-factor APIs located the canonical comparisons
  used above, avoiding any new definition of restriction or derived scalar extension.

No established statement fault or dispute was found. The node's fields other than `lean`
are unchanged.

Validation: every compile uses `scompile.py` on the server, nice 19, two threads, limit
60 seconds per file. Initial elaboration identified missing explicit localization-instance
binders, then ambiguous implicit module universes on relative restriction; both were fixed
by explicit binders and `ModuleCat.restrictScalars.{max u v}`. The subsequent compile
accepted the full statement, with only long-line warnings; these lines were wrapped and
the final clean compile and delivery dry run are recorded below.

Final `scompile.py` result: exit 0, no warnings; the delivered module compiled in 2.0 s.
`deliver2.py NW lem-weil-pbc-pseudocoherent-normalized-algebra-tower --no-push` printed
`OK (dry run)`: the commit compiles and passes preflight except for the independent second
reading, which the second reader must write. Nothing was pushed. This worker has not
written or claimed an independent second reading.

## Second reading by NW

Independent second reader: I opened the sandbox node and the whole Lean module, then
read More on Algebra, lemma-Rlim-pseudo-coherent-gives-complete-pseudo-coherent
(09AV), the preceding lemma-Rlim-pseudo-coherent-gives-pseudo-coherent (0CQF),
and lemma-Noetherian-pseudo-coherent (066E), including their proofs. The source has
no ambient field, characteristic, nonzero-ring, or perfectness assumption. The
Noetherian hypothesis in this node permits replacing pseudo-coherence of the first
reduction by 066E(2). The node has no statement_change, new definition node, or
dependency replacement to review. Its natural statement is unchanged.

My inventory and comparison, with the node and Lean open:

| Object, hypothesis, or conclusion of the node | Lean rendering and verdict |
| --- | --- |
| Commutative Noetherian ring C | `{C : Type u} [CommRing C] [IsNoetherianRing C]`: exact. |
| Ideal J, and completeness for the canonical map to the quotients | `(J : Ideal C) [IsAdicComplete J C]`: exact; includes Hausdorffness. |
| E_n in the derived category of C/J^n for positive n | `K n : DerivedCategory (ModuleCat.{max u v} (C ⧸ J ^ (n + 1)))`: exact reindexing, with `K 0` the first reduction. |
| Supplied transitions in D(C/J^(n+1)) | `t n`, into derived restriction along the quotient factor: exact ring, direction, and category. |
| Those transitions induce derived-reduction isomorphisms | `hnorm`, bijectivity against every `N` of precomposition with `t n` after restriction: exact universal-property form, as justified below. |
| Tower viewed over C | `f` and `hf`: the image of each supplied transition, using the canonical composition and quotient-factor comparisons. No arbitrary comparison is substituted. |
| E is its derived limit, with its projections | `E`, `p`, `δ`, `hE : IsDerivedLimitTriangle f E p δ`, with the stipulated product instance: exactly the recorded Roos-triangle definition. Projections are `p ≫ Pi.π _ n`. |
| First reduction bounded above | `hbounded : ∃ b : ℤ, ∀ i, b < i → IsZero (H^i(K 0))`: exact; no lower bound. |
| Every cohomology module of the first reduction finitely generated | `hfinite : ∀ i : ℤ, Module.Finite ... (H^i(K 0))`: exact, over the first quotient, not over an unrelated ring. |
| E pseudo-coherent | `IsPseudoCoherent E`: the recorded bounded-above finite-free representative predicate, exact. |
| Projections induce all derived-reduction isomorphisms | For every derived scalar-extension adjunction `L n ⊣ Res_n`, `∃ e`, with `(e n).hom` equal to the adjunct of `p ≫ Pi.π _ n`: exact and fixes the maps. |
| Compatibility with supplied transitions and quotient cocycles | The equation for all `m n` and `h : n ≤ m`, using `Functor.ofOpSequence f`: includes adjacent, identity, and arbitrary composite transitions. Exact. |
| Derived J-completeness | The final `HasProduct` and `IsDerivedLimit` clauses exhibit E as the derived limit of its reductions with transported transitions. Exact; product existence for the reduction tower is concluded. |
| No perfectness of the first reduction | No perfectness, bounded-below, Tor-dimension, flatness, or finite-rank cohomology hypothesis: exact. |

I checked the two less direct encodings rather than relying on their names.
For normalization, let T be derived extension along the successive quotient and
let a : T(K(n+1)) → K(n) be the adjunct of `t n`. The `hnorm` map corresponds,
under the derived adjunction, to precomposition by a for every N. Yoneda says
that these maps are all bijective precisely when a is invertible. It is therefore
the normalization of this supplied transition, not merely an unrelated isomorphism.
The test objects range over the same module universe as K, so none are lost.

For compatibility put η_n = `(adj n).unit.app E`. The canonical map from L_m E
to the restriction of L_n E is the adjunct of η_n under adj_m, after the
canonical restriction-composition comparison. Composing it with the restricted
isomorphism e_n and composing e_m with the supplied transition have equal
adjuncts exactly by the displayed all-level equation. Thus the equation implies
compatibility already over the larger quotient; it does not rely on faithfulness
of restriction on derived morphisms. Uniqueness of adjuncts gives the quotient
cocycles. Consequently the conjugated transitions in the completeness clause
are the canonical reduction transitions transported through these isomorphisms.
Quantifying L and adj inside the conclusion expresses any choice of derived
extension, unique as a left adjoint; it imposes no new hypothesis on the tower.

Dependency checks: I opened every stmt_deps node and its recorded declaration.
`IsAdicComplete` extends `IsHausdorff` and `IsPrecomplete`, and
`AdicCompletion.of_bijective_iff` identifies it with the node's canonical-map
condition. `isNoetherianRing_iff_ideal_fg` and `Module.Finite.fg_top` give precisely
the ring and module finiteness notions. Mathlib `DerivedCategory` and
`HasDerivedCategory` supply the specified localization, not a bounded derived
category. In RingPseudoCoherent, `IsPseudoCoherent` requires a complex strictly
bounded above, degreewise free and finite, and an isomorphism to E. In DerivedLimit,
`IsDerivedLimitTriangle` is distinguishedness of the triangle whose middle map is
`1 - towerProductShift f`; `IsDerivedLimit` existentially quantifies its outer maps.
I also read DerivedChangeOfRings and PseudoCoherentNilpotentInvariance. The former
is the general sheaf theorem, used as a proof ingredient via the one-object site;
it is not used as though its categories were definitionally ModuleCat. The latter
uses actual total left derived extension of scalars with a universal counit.
No dependency module is newly delivered or needs replacement. The signatures of
`restrictScalarsComp'`, `mapDerivedCategoryCompIso`, and
`mapDerivedCategoryNatIso` confirm the inverse directions used in hf.

Edge cases: J=0 admits constant normalized towers over C. J=top forces the
complete Hausdorff ring to be the zero ring, which is admitted. Zero objects,
zero cohomology, and rank-zero free terms are admitted. The index n=0 is the
positive first quotient; no positive level is omitted, and the exponent-zero
quotient is not required by the source. There is no empty index family: this is
the fixed countable positive tower. Empty schemes are inapplicable. Arbitrary
integer upper bounds and unbounded negative cohomology are allowed. All
characteristics are included. The ring universe u, module universe max u v,
and localization morphism universe w are explicitly bound; localization and
product instances describe the chosen categories and Roos triangle. The singular
ring k[ε]/(ε²), J=0, and constant residue-field complex illustrates that the
statement admits a nonperfect first reduction.

Independent searches, with different queries from the first worker:

- LeanFinder: `adic quotient compatible complexes inverse limit finite free bounded
  above derived category` returned eight results on local cohomology and derived
  truncation representatives; none is the effectivity theorem.
- Loogle: `IsAdicComplete, Module.Finite` returned zero results.
- msearch grep: `normalizedAlgebraTower|pseudoCoherent.*[Ll]imit|[Ll]imit.*pseudoCoherent`
  returned zero results.
- Direct rg in Mathlib, upstream WeilConjectures, and the project's lean/Sheaf for
  `pseudoCoherent_normalized`, pseudo-coherent/tower-or-limit in both orders, and
  `Rlim-pseudo` found no matching existing theorem. Searches for the canonical
  scalar-restriction comparison APIs found the declarations read above.

No mismatch found; no Lean or node edits were warranted. The sole theorem has
whole proof `sorry`; there are no definitions, hollow data, private notions,
local notation, or local instances in this module. The source and blueprint tags
are present in both docstrings. The declaration docstring follows all six proof
steps, including marked lifts, compatible bases, the strict tower limit, the
projection-adjunction calculation, and cocycles/completeness. Every Lean line
has at most 100 characters, and autoImplicit is explicitly false.

Second-reader validation: scompile.py completed with exit 0 and no warnings;
the delivered module compiled in 2.3 seconds (nice 19, two threads, 60-second
limit per file). Its side-only dependency overlay also compiled cleanly.
A direct string comparison confirmed that lean.statement is verbatim the complete
theorem signature in the file. No variable or universe is left unbound.
The second-reader deliver2.py --no-push check printed OK: the complete delivery
passes preflight and compiles. The statement and definitions remain unchanged.
