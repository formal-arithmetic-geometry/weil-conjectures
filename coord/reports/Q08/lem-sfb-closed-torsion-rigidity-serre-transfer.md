## Worker report

States `AlgebraicGeometry.ProEtale.CondensedRing.closed_torsion_rigidity_serre_transfer`
in `Sheaf.Paper.ClosedTorsionRigiditySerreTransfer`. The sole theorem has proof `sorry`.
The two helper definitions have actual data: restriction of sections by the module
adjunction unit and presheaf restriction, then its canonical `Functor.rightDerivedPullback`.
No node fields except `lean` change. No new nodes, dependency repairs, or statement corrections.

Clause-by-clause comparison:

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`. The fixed algebraic closure is `PadicAlgCl ℓ`.
  A finite subextension is `PadicAlgCl.FiniteIntermediateField ℓ` inside that closure.
- The six coefficient families, with their specified topologies, are precisely the six
  disjuncts of `hΛ`. The first quantifies a finite commutative discrete topological ring
  with `(∃ n, ∀ a, (ℓ ^ n) • a = 0)`. The remaining cases are `continuousMapRingObj`
  of `ℤ_[ℓ]`, `ℚ_[ℓ]`, a finite intermediate field, `PadicAlgCl ℓ`, and
  `padicIntegersRingObj ℓ E`. The latter is the valuation subring with its induced topology.
  `Mon.mk` isomorphisms identify the specified condensed rings, preserving their ring
  structures. These are coordinate-free representations of exactly those coefficients.
  In particular the last disjunct is all continuous maps into the algebraic closure;
  it is NOT `Profinite.padicAlgClRingObj`. The dependency's present
  `IsLocalizingAdmissibleCoefficient` includes that extra coefficient as well, so its
  raw predicate would strengthen this item's conclusion. The six clauses are therefore
  spelled out using the dependency's same actual coefficient constructions, as in the
  accepted sibling `TorsionCdTopologicalSerreTransfer`.
- A commutative condensed ring is the section parameter `Λ : Sheaf
  (coherentTopology Profinite.{u}) Ab.{u + 1}` with `[MonObj Λ] [IsCommMonObj Λ]`.
  `condensedRingObj Λ T` and `condensedRingObj Λ T₀` are the specified point-pullbacks.
- The schemes are `{T₀ T : Scheme.{u}}`. Both have `CompactSpace` and
  `QuasiSeparatedSpace` instances: precisely qcqs. The morphism is `(t : T₀ ⟶ T)`
  with `[IsClosedImmersion t]`. No stronger geometric assumption is made.
- Small sites and size: `T.smallEtaleTopology` and `Scheme.ProEt.topology T` are the
  recorded sites. Scheme objects have universe `u`; the small sites have object universe
  `u+1` and morphism universe `u`; abelian groups have universe `u+1`. The closure uses
  `.weakSerreCoproductClosure.{u + 1}`, exactly the fixed small indexing universe.
- Every torsion abelian sheaf is quantified in `ht` by `(F : Sheaf
  T.smallEtaleTopology Ab.{u + 1})` and `Scheme.IsTorsionAbelianSheaf F`.
  Reading that definition confirms local torsion: it is the colimit of all positive-integer
  torsion kernels, with no global annihilator. All nonnegative integer degrees are rendered
  by `∀ q : ℕ`; this is exactly the degrees `q ≥ 0` in the node.
- Bijective actual restriction is `Function.Bijective (Etale.cohomologyMap t F q)`.
  This recorded canonical map acts on `Sheaf.H`, the existing sheaf cohomology construction,
  and uses exact étale pullback and the canonical constant-sheaf comparison. It is the
  sheaf-in-degree-zero form of ordinary right-derived global sections, not an arbitrary map.
- Membership in the hull is `hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
  (IsConstantModelConstructible Λ T) M`. The imported definition is the intersection
  over all replete properties containing these generators and closed under kernels,
  cokernels, extensions, and every small coproduct. It contains zero from the empty
  coproduct. Mathlib's `IsClosedUnderExtensions` explicitly takes only the two end
  memberships to give middle membership in any short exact sequence. Thus it does not
  silently require a middle-term membership or a lifting of extensions to presentations.
- `M` is an internal module over the original point-pulled-back ring, with no completion
  or finite-type restriction. `DerivedCategory.singleFunctor _ 0` places it in degree zero.
- The conclusion is `IsIso ((torsionRigidityDerivedRestriction Λ t).app
  ((DerivedCategory.singleFunctor _ 0).obj M))`, in the ordinary unbounded
  `DerivedCategory Ab.{u + 1}`. The helper target is exact `upperStar Λ t` acting
  termwise on the derived category, followed by target ordinary derived global sections.
  Exactness identifies this target with derived sections of `(t^* M)[0]`.
  It asserts invertibility of the actual canonical arrow, not existence of an unrelated
  isomorphism and not only degreewise equivalences.
- No henselianity, properness, finite presentation, Noetherianity, invertibility of ell,
  module completeness, or finite-subextension-valued convention is introduced.

Dependency declarations read and used:

- `Sheaf.Paper.LocalizingAdmissibleCoefficients`: coefficient convention and the concrete
  `Profinite.continuousMapRingObj` / `Profinite.padicIntegersRingObj` models. The enlarged
  coefficient predicate itself cannot render precisely this item's six cases, as above.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `Scheme.ProEt.topology`.
- `def-weil-pbc-scheme-conventions` and `def-weil-size-convention` are convention-only
  records, with no declaration; their topology and universe conventions are explicit above.
- `WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf`:
  `Scheme.IsTorsionAbelianSheaf`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: `Etale.cohomology`, read for
  the ordinary derived-section convention. The hypothesis uses the sheaf cohomology version
  through the next dependency, with no second cohomology definition.
- `Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback`: publicly imports
  `Etale.cohomologyMap` from `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`;
  the recorded `Etale.abelianDerivedCohomologyPullback` handles the derived version.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: public ordinary module-derived framework;
  the same exact `CondensedRing.upperStar` and general `Functor.rightDerivedFunctor` are used.
- `Sheaf.Paper.CondensedConstantConstructibility`: `IsConstantModelConstructible` with
  its finite scalar presentations chosen on the point before pullback. No weaker arbitrary
  locally finitely presented model is substituted.
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`: `condensedModuleSections`, exactly
  action-forgetting evaluation at the final object; its existing total right derived functor
  computes both sides.
- `WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure`:
  `ObjectProperty.weakSerreCoproductClosure`, matching the inline hull definition exactly.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`:
  `Functor.rightDerivedPullback`, with its K-injective normalization read in the source.

The section-map helper uses the module unit followed by the actual map from `id_T₀` to
`T₀ ×_T T`. This is the specialization of the already implemented general evaluation
construction `closedFibreModuleDerivedRestriction` in the downstream
`ProperWContractibleClosedFibreRigidity` module. Importing that module here would close
an import cycle: that theorem's proof depends on this item. This module therefore builds
only the canonical final-object specialization using the shared adjunction and generic
derived-descent API; it introduces no copy of the general evaluation interface and no
arbitrary map or choice. Its helper docstrings and lean.declarations are owned by this node.

Every already stated proof dependency is imported, publicly if also needed in the
signature, otherwise by a plain proof import. The following two proof dependencies have
no recorded Lean module yet and therefore cannot be imported:
`lem-sfb-qcqs-finite-complex-heart-filtered-closure` and
`lem-sfb-supported-three-term-scalar-rigidity`. They are retained unchanged in the DAG
and in the eight-step natural-language theorem proof. Neither is needed to type the statement.

Edge cases checked: `t = id` is permitted; both empty schemes are permitted, with the
zero module category. An empty source with nonempty target cannot satisfy the assumed
restriction in degree zero for all torsion sheaves; no artificial nonempty hypothesis is
added. The zero ring and zero module are allowed; exponent zero forces the finite ring
case to be the zero ring and is included. Ell is any prime, including the residue
characteristic. There is no restriction to bounded torsion. Empty coproducts give zero,
and extensions require only both ends. Independent scheme-site object and morphism
universes are retained. All-continuous algebraic closure coefficients are retained.

Searches made (2026-10-23 UTC; msearch.py results retained in searches.jsonl):

- LeanFinder: `closed immersion torsion etale cohomology rigidity extends to weak Serre
  coproduct closure of constructible condensed modules`: eight unrelated condensed/solid
  module and Grothendieck/AB4/AB5 results; no theorem match.
- Loogle: `CategoryTheory.ObjectProperty.weakSerreCoproductClosure,
  AlgebraicGeometry.Etale.cohomologyMap`: no hits, unknown first identifier in Mathlib.
- Mathlib grep via msearch.py: `weakSerreCoproductClosure|closed.*torsion.*rigidity`
  in CategoryTheory: zero hits.
- LeanSearch: `weak Serre subcategory coproduct closure`: eight results, mostly the
  ordinary Serre class API; that API imposes closure under all subobjects and quotients
  and is not the weak hull. No exact theorem found.
- rg of WeilConjectures and Sheaf for the item id: only the downstream proper closed-fibre
  theorem docstring. Focused conceptual searches found the exact existing upstream
  `weakSerreCoproductClosure`, the accepted six-case sibling coefficient convention,
  and the downstream general evaluation helper. No existing statement matches this item.
- DAG conceptual grep found hull-using sibling statements but no separate missing
  definition node. Every notion already exists; no new definition node is needed.

Node/source caveat: the node explicitly says its full coefficient-transfer source is
WANTED; the latest blueprint paragraph supplies the motivation, not an independent
proof of this auxiliary obligation. This caveat is retained in both module and theorem
docstrings. No statement is corrected or weakened, and no counterexample was found.

Validation: scompile.py compiled this module both as a sandbox module and under its
library module path, against the published live build, in 7.2 s and 6.4 s. Both passed
with no error and no warnings. Only the single theorem proof is postponed.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
