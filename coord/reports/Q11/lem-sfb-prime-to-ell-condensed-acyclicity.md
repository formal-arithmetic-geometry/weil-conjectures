## Worker report

This stage-2 delivery states `Profinite.CondensedAction.prime_to_ell_condensed_acyclicity`
in `Sheaf.CategoryTheory.PrimeToEllCondensedAcyclicity`. Its proof is `sorry`.
The module supplies three fully defined helpers belonging to the same assertion:
`scalarRing` bundles the recorded continuous-map ring object, `trivialDerivedAugmentation`
constructs the canonical arrow using any equivariant injective resolution, and
`ScalarAcyclic` states invertibility in the ordinary unbounded derived category.
There are no new independent notions or dependency repairs.

The item's TeX, proof, proof_deps, split status, and N5 maintainer review are unchanged.
The previous attempt's refusal concerned stage-1 splitting; this delivery performs no
split. The additional statement dependency `def-sfb-condensed-equivariant-bar-data` is
already landed and owns the exact action-category/derived-resolution interfaces used here.

Hypotheses and clauses, in order:

* A prime ell is `(ell : ℕ) [Fact ell.Prime]`.
* The fixed norm-topological algebraic closure is `(Ω : Type u) [NormedField Ω]
  [NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]`. NormedAlgebra extends the
  base algebra structure and makes the norm extend the ell-adic norm (Mathlib's
  `norm_algebraMap'`). There is no `CompleteSpace Ω` assumption.
* A finite intermediate field is `(E : IntermediateField ℚ_[ell] Ω)
  [FiniteDimensional ℚ_[ell] E]`. Its norm and topology are inherited from Ω by
  Mathlib's SubfieldClass instances, so this is the source's extended norm topology.
* Both scalar choices are the two conjuncts `ScalarAcyclic E K ∧ ScalarAcyclic Ω K`.
* All continuous sections are precisely `continuousMapRingObjOfUniverse.{u,u} F`,
  with its recorded `continuousMapRingObjOfUniverseMonObj` and commutativity proof.
  `scalarRing` only bundles these existing data. Its sections are universe lifts of
  `C(S,F)`; restrictions and ring operations are the existing pointwise ones.
* The small coherent profinite-site convention is `Profinite.{u}` with
  `coherentTopology`, abelian coefficients in `u+1`, and standard unbounded
  localizations in `u+2`. All carriers are placed in a common ambient universe
  containing the site and coefficients; this imposes no cardinal bound on them.
* Profinite K is the explicit group, topology, topological-group, compact,
  Hausdorff, and totally-disconnected binders on `(K : Type u)`.
* Every finite continuous quotient has prime-to-ell order: `hK` quantifies over
  every finite discrete group `Q : Type u`, every continuous homomorphism
  `q : K →ₜ* Q`, and its surjectivity, and concludes `Nat.Coprime (Nat.card Q) ell`.
  Every finite quotient is represented in this universe, and every such
  surjective continuous homomorphism is a finite continuous quotient.
* Ordinary internal modules and their internal condensed K-action are the recorded
  `CondensedBar.Modules` and `CondensedBar.Equivariant`, hence exactly
  `Profinite.CondensedAction.Modules` and `ActionModule`, not topological-module or
  abstract-group representation categories.
* The coefficient object is `Mod.regular (scalarRing F).X`; its action is
  `(trivial (R := (scalarRing F).toMon) (P := K)).obj ...`.
* `ScalarAcyclic` existentially supplies the abelian and Grothendieck structures
  needed to form ordinary right derived invariants and the normalized `Invariants`
  datum V. These are conclusions expressing existence, not extra assumptions.
  The abelian datum preserves the already fixed equivariant-map additive structure.
* The augmentation's source is `Q.obj (extend ((CochainComplex.single₀ _).obj M))`,
  exactly the module in cochain degree zero. Its target is the ordinary
  `V.functor.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj
  (trivial.obj M))`, exactly RΓ applied to the trivial degree-zero object.
* The map is fully constructed: apply `single₀` to `V.adjunction.unit.app M`,
  identify `single₀ (Γ(trivial M))` with `Γ(single₀ (trivial M))` via the inverse
  of `HomologicalComplex.singleMapHomologicalComplex`, then apply Γ to `I.ι`,
  extend by zero, localize, and compose with `(resolutionComparison V I).inv`.
  The normalized transpose law makes the first factor the identity on invariant
  sections: the transpose of the identity followed by the invariant inclusion
  equals that identity. Thus the map uses Γ(C_F)=C_F and the actual inclusion
  into a resolution, without an arbitrary map or a chosen bar isomorphism.
* `IsIso (trivialDerivedAugmentation V (Mod.regular ...) I)` is the conclusion
  for every equivariant injective resolution I. Independence is encoded by using
  every resolution and the existing canonical ordinary derived comparison.
* No completion, solidification, finite-subextension-valued replacement, or
  restriction to locally constant functions occurs anywhere in the statement.

Dependency declarations read and used:

* `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingObjOfUniverse`, its `MonObj` construction, and
  `Profinite.isCommMonObj_continuousMapRingObjOfUniverse`. Their full definitions
  and docstrings fix the lifted all-continuous sections and tensor ring structure.
* `Sheaf.CategoryTheory.CondensedActionModule` (publicly exported by bar data):
  `Modules`, `ActionModule`, `trivial`, `Invariants` in `Profinite.CondensedAction`.
  The full `Invariants` signature was checked: additive functor, inclusion,
  sectionwise injectivity and fixed image, and both transpose normalizations.
* `Sheaf.CategoryTheory.CondensedEquivariantBarData`:
  `CategoryTheory.CondensedBar.Ring`, `Modules`, `Equivariant`, `ActionAbelian`,
  `Invariants`, `extend`, and `resolutionComparison`. The latter is explicitly
  ordinary total right derivation followed by applying invariants to an injective
  resolution, with the universal right-derived unit inverted on that resolution.
* `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  the recorded `sk-def-sfb-derived-categories` convention module is publicly imported.
  Its universal unbounded right-derived interface was read. For these Grothendieck
  categories the bar interface uses the existing upstream `Functor.rightDerivedFunctor`
  and its normalized injective-resolution comparison; these represent the same
  universal derived functor, as the dependency's lean.note explicitly explains.
* `def-weil-size-convention` has a metatheoretic convention record, not a declaration.
  It is rendered by the explicit universes and standard localization structures above.

Proof imports: `Sheaf.CategoryTheory.CondensedDerivedInvariantBar` and
`WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation`. The analytic proof
nodes `lem-sfb-normed-scalar-profinite-hom-acyclic` and
`lem-sfb-prime-to-ell-cochain-finite-quotient-descent` currently have no Lean modules,
so there is no module to import for either. Their statements and the six proof steps
are retained in the theorem docstring. No proof dependency is removed or restated.
The source paragraph (3) was opened in the current main-20261015 blueprint: it
provides the direct-image geometric context; this scalar calculation is honestly
recorded by the node as agent-formulated with an exact reference WANTED.

Edge cases checked before writing:

* K=1 satisfies the quotient-order hypothesis. Its invariant inclusion is the identity;
  the displayed arrow is the identity under the canonical derived comparisons, for
  every resolution, rather than only for a specially chosen resolution.
* For finite K of prime-to-ell order, the assertion is ordinary finite averaging and
  uses the same section module C(S,F) at every profinite S.
* E equal to the base field is included by the bottom intermediate field.
* Positive, zero, and negative cohomological degrees are all covered by the derived
  `IsIso`, with no positive-degree-only weakening. The zero-degree source is explicit.
* The empty profinite test set remains an object of the site and uses all continuous
  maps from it; no nonemptiness condition was imposed on test objects.
* Noncomplete Ω is allowed. The norm-topological field is never replaced by its
  completion. The proof's finite sums do not assert existence of an infinite integral.
* K=Z_ell is excluded: its finite quotient Z/ell has order ell. Thus hK is meaningful.
* Every datum needed to type a derived category is existentially supplied or defined
  by `HasDerivedCategory.standard`; no extra analytic or abelianness hypothesis was
  silently appended to the theorem.

Searches for an existing declaration (all through the prescribed tooling or named
read-only source directories):

* msearch.py leanfinder: "Derived invariants of a pro-prime-to-ell profinite group
  with trivial all-continuous condensed ell-adic scalar coefficients are isomorphic
  to the coefficient module in degree zero" returned 8 hits, including
  `ContinuousCohomology.continuousCohomologyZeroIso`, discrete condensed comparisons,
  `groupCohomology.H0IsoOfIsTrivial`, and standard representation resolutions. None
  states ordinary internal condensed derived acyclicity in this coefficient category.
* msearch.py loogle: `"Condensed", "invariants"` returned 0 hits.
* msearch.py leansearch: "The canonical augmentation of trivial condensed ell-adic
  scalars to derived invariants of a pro-prime-to-ell group is an isomorphism" returned
  8 hits: representation invariants/degree-zero cohomology, discrete condensed
  characterizations and solidification. None is this ordinary derived assertion.
* msearch.py grep: `(Condensed|profinite).*(invariant|acyclic)|
  (invariant|acyclic).*(Condensed|profinite)` returned 5 hits, all in
  Mathlib/RingTheory/Invariant/Profinite.lean, concerning algebraic integrality.
* Read-only rg in WeilConjectures and Sheaf for the node id and for condensed
  prime-to-ell/acyclic patterns found no existing statement. Reading the condensed
  action/bar modules found the reusable invariant-resolution interface instead.
* Declaration-name searches in WeilConjectures, Sheaf, and dag/lean_names_upstream.json
  found no full-name collision for the four declarations in this delivery. Other
  namespaces have unrelated `scalarRing` declarations, which do not collide.

No STATEMENT-DISPUTED flag is added: the source and node retain the analytic inputs as
WANTED, and no counterexample was established. This is a statement delivery only.

Validation: the complete delivered module was compiled with scompile.py. An initial
namespace collision between `CondensedAction.Equivariant` (a map predicate) and
`CondensedBar.Equivariant` (the action category) was repaired by fully qualifying the
category. The next compile had only two long-line warnings; these were shortened.
No live Lean source or stage-1 split was modified. The prescribed dry run and delivery
are performed after this report is written.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
