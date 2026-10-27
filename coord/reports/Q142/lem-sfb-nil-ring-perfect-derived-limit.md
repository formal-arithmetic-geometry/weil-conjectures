## Worker report

The module `Sheaf.RingTheory.NilRingPerfectDerivedLimit` states
`DerivedCategory.nilRingPerfectDerivedLimit`, with `sorry` as its entire proof.
Its four helper definitions construct the restriction compositor, the restricted
tower transition, the projection adjunct, and the scalar-extension associator.
Their data contain no postponed proofs or choices. All five declarations belong
to this node, and carry its source and blueprint docstrings.

Source read: `literature/stacks-project/more-algebra.tex`,
`lemma-Rlim-perfect-gives-perfect` (Tag 0CQG), lines 28401 onwards, including the
proof. This delivery states its all-perfect branch, plus the node's formal
naturality and transition identities. No statement correction is needed.

Hypothesis and clause correspondence:

- The size convention is expressed by explicit universes `u w`: the commutative
  rings and modules have universe `u`, and `HasDerivedCategory.{w}` has an
  independent localization universe. No identification `w = u` is imposed.
- The inverse sequence is `R : ℕ → Type u`, with `∀ n, CommRing (R n)` and
  `v : ∀ n, R (n + 1) →+* R n`. Index `0` denotes the source's index `1`.
- Surjectivity is `hsurj : ∀ n, Function.Surjective (v n)`.
- Locally nilpotent kernels are exactly
  `hnil : ∀ n (x : R (n + 1)), x ∈ RingHom.ker (v n) → IsNilpotent x`.
  This is elementwise nilpotence, with no common exponent or nilpotent-ideal
  hypothesis.
- The ring limit is the commutative ring `A`, its homomorphisms `q n`, the
  compatibility `hq : q n = (v n).comp (q (n + 1))`, and `hring`: every compatible
  tuple has a unique antecedent in `A`. This characterizes the inverse-limit ring
  with its projections, independently of a chosen construction or presentation.
- `K n : DerivedCategory (ModuleCat.{u} (R n))` is the level object.
  `hperfect : ∀ n, IsPerfectRingComplex (K n)` uses the dependency's exact bounded
  finite-projective definition, rather than a new perfectness predicate.
- `t n` has source `K (n + 1)` and target the exact derived restriction of `K n`.
  `B n` with `badj n` presents derived extension along `v n` as the left adjoint
  to that exact restriction. `hbase` says its adjunct of `t n` is invertible.
- `L n` with `adj n` similarly presents extension along `q n`. These are
  presentations of the specified scalar extension, not unconstrained functors
  or additional flatness hypotheses: the adjunction determines each left
  adjoint up to its unique unit-compatible isomorphism. In particular the
  K-flat derived extension of the recorded change-of-rings dependency is such
  a presentation. The same interpretation is used in the existing
  `Sheaf.RingTheory.RlimPerfectComplete` interface. Quantifying over all
  presentations makes the statement independent of that choice and does not
  replace any canonical map by arbitrary data.
- The restricted level is
  `(ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (K n)`.
  `nilRingRestrictionComp` is constructed by exact derived factorization of
  `ModuleCat.restrictScalarsComp'`, whose underived maps are identity on
  elements. `nilRingTowerTransition` first restricts `t n`, then applies the
  inverse of this compositor. These are the node's tower in `D(A)`.
- `HasProduct` supplies precisely the product occurring in the chosen Roos
  triangle. Its existence is part of the meaning of the input derived limit;
  no special model or functorial choice of limit is imposed.
- `T`, `p`, `δ`, and `hlim : IsDerivedLimitTriangle ... T p δ` specify any
  derived limit together with the node's distinguished Roos triangle.
  The definition uses the existing `1-s` convention, not its negative.
- The first conclusion is exactly `IsPerfectRingComplex T`.
- `nilRingLimitReduction q L adj K T p n` is defined as
  `((adj n).homEquiv T (K n)).symm (p ≫ Pi.π _ n)`.
  The second conclusion says this particular morphism is an isomorphism for
  every `n`; it does not assert merely the existence of an isomorphism.
- The third conclusion is the transition identity. The direct reduction equals
  `nilRingExtensionAssoc...hom.app T`, followed by `B n` of the next reduction,
  followed by the adjunct of `t n`. The associator is constructed using
  `Adjunction.leftAdjointUniq` between the direct adjunction and the composite
  adjunction transported along the canonical restriction compositor. It is
  therefore the canonical scalar-extension associativity identification.
- The final conclusion is naturality. It quantifies over a second tower `K',t'`
  with levelwise perfectness, invertible transition adjuncts, and its own
  specified `T',p',δ'` Roos triangle. The equation for `φ` is the typed version
  of compatibility of the two towers: `t n` followed by restricted `φ n` equals
  `φ (n+1)` followed by `t' n`. The equation for `f : T ⟶ T'` is exactly
  compatibility with all projections. The conclusion says
  `(L n).map f ≫ rho'_n = rho_n ≫ φ n`, which is the node's naturality equation
  in Lean's left-to-right composition notation. There is no assumption that
  `f` is a functorially chosen morphism of derived limits.
- Neither `A_n = A/I^n`, Noetherianity, flatness of any ring map, nonzero rings,
  nonzero complexes, nor a common exponent killing the kernels occurs.

Dependency declarations read and used:

- `def-weil-size-convention`: its recorded metatheoretic convention, implemented
  by explicit universes and localization instances; no declaration is required.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`; exact scalar restriction uses
  `Functor.mapDerivedCategory` and its canonical factorization comparisons.
- `def-pc-perfect-ring-complex`:
  `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`,
  `DerivedCategory.IsPerfectRingComplex`, read in full. It requires bounded
  terms, `Module.Projective`, `Module.Finite`, and a derived isomorphism.
- `def-weil-derived-limit`:
  `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`,
  `CategoryTheory.IsDerivedLimitTriangle`. Its distinguished triangle uses
  `CategoryTheory.towerTransitionEndomorphism`, read in its source module.
- `def-pc-module-kflat-complex`:
  `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`,
  `CategoryTheory.MorphismProperty.kFlat`, publicly available through the
  change-of-rings dependency. No replacement predicate is defined.
- `lem-pur-derived-change-of-rings`:
  `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`,
  `ModuleCat.OrdinaryDerivedChangeOfRings`,
  `ModuleCat.nonempty_ordinaryDerivedChangeOfRings`,
  `ModuleCat.ordinaryDerivedChangeOfRings`, and
  `ModuleCat.ordinaryDerivedExtendScalars`. Read the universal cochain counit,
  K-flat computation clause, and normalization clauses in full. This is the
  ordinary-module presentation of the dependency retained by public import.
- `lem-pur-sheaf-ring-derived-coefficient-adjunction`:
  `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`,
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`, read including the
  normalization and transpose clauses. Its universal Hom-bijection notion is
  expressed here by `Adjunction.homEquiv` on ordinary module categories.
  This original dependency remains publicly imported. No second derived
  extension construction or specialized copy of the sheaf theorem is made.

The following recorded proof dependencies are plain imports:
`WeilConjectures.Algebra.Homology.BoundedFlatKFlat`,
`WeilConjectures.RingTheory.PseudoCoherentBoundedFiniteFreeModel`, and
`Sheaf.RingTheory.PseudoCoherentMaximalFibrePerfect`. The pseudo-coherent ring
predicate is available through those imports. The triangulated-category
interface is already available through the derived-limit dependency. The two
new nil-ring proof lemmas, `lem-sfb-nil-ring-pseudocoherent-derived-limit` and
`lem-sfb-nil-ring-tower-limit-henselian`, have no recorded Lean declaration in
the read checkout; they are not imported. They are proof dependencies, not
missing notions required to type this statement. Their proof roles are
preserved explicitly in the theorem docstring.

Edge cases checked by reading the statement and definitions:

- The nonempty sequential index includes its initial level (Lean index `0`),
  with no accidental omission of that level or of a transition.
- The zero complex admits a bounded finite-projective model; no nonzero object
  or positive rank hypothesis excludes it.
- The zero ring is permitted by `CommRing`; nil-kernel surjections involving
  it remain subject only to the actual stated hypotheses.
- Identity transitions and zero kernels are allowed, with no strictness,
  nontriviality, positive nilpotence bound, or decreasing-ideal requirement.
- Elementwise nilpotent kernels which are not nilpotent ideals are allowed.
- The second Roos triangle and its compatible map are arbitrary; the statement
  assumes no canonical/functorial choice and no uniqueness of the map.
- Separate localization and coefficient universes remain explicit throughout,
  including in the restriction compositor and adjunction associator.

Searches before writing (no exact match):

- `msearch.py`, LeanFinder: "Perfect derived inverse limit of compatible perfect
  complexes over surjective rings with nil kernels"; eight hits concerned ring
  perfection, perfectoid rings, and ordinary adic lifting, not perfect complexes.
- `msearch.py`, Loogle: `DerivedCategory, "limit"`; zero hits.
- `msearch.py`, grep of Mathlib Algebra: `perfect.*limit|limit.*perfect`; zero hits.
- `msearch.py`, LeanSearch: "Perfect complexes over surjective ring towers with
  nil kernels are reconstructed by derived inverse limits"; eight hits concerned
  ring perfection or ordinary profinite limits, not this derived assertion.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf`, concepts including
  `nil.*[Tt]ower`, `[Nn]il.*[Ll]imit`, and perfect inverse/derived limits. The
  closest prior theorem was `DerivedCategory.rlim_perfect_complete` in
  `Sheaf.RingTheory.RlimPerfectComplete`; it requires an adic-power quotient
  presentation and thus does not state this general nil-kernel result.
- `rg` of the upstream tree for the exact item id: no match. Exact-name search
  for all five proposed declarations in Mathlib, upstream, the Sheaf tree and
  `dag/lean_names_upstream.json`: no match.
- API searches and full source reads found exact restriction of scalars,
  `ModuleCat.restrictScalarsComp'`, its derived factorization,
  `Adjunction.leftAdjointUniq`, the arbitrary-localization-universe perfect
  predicate, and the Roos triangle predicate, so no new notion/node is needed.

Validation: the prescribed `scompile.py Q142
lem-sfb-nil-ring-perfect-derived-limit` compiled the delivered file both as a
sandbox module and by its library module name, without errors or warnings.
The theorem's only proof is `sorry`. All four definitions are fully constructed.
No existing node field changes except the item's `lean` record.

## Second reading by Q142

The dispatcher forbids starting another agent. This section records a fresh
second pass by the same worker; independent delivery review is the maintainer's.
I reopened the node and the complete file after the clean server compile.

I checked that `hsurj`, `hnil`, `hq`, and `hring` say surjective ring transitions,
elementwise nil kernels, and exactly the inverse-limit ring, rather than an adic
special case. I unfolded `IsPerfectRingComplex` to check both boundedness clauses
and finite projectivity. I checked that `hbase` transposes the given `t`, and
that the target of `nilRingTowerTransition` uses the inverse restriction
compositor, with the correct direction. I unfolded the recorded
`IsDerivedLimitTriangle` to verify the product, `p`, `1-s`, and `δ` match the
node. I checked that the actual `p ≫ Pi.π` is transposed in every reduction.
The transition identity has the correct direction for the direct-to-iterated
extension associator and ends in the adjunct of `t n`. The naturality clause
retains both full towers and both chosen triangles, the restricted level-map
compatibility, and precisely the assumed projection condition on an arbitrary
`f`. Both equations use the same adjunction presentations as the isomorphism
clauses. No assumptions or conclusion clauses were missing, and this second
pass required no statement change. No unresolved statement dispute was found.
