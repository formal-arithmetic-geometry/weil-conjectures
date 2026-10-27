## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeMPseudoCoherenceDerivedSections` states
`AlgebraicGeometry.Scheme.relative_mPseudoCoherence_derivedSections_tfae` with `sorry`.
There are no new definitions, helper theorems, dependency modules, or statement corrections.
Only the item's `lean` field changes.

Source read: `literature/stacks-project/more-morphisms.tex`,
`lemma-qcoh-relative-pseudo-coherence-characterize` (Tag 09VF), lines 16907--16955:
the three conditions and the proof. The locally finite type hypothesis, quasi-coherent
cohomology, fixed integer degree, and the covering/every-pair conditions agree with this
source and with the DAG statement. The DAG proof's unbounded affine-pushforward argument
is retained in the Lean docstring.

Hypotheses and objects:

- Schemes and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Locally finite type: `[LocallyOfFiniteType f]`.
- An object of the unbounded category with quasi-coherent cohomology:
  `(E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)`.
  This is the ordinary derived-category object plus its full-subcategory property.
- The fixed degree: `(m : ℤ)`, outside all choices of charts or presentations.
- The two `HasDerivedCategory` families supply the localization infrastructure for
  scheme-module categories and ordinary modules. They impose no geometric, Noetherian,
  or cohomological-boundedness condition. The scheme and ordinary-module localization
  morphism universes `w` and `wA` are independent.

Clauses:

1. The first entry of `List.TFAE` is exactly
   `Scheme.IsMPseudoCoherentRelativeTo f m E`, the recorded definition.
2. The second entry uses `∀ s : S, ∃ V, ∃ hV : IsAffineOpen V, s ∈ V ∧ ...`.
   For each chosen affine base neighbourhood it requires
   `∀ x : X, f x ∈ V → ∃ U, ∃ hU : IsAffineOpen U, x ∈ U ∧ ∃ hUV, ...`.
   The witness `hUV : U ≤ f ⁻¹ᵁ V` expresses containment over V.
   These neighbourhood quantifiers express an affine cover of the base, followed by
   an affine cover of each inverse image. They are equivalent to the node's indexed
   covers: take the witnesses indexed by base points and then the source points, or
   extract a member containing each point from given covers. No cover is required
   finite, nonempty, or independent of m.
3. The third entry universally quantifies over every `U : X.Opens`,
   `hU : IsAffineOpen U`, `V : S.Opens`, `hV : IsAffineOpen V`, and
   `hUV : U ≤ f ⁻¹ᵁ V`. It requires precisely the same module condition.
   `List.TFAE` says all three entries are equivalent, with no extra conclusion.

In both module conditions, the derived sections object is

```
(RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
  ModuleCat.restrictScalars U.topIso.inv.hom).rightDerivedFunctor.obj
    ((derivedPullback U.ι).obj E)
```

Here `derivedPullback U.ι` is restriction to the open subscheme, and the global-sections
functor is valued in modules over its global functions. The canonical ring isomorphism
`U.topIso : Γ(U.toScheme, ⊤) ≅ Γ(X,U)` transports these coefficients to `Γ(X,U)`.
Restriction along its inverse has the correct direction. This is the standard unbounded
module-valued RΓ, obtained using K-injective resolutions, as in the recorded
`exists_affineQCohDerivedEquivalence`; it is not additive-group-valued cohomology or an
arbitrary choice of a quasi-inverse. Deriving the composite with this exact scalar
transport is canonically the same as transporting derived sections afterward. The
right-derived-functor construction is also the one used by the recorded
`RingedSpace.derivedModuleDirectImage`, specialized to the map to the ringed point;
on the point, module evaluation identifies its direct image with global sections.

The ring-relative predicate is applied explicitly with
`R = Γ(S,V)`, `A = Γ(X,U)`, algebra structure
`(f.appLE V U hUV).hom.toAlgebra`, and finite-type evidence
`f.finiteType_appLE hV hU hUV`. Thus the action is induced by f in every chart; it is
neither an additional algebra choice nor an additional finite-type hypothesis.
`RingHom.FiniteType` is definitionally `Algebra.FiniteType` for this algebra structure.
The recorded ring-relative definition supplies exactly the existential polynomial
presentation and scalar restriction in the node, with n allowed to be zero.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`,
  `Scheme.Hom.finiteType_appLE`; the morphism-conventions node delegates here.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty` (and the corresponding full subcategory).
- `WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage`:
  `RingedSpace.derivedModuleDirectImage`, the unbounded right-derived construction.
- `WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence`:
  `exists_affineQCohDerivedEquivalence`, including its module-valued RΓ clause.
- `Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`:
  `Scheme.IsMPseudoCoherentRelativeTo`, including the covering, embedding, and
  derived-pushforward condition.
- `Sheaf.RingTheory.RelativeMPseudoCoherent`:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`, including its full signature and
  explicit algebra and finite-type instances.
- For the coefficient identification, `Mathlib.AlgebraicGeometry.Restrict`:
  `Scheme.Opens.topIso`; for ordinary Γ,
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `RingedSpace.globalSectionsFunctor`. These are available through the public imports.

Proof dependencies with recorded modules or Mathlib matches are imported: finite type,
relative affine space, closed immersions, affine derived equivalence, ringed-space derived
image, affine pushforward of a K-injective resolution, the Tilde pushforward/scalar
comparison, the fixed-degree affine criterion, the two relative definitions, and the affine
basis theorem. Their signatures and docstrings were read. The proof-only node
`lem-sfb-relative-pseudocoherence-all-affine-charts` has no `lean` or `mathlib_match`
record in the supplied repository, so there is no module to import for it; its use remains
in the complete proof docstring. It is not needed to state this theorem.

Edge cases checked: empty base (the covering condition is vacuous and the all-pairs
condition still includes the empty opens), empty source and empty affine charts (their
module categories are zero, and the relative definitions allow zero rings), zero object,
all integer m including zero and negative degrees, and polynomial dimension zero in the
recorded ring-relative predicate. The input complex has no global upper or lower bound.
No separation, quasi-compactness, Noetherianity, characteristic, or nontrivial-ring
hypothesis is added. Both sets of covering witnesses and their polynomial presentations
may depend on the fixed m.

Searches actually run:

- `msearch.py ... leanfinder` with query "Relative m pseudo coherence of a quasi coherent
  derived scheme complex is equivalent to relative m pseudo coherence of its module valued
  derived sections on all affine pairs": 8 hits, all ordinary quasicoherent-data declarations
  (`QuasicoherentData.X`, `.presentation`, `quasicoherentDataOfIsFinitePresentation`, `.I`,
  `QuasicoherentData`, `IsQuasicoherent.nonempty_quasicoherentData`, `isQuasicoherent`,
  `QuasicoherentData.IsFinitePresentation`). None states the derived relative criterion.
- `msearch.py ... loogle '"PseudoCoherent"'`: OK, 0 hits.
- `msearch.py ... grep 'relative.*pseudo.?coher|pseudo.?coher.*relative'`: OK, 0 hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `IsMPseudoCoherentRelativeTo|relative_mPseudoCoherent.*sections|lem-sfb-relative-m-pseudocoherence-derived-sections`:
  found the two required definitions and the closed-support comparison; no existing
  theorem identifies relative degreewise pseudo-coherence with affine derived sections.
- Further targeted source searches found `Scheme.Opens.topIso` and the shared
  module-valued global-sections/right-derived-functor definitions; these are reused.

Validation: scompile.py compiled this delivered file separately as a sandbox module and
under its final library module name, with no errors or unexpected warnings. The final
revision, with explicit source/base section rings and all recorded dependency imports,
also compiled cleanly. No declaration is auto-implicit and no Lean line exceeds 100 columns.
No statement fault or disputed statement was found.

## Second reading by Q140

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
