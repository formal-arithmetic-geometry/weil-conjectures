## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedImmersionUnboundedProjectionFormula`
states `AlgebraicGeometry.closedImmersion_unbounded_projection_formula` with
one `sorry`. It contains no new definitions and proves nothing. The mathematical
statement, source, and accepted seven-step proof split are unchanged. The old
stage-1 unchanged-item refusal is superseded by the explicit stage-2 handoff in
coord/brief-stage2.md section 0; the live item has no Lean record.

Clause-by-clause correspondence:

- Schemes and a closed immersion: `{Z P : Scheme.{u}} (i : Z ⟶ P)
  [IsClosedImmersion i]`. No properness, finiteness, quasi-coherence, flatness,
  or Tor-dimension hypothesis is added.
- The shared unbounded derived categories are `schemeDerivedCategory Z` and
  `schemeDerivedCategory P`, with the published `HasDerivedCategory.{w}` family.
  This fixes the localization models for the existing canonical-map API on all
  schemes; it is a choice of localization, not a geometric assumption on i.
  Universes `u w` are declared explicitly and auto-implicit binding is disabled.
- Direct image on all structure-module sheaves is exactly
  `RingedSpace.moduleDirectImage i.toLRSHom.toShHom`, the same functor whose
  right derived functor is the recorded `schemeDerivedDirectImage i`.
  Its exactness is the first two conjuncts, `PreservesFiniteLimits` and
  `PreservesFiniteColimits`. For additive functors between these abelian
  categories these are equivalent to exactness.
- Every representative complex computes Ri_*: the third conjunct quantifies
  over every `A : CochainComplex (SheafOfModules (moduleRings Z.toRingedSpace)) ℤ`
  without an injectivity or boundedness condition and asserts `IsIso` of
  `rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj A)`.
  The published right-derived unit is from termwise direct image followed by
  Qh to Qh followed by Ri_*. The canonical `quotientCompQhIso` identifies these
  two endpoints with Q(i_*A) and Ri_*(Q A), respectively. Thus this is the
  canonical comparison in the node, not an unspecified object isomorphism.
- The fourth conjunct quantifies independently over all
  `(E : schemeDerivedCategory Z) (Q : schemeDerivedCategory P)` and asserts
  `IsIso` of an actual morphism from `Ri_*E ⊗ Q` to
  `Ri_*(E ⊗ Li^*Q)`, using `schemeDerivedTensorMonoidal` on both categories.
  The morphism is the adjoint under `relativeMVAdj i` of
  `τ (Ri_*E) Q ≫ (counit.app E ⊗ₘ 𝟙 (Li^*Q))`.
  Here τ is `Classical.choose (exists_canonicalPullbackTensorComparison i)`.
  This theorem specifies its K-flat representative equation, and
  `IsCanonicalPullbackTensorComparison.unique` proves uniqueness. It is
  therefore the canonical tensor comparison, never an arbitrary chosen map.
  `relativeMVAdj` is pinned to the actual derived units and counits.
- No cohomological boundedness, quasi-coherence, or Tor-amplitude predicate is
  present on either E or Q. Both are objects of the full unbounded categories.

Recorded statement dependencies used (sources and docstrings read):

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and its category morphisms.
- def-weil-closed-immersion: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding and surjective stalk maps).
- def-pc-derived-category: `WeilConjectures.AlgebraicGeometry.DerivedCategory`,
  `AlgebraicGeometry.schemeDerivedCategory`, the localization of the shared
  `SheafOfModules` category with Mathlib's abelian structure.
- def-pc-derived-pullback: `WeilConjectures.AlgebraicGeometry.DerivedPullback`,
  `AlgebraicGeometry.derivedPullback`, its `derivedPullback_spec` and canonical
  transport from `Scheme.Modules.derivedPullback`.
- def-pc-derived-direct-image:
  `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`,
  `AlgebraicGeometry.schemeDerivedDirectImage`, abbreviating the ringed-space
  `derivedModuleDirectImage` of the actual `moduleDirectImage`.
- def-pc-scheme-derived-tensor-structure:
  `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`,
  `AlgebraicGeometry.schemeDerivedTensorMonoidal`, the global K-flat-derived
  monoidal instance, not a second monoidal choice.
- def-pc-derived-pullback-tensor-comparison:
  `WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison`,
  `AlgebraicGeometry.exists_canonicalPullbackTensorComparison`, with
  `IsCanonicalPullbackTensorComparison` and its uniqueness theorem.
- def-pc-relative-mv-maps: `WeilConjectures.AlgebraicGeometry.RelativeMVMaps`,
  `AlgebraicGeometry.relativeMVAdj`, the pinned derived adjunction.

The final two definitions were already recorded proof dependencies. They are
added as already landed statement dependencies under brief-stage2 section 5,
because the signature uses them to specify the canonical map. No new node and
no dependency-interface repair is required. Every stated proof dependency's
module is imported privately, including the Mathlib stalk mono/epi leaves;
all seven proof steps, the cone argument, and the canonical-map identification
are in the theorem docstring for stage 3.

Edge cases checked against Tag 0B55 and the signature:

- Z empty and P empty: full module categories and zero comparisons are allowed;
  there are no nonemptiness assumptions.
- Identity immersion: the projection arrow is the unit/counit tensor identity
  under the canonical comparisons, so the assertion has its expected form.
- Spec(Z/2) into Spec(Z): the statement allows arbitrary derived tensors,
  including higher Tor, and does not mistake derived pullback for exact pullback.
- Zero E or Q: tensors and direct images give the zero-object isomorphism.
- Complexes unbounded in both directions: degrees range over ℤ and no truncation
  or bounded subcategory occurs. No requirement that A itself be K-flat or
  K-injective is introduced by the computation assertion.
- Empty direct sums are included in the natural-language proof of the direct-sum
  argument, as in the accepted node proof.

Searches performed with the prescribed wrapper:

- leanfinder: "For a closed immersion of schemes the derived direct image on all
  structure module sheaves is exact and the unbounded derived projection formula
  is an isomorphism". Eight hits concerned closed-immersion geometry or ordinary
  open-immersion module restriction/pushforward; none stated this result.
- loogle: `"projectionFormula"`. Zero hits.
- grep in Mathlib: `projection.?formula|projectionFormula`. Three unrelated hits,
  in Witt vectors and covariant derivatives.
- rg in both project roots for `projectionFormula|projection.formula|ProjectionFormula`
  and declaration searches in algebraic-geometry projection modules: existing
  qcqs results impose quasi-coherent inputs, proper-support results impose
  quasi-coherence/proper support, ordinary module formulas concern invertible
  modules, and closed-structure formulas concern i_*O_Z. None states the full
  unbounded all-module theorem here. The published canonical tensor comparison
  and adjunction are reused rather than reconstructed.
- rg for the exact item id in `lean/WeilConjectures`: no existing declaration.
- rg for `closedImmersion_unbounded_projection_formula` in Mathlib-facing source
  roots and `dag/lean_names_upstream.json`: no name collision.
- The live node, queue stage 2 entry, preserved empty sandbox, and repair-notes
  filenames were checked; there is no released repair note for this item.

No statement dispute or mathematical node fault was found. Stacks Tag 0B55
actually assumes only a closed embedding of ringed spaces, so its scheme
specialization applies exactly as written.

Validation: scompile.py compiled this module as both the sandbox module and its
library module with no errors or warnings. The required final dry run and push
are performed through deliver2.py; no live file or launcher tool is edited.

## Second reading by Q91

The dispatcher explicitly forbids starting other agents and assigns independent
review to the maintainer. This is a second pass by the same worker, not a claim
of independent certification. I reopened the node and signature and checked
that all four conjuncts are present: finite limits/colimits express exactness;
the unit is evaluated at every complex; the projection arrow is the pinned
adjunction mate of the canonical tensor comparison; both derived inputs are
unrestricted. I checked the tensor order and direction: Ri_*E is the first
factor, Q the second; the counit acts in the first factor after tensor
comparison. I checked the right-derived unit's homotopy-category domain against
its source declaration and the Q versus Qh endpoint identifications. The
localization-family binder follows the published canonical API and introduces
no hypothesis on E, Q, or the closed immersion. No mismatch or source correction
was found. Independent review remains the maintainer's delivery review.
