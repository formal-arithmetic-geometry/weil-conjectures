## Worker report

The module `Sheaf.AlgebraicGeometry.NormalizationNormalLocallyFinite` states
`AlgebraicGeometry.Scheme.isIso_fromReducedNormalization_of_normal_locally_finite`.
Its only theorem has the prescribed `sorry` proof. No definitions or extra nodes are added;
the item JSON changes only in `lean`. No statement correction or disputed statement.

Clause-by-clause translation:

- A scheme X: `(X : Scheme.{u})`, with the universe explicitly declared.
- Every quasi-compact open has finitely many irreducible components:
  `hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite`.
  Here `U` in `irreducibleComponents U` is the subtype with its subspace topology;
  these are the components of U, rather than the components of X contained in U.
  Mathlib `isCompact_iff_compactSpace` identifies the compact-subset condition with
  `CompactSpace U`, the recorded quasi-compactness notion; neither requires Hausdorffness.
- Each local ring is an integrally closed domain:
  `hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
  IsIntegrallyClosed (X.presheaf.stalk x)`. Both conjuncts are necessary: integral
  closedness alone is not used as a replacement for being a domain.
- The componentwise normalization morphism is an isomorphism:
  `IsIso X.fromReducedNormalization`, using the actual canonical map from the recorded
  construction, rather than an unspecified isomorphism between the underlying schemes.
- No local Noetherianity, quasi-compactness of X, excellence, finite type, or nonemptiness
  is assumed. There are no such binders or inferred structure requirements.

Statement dependencies, read at their full declarations and docstrings:

- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.Topology.Irreducible`, `irreducibleComponents`, defined as maximal irreducible
  subsets. This is the Mathlib match for def-weil-irreducible-components.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`, together
  with Mathlib `IsDomain`, exactly the inline normal-domain conjunction recorded on
  def-weil-pbc-normal-ring.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`,
  `AlgebraicGeometry.Scheme.reducedNormalization` and `fromReducedNormalization`.
  The former is the coproduct of function-field normalizations of the reduced induced
  components; the latter is the coproduct map composed with their closed inclusions.
- `Mathlib.Topology.Defs.Filter`, `CompactSpace`, and its equivalent subset formulation
  in `Mathlib.Topology.Compactness.Compact`.

Available proof-dependency modules are included as plain imports: Mathlib FunctionField,
AffineScheme, LocalProperties.IntegrallyClosed, Morphisms.FiniteType,
Morphisms.QuasiSeparated, Normalization and Limits; the upstream
`WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`. Their recorded function-field,
localization, local-normality, local-spectrum, relative-normalization and coproduct
interfaces match the proof plan. The proof-only node
lem-sfb-normal-locally-finite-components has no recorded Lean declaration yet, so there
is no module to import for it. It is not needed to type the present statement.

Sources read: `literature/stacks-project/morphisms.tex`, labels
lemma-normalization-trivial (0H7D), lemma-normalization-in-terms-of-components (0CDV),
and lemma-finite-birational-over-normal; `properties.tex`,
lemma-normal-locally-finite-nr-irreducibles (0357). These give precisely the stated
sufficient direction, with the quasi-compact-open formulation explicitly in 0357.
The docstring carries all seven approved proof steps, including the generic-point
pushforward algebra identification, affine inverse gluing, both inverse identities,
and the empty coproduct.

Edge cases checked mathematically before writing:

- Empty X: the stalk condition is vacuous; each open has no components; the recorded
  normalization is the empty coproduct and the canonical map is an isomorphism.
- Empty U inside any X: compact and has no irreducible components, so `hfinite` imposes
  no accidental nonempty-open restriction.
- Infinite disjoint unions of normal integral schemes: a quasi-compact open meets only
  finitely many open summands. Global compactness or finiteness of the index is not required.
- A non-Noetherian normal valuation domain: the statement permits its spectrum and
  does not replace normality by regularity or local Noetherianity.
- Spec(A × B) for normal domains A, B: reducibility is allowed, while each stalk is a
  normal domain. No global domain or integral-scheme assumption was added.
- A crossing Spec(k[x,y]/(xy)) fails the domain-stalk condition at the intersection.
  A nonreduced one-point scheme also fails it. Neither supplies a counterexample.

Searches for reuse (2026-10-24):

- `msearch.py ... leanfinder`: “The componentwise normalization of a scheme with
  integrally closed domain stalks and finitely many irreducible components on
  quasi-compact opens is an isomorphism”. Eight hits, all relative-normalization
  interfaces; none states this theorem. In particular
  `Scheme.Hom.instIsIsoToNormalizationOfIsIntegralHom` concerns `f.toNormalization`
  under an integral-morphism hypothesis, a different canonical map and hypotheses.
- `msearch.py ... loogle '"normalization", "IsIso"'`: four hits, relative normalization,
  smooth base change, and Zariski-main open-locus statements; no match.
- `msearch.py ... grep 'normalization.*[Nn]ormal|[Nn]ormal.*normalization'
  AlgebraicGeometry`: relative-normalization and Zariski-main hits; no match.
- `msearch.py ... leansearch`: “The normalization morphism of a normal scheme with
  locally finitely many irreducible components is an isomorphism”. Eight hits,
  relative-normalization construction and properties, no exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for normality/normalization,
  `fromReducedNormalization`, and the item id: the upstream integral-scheme
  normalization-over-normal-locus theorem is a special case. The project
  `componentwiseNormalization_properties` assumes locally Noetherian X, and
  `reducedNormalization_over_normal_reduction` assumes finite type over a field;
  neither states the assigned generality. Item-id hits are proof-plan citations.
  No upstream declaration carries this item id. The new theorem name has no collision.
- No repair-note file for this item was found in `coord/repair-notes`.

Validation: prescribed `scompile.py Q06 lem-sfb-normalization-normal-locally-finite`
compiled both its sandbox and final library module successfully (1.6 s / 1.8 s).
The universe and every binder are explicit, with `autoImplicit false`.

## Second reading by Q06

Final rereading by the same worker (no other agents were started; the maintainer provides
independent review). Compared the node and source against the final signature again:
`∀ U : X.Opens` includes all opens, `IsCompact (U : Set X)` selects exactly the
quasi-compact ones, and `(irreducibleComponents U).Finite` counts components in the
subspace. `∀ x : X` covers every stalk, with both domain and integral-closedness
conjuncts. `IsIso X.fromReducedNormalization` concerns precisely the componentwise
canonical map of the dependency node. The two hypotheses and the conclusion match,
including the empty scheme and infinite component families. No mismatch was found
and no mathematical statement changed. The seven proof-plan steps match the node.
There are no new nodes or repaired dependency modules to review.
