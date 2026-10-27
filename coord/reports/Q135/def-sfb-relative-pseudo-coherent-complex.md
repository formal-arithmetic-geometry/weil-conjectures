## Worker report

The module Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex defines
AlgebraicGeometry.Scheme.IsMPseudoCoherentRelativeTo and
AlgebraicGeometry.Scheme.IsPseudoCoherentRelativeTo. Both are actual predicates;
there are no new theorems or sorry proofs. The node changes only in lean.

Source checked: literature/stacks-project/more-morphisms.tex,
definition-relative-pseudo-coherence, Tag 09UI, clauses (1) and (2), together
with lemma-relatively-pseudo-coherent, Tag 09VC, condition (1).
The local tags table confirms these identifiers. The node faithfully spells out
the existential embedding condition, so no statement correction is required.

Clause-by-clause correspondence:

- Schemes and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Locally finite type: `[LocallyOfFiniteType f]`, with no separatedness,
  quasi-compactness, Noetherian or finite-presentation assumption.
- The unrestricted derived object: `(E : schemeDerivedCategory X)`;
  quasi-coherent cohomology is not required. The family of
  `HasDerivedCategory.{w}` instances on schemes supplies the common localization
  universe for the source, all opens and all ambient affine spaces. This is the
  project's structural derived-category convention, not a finiteness hypothesis;
  Mathlib's standard localization supplies it in a sufficiently large universe.
- An arbitrary degree: `(m : ℤ)`.
- The affine cover of S: `∀ s : S, ∃ V : S.Opens, IsAffineOpen V ∧ s ∈ V ∧ ...`.
  This is the neighbourhood formulation of the existential cover: choose V for
  each point to get a cover; conversely select a cover member containing s.
- Over each chosen V, the affine cover of its inverse image:
  `∀ x : X, f x ∈ V → ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ...`,
  followed by `∃ hUV : U ≤ f ⁻¹ᵁ V`. Thus these opens lie inside the preimage
  and their union equals it. The point-indexed choice imposes no finiteness
  restriction on either cover and expresses precisely arbitrary open covers.
- The finite dimension n_ab >= 0: `∃ n : ℕ`; variables are indexed by
  `ULift.{u} (Fin n)`, with exactly n elements in the scheme's universe.
- The closed immersion: `∃ i : U.toScheme ⟶ AffineSpace ... V.toScheme`,
  followed by `IsClosedImmersion i`.
- The immersion is over V: `i ≫ (AffineSpace ... V.toScheme ↘ V.toScheme) =
  f.resLE V U hUV`. This uses the canonical first projection of relative affine
  space and the actual restricted morphism, not an arbitrary map to V.
- Restriction of E: `(derivedPullback U.ι).obj E`, as in the recorded absolute
  m-pseudo-coherent definition.
- The required derived direct image: `(schemeDerivedDirectImage i).obj` applied
  to that restriction.
- Its absolute m-pseudo-coherence: the recorded `Scheme.IsMPseudoCoherent` on
  the ambient `AffineSpace (ULift.{u} (Fin n)) V.toScheme`, at the same m.
- The all-degree notion: `∀ m : ℤ, IsMPseudoCoherentRelativeTo f m E`.
  All choices of V, U, n and i lie inside the quantifier over m, exactly retaining
  the explicit permission for covers and embeddings to vary with m.

Recorded dependency interfaces read and used:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme,
  AlgebraicGeometry.Scheme and Scheme.Hom.
- def-pc-derived-category: WeilConjectures.AlgebraicGeometry.DerivedCategory,
  AlgebraicGeometry.schemeDerivedCategory.
- def-pc-morphism-conventions is a convention record with no own declaration;
  its locally finite type notion is AlgebraicGeometry.LocallyOfFiniteType in
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType.
- def-pc-derived-direct-image:
  WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage,
  AlgebraicGeometry.schemeDerivedDirectImage, the unbounded ringed-space
  derived direct-image construction specialized to schemes.
- def-sfb-m-pseudo-coherent-complex:
  Sheaf.AlgebraicGeometry.MPseudoCoherentComplex,
  AlgebraicGeometry.Scheme.IsMPseudoCoherent. Its full signature and docstring
  were read, including its derived pullback restriction and local strictly
  perfect approximations. It publicly imports the recorded derivedPullback.
- def-weil-closed-immersion:
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  AlgebraicGeometry.IsClosedImmersion.
- def-nagata-relative-affine-space: Mathlib.AlgebraicGeometry.AffineSpace,
  AlgebraicGeometry.AffineSpace. Its pullback definition and canonical first
  projection were read. Its documented finite-dimensional convention is
  ULift.{u} (Fin n), used here verbatim.

Edge cases checked mathematically before writing: empty S (both neighbourhood
quantifiers vacuous, agreeing with empty covers); empty X over nonempty S
(only affine neighbourhoods of S remain); n=0 (the empty variable type is allowed,
affine zero-space is the base); arbitrary negative and positive m (no bound);
the zero complex (admits the zero strictly perfect approximation on every chart);
no finite-type or quasi-compactness restriction on a whole cover. For a field
base and identity morphism, an infinite-dimensional vector space in degree zero
is 1-pseudo-coherent by the zero approximation but fails the finite-generation
test in degree zero; the definition retains the degree distinction through the
existing absolute predicate. Nothing forces the charts to work uniformly in m.

Searches (all via prescribed msearch.py unless specified):

- leanfinder: "Relative m pseudo coherent derived complex on a scheme over a base
  via closed immersions into finite affine space" returned eight hits about
  affine transition limits, affine-space finite presentation and smooth
  relative dimension; none defines relative pseudo-coherence of complexes.
- loogle: `"PseudoCoherent", "AffineSpace"` returned zero hits.
- grep: `Relative.*PseudoCoherent|relative.*pseudo.?coherent|IsMPseudoCoherent`
  returned zero Mathlib hits.
- leansearch: "relative pseudo coherence for derived complexes on schemes"
  returned eight hits about quasi-coherent modules, derived localization,
  truncation fractions and module pseudofunctors; none matches the relative
  notion.
- Direct rg in lean/WeilConjectures and lean/Sheaf for pseudo-coherent variants
  found the ring-level and absolute scheme predicates, including the supplied
  Scheme.IsMPseudoCoherent, but no scheme-relative predicate. The ring-relative
  DerivedCategory.IsMPseudoCoherentRelativeTo in
  Sheaf/RingTheory/RelativeMPseudoCoherent.lean is a different ring-level notion.
- Direct grep for the item's blueprint id in lean/WeilConjectures found nothing.
- Direct rg for IsMPseudoCoherentRelativeTo / IsPseudoCoherentRelativeTo in
  dag/lean_names_upstream.json and the Mathlib, upstream and Sheaf geometry
  directories found no declarations with the proposed scheme-relative names.

No new nodes, dependency repairs, disputed statements or other node faults.
The prescribed server scompile.py compiled both the sandbox and library module
cleanly, with no warnings; delivery dry-run and final compilation follow.

## Second reading by Q135

The dispatcher expressly forbids starting other agents, and the maintainer's
independent review reads this delivery. This section records a separate
self-reading of the finished module against the open node and the Stacks source;
it does not claim an independent worker reviewed the file.

Re-read the two nested neighbourhood quantifiers against both covers in the
node: each chosen V contains its indexing base point, and every x over V has
an affine U containing x and contained in its preimage. Re-read the embedding
condition: its target is finite affine space over that very V, and equality
with f.resLE fixes its structure morphism over V. Re-read the derived object:
only E restricted via the canonical inclusion is pushed forward, at the same
integer m and in the full unbounded derived category. Re-read the second
definition: universal quantification over m surrounds the existential charts,
so it does not introduce uniform choices. The locally finite type binder is
present in both definitions, and no mathematical assumption is added.
No mathematical mismatch was found. The source-tag cross-check corrected the
affine-embedding lemma citation from the section tag 09UH to its lemma tag 09VC.
