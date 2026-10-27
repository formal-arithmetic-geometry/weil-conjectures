## Worker report

The module Sheaf.AlgebraicGeometry.Morphisms.FibreRegularSequenceFlatSlice states
AlgebraicGeometry.exists_affine_flat_slice_of_fiber_regular_sequence, with its sole proof
`sorry`. No definitions, extra theorems, or dependency modules are introduced. The statement
was checked directly against Stacks more-morphisms.tex, lemma-slice-given-elements
(Tag 06LI), including its first proof and its explicit maximal-ideal observation.

Clause-by-clause correspondence:

- Schemes T and B, and their morphism g: `{T B : Scheme.{u}} (g : T ⟶ B)`.
  The universe u is arbitrary.
- Local finite presentation of g: `[LocallyOfFinitePresentation g]`.
- The point t: `(t : T)`; its base point b is exactly `g t` throughout.
- Flatness only at t: `(hflat : (g.stalkMap t).hom.Flat)`. Global flatness of g is
  not assumed.
- Every nonnegative length r and its specified ordered germs: `(r : ℕ)` and
  `(h : Fin r → T.presheaf.stalk t)`.
- The actual scheme-theoretic fibre and its distinguished point are `g.fiber (g t)`
  and `g.asFiber t`. The original germs map to its local ring by
  `(g.fiberStalkMap t).hom`; this definition is the projection stalk map with its
  source transported by `fiberι_asFiber`, not an arbitrary ring homomorphism.
- Regularity is `RingTheory.Sequence.IsRegular` on that fibre stalk, with list
  `List.ofFn (fun i : Fin r ↦ (g.fiberStalkMap t).hom (h i))`.
  It includes both injective multiplication on each successive quotient and a
  nonzero final quotient. There is no extra maximal-ideal hypothesis.
- The affine open neighbourhood is `∃ (W : T.Opens) (hW : IsAffineOpen W)
  (ht : t ∈ W)`.
- Its sections are `a : Fin r → Γ(T, W)`. These are the sections of the restricted
  structure sheaf, canonically the same ring as Γ(W,O_W).
- Every prescribed germ is retained by
  `∀ i : Fin r, T.presheaf.germ W t ht (a i) = h i`.
- D is the actual affine closed subscheme `Spec (Γ(T,W) ⧸ Ideal.span (Set.range a))`.
  Its morphism to T is `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
  (Ideal.span (Set.range a)))) ≫ hW.fromSpec`. The quotient map is surjective,
  so it defines the canonical closed subscheme of W. `hW.fromSpec` is the open
  affine chart, not a freely chosen embedding. Thus no existential D or map
  could change the ideal or the scheme structure. Closedness is inherent in this
  construction rather than an additional conclusion of the theorem.
- Containment t ∈ D is precisely membership in `Set.range` of that morphism.
- Flatness and local finite presentation of D → B are the final `Flat` and
  `LocallyOfFinitePresentation` clauses on that same morphism composed with g.

Recorded dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  AlgebraicGeometry.LocallyOfFinitePresentation.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: AlgebraicGeometry.Flat, with the
  stalk interpretation checked against Flat.iff_flat_stalkMap.
- Mathlib.RingTheory.Regular.RegularSequence: RingTheory.Sequence.IsRegular,
  IsWeaklyRegular and their full defining conditions.
- Mathlib.AlgebraicGeometry.Fiber: Scheme.Hom.fiber, fiberι, fiberToSpecResidueField,
  fiberHomeo, asFiber and fiberι_asFiber.
- Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion;
  the chosen affine chart is the canonical open immersion hW.fromSpec.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  AlgebraicGeometry.IsClosedImmersion; the closed subscheme is constructed from
  the surjective quotient ring map, as in the existing hypersurface statement.
- Sheaf.AlgebraicGeometry.FibreStalkQuotient: Scheme.Hom.fiberStalkMap, a real
  canonical construction. Its already-landed owning node
  def-trf-fibre-stalk-map is added to stmt_deps, as permitted by the
  landed-dependency rule; no statement correction or new node is needed.

The proof-only imports follow every recorded usable module in proof_deps:
Mathlib's AffineScheme, ResidueField, Morphisms.FiniteType, Pullbacks, and
RingTheory.Spectrum.Prime.Topology; Sheaf.AlgebraicGeometry.Morphisms.
FibreRegularElementFlatHypersurface; and WeilConjectures.Topology.
PresheafModuleStalkFunctor. The module for lem-sfb-relative-flat-affine-charts is
not yet recorded, so there is no module to import for that proof dependency.
The theorem docstring spells out all seven proof steps and their dependencies.

Edge cases checked: r = 0 gives the empty list and zero generated ideal, hence
D = W; it requires only the open flat locus near t and imposes no equation.
For r = 1 this has the conclusion of the existing 056Y hypersurface statement;
regularity forces the germ into the maximal ideal, so no additional hypothesis
is needed. A zero or unit fibre image cannot be a one-element regular sequence
in the nonzero local ring: respectively injectivity or the nonzero quotient
fails. The empty scheme T has no point t, as required. Nonreduced schemes,
positive characteristic, nonclosed points, and non-Noetherian bases are not
excluded by any binder. Repetition of generators and their ordering are handled
by the ordered list, not by regularity of an unordered set.

Searches for an existing statement:

- msearch.py leanfinder, query: "A locally finitely presented scheme morphism flat
  at a point admits an affine neighbourhood where germs regular in its fibre cut
  out a flat locally finitely presented closed subscheme". Eight hits:
  spread_out_of_isGermInjective', exists_lift_of_germInjective,
  IsSmooth.exists_isStandardSmooth, Scheme.Hom.flat_appLE, flat_iff,
  Flat.generalizingMap, Flat.stalkMap, Flat.of_stalkMap. None states this result.
- msearch.py loogle, query `AlgebraicGeometry.Flat, RingTheory.Sequence.IsRegular`:
  OK, zero hits.
- msearch.py grep, query `regular.*(sequence|slice)|slice.*flat` in AlgebraicGeometry:
  OK, zero hits.
- rg in lean/WeilConjectures and lean/Sheaf, by fibre/fiber regularity, flat slices,
  and regular_slice: related algebra regular-sequence results, CM slices with
  extra assumptions/conclusions, and the single-element hypersurface statement
  exist. None is this arbitrary-length, prescribed-germ 06LI assertion.
- rg of the exact item id in lean/WeilConjectures returned no match; no duplicate
  of the new declaration name was found.

No statement dispute, correction, or dependency interface fault was found.

## Second reading by Q103

Author self-check only; the dispatcher brief assigns independent review to the
maintainer. Re-read the node and the complete module together. Each hypothesis
and conclusion matches the clause mapping above: pointwise input flatness,
ordered finite fibre-regular germs, affine neighbourhood, section germs, the
canonical scheme quotient containing t, and global flatness and local finite
presentation for its composite to B. In particular the closed subscheme is not
replaced by its reduced zero locus, regularity is not merely weak regularity,
and length zero is retained. No correction was needed. The only extra recorded
statement dependency identifies the already-landed canonical fibre stalk map.

## Repair of return H2

The return on immutable head 6874b4dc0c2f identified that the theorem node
lem-sbc-scheme-fibre-stalk-quotient was incorrectly added to stmt_deps just to
supply the plain definition Scheme.Hom.fiberStalkMap. Read the current owning
node def-trf-fibre-stalk-map (existing: true, N6, 2026-10-23) and the full explicit
definition in Sheaf.AlgebraicGeometry.FibreStalkQuotient. The definition uses
stalk transport and the fibre projection directly; it does not choose data
from the accompanying theorem.

Replaced exactly that added statement dependency with def-trf-fibre-stalk-map.
The module and lean.statement remain byte-identical to the returned delivery.
Rebased the node metadata on the current read-only main copy while retaining
the same lean record. The independent reviewer accepted all mathematical
clauses; no Lean or mathematical statement change was requested or made.
