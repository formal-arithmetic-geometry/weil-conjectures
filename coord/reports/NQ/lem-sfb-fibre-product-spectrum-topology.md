## Worker report

The module `Sheaf.RingTheory.FibreProductSpectrumTopology` states
`PrimeSpectrum.pullback_jointly_surjective_and_existsUnique_continuousMap`.
Its only postponed proof is this named theorem, with all nine proof steps from the
node in its docstring. No definitions or auxiliary theorems are added, and no
statement correction is needed.

Hypotheses and clauses, matched to the node:

- Arbitrary commutative rings A, D, T with identity are the three explicit type
  binders and `[CommRing A] [CommRing D] [CommRing T]`. There is no `Nontrivial`
  binder. The universes `uA`, `uD`, `uT` are independent.
- The unital maps are `(α : A →+* D)` and `(β : T →+* D)`. The only map
  hypothesis is `(hα : Function.Surjective α)`; no condition on β is imposed.
- P is Mathlib's `α.pullback β` (`RingHom.pullback`), literally the subring of
  pairs `(a,t)` with `α a = β t`. It inherits componentwise operations. Its
  component maps are `α.pullbackFst β` and `α.pullbackSnd β`. These are existing
  constructions, not a new private copy or an arbitrary ring with chosen maps.
- The spectra with Zariski topology are `PrimeSpectrum A`, `PrimeSpectrum D`,
  `PrimeSpectrum T`, and `PrimeSpectrum (α.pullback β)`. These are exactly the
  underlying spaces of the recorded `AlgebraicGeometry.Spec` declaration.
  The induced maps are `PrimeSpectrum.comap`, contraction of prime ideals.
- Joint surjectivity is the first conjunct: every `p` is the image of a point
  `a` in `PrimeSpectrum A` or a point `t` in `PrimeSpectrum T`.
- An arbitrary topological target is `∀ (H : Type uH) [TopologicalSpace H]`.
  This universe is independent of all ring universes. Continuous maps u and v
  are the binders `C(PrimeSpectrum A, H)` and `C(PrimeSpectrum T, H)`.
- Agreement of composites from Spec D is exactly
  `u ∘ comap α = v ∘ comap β`.
- Existence of a continuous h is `∃! h : C(PrimeSpectrum (α.pullback β), H)`.
  The predicate specifies both restrictions:
  `h ∘ comap (α.pullbackFst β) = u` and
  `h ∘ comap (α.pullbackSnd β) = v`.
  The uniqueness quantifier ranges over continuous maps with these restrictions.
  This is the explicit topological pushout universal property in the node.
  Continuity and commutativity of the canonical legs already follow from the
  existing `continuous_comap`, `comap_comp`, and `RingHom.pullback_comm_sq`;
  they require no extra hypothesis.

Dependency declarations read and used:

- Statement dependency `def-weil-affine-spectrum` records
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`, which is publicly imported. Their underlying
  space and underlying map are precisely `PrimeSpectrum` and `PrimeSpectrum.comap`.
- `RingHom.pullback`, `RingHom.pullbackFst`, `RingHom.pullbackSnd` in
  `Mathlib.RingTheory.LocalRing.Pullback` provide the explicit ring and maps.
- `PrimeSpectrum.comap` in `Mathlib.RingTheory.Spectrum.Prime.RingHom` and
  `PrimeSpectrum.continuous_comap` in `Mathlib.RingTheory.Spectrum.Prime.Topology`
  give the contraction maps and continuity; Topology is publicly imported.
- Proof dependency `def-weil-ring-localization-away` records `Localization.Away`
  in `Mathlib.GroupTheory.MonoidLocalization.Away`; ring operations and its
  algebra interface come via the plain proof import
  `Mathlib.RingTheory.Localization.Away.Basic`.
- The three remaining proof dependencies are Mathlib leaves. Their recorded
  matches are `PrimeSpectrum.isClosedEmbedding_comap_of_surjective` and
  `PrimeSpectrum.range_comap_of_surjective` (quotient spectrum),
  `PrimeSpectrum.isTopologicalBasis_basic_opens`,
  `PrimeSpectrum.localization_away_isOpenEmbedding`,
  `PrimeSpectrum.localization_away_comap_range` (principal localization), and
  `PrimeSpectrum.zeroLocus_eq_iff` with `Ideal.radical_eq_sInf` (radicals).
  Their signatures were read; their modules are already reached through the
  public Topology import. No genuine dependency lacks an interface.

Source checked: `literature/stacks-project/more-algebra.tex`,
`situation-module-over-fibre-product` and `lemma-points-of-fibre-product`
(Tag 0B7J, lines 525–604). The source's A′, A, B are respectively this node's
A, D, T. Its only assumption is surjectivity of A′ → A.

Edge cases checked before writing:

- If D is the zero ring, P = A × T, so this is the disjoint union of spectra.
- If A is zero, surjectivity forces D zero and P = T. If T is zero, its unital
  map forces D zero and P = A. If all rings are zero, all spectra are empty.
- If α is an isomorphism, P is canonically T and descent reduces to v.
- β may fail both injectivity and surjectivity (for example Z → F₂[x]);
  no embedding assumption on Spec T → Spec D appears.
- H can be empty, disconnected, non-Hausdorff, or live in any universe. The
  existence assertion is conditional on the compatible u and v. For an empty
  source spectrum the unique empty map is allowed.

Searches (the exact wrapper outputs are also in `searches.jsonl`):

- `msearch.py ... leanfinder "The prime spectrum of a fibre product of rings along
  a surjective map is a topological pushout, jointly surjective with unique
  continuous descent"`: 8 results, all about scheme pullbacks from ring
  pushouts or tensor products; none is this theorem.
- `msearch.py ... leansearch "The spectrum of the pullback of rings along a
  surjection is the topological pushout of the spectra"`: 8 results, including
  `isPullback_Spec_map_pushout`, the closed embedding of a quotient spectrum,
  and `pullbackSpecIso`; none states this topological pushout.
- `msearch.py ... loogle 'PrimeSpectrum, "pullback"'`: no results.
- `msearch.py ... grep 'pullback|fiberProduct|fibreProduct|pushout'
  RingTheory/Spectrum`: only the docstring about contraction of primes.
- Direct `rg` of Mathlib's ring constructions found `RingHom.pullback` and its
  projection abbreviations; their complete definitions were read and reused.
  `CommRingCat.pullbackCone` was also read and constructs the same subring.
- Direct `rg` for the node id and proposed declaration name in
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found
  only the use in the proof plan of `AffineClosedPinchingPushout.lean`.
  That theorem concerns the pushout of schemes, not arbitrary continuous maps.

Validation: the prescribed `scompile.py` compiled the delivered file both as a
sandbox module and at its actual library module path, with no errors or warnings.
No statement dispute or node fault was found.

## Second reading by NQ

I performed a separate rereading of the node, source, and final signature after
compilation; the dispatch brief prohibits starting another agent, so this is a
self-check rather than a claim of independent review. The maintainer's delivery
review supplies the independent reading.

The rereading checked all three CommRing binders against “allowing zero rings”,
the orientation A → D ← T, the surjectivity hypothesis only on α, the literal
matching-pairs subring, and both projection contractions. The first conjunct
covers every prime of P. The second conjunct quantifies over arbitrary spaces
and continuous maps, uses equality after contraction from Spec D, and asks for
exactly one continuous map satisfying both restrictions. The independent universe
binders impose no equality of ring or space sizes. No clause or hypothesis was
missing, no additional hypothesis was introduced, and no change was needed.
