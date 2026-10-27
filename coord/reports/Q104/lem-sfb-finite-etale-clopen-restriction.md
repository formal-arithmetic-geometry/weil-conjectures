## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteEtaleClopenRestrictionSurjective` states
`AlgebraicGeometry.Scheme.finiteEtale_clopen_restriction_surjective` with its sole
proof left as `sorry`. There are no new definitions or nodes, dependency repairs,
or statement corrections. Only the item's `lean` field changes. Its signature is
copied verbatim from the module, excluding `:=` and the proof.

Hypothesis and conclusion correspondence:

- The schemes X and Y are `{X Y : Scheme.{u}}`, with the universe `u` explicitly
  declared. Both the source and target of the named map are the node's schemes.
- Irreducibility of X is `[IrreducibleSpace X]`, including nonemptiness as required
  by def-weil-irreducible-components. It concerns the underlying space of X.
- The named map p:Y→X is `(p : Y ⟶ X)`. Its finiteness and etaleness are
  `[IsFinite p] [Etale p]`.
- The open subset U with its open subscheme structure is `(U : Y.Opens)`.
  Its canonical open subscheme is `U.toScheme`, and the inclusion j is exactly
  `U.ι : U.toScheme ⟶ Y`, not an arbitrary immersion or a closed subscheme with
  a different structure sheaf. Openness is part of the bundled open subset.
- Closedness of the same underlying subset is `(hU : IsClosed (U : Set Y))`.
  Nonemptiness is `(hne : (U : Set Y).Nonempty)`. No closedness or nonemptiness
  assumption is inferred from the finiteness of p.
- The assertion that j is a closed immersion is `IsClosedImmersion U.ι`.
- The assertion that p∘j is finite is `IsFinite (U.ι ≫ p)`.
- The assertion that p∘j is etale is `Etale (U.ι ≫ p)`.
- The assertion that p∘j is surjective is `Surjective (U.ι ≫ p)`.
- No normality, reducedness, integrality, Noetherian, quasi-compactness of X, or
  surjectivity of p is assumed. The four conclusions concern the named canonical
  inclusion and its composite, without any extra conjunct.

Statement dependency declarations read and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom`; schemes and their morphisms.
- def-weil-irreducible-components: the recorded Mathlib match is
  `irreducibleComponents` in `Mathlib.Topology.Irreducible`. That same module
  defines `IsIrreducible` and `IrreducibleSpace`, the latter used here for the
  node's whole-space irreducibility. It includes `PreirreducibleSpace` and
  `Nonempty`, agreeing with the closed-cover definition.
- def-weil-finite-integral-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`; affine with finite ring maps on affine opens.
  The integral-morphism branch of that definition is not needed by this item.
- def-weil-etale-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`; affine-locally etale ring maps. The source's
  `iff_flat_and_formallyUnramified` supplies its equivalent defining conditions.
  Search-service hits using the old `IsEtale` spelling are not used.
- def-weil-open-immersion: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`. The canonical `U.ι` and its open-immersion
  instance are supplied by `Mathlib.AlgebraicGeometry.Restrict`,
  `AlgebraicGeometry.Scheme.Opens.toScheme` and `Scheme.Opens.ι`.
- def-weil-closed-immersion: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`; closed embedding and surjective stalk maps.
- def-weil-surjective-morphism: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `AlgebraicGeometry.Surjective`; surjectivity on underlying points.

All these modules are public imports. Proof dependencies are available through
plain imports when they are not already statement imports:

- lem-weil-pbc-immersion-closed-image-closed-immersion:
  `IsClosedImmersion.iff_isPreimmersion` / `of_isPreimmersion` in ClosedImmersion,
  and `IsImmersion` in `Mathlib.AlgebraicGeometry.Morphisms.Immersion`.
- lem-weil-pbc-closed-immersion-finite and lem-weil-pbc-finite-composition:
  `IsClosedImmersion.iff_isFinite_and_mono` and the composition instance in Finite.
- lem-weil-pbc-etale-composition-cancellation: the open-immersion instance,
  `Etale.etale_comp`, and `Etale.of_comp` in Etale.
- lem-weil-pbc-finite-closed-map-finite-fibres: the finite-to-proper instance in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Scheme.Hom.isClosedMap` in
  `Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed`, and
  `Scheme.Hom.finite_preimage_singleton` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`.
- lem-weil-pbc-etale-morphism-open-map: `Scheme.Hom.isOpenMap` in
  `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`.
- The irreducibility and surjectivity definition nodes are already public imports.

The theorem docstring carries all four proof steps and names their DAG inputs.
The cited Stacks sources were read locally: schemes.tex, lemma-immersion-when-closed
(Tag 01IQ); morphisms.tex, lemma-closed-immersion-finite (035C),
lemma-composition-finite (01WK), lemma-open-immersion-etale (02GP),
lemma-composition-etale (02GN), lemma-finite-proper (01WN), and lemma-etale-open
(03WT). The argument uses only that the composite has a nonempty clopen image
and the closed-cover definition of irreducibility.

Edge cases checked before writing:

- U=∅ is excluded exactly by `hne`; without it, an empty finite-etale cover of
  a nonempty irreducible scheme would contradict the surjectivity conclusion.
- Y=∅ admits no such U, so the hypotheses correctly exclude it.
- X=∅ is excluded by the node's irreducibility, including its nonempty clause.
- U=Y is allowed: its inclusion is the identity open subscheme inclusion, and
  a nonempty finite-etale source has nonempty clopen image in X.
- p itself need not be assumed surjective: the conclusion implies this after
  choosing a nonempty clopen source subset.
- Irreducibility is essential to the stated hypotheses: taking X=Y to be two
  disjoint points, p the identity, and U one point gives a nonsurjective composite.
- Nonreduced irreducible targets and non-Noetherian targets are not excluded.
  The clopen-image proof does not use reducedness, normality or Noetherianity.

Searches actually run (all wrappers called with Q104 and this item):

1. msearch.py leanfinder, query:
   "A nonempty clopen source restriction of a finite etale morphism over an
   irreducible scheme is a closed immersion into the source and finite etale
   surjective over the target". Eight hits: Scheme.Etale, IsEtale,
   instIsClosedImmersionLiftCoborder, instIsClosedImmersionMorphismRestrict,
   IsFinite.instOfIsClosedImmersion, isIso_of_isClosedImmersion_of_surjective,
   the IsEtale postcomposition instance, and
   IsClosedImmersion.iff_isFinite_and_mono. None states all the conclusions for
   the given source restriction; no exact match.
2. msearch.py loogle, query `"IsFinite", "IsClopen"`: zero hits.
3. msearch.py grep on AlgebraicGeometry, query
   `clopen.*[Ee]tale|[Ee]tale.*clopen|[Ii]rreducible.*[Ss]urjective|[Ss]urjective.*[Ii]rreducible`:
   one hit, Geometrically/Irreducible.lean:71, a surjectivity instance under
   geometrically irreducible fibre hypotheses; not the present statement.
4. rg over lean/WeilConjectures and lean/Sheaf with
   `clopen.*[Ee]tale|[Ee]tale.*clopen|finite_etale_clopen|lem-sfb-finite-etale-clopen-restriction`:
   related clopen etale material, including FiniteEtaleClopenRestrictionRank.
   Its full signature was read: it gives finite-etale restrictions and rank base
   change, with no irreducibility/nonemptiness, closed-inclusion conclusion, or
   surjectivity conclusion; it is not this statement.
5. rg for the exact proposed declaration name and blueprint id over both source
   trees and dag/lean_names_upstream.json: no existing declaration for this item.

Validation: scompile.py compiled this file in sandbox and library module mode
against the published server build, with no errors or warnings (6.2 s and 4.9 s).
No STATEMENT-DISPUTED issue or dependency interface fault was found.

## Second reading by Q104

I re-read the node and completed module after compilation. This is a self-check;
the independent reading is the maintainer's delivery review, as specified in the
worker assignment. No additional agent was started. Each node hypothesis appears
in the binders listed above; all four conclusions occur in the conjunction.
The base remains X, the total space remains Y, the subset is a source open, and
`U.ι ≫ p` has the correct order. Closedness and nonemptiness are explicit proofs
about the same subset. Irreducibility has its nonempty meaning, not merely
preirreducibility. No extra scheme hypotheses, missing clause, or mismatch was
found, and no correction was needed. Only one named theorem is postponed.
