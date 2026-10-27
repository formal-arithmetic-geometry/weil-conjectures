## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothTraitBirationalImmersion` states
`AlgebraicGeometry.smooth_trait_birational_immersion`, with one `sorry` and no new definitions.
The existing node is changed only in `lean`; no statement correction or dependency repair is needed.
The module compiles through the prescribed scompile.py wrapper in sandbox and library modes,
without errors or unexpected warnings (both checks took 1.7 seconds).

Hypothesis and conclusion correspondence:

- The DVR R is `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`.
  The class excludes fields, precisely as the dependency's definition requires.
- F = Frac(R) is the canonical `FractionRing R`, with its existing field and R-algebra
  structures; there is no arbitrary choice of field or of a map into it.
- T = Spec R is `Spec (CommRingCat.of R)`. `X Z : Over T` packages exactly the two
  schemes and their structure morphisms, with no extra geometric hypothesis.
- Smoothness is `[Smooth X.hom] [Smooth Z.hom]`.
- Separatedness is `[IsSeparated X.hom] [IsSeparated Z.hom]`; this existing Mathlib
  class means that the respective pullback diagonal is a closed immersion, as the node says.
- Finite type is `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]` and the corresponding
  pair for Z, exactly the recorded convention for def-weil-finite-type-morphism.
- The open U is `(U : X.left.Opens)`; its canonical inclusion is `U.ι`.
- Containment of X_F is `hgeneric`: the range of `pullback.fst X.hom (Spec.map
  (CommRingCat.ofHom (algebraMap R (FractionRing R))))` is contained in U. This is the
  image of the actual scheme-theoretic generic base change under its projection to X.
- Density in both fibres is `hdense : ∀ t : Spec (CommRingCat.of R), Dense
  ((X.hom.fiberι t) ⁻¹' (U : Set X.left))`. A DVR has exactly its generic and closed
  points; quantifying over all t means precisely the two fibres, including empty fibres.
  `fiber` is the pullback along the canonical map from the point's residue-field spectrum;
  `fiberι` is its first projection. Density concerns the fibre's own topology.
- The first conclusion is the first conjunct, `∀ x : X.left,
  ringKrullDim (X.left.presheaf.stalk x) ≤ 1 → x ∈ U`.
  `ringKrullDim` is the Krull dimension of the local ring's prime spectrum ordered by
  inclusion, hence the required supremum of lengths of prime chains.
- A T-morphism f is `f : X ⟶ Z` in Over T. Its compatibility with structure maps is
  part of that type, rather than an additional assumption on an arbitrary map.
- The hypothesis on f_F is `IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom
  (algebraMap R (FractionRing R))))).map f).left`. This is exactly the induced map
  between the two generic-fibre schemes, not an unrelated isomorphism between them.
- The restricted open immersion is `IsOpenImmersion (U.ι ≫ f.left)`; the second conclusion
  is `IsOpenImmersion f.left`. It is quantified after the first conjunct, so the first
  conclusion does not depend on either of these extra hypotheses on f.

Dependency declarations read and reused:

- def-sc-discrete-valuation-ring: `IsDiscreteValuationRing`,
  Mathlib.RingTheory.DiscreteValuationRing.Basic (full class and uniformizer convention).
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme (full declarations and docstrings).
- def-pc-base-change: WeilConjectures.AlgebraicGeometry.BaseChangeConventions;
  its module docstring and `baseChange_morphism_projections` specify that scheme base
  change is `Limits.pullback` and morphism base change is `(Over.pullback _).map`.
  The recorded `Scheme.Modules.moduleBaseChange` is only its module-sheaf clause and is
  not misused as scheme base change. The source explicitly endorses these scheme APIs.
  The Mathlib declarations `Scheme.Hom.fiber`, `fiberι`, `Over.pullback`, and `Over.homMk`
  were also read in full.
- def-sbc-smooth-morphisms: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType and
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- def-weil-closed-immersion: `AlgebraicGeometry.IsClosedImmersion`,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion, used by `IsSeparated` from
  Mathlib.AlgebraicGeometry.Morphisms.Separated.
- def-weil-open-immersion: `AlgebraicGeometry.IsOpenImmersion`,
  Mathlib.AlgebraicGeometry.OpenImmersion.

All recorded proof-dependency modules that are stated are imported privately, including
Mathlib leaves through their source modules. The one currently unstated proof dependency,
lem-sfb-smooth-morphism-cotangent-isomorphism-etale, is cited in the proof docstring but
cannot yet be imported. It is not needed to express this statement, and is not a missing
statement prerequisite. There is no import cycle detected in the actual compile.
The declaration docstring carries all seven accepted proof steps and their dependency ids.

Edge cases checked before writing and again against the signature:

- Empty X and empty fibres: the first conclusion is vacuous where appropriate; `Dense`
  in an empty fibre is valid. No surjectivity or nonempty-fibre assumption is imposed.
  The second conclusion permits the empty open immersion.
- A nonempty smooth scheme may have empty special fibre (e.g. Spec F over Spec R);
  the fibrewise density condition remains meaningful and does not rule it out.
- U = top gives the immediate containment and reduces the second implication to the
  stipulated global open immersion. U empty cannot contain a nonempty generic fibre;
  flat openness then excludes a nonempty source with empty generic fibre.
- Points of local-ring dimension zero are included, as are the special-fibre component
  generic points of local-ring dimension one. The dimension is not the dimension of
  the whole scheme or the local topological dimension at x.
- Reducible/disconnected X and Z and varying smooth relative dimension are allowed;
  there is no integral, connected, equidimensional, proper, excellent or henselian binder.
- Relative dimension zero is allowed (the proof docstring treats determinant rank zero).
- All residue characteristics are allowed. Universes are explicit (`universe u`,
  `set_option autoImplicit false`); the canonical fraction field stays in the same universe.
- A map that is only generically invertible is not enough without the U-restriction:
  the usual scaling/dilatation examples fail the open-immersion condition at special
  component generic points. Nonseparated doubled-origin examples are excluded by the
  stated separatedness assumptions, not by an added hypothesis.

Searches for an existing statement (2026-10-24):

- msearch.py leanfinder: "A morphism between smooth separated schemes of finite type
  over a discrete valuation ring is an open immersion if it is an isomorphism on generic
  fibers and an open immersion on an open dense in both fibers". Eight hits: definitions
  of open/preimmersions, isomorphisms as surjective open immersions, and stalk criteria;
  no trait no-shrinking theorem.
- msearch.py leansearch: "A morphism between smooth schemes over a discrete valuation
  ring which is an open immersion on a fibrewise dense open containing the generic fibre
  is an open immersion". Eight analogous elementary immersion hits, no exact match.
- msearch.py loogle: "AlgebraicGeometry.IsOpenImmersion, AlgebraicGeometry.Smooth".
  Two hits: smoothness respects open immersions, and open immersions are smooth;
  neither states either conclusion of this node.
- msearch.py grep in Mathlib/AlgebraicGeometry:
  `birational|IsOpenImmersion.*[Dd]ense|[Dd]ense.*IsOpenImmersion`.
  Eight hits concerning birational rational-map modules, no trait criterion.
- rg in lean/WeilConjectures/AlgebraicGeometry and lean/Sheaf/AlgebraicGeometry for
  smooth/trait, birational/immersion, dense fibres and dimension-one patterns found
  related generic-density and local-dimension modules only; exact declaration-name
  searches `isOpenImmersion_of_smooth_trait|smooth_trait_birational_immersion` found none.
- rg over all lean/WeilConjectures and lean/Sheaf for the node id found no declaration;
  broader trait/fibre density searches likewise found no exact statement.

Source check: opened the primary BLR scan linked in the node, page index 120,
printed page 114, Theorem 5 and its final proof paragraph. It uses generic invertibility,
codimension-one control, a pulled-back top differential with no zeros, the relative
cotangent criterion and the birational open-immersion inference. The accepted node
extracts that argument for arbitrary smooth trait models, without a group structure;
its supplied seven-step proof supplies the generalization and empty-fibre cases.
Source link: https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf
No mathematical node fault or STATEMENT-DISPUTED issue found.

## Second reading by Q128

Performed a separate self-review by reopening the node and complete delivered Lean file
and checking the rendered signature against each clause above. This is not claimed as
an independent worker review: the dispatcher's explicit instruction prohibits starting
other agents, and the maintainer's independent delivery review is still required.

The re-reading checked that both X and Z retain smoothness, separatedness and finite type;
that `hdense` is density on each actual scheme fibre; and that `hgeneric` uses the fraction
field's canonical spectrum map, with the first pullback projection targeting X.
The map in the isomorphism hypothesis is `(Over.pullback _).map f`, hence retains f and
its compatibility over T; using an arbitrary isomorphism of generic fibres would have
been incorrect. Restriction composes `U.ι` before `f.left` in Lean's composition order.
The first conclusion remains before the quantification of f and its two hypotheses.
The chain dimension uses the stalk's prime-spectrum order. No mismatches were found;
no statement, dependency or definition changes were made in the second reading.
