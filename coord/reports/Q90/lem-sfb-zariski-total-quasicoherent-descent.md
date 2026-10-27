## Worker report

The delivery states `AlgebraicGeometry.ZariskiTotal.zariski_total_quasicoherent_descent`
in `Sheaf.AlgebraicGeometry.ZariskiTotalQuasicoherentDescent`. Its only theorem proof
is `sorry`. Every definition has explicit data. The original node is unchanged
except for `lean`; there are no new nodes or dependency repairs.

I read the item, all six statement dependencies and their recorded declarations,
the complete semisimplicial ringed total interface (including its canonical
transition and augmentation equations), the recorded scheme-derived category and
quasi-coherence definitions, and the source passages Stacks 0D7V
(`sites-cohomology.tex`, lemma-equivalence-unbounded-one) and 0DHF
(`spaces-simplicial.tex`, lemma-coh-descent-qcoh-unbounded-for-fppf-hypercovering,
particularly Ad (1)--(5)). The latter is used as the node's specified pattern for
the small Zariski specialization, not as a claim that this is an étale site.
The node's eight proof steps are reproduced in the theorem's docstring.

Clause-by-clause correspondence:

- Any scheme: `T : Scheme.{u}`. There is no Noetherian, separated, quasi-compact,
  quasi-separated, dimensional, characteristic, or boundedness hypothesis.
- A set-indexed open cover: `I : Type u`, `W : I → T.Opens`, and
  `hcover : ⨆ i, W i = ⊤`. Opens are the actual open subschemes `W i` with
  their existing `Scheme.Opens.ι` open inclusions; using opens gives the
  canonical representative of an arbitrary family of open subschemes. No
  `Nonempty I` or finiteness hypothesis is imposed. The universe `u` is the
  chosen common small bound of the schemes, sites, rings and index set;
  ordinary derived categories use `u + 1`, as in the recorded total interface.
- `T_n` is exactly `level W n`, the coproduct indexed by all
  `Fin (n.len + 1) → I`, of `(⨅ r, W (t r)).toScheme`.
  `intersection` uses the actual lattice intersection, not a chosen affine
  replacement. `augmentation` is `Sigma.desc` of the open inclusions.
- Faces use only `SemiSimplexCategory`: `face W a` restricts the tuple by
  `t ∘ SemiSimplexCategory.homEquiv a` and uses the canonical inclusion of
  its full intersection into that subtuple's intersection, followed by the
  coproduct injection. Thus the injection drops exactly the omitted indices;
  no degeneracy maps or truncation of the index category are introduced.
- The small ringed Zariski site is `site T`: objects `T.Opens`, its existing
  `Opens.grothendieckTopology`, and `T.sheaf : Sheaf _ CommRingCat`.
  Its ring and module carriers are the dependency's `Site.rings` and
  `Site.modules`; downstairs these are definitionally the shared
  `moduleRings T.toRingedSpace` and `SheafOfModules` carriers.
- `Model W` is a certificate for the specialization of the recorded
  `RingDiagram`/`Presentation`/`AugmentationPresentation`, not an arbitrary
  total category. `fibre` identifies the whole ringed site with
  `site (level W n.unop)`; `baseChange` pins the underlying diagram functors
  to inverse image of opens under the concrete face maps. `faceDirect`,
  `faceRing`, `augmentationDirect` and `augmentationRing` fix direct images
  to ordinary topological pushforward and the adjoint structural ring maps
  to the actual scheme morphisms' `c`. This includes the ring structure,
  not just the underlying topological maps. The total module category is
  therefore the dependency's ordinary sheaf-of-modules category on the
  actual total site, with its exact, jointly conservative evaluations.
  The theorem asserts existence of `M : Model W`; it does not assume such
  a model, and does not choose unspecified data from a sorry existence proof.
- Exact face and augmentation structure-module pullbacks are
  `Descent.exactFaces` and `Descent.exactAugmentation`. They concern the
  dependency's canonical scalar-extension pullbacks with its insertion
  normalizations. `exactDerived : IsIso M.total.pullback.epsilon` says that
  the left derived augmentation pullback is computed on every complex by
  the ordinary exact augmentation pullback.
- The ordinary unbounded categories are the dependency's `Site.D`, namely
  the actual localization `DerivedCategory`, with no `Plus`, degree bound,
  or condition on negative self extensions.
- The subcategory `L_cart` is `M.cartesianQCoh.FullSubcategory`.
  Its predicate is `M.presentation.IsCartesian E` conjoined with, for
  every component `n` and every integer `q`, quasi-coherence of
  `H^q(e_n E)`. The cast along `M.fibre n` only transports the existing
  sheaf-of-modules carrier to its identified scheme; the predicate is
  Mathlib's actual `SheafOfModules.IsQuasicoherent`. The cartesian clause
  is exactly invertibility of all the dependency's constructed derived
  transitions, not merely an independently specified diagram in homotopy
  categories.
- The downstairs predicate is the dependency's unchanged
  `@schemeDerivedQCohProperty T (site T).hasDerived`; its full subcategory
  is precisely `D_QCoh(O_T)`, using the same standard localization as the
  total interface. No private definition of quasi-coherence or `D_QCoh`
  is made.
- The augmentation-induced equivalence is `Descent.equivalence`.
  `forward` identifies its functor, on actual objects and all morphisms,
  with the inclusion followed by `M.total.pullback.derived`. The stored
  `shift` and `triangulated` assert that it is a triangulated functor
  between the full subcategories, with their inherited triangulations
  provided by `sourceTriangulated` and `targetTriangulated`.
- Its inverse is the restriction of the ambient `Ra_*`: `pushforward`
  is an ambient functor, and `beta`/`rightDerived` assert the universal
  right-derived property for the actual `M.total.map.modules`, with the
  homotopy-category localization and no boundedness restriction.
  `backward` identifies the equivalence's inverse with its restriction.
- `adjunction` is the ambient derived adjunction.
  `unit_model` and `counit_model` give the two standard derived-adjunction
  normalization equations on every homotopy object, using the original
  module adjunction, its induced homotopy adjunction, `epsilon` and `beta`.
  These exclude an arbitrary adjunction with arbitrarily chosen unit and
  counit. `unit_iso` holds for every downstairs quasi-coherent derived
  object and `counit_iso` for every upstairs cartesian quasi-coherent
  total derived object. Both are ambient isomorphism assertions.
- The conclusion `∃ M : Model W, Nonempty (Descent M)` asserts all these
  constructions and properties simultaneously. The only inputs are the
  scheme and its open cover, exactly as in the node. The certificate
  structures contain output data and their defining characterizations;
  they are not extra hypotheses or hollow definitions.

Statement dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Scheme.Opens` and the existing open-subsheme interface.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  canonical open inclusions are used through the existing `Scheme.Opens.ι`.
- `def-weil-size-convention` is metatheoretic, with no Lean declaration:
  explicit `u`, small Zariski sites and `Site.hasDerived` implement it.
- `Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory`:
  `CategoryTheory.SemisimplicialRingedTotal.Site`, `RingDiagram`,
  `Presentation`, `Presentation.IsCartesian`, `Augmentation`,
  `AugmentationPresentation`, and their exact evaluation and normalized
  pullback interfaces. These are used directly, not replaced by copies.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, `schemeDerivedQCohProperty`,
  `schemeDerivedQCohCategory` (the statement uses the defining predicate
  and its `FullSubcategory`, definitionally the recorded category).
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` exposes the recorded
  `SheafOfModules.IsQuasicoherent`; only the node's quasi-coherence clause
  is needed, not finite type or coherence.

Every available proof-dependency module is imported plainly, including open
restriction, quasi-coherent kernel/cokernel/extension closure, module gluing,
Grothendieck modules, enough injectives, the evaluation free adjoint, the
module/abelian cohomology comparison, affine vanishing, and the total-site
pseudofunctor. The proof-only nodes
`lem-sfb-zariski-cech-module-derived-unit` and
`lem-sfb-ringed-unbounded-descent-criterion` currently have no Lean record;
there is no missing notion in this statement depending on them. Their eventual
proof imports remain for the maintainer to add when stated, as required by the
stage rules. No new postponed theorem is introduced for either proof step.

Edge cases checked against the formulas before writing the theorem:

- The empty index set is allowed: its cover condition forces `T` empty;
  every tuple index type is empty, hence each `level` is the empty coproduct.
  Module and derived categories on those empty schemes are the zero category.
- Empty tuple intersections remain summands; they are not deleted or assumed
  nonempty, and the face formula still gives their unique open inclusion.
- Repeated indices remain distinct tuple labels. In particular the repeated
  triple used to force the diagonal gluing transition to be the identity is
  present; face-only indexing does not discard it.
- In degree zero the intersections have one entry and the augmentation is the
  corresponding open inclusion. A cover with a single member equal to `T`
  has the expected identity descent. Multiple copies of `T` are also allowed.
- The zero complex belongs to both full subcategories; all integer cohomology
  degrees are quantified, including arbitrarily negative degrees.
- No affine intersection assumption is built into `intersection`, `Model`, or
  `Descent`; non-quasi-separated schemes and infinite covers are included.

Searches actually run with `batch2/msearch.py`, group Q90, this item:

- LeanFinder: `Unbounded quasi coherent derived complexes descend along a
  Zariski open cover to cartesian objects of the semisimplicial ringed total
  site` returned eight hits, headed by `SheafOfModules.QuasicoherentData.coversTop`
  and Mayer--Vietoris-square declarations; no ordinary unbounded total descent.
- Loogle: `SheafOfModules, DerivedCategory` returned `OK 0 hit(s)`.
- LeanSearch: `Zariski Cech cover derived quasi coherent descent unbounded total
  site` returned eight hits: underived quasi-coherence data/predicates,
  `Scheme.Cover` and `Scheme.zariskiPretopology`; none states this theorem.
- Mathlib grep: `zariski.*descent|cech.*derived|Cech.*[Tt]otal` returned
  `OK 0 hit(s)`.
- Repository `rg` searches for `zariski.*(total|cech)|total.*zariski`,
  `Cech|cech|SemiSimplex|semisimplicial`, and the proposed namespace/theorem
  in `lean/Sheaf`, `lean/WeilConjectures`, and `dag/lean_names_upstream.json`
  located the generic total interfaces and explicit ordinary Čech complexes,
  but no statement of this unbounded equivalence or concrete ringed-Zariski
  Čech specialization. The item-id search of `lean/WeilConjectures` had no hit.
  The proposed declaration names had no hit before this delivery.

No statement fault or dispute was found. No statement correction is made.

## Second reading by Q90

I reopened the node and the complete module for a separate clause-by-clause
reading after compilation. This is the worker's second pass; the dispatcher
explicitly prohibits starting another agent, and the maintainer supplies the
independent delivery review.

The input really is just `T`, `I`, `W`, `hcover`; `Model` and `Descent` occur
in the existential conclusion. The concrete `Sigma.desc` face formula has the
correct variance: `a : m ⟶ n` in the opposite semi-simplex category gives
`level W m.unop ⟶ level W n.unop`, and inverse image of opens is the diagram's
contravariant transition. The ring-map equations use `c` of those very same
scheme morphisms, so arbitrary rings or arbitrary augmentation maps are not
substituted. The fibre equality identifies the topology and ring as well as
the category, which is needed for the component quasi-coherence cast.

I checked the distinction between `L` and `L_cart`: the stored predicate is
exactly their intersection, quantified over every component and every integer
cohomology degree. The source uses the existing `schemeDerivedQCohProperty`;
there is no finite-type requirement. The equivalence is between full
subcategories of the actual ambient localizations, with functor isomorphisms
fixing forward pullback and inverse pushforward on morphisms as well as
objects. The ambient right-derived universal property and the two adjunction
normalizations are present, so the unit and counit assertions concern the
canonical derived adjunction, rather than an unspecified equivalence.
The triangulated property is explicit. The zero/empty/repeated-index cases and
absence of a lower bound were rechecked. No mismatch requiring a node change
was found. During elaboration I corrected the topology namespace to the
existing `Opens.grothendieckTopology` and made the target ring explicit in
the transported quasi-coherence predicate; these were type annotations, not
changes to mathematical content.

Validation: prescribed `scompile.py` compiled the module in its sandbox and
at its actual library module path cleanly before adding the available plain
proof imports; final compilation and delivery preflight are recorded below.

Final validation: `scompile.py Q90 lem-sfb-zariski-total-quasicoherent-descent`
compiled the final module, including all the available proof imports, both in
its sandbox and at its real library module path, with no errors or warnings.
`deliver2.py Q90 lem-sfb-zariski-total-quasicoherent-descent --no-push`
reported `OK (dry run): commit 7985eea7a58 passes the preflight and compiles;
nothing pushed`. No timeout override or local/global build was used.
