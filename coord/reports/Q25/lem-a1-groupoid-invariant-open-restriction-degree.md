## Worker report

The delivery states `AlgebraicGeometry.IsGroupoidScheme.existsUnique_invariantOpen_restriction_degree`
in `Sheaf.AlgebraicGeometry.GroupoidInvariantOpenRestrictionDegree`, with one postponed proof.
It introduces no definitions, auxiliary nodes, dependency repairs, or statement corrections.
Only the item's `lean` record changes. No mathematical fault or disputed statement was found.

Sources read: `literature/stacks-project/groupoids.tex`, the full statement and omitted proof
of `lemma-restrict-groupoid` (02VB), `definition-invariant-open` and the following paragraph
(03BC), and `lemma-finite-locally-free-disjoint-free` with its proof (03BI).
The paragraph after 03BC identifies the restricted arrow scheme with the common inverse-image
open; the end of 03BI identifies the target morphism with the source by inversion.
The supplied node expands these passages without imposing the affine or finite hypotheses
of the rank-stratification application.

Hypotheses and objects, in order:

- Schemes U and R: `{U R : Scheme.{u}}`, with explicit universe `u`.
- Source, target, identity, inverse, and composition: `(s t : R ⟶ U)`, `(e : U ⟶ R)`,
  `(i : R ⟶ R)`, `(c : pullback s t ⟶ R)`.
- These maps form a groupoid: `(hG : IsGroupoidScheme s t e i c)`. This is exactly the
  dependency's recorded structure, with all endpoint, unit, inverse and associativity laws
  on points of every test scheme. Its signature and complete docstring were read.
- The open W: `(W : U.Opens)`, with scheme `W.toScheme` and inclusion `W.ι`.
- Invariance: `(hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W)`, equality of opens, equivalently equality of their
  underlying open sets. The notation is Mathlib's inverse image of opens.
- V, j and k are the actual prescribed objects `(s ⁻¹ᵁ W).toScheme`, `W.ι`, and
  `(s ⁻¹ᵁ W).ι`. Equality hW identifies this V with the target inverse-image open too.
  These are not independently chosen schemes or arbitrary inclusion maps.

Conclusions, clause by clause:

- Unique restricted source, target, identity, inverse and composition are the five nested
  `∃!` binders `sW`, `tW`, `eW`, `iW`, `cW`. Each has precisely the displayed domain and
  codomain in the node; composition has domain `pullback sW tW`. Uniqueness is of the
  compatible restricted maps; dependency of the composition domain on source and target
  is handled by the order of the binders.
- The restricted data form a groupoid: `IsGroupoidScheme sW tW eW iW cW`.
- The source and target commuting squares are the existentially bound proof witnesses
  `hs : sW ≫ W.ι = (s ⁻¹ᵁ W).ι ≫ s` and
  `ht : tW ≫ W.ι = (s ⁻¹ᵁ W).ι ≫ t`. Quantifying proofs supplies these equations, rather
  than assuming them as new hypotheses. Proof irrelevance prevents extra choices here.
- The identity and inverse commuting squares are
  `eW ≫ (s ⁻¹ᵁ W).ι = W.ι ≫ e` and
  `iW ≫ (s ⁻¹ᵁ W).ι = (s ⁻¹ᵁ W).ι ≫ i`.
- The composition square is
  `cW ≫ (s ⁻¹ᵁ W).ι =
    pullback.map sW tW s t (s ⁻¹ᵁ W).ι (s ⁻¹ᵁ W).ι W.ι hs ht ≫ c`.
  The right-hand map is the canonical lambda from the node: the recorded Mathlib
  `pullback.map` induced by k on both factors and j on the base. Its full signature and
  definition were read, including the orientation of its two square witnesses.
- The involutive isomorphism is `IsIso iW ∧ iW ≫ iW = 𝟙 (s ⁻¹ᵁ W).toScheme`.
- Identification over W is `iW ≫ sW = tW`. The inverse and base identity are already
  specified by involutivity and the shared codomain, so no additional arbitrary isomorphism
  is substituted for the restricted inverse.
- Every nonnegative integer degree is `∀ r : ℕ`; the conclusion is
  `sW.IsFiniteLocallyFreeOfDegree r → tW.IsFiniteLocallyFreeOfDegree r`.
  The recorded upstream class includes finiteness, flatness, local finite presentation,
  and fibre-section dimension r, so none of these components is dropped.
- W may be empty: there is no nonemptiness binder. There is no affineness assumption and
  no finiteness or flatness assumption on the original s or t.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`; read their
  complete structure signatures and docstrings. This module is public through the groupoid
  dependency.
- `Sheaf.AlgebraicGeometry.GroupoidScheme`: `AlgebraicGeometry.IsGroupoidScheme`, imported
  publicly and used twice, for original and restricted data.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`, public
  through `Mathlib.AlgebraicGeometry.Restrict`; the canonical `Scheme.Opens.ι` has this
  instance. Read the recorded abbreviation and the restriction constructions.
- `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Opens.toScheme`, `Scheme.Opens.ι`, and
  inverse image of opens; imported publicly.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.map`,
  projections and universal map, public through the groupoid dependency's import of
  `Mathlib.AlgebraicGeometry.Pullbacks`. All displayed fibre products are the recorded ones.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFreeOfDegree` and its parent `Scheme.Hom.IsFiniteLocallyFree`,
  imported publicly. Read their exact classes and docstrings, including `fiberDegree_eq`.

Proof dependencies are available through these same imports: `IsOpenImmersion.lift`,
`lift_fac`, `lift_uniq`, and `IsOpenImmersion.mono` in OpenImmersion, and `IsFinite`, `Flat`,
`LocallyOfFinitePresentation` publicly imported by FiberDegree. Their source signatures
were read. The seven numbered paragraphs of the theorem docstring give all seven steps
of the node proof and name the relevant DAG dependencies. No theorem is proved here.

Edge cases checked mathematically before writing:

- W empty forces V empty, and the five maps and their fibre product are maps of empty
  schemes. Isomorphism and uniqueness hold and the degree class is vacuous over W.
- r = 0 is included. Over a nonempty W the groupoid identity prevents the source from
  having empty fibres, so this implication has an impossible premise; over empty W both
  degree-zero classes hold. No positivity hypothesis is warranted.
- W equal to the whole object scheme returns the original operations up to their canonical
  open-scheme identifications. The inverse remains involutive.
- The source and target may be nonaffine and need not be finite locally free. Only the
  restricted source degree is conditional in the conclusion, as required.
- All objects live in an arbitrary explicit universe u, matching the dependency interface;
  no index-size restriction or auto-bound implicit is introduced.

Searches actually run, through the prescribed Q25/item wrapper:

- LeanFinder: `Restriction of a groupoid scheme to an invariant open and inversion transport
  of finite locally free degree`. Eight hits, including `morphismRestrict`,
  `IsFinite.instMorphismRestrict`, `morphismRestrictRestrict` and
  `instIsIsoSchemeMorphismRestrict`. These restrict individual morphisms; none gives the
  groupoid laws, uniqueness of its five operations and degree comparison together.
- Loogle: `"Groupoid", "restrict"`. Five hits, all manifold structure-groupoid restriction
  or restriction-closed groupoid results. No internal groupoid scheme result.
- Mathlib grep: `groupoid.*(restrict|invariant)|IsGroupoidScheme`. Twenty-five hits, all in
  manifold local invariant properties and structure groupoids; no scheme result.
- Local `rg` for `groupoid.*(restrict|invariant)|IsGroupoidScheme|invariantOpen` in
  `lean/Sheaf/AlgebraicGeometry` and `lean/WeilConjectures`. The landed groupoid definition,
  invariant-rank-strata theorem and other groupoid applications were found, but none is
  this unrestricted invariant-open theorem. The rank-strata theorem requires affine input
  and finite locally free original structure morphisms and does not assert uniqueness.
- `grep -rn 'lem-a1-groupoid-invariant-open-restriction-degree' lean/WeilConjectures`:
  no match. The proposed declaration is new, while all its notions are existing ones.

Validation: scompile.py compiled both the sandbox probe and the library module successfully
(18.9 seconds and 6.7 seconds respectively), with no errors or unexpected warnings.

## Second reading by Q25

The dispatcher expressly prohibits starting another agent; this is a second reading by
this worker, not a claim of an independent review. The maintainer's delivery review remains
independent. I reread the node alongside the completed module and checked the five dependent
unique binders, the exact source/target square orientations, the canonical pullback map and
all remaining conjuncts against the node. In particular, lambda uses k twice and j on the
base, the inverse equation uses the restricted inverse itself, and r ranges over all natural
numbers. I checked that hG and hW are the only mathematical assumptions beyond the objects
and maps, and that the finite locally free degree class is the upstream recorded one.
No mismatch was found and no source statement was changed. The node copy preserves all
original fields other than `lean`, with its signature copied verbatim from the module.
