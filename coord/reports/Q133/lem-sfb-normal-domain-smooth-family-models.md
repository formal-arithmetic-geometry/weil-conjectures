## Worker report

The delivery states `AlgebraicGeometry.exists_normal_domain_smooth_family_models` in
`Sheaf.AlgebraicGeometry.NormalDomainSmoothFamilyModels`. There is one theorem and its whole
proof is `sorry`, as required at stage 2. There are no new definitions, auxiliary axioms,
node corrections, or dependency repairs. Only the item's `lean` record changes.

I read the complete node, all eight statement dependencies and their recorded declarations,
the seven proof steps, the stage brief, and delivery-errors H. Source readings were Stacks
`pione.tex`, lemma-extend-covering-general (0EZJ), the normal approximation and family descent
paragraphs; `more-morphisms.tex`, lemma-nr-geom-connected-components-constructible (055I);
and `limits.tex`, lemma-limit-contained-in-constructible (05F4). I also read the current
blueprint unit `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/_section.md`. The item is supporting unpointed approximation,
not that unit's target statement. The proof docstring includes all seven node proof steps,
including the constructible count-one locus that replaces the pointed argument in 0EZJ.

Hypotheses and conclusion, clause by clause:

| Node clause | Lean rendering |
| --- | --- |
| R is an integrally closed integral domain | `(R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]` |
| S is Spec R; X is a scheme and f is a morphism to S | `{X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))` |
| f is smooth | `[Smooth f]` |
| f is separated, i.e. its diagonal is a closed immersion | `[IsSeparated f]`; Mathlib's class has precisely `IsClosedImmersion (pullback.diagonal f)` |
| f is finitely presented | `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`; this is the comparison clause of def-sbc-locally-finite-presentation |
| Nonempty geometrically connected residue-field fibres after every field extension | `[GeometricallyConnected f]`; this uses `ConnectedSpace` on every field-valued base change, and `ConnectedSpace` includes `Nonempty`. Mathlib's `GeometricallyConnected.iff_geometricallyConnected_fiber` identifies the residue-field formulation |
| A small nonempty directed set I | `I : Set (Subalgebra ℤ R)`, with `I.Nonempty` and `DirectedOn (· ≤ ·) I`; its subtype has the inherited inclusion partial order |
| Subrings A_i of R | For `i : I`, `A_i` is `i.val`. Integer subalgebras and unital subrings encode the same subrings, since integer scalars belong to every unital subring |
| Each A_i is an integrally closed domain finitely generated over Z, hence Noetherian | `∀ i : I, IsDomain i.val ∧ IsIntegrallyClosed i.val ∧ i.val.FG ∧ IsNoetherianRing i.val` |
| R is the union of the A_i | `∀ r : R, ∃ i : I, r ∈ i.val`; the reverse inclusion is part of being a subalgebra of R |
| The base schemes are Spec A_i | `D : (↥I)ᵒᵖ ⥤ Scheme.{u}` and `eA : ∀ i, D.obj (op i) ≅ Spec (CommRingCat.of i.val)` |
| For j ≥ i the ring map is inclusion, and the scheme map is the induced spectrum map | The first equality for `D.map (homOfLE h).op` conjugates it by `eA` to `Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)` |
| The maps S → S_i are the canonical ones | `α` is the cone natural transformation; `α.app (op i) ≫ (eA i).hom = Spec.map (CommRingCat.ofHom i.val.val.toRingHom)` |
| All base stages are Noetherian and quasi-separated, and all S → S_i are dominant | `∀ i, IsNoetherian (D.obj i) ∧ QuasiSeparatedSpace (D.obj i) ∧ IsDominant (α.app i)` |
| Every base transition is affine | `∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a)` |
| A chosen initial model at i_0 | `∃ (i₀ : I) (X₀ : Scheme.{u}) (p : X₀ ⟶ D.obj (op i₀))` |
| X is the base change of X_0, by an S-isomorphism | `e : X ≅ pullback p (α.app (op i₀))` and `e.hom ≫ pullback.snd p (α.app (op i₀)) = f` |
| The initial model is smooth, separated, finitely presented, with nonempty geometrically connected fibres | `Smooth p ∧ IsSeparated p ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ QuasiSeparated p ∧ GeometricallyConnected p` |
| The initial model is Noetherian and quasi-separated | `IsNoetherian X₀ ∧ QuasiSeparatedSpace X₀` |
| Models are defined for each i ≥ i_0 by canonical base change | `j : Over (op i₀)` is exactly a later index together with its unique arrow to `op i₀`; `(baseChangeDiagram D p).obj j` is definitionally `pullback p (D.map j.hom)` |
| Every later f_i has all the required properties | The universal conjunction on `j : Over (op i₀)` lists `Smooth`, `IsSeparated`, `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated`, `GeometricallyConnected` of `pullback.snd p (D.map j.hom)` |
| All later family stages are Noetherian and quasi-separated | The last two conjuncts of the same universal statement are `IsNoetherian` and `QuasiSeparatedSpace` of the diagram object |
| Every family transition is canonical | The existing `baseChangeDiagram` defines its maps with `pullback.map`, using identity on X₀ and `D.map a.left` on the base; there are no arbitrary family transition witnesses |
| Every family transition is affine | `∀ {j k} (a : j ⟶ k), IsAffineHom ((baseChangeDiagram D p).map a)` |
| S is the scheme limit on the tail | `Nonempty (IsLimit ((Cone.mk (Spec (CommRingCat.of R)) α).whisker (Over.forget (op i₀))))` |
| X is the scheme limit on the tail, with its canonical projections | `Nonempty (IsLimit ((baseChangeCone D (Cone.mk _ α) p).extend e.hom))`; the canonical pullback cone is transported along the supplied S-isomorphism |
| Universe contains R and X | The single explicit `universe u` contains `R : Type u`, `X : Scheme.{u}`, the subtype of subalgebras, its opposite and Over category, and both scheme diagrams |
| No section, group structure, or invertible module | None occurs among the binders or conclusions |

The `eA` witnesses are only identifications of the diagram objects with the specified affine
spectra. Both the transition maps and all cone legs are fixed by explicit compatibility
equations, so the choice adds no geometric freedom. One could take literal spectra and
identity isomorphisms. Likewise the pullback along the identity at i₀ is canonically X₀;
the existing `baseChangeDiagram` convention retains that canonical isomorphism.

Dependency declarations used, with their recorded modules:

| Dependency | Module and declaration |
| --- | --- |
| def-weil-pbc-normal-ring | `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`, and `IsDomain`, as prescribed by its inline normal-domain record |
| def-weil-affine-spectrum | `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec` and `Spec.map` |
| def-pc-scheme | `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and `Scheme.Hom` |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth` |
| def-sbc-locally-finite-presentation | `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `AlgebraicGeometry.LocallyOfFinitePresentation` |
| def-weil-residue-field | `Mathlib.AlgebraicGeometry.ResidueField`, `Scheme.residueField` and `Scheme.Hom.residueFieldMap`; used through the existing geometric-connectedness fibre interface, not duplicated |
| def-pc-fibre-product | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback`, `pullback.snd`, and the canonical `pullback.map` construction |
| pqf-def-locnoeth | `Mathlib.AlgebraicGeometry.Noetherian`, `IsLocallyNoetherian`, included in `IsNoetherian` together with compactness |

The already stated proof dependencies are imported without `public`, except that
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` is public because its
existing `AlgebraicGeometry.baseChangeDiagram` and `baseChangeCone` also occur in the
signature. Its `Scheme.exists_pullback_hom_of_isLimit` is the recorded spreading-out input.
Other proof imports are `WeilConjectures.RingTheory.NormalFiniteTypeSubalgebraExtension`,
`WeilConjectures.AlgebraicGeometry.Morphisms.AffineLimitSmoothStage`,
`WeilConjectures.AlgebraicGeometry.ExistsIsSeparatedOverPullbackMap`,
`Sheaf.AlgebraicGeometry.GeometricComponentCountBaseChange`,
`WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible`, and
`Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure`. The remaining proof
nodes without recorded modules do not require guessed imports. No proof-import cycle
was found by the prescribed server compilation.

Edge cases checked: the zero ring is excluded exactly by `IsDomain R`; Spec R is nonempty.
The empty family is excluded by `GeometricallyConnected`, exactly as required, rather than
accepted by a vacuous preconnectedness predicate. A disconnected fibre fails the same
hypothesis. A field base, characteristic p, characteristic zero, and the identity family
need no different statement or invertibility assumptions. I cannot be empty; a singleton
index and identity transitions are allowed when the data already descend. The tail contains
its initial object in the order direction and is nonempty. No finite index, countability,
finite dimension, relative dimension, or section restriction has been imposed. All variables
and the sole universe are explicitly bound. The limit witnesses assert the full universal
property in Scheme, rather than merely an isomorphism of sets or affine charts.

Searches for existing declarations, before writing:

- `msearch.py ... leanfinder`, query: "A smooth separated finitely presented scheme over a
  normal domain descends to a directed system of normal finitely generated integer
  subalgebras with geometrically connected nonempty fibres". Eight hits: affine smooth
  algebra descent and normalization machinery, no theorem with these scheme-limit clauses.
- `msearch.py ... loogle`, query:
  `AlgebraicGeometry.GeometricallyConnected, AlgebraicGeometry.Scheme.exists_pullback_hom_of_isLimit`.
  No hits; the public Loogle service did not know the project's latter identifier.
- `msearch.py ... grep`, query `normal.*model|Normal.*Model|GeometricallyConnected`, restricted
  to `AlgebraicGeometry`. Five hits, all in `Mathlib/AlgebraicGeometry/Geometrically/Connected.lean`.
  This located the exact existing fibre property, which was reused.
- `msearch.py ... leansearch`, query: "normal domain smooth scheme finite presentation directed
  finitely generated subalgebras descent geometrically connected fibres". Eight hits, mostly
  `Algebra.Smooth.exists_subalgebra_fg` and standard-smooth finite-presentation results;
  none states the item.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, normal-family and normal-subalgebra patterns:
  found `NormalPointedFamilyApproximation`, `NormalNoetherianRefinement`, and
  `NormalFamilyGenericLimit`. I read them: the family approximations require a section,
  and the base refinement does not assert this unpointed arithmetic-subring family statement.
- Exact `rg` for `exists_normal_domain_smooth_family_models` and
  `normal-domain-smooth-family-models` in both source roots found no declaration; the only
  item reference is in the downstream `NormalBaseFibrewiseLineLocality` proof docstring.
- Direct Mathlib/source reads of `Subalgebra.inclusion`, `Spec.map`, `GeometricallyConnected`,
  `Scheme.residueField`, `IsSeparated`, `IsNoetherian`, and `baseChangeDiagram` supplied all
  required constructions. No missing notion required a new node.

Validation: the first version compiled cleanly in both sandbox and final library module
mode through `scompile.py` (4.2 s and 3.1 s). The final signature additionally states the
initial model's Noetherian and quasi-separated properties explicitly. Its final compile,
preflight, and delivery results are recorded below after running the wrappers.
No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q133

This is a separate rereading in the same worker session, not an independent agent review:
the dispatcher explicitly forbids starting other agents, and the maintainer independently
reviews this delivery. With the original node and the Lean file both open, I checked every
row above again, especially arrow orientation, nonemptiness, canonical maps, and both limits.

The equations use `(homOfLE h).op`, so j ≥ i gives S_j → S_i and the underlying ring map
A_i → A_j. `α` becomes precisely Spec of A_i → R after composing with `eA i`. The equality
for `e.hom` is over S, not just an abstract scheme isomorphism. `Over (op i₀)` includes all
and only the tail stages; its canonical base-change functor fixes both objects and maps.
`Cone.extend e.hom` has vertex X and its structure map agrees with f by the displayed
equality. Both `IsLimit` clauses concern those exact cones. The geometric condition uses
`ConnectedSpace`, not `PreconnectedSpace`, so empty fibres cannot slip through.

One presentation omission found in rereading was that Noetherian and quasi-separated X₀
were only implied via its identity-base-change stage. I added `IsNoetherian X₀ ∧
QuasiSeparatedSpace X₀` explicitly. No hypothesis, conclusion, or node text otherwise changed.
The mathematical assertion matches the node, using canonical isomorphisms for spectrum
and identity-pullback identifications; no extra structures or existence hypotheses occur.

Final validation: `scompile.py Q133 lem-sfb-normal-domain-smooth-family-models` accepted
both module-mode checks with no errors or unexpected warnings; the final library module
compiled in 3.1 s. `deliver2.py Q133 lem-sfb-normal-domain-smooth-family-models --no-push`
printed `OK (dry run): commit fe974316c54 passes the preflight and compiles; nothing pushed`.
The independent maintainer review remains part of landing, as specified by the dispatcher.
