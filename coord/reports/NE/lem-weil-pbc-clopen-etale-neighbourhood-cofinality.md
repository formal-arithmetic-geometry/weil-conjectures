## Worker report

The module `Sheaf.AlgebraicGeometry.ClopenEtaleNeighbourhoodCofinality` states
`AlgebraicGeometry.clopen_etale_neighbourhood_cofinality`, with its entire proof
`sorry`. No definition or additional node is needed, and the natural-language
statement and dependencies are unchanged.

Hypotheses, matched individually:

- The separably closed field is `(K : Type v) [Field K] [IsSepClosed K]`
  (own universe; maintainer review fix, see below).
- The commutative K-algebra is `(C : Type u) [CommRing C] [Algebra K C]`.
  The scheme E is written explicitly as `Spec (.of C)` throughout.
- For every prime, the structural map is an isomorphism: `hlocal` says
  `∀ p : PrimeSpectrum C, Function.Bijective (algebraMap K
  (Localization.AtPrime p.asIdeal))`. This is bijectivity of the specified
  structural ring map, not existence of an arbitrary field isomorphism.
- The clopen basis hypothesis is `hbasis`: every open U and x in U admit an
  open W that is closed, contains x, and satisfies W ≤ U. Openness is carried
  by `Scheme.Opens`; it is not an extra hypothesis on W.
- The fixed geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
  and `zbar : Spec (.of Ω) ⟶ Spec (.of C)`. The point z is a
  `PrimeSpectrum C`, and `hz : zbar default = z` records lying over z.
  The use of default is the unique point of the field spectrum. There is no
  constraint that Ω be K or a selected algebraic closure, and no extra
  K-algebra structure on Ω is required. The shared ambient universe is the
  convention of schemes and the recorded geometric-point API; u is arbitrary.

Conclusions, matched individually:

- The first conjunct quantifies over every object V of
  `(Scheme.pointSmallEtale zbar).fiber.Elements`, exactly the recorded
  pointed-neighbourhood category. It supplies an open W with `IsClosed`,
  `z ∈ W`, a marked lift w and a morphism b to V's underlying scheme.
  `w ≫ W.ι = zbar` is the factorization; `b ≫ V.1.hom = W.ι` says b
  is an E-morphism; `w ≫ b = V.2.left` is the pointed equation. The lift
  through W is unique because its inclusion is a monomorphism; quantifying
  the lift existentially does not introduce any choice of marking.
- The second conjunct quantifies over V, both clopen neighbourhoods W₁,W₂,
  their lifts w₁,w₂, and both E-morphisms b₁,b₂. It assumes exactly their
  base equations and pointed equations. The witness W₃ is closed and open,
  contains z and has inequalities `h₃₁ : W₃ ≤ W₁`, `h₃₂ : W₃ ≤ W₂`.
  Thus it lies in their intersection. Equality after composition with the
  canonical `Scheme.homOfLE` maps is equality of the restricted scheme
  morphisms, not just equality of maps of points.
- The third conjunct is `Functor.Initial` for the `ObjectProperty.ι`
  inclusion of the full subcategory of pointed neighbourhoods whose
  structural morphism is an open immersion with closed image. An open
  immersion identifies its source canonically over E with the open
  subscheme of its image. Its marked point ensures this image contains z.
  Closedness makes it a clopen neighbourhood. Conversely every clopen
  open-subscheme inclusion is such an object, with its unique marking.
  Every map over E between two open immersions is the unique inclusion
  of their image opens. Thus this is the clopen pointed subsystem, expressed
  with its isomorphic representatives, and is equivalent over the whole
  neighbourhood category to the poset of literal clopen opens containing z.
  Initiality of this inclusion is precisely the node's assertion and is
  unchanged by using these representatives.
- The fourth conjunct ranges over ALL clopen W, not only those containing z.
  It supplies `e : C`, `IsIdempotentElem e`, and equality with
  `PrimeSpectrum.basicOpen e`. The isomorphism
  `i : W.toScheme ≅ Spec (.of (Localization.Away e))` identifies the open
  subscheme with Spec C_e. The final equation compares `i.hom` followed by
  the spectrum of the structural localization map with `W.ι`, so this is
  the required identification over E, not just an abstract scheme isomorphism.

Dependency declarations read and used:

- `def-pc-separably-closed`: `Mathlib.FieldTheory.IsSepClosed`, `IsSepClosed`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map`.
- `def-weil-geometric-point`: `Mathlib.FieldTheory.IsAlgClosed.Basic`,
  `IsAlgClosed`; also read `Scheme.SpecToEquivOfField` in
  `Mathlib.AlgebraicGeometry.ResidueField` for its point interpretation.
- `def-weil-pbc-pointed-etale-neighbourhoods`: its Mathlib match,
  `Functor.Elements` and `categoryOfElements` from `Mathlib.CategoryTheory.Elements`
  on the fiber of `Scheme.pointSmallEtale` from
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`. The objects contain an
  étale object and an Over morphism marking it; arrows preserve the marking.
  No replacement category is defined. The upstream `Scheme.Hom.Nbhd`
  abbreviation in `SplitNeighborhood.lean` was also read and is exactly
  this same type; importing the finite splitting machinery is unnecessary.
- `lem-weil-pbc-initial-functor-limit`: its Mathlib match `Functor.Initial`
  in `Mathlib.CategoryTheory.Limits.Final`, whose comma categories are
  `CostructuredArrow`. This is initiality, with arrows from the clopens to V.

The proof plan is transcribed in the declaration docstring, including all eight
steps and their node citations. Published proof dependencies are imported:
`WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts` and
`Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations`. The additional
proof import `Mathlib.Algebra.Category.Ring.FinitePresentation` supplies the
recorded filtered-colimit factorization match. Other Mathlib proof dependencies
are available through the étale-point imports: idempotents and basic opens,
affine open localization, open-immersion lifts, and the affine étale criterion.
No unavailable proof dependency is restated, and no import cycle is introduced.

Edge cases checked:

- C = 0: there is no z and no geometric point, so the pointed assertion is
  vacuous; no nontriviality hypothesis on C was added.
- C = K and finite products of K: the marking can select any factor and Ω
  can be any algebraically closed field carrying the given point.
- Locally constant K-valued functions on a profinite space: points need not
  be open. The hypotheses remain the clopen basis and the actual stalk-map
  bijectivity, with no discrete or finite restriction on E.
- Empty clopen: retained in the final universal clause, with e = 0 and its
  zero-ring localization. Whole spectrum: e = 1. Empty opens cannot be
  neighbourhood witnesses since the statement explicitly requires z ∈ W.
- Two maps into a nonseparated étale V: equalization is after restriction,
  with no separation assumption. It is not global equality.
- The proof's zero-generator presentation has empty product 1; all fields
  may have arbitrary characteristic and K need only be separably closed.

Searches (2026-10-17):

- `msearch.py ... leanfinder "Clopen neighborhoods are initial among pointed
  etale neighborhoods when all local rings are a separably closed field"`:
  eight hits about the étale locus and `Scheme.Etale`; no matching theorem.
- `msearch.py ... loogle '"Etale", "IsClopen"'`: zero hits.
- `msearch.py ... grep 'clopen.*etale|etale.*clopen|pointed.*neigh'
  AlgebraicGeometry`: zero hits in Mathlib's AlgebraicGeometry directory.
- `msearch.py ... leansearch "Clopen pointed etale neighborhoods are cofinal
  in the etale neighborhoods of a geometric point with separably closed
  local rings"`: eight hits on idempotent basic opens, the clopen basis,
  and the étale locus; none states the refinement/equalization/initiality.
- `rg` of upstream WeilConjectures for clopen neighbourhoods found finite
  split neighbourhood constructions and their stalk uses, not this theorem.
  Searching the exact node id in that tree found no declaration.
- `rg` of `lean/Sheaf` for clopen neighbourhoods found
  `IntegralPointedClopenRefinement` (a different, integral base-change
  statement), and `StrictLocalGeometricFibreTest` (its consumer, whose
  proof docstring records this argument, but whose signature does not
  assert it). Neither replaces the present statement.
- `rg` of `dag/lean_names_upstream.json`, upstream, and `lean/Sheaf` for
  the new declaration name or a clopen-étale cofinality declaration found
  no existing declaration.

Source reading: the actual local Stacks text of Tags 03PN (definition of
geometric points and their pointed neighbourhood morphisms), 09AY, and 0EZV
was read. As the node says, this precise finite-presentation refinement
is the project's intervening argument, not a verbatim claim of 0EZV.

Validation: `scompile.py NE lem-weil-pbc-clopen-etale-neighbourhood-cofinality`
compiled the sandbox and library-path forms cleanly. All universes and
variables are explicitly bound; the only theorem proof is `sorry`.
No statement dispute, correction, dependency repair, or new node.

## Second reading by NE

A separate author self-check pass read the node and the final signature together;
the maintainer supplies the independent delivery review. The four conjuncts
match respectively refinement, restriction equality, initiality, and the
idempotent/localization description. I checked the directions of composition:
`w ≫ b` is b after the marking, `b ≫ V.1.hom` is the structural map,
and `homOfLE h ≫ b` restricts b. I checked that both maps in equalization
are required to be pointed E-morphisms, and that the final isomorphism
commutes with the specified C-localization map. The full-subcategory
formulation retains the canonical open-subscheme/marking interpretation
by the image-open isomorphism, with no arbitrary replacement map.
No mathematical mismatch was found. The only edit after the first clean
compile was adding the finite-presentation Mathlib proof import, to make
the recorded factorization dependency available to the eventual proof.

## Maintainer review fix (2026-10-18)

The delivered signature bound `(K C : Type u)`, placing the separably closed field K in the
universe of C. The node puts no such restriction on K (it only enters through the structural
maps `K → C_z`), so this was an unstated universe restriction. The fix binds
`(K : Type v) (C : Type u)` with `universe u v`; nothing else changes. The consumer
`strictLocalGeometricFibreTest` (K : Type u) instantiates v := u. The fixed module compiles
cleanly through tools/nt_compile.py.

