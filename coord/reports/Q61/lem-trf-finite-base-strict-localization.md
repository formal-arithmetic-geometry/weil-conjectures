## Worker report

The module `Sheaf.TraceFormula.FiniteBaseStrictLocalization` states both clauses of
`lem-trf-finite-base-strict-localization`, as two named theorems with `sorry` proofs.
There are no new definitions, no dependency repairs, and no statement correction.

Clause-by-clause correspondence:

- Schemes and a finite morphism: `{T S : Scheme.{u}} (h : T ⟶ S) [IsFinite h]`.
  The geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (s : Spec (.of Ω) ⟶ S)`. The strict localization is the existing
  `strictHenselizationScheme s`; its coordinate ring is `strictHenselizationRing s`.
- The geometric fibre is `pullback h s`. Its finite component set is rendered by
  `Finite (ConnectedComponents (pullback h s : Scheme.{u}))`.
- The index type `{t : Spec (.of Ω) ⟶ T // t ≫ h = s}` is the set of geometric
  lifts of `s`, using exactly Ω. The map in `Function.Bijective` sends a lift to
  the connected component of its point in the geometric fibre. That point is the
  image of `IsLocalRing.closedPoint Ω` under `pullback.lift t.val (𝟙 _) ...`.
  The identity second projection makes this an Ω-point. The fibre-product
  universal property identifies such lifts with Ω-points of the fibre, and
  bijectivity says exactly that each component has a unique such point. Thus
  indexing the coproduct by the lifts is the stated component indexing, with
  no choice of geometric points or replacement field.
- The isomorphism `e` has source the scheme coproduct of the existing
  `strictHenselizationScheme t.val` and target
  `pullback h (strictHenselizationStructuralMap s)`. Its two coprojection
  equations specify its components over T and S_(s), respectively. The latter
  is precisely `strictHenselizationMap h t.val`, followed by equality transport
  from `t.val ≫ h` to `s`. Consequently this is the canonical map, not an
  arbitrary isomorphism between the two objects.
- For every summand, an existential `IsLocalRing` supplies the structure needed
  to speak about its residue field; it is a conclusion, not a hypothesis.
  `IsStrictlyHenselianLocalRing` means henselian local with separably closed
  residue field. `IsFinite` of its canonical map to S_(s) is the finite
  S_(s)-scheme assertion. The existential ring homomorphism φ is fixed by
  `Spec.map (CommRingCat.ofHom φ) =` that actual canonical map, so it cannot be
  chosen independently. `IsLocalHom φ` states locality, and
  `(IsLocalRing.ResidueField.map φ).Finite` and `IsPurelyInseparable` with the
  explicit algebra structure `(IsLocalRing.ResidueField.map φ).toAlgebra`
  state exactly the finite purely inseparable extension of closed-point
  residue fields. `RingHom.Finite` is module finiteness for this algebra map.
- Empty indexing is allowed: no `Nonempty` or positive cardinality hypothesis
  occurs. Both an empty fibre and the empty coproduct are covered.
- The second theorem accepts any original cartesian square as
  `(p : W ⟶ Y) (q : W ⟶ T) (g : Y ⟶ S) (h : T ⟶ S)
  [IsFinite h] (H : IsPullback p q g h)`. This includes the chosen fibre product
  and all projection-preserving isomorphic presentations of it. The geometric
  point `w : Spec (.of Ξ) ⟶ W` uses one algebraically closed field Ξ throughout.
  The projected geometric points are `w ≫ p`, `w ≫ q`, and `(w ≫ p) ≫ g`.
- Its conclusion `IsPullback (strictHenselizationMap p w)
  (strictHenselizationMap q w) ...` is exactly the canonical isomorphism
  W_(w) ≅ Y_(y) ×_{S_(u)} T_(t): `IsPullback.isoPullback` supplies this
  isomorphism and its projection identities. The right map includes equality
  transport along `H.w`, associativity, and composition by w, solely to put
  the two copies of the common point in the same type. These transports add
  no extra geometric data or assumption.
- Compatibility over W follows from these projection identities,
  `strictHenselizationMap_over` for p and q, and uniqueness in the original
  cartesian square H. Thus all three structural-map compatibilities in the
  node are retained by the pullback formulation. There is no finiteness,
  finite-type, separation, or affine hypothesis on g.

Dependency declarations used, with their source signatures and docstrings read:

- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`,
  the affine-local finite ring-map definition. This is the recorded finite
  morphism definition; the integral variant is not needed in this statement.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points
  are the recorded inline morphisms from spectra of algebraically closed
  fields. `Mathlib.AlgebraicGeometry.ResidueField` supplies the recorded
  `Scheme.SpecToEquivOfField`, used to check this interpretation.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: the existing
  `Scheme.strictHenselizationRing` and `Scheme.strictHenselizationScheme`,
  formed from the pointed étale coordinate-ring colimit.
- `Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift`: the recorded
  `Scheme.strictHenselizationClosedLift_over`; its public imports expose
  `Scheme.strictHenselizationStructuralMap`,
  `Scheme.strictHenselizationMap`, and `Scheme.strictHenselizationMap_over`.
  The map is the existing unique pointed functorial map, as characterized by
  `strictHenselizationMap_existsUnique`. No new functorial map is introduced.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: the recorded
  `pullback`, `pullback.fst`, `pullback.snd`, and `pullback.lift`.
  `Mathlib.AlgebraicGeometry.Limits` supplies scheme coproducts and `Sigma.ι`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`:
  `IsStrictlyHenselianLocalRing`, with its henselian-local parent and its
  separably closed residue field field. This is publicly imported through
  the recorded functoriality module, rather than redefined.
- `Mathlib.FieldTheory.PurelyInseparable.Basic`: `IsPurelyInseparable`;
  finiteness is `RingHom.Finite` for the induced residue ring map, equivalently
  the recorded `Module.Finite` for its `.toAlgebra` structure.

The existing stated proof dependencies are imported non-publicly:
`Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance`,
`Sheaf.RingTheory.FiniteRingMapQuasiFinite`, and
`WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct`.
The affine-spectrum formula and finite-morphism permanence are already exposed
by the Mathlib pullback and finite-morphism imports. The unique-embedding input
is in the imported purely-inseparable and algebraically-closed-field modules.
The two new ring strict-henselization lemmas in proof_deps have no Lean record
in the current DAG, so have no module to import; neither is needed to type the
statement. The docstrings give their exact uses in the future proof.

Edge cases checked against the node and Stacks 03QP, 04GH, 05WR, and 0GIP:

- Empty fibre: all lift/component indices are empty; the target is empty by
  finite-module Nakayama, and all per-summand assertions are vacuous.
- Identity finite morphism: there is exactly one lift and the decomposition
  is the strict localization itself. The square theorem becomes the identity
  pullback square for every Y.
- Nonreduced finite fibre, such as Ω[ε]/(ε²): the unique Ω-point still indexes
  its one component; the summand retains the nilpotents. No reducedness is
  asserted or assumed.
- Finite purely inseparable residue extension: the residue extension is
  finite purely inseparable and is not silently replaced by equality of
  residue fields. The base strict-local residue field need not be Ω.
- Ω transcendental over the original residue field, or an imperfect residue
  field: the construction still uses the separable algebraic closure inside Ω,
  as the existing strict henselization requires, without asserting residue Ω.
- Arbitrary Y, including an empty scheme or a morphism not of finite type:
  the second theorem imposes no condition on g. Its affine-ring source is
  0GIP with a finite A→B and an arbitrary A→C.
- Universe: schemes and geometric-point fields use the same explicit u as
  the existing dependency interface; no independently smaller test universe
  is introduced. The lift subtype and component set are in Type u, so their
  full (possibly empty) coproduct exists in Scheme.{u}.

Searches for an existing exact statement:

- `msearch.py leanfinder`, query “finite morphism strict localization decomposes
  as coproduct of strict localizations of geometric fibre components”: eight
  hits on scheme extensivity, coproduct finiteness, and sigmaSpec for finite
  products of rings. None identifies strict localizations or states either
  clause. The sigmaSpec statement and the finite coproduct infrastructure were
  inspected; the former compares arbitrary finite products of coordinate rings,
  not the strict-local factors of a finite base change.
- `msearch.py loogle`, query `IsFinite, IsPurelyInseparable`: zero hits,
  unknown unqualified `IsFinite`.
- `msearch.py grep`, query `strictHenselization|strictLocalization`, restricted
  to Mathlib AlgebraicGeometry: zero hits.
- `rg` in `WeilConjectures/`, the project `lean/Sheaf/`, and the upstream name
  table, searching strict henselization/localization, finite strict-local
  decomposition, and the proposed declaration names: the project contains
  the construction and functoriality, ind-étale invariance, and the component
  comparison for geometric fibres, but no statement of these finite strict-local
  clauses. The upstream source contains strictly henselian cohomology and
  integral base-change applications, not this statement. Searching the item id
  in the upstream source found no declaration.

Validation: the delivered module compiled cleanly with `scompile.py`, both as
sandbox source and under its final library module path. Every theorem proof is
`sorry`; no facts were proved. All variables and universes are explicit and
`autoImplicit` is disabled. The node copy changes only `lean`.

## Second reading by Q61

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
