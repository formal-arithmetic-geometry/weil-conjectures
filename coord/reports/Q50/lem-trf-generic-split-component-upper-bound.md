## Worker report

The module `Sheaf.AlgebraicGeometry.GenericSplitComponentUpperBound` states
`AlgebraicGeometry.exists_generic_split_component_upper_bound`, with `sorry` as
its only proof. No definitions, extra nodes, dependency repairs, or statement
corrections are needed. Only the item's `lean` field changes.

I read the item's complete statement, proof and source, all ten statement-dependency
nodes and their recorded declarations or Mathlib matches, and the proof-dependency
interfaces. The source is Stacks `more-morphisms.tex`, Tag 055A, second and final
proof paragraphs, with the finite separable construction in Tag 0551. These give
precisely the generic splitting and upper-bound parts of the item. No flatness,
reducedness or Noetherian hypothesis is needed on the original morphism or base.

Hypothesis and clause correspondence:

- Schemes and the morphism are `{X S : Scheme.{u}}` and `(f : X ⟶ S)`.
- Finite type is `[LocallyOfFiniteType f] [QuasiCompact f]`, the conjunction
  recorded by `def-weil-finite-type-morphism`.
- The base is irreducible by `[IrreducibleSpace S]`, including nonemptiness.
  Its supplied generic point is `(η : S)` with
  `hη : IsGenericPoint η (Set.univ : Set S)`.
- The field k is exactly `S.residueField η`. Every occurrence of a fibre uses
  `f.fiberToSpecResidueField`, hence the actual scheme-theoretic fibre and its
  structure map, rather than the underlying point-set fibre.
- The existential field extension is `(L : Type u) (_ : Field L)` together with
  `a : Spec (CommRingCat.of L) ⟶ Spec (S.residueField η)`.
  As in the recorded generic-splitting and spreading declarations, this represents
  the field embedding by its spectrum morphism. `Spec.homEquiv` identifies it with
  a unital ring map k → L, which is injective because its source is a field.
  It is therefore exactly a field extension in `def-pc-field-extension`; it is
  not an arbitrary morphism unrelated to that extension. `IsFinite a` means that
  its coordinate algebra is finite as a module, and `Etale a` is scheme etaleness.
- The integer n ≥ 0 is `(n : ℕ)`; the open is `(W : Set S)` with
  `IsOpen W ∧ η ∈ W`.
- G is written in full as `pullback (f.fiberToSpecResidueField η) a`.
  Its list of components is `A : Fin n → Set G`. `Function.Injective A`
  says the listed subsets are distinct, and `Set.range A = irreducibleComponents G`
  says they are precisely all components. `(⋃ i, A i) = Set.univ` is their cover.
  Closedness follows from membership in the recorded maximal-irreducible-component
  notion; no separate, stronger structure on these subsets is imposed.
- For each `i : Fin n`, each field E, and each field extension represented by
  `z : Spec E ⟶ Spec L`, the inverse image of `A i` under the first projection
  of `G ×_L Spec E` is `IsIrreducible`. Mathlib's `IsIrreducible` includes both
  nonemptiness and preirreducibility. This is the node's entire geometric clause.
- `∀ s ∈ W, ∀ (K : Type u) (_ : Field K) (y : Spec K ⟶ Spec (S.residueField s))`
  quantifies over every point of the open and every extension of its residue field.
  The test scheme is `pullback (f.fiberToSpecResidueField s) y`.
- Its number of components is at most n precisely because there exists an injective
  map from its component subtype into `Fin n`. This condition excludes infinite
  component sets as well; it does not use a natural-valued cardinality that could
  collapse an infinite set to zero.
- The explicit final clause is
  `n = 0 → IsEmpty ↥(pullback (f.fiberToSpecResidueField s) y)`.
  When n is zero the list is indexed by `Fin 0` and its union is empty, so the
  generic split fibre G is empty too. Taking y to be the identity extension gives
  emptiness of each original fibre over W. Thus every zero-case assertion is kept.

Dependencies used (all source signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`; the field-extension/spectrum correspondence is the recorded
  `Spec.homEquiv` in `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, `IsIrreducible` and
  `IrreducibleSpace`; `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, imported via
  `Mathlib.AlgebraicGeometry.Fiber`; the latter supplies `Scheme.Hom.fiber`,
  `Scheme.Hom.fiberToSpecResidueField` and the existing pullback infrastructure.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, the recorded equivalent interpretation
  of the field extensions; no replacement field-extension notion is defined.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd` (available through the fibre module).
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- Proof-only imports include `WeilConjectures.AlgebraicGeometry.GenericComponentsSplit`:
  `exists_finite_etale_geometric_component_extension`, and
  `WeilConjectures.AlgebraicGeometry.GeometricGenericCoverSpread`:
  `exists_open_spreading_geometric_generic_cover`.
- The other proof nodes are Mathlib matches: finite-type composition/base-change
  instances, `LocallyOfFiniteType.isLocallyNoetherian`,
  `QuasiCompact.compactSpace_of_compactSpace`,
  `finite_irreducibleComponents_of_isNoetherian` (the Noetherian module is imported
  privately), and `exists_mem_irreducibleComponents_subset_of_isIrreducible`,
  `mem_irreducibleComponent`, `irreducibleComponent_mem_irreducibleComponents`.

Edge cases checked before writing: an empty total space and an empty generic
fibre allow n = 0 with L = k; a nonempty irreducible component cannot be represented
by an empty subset because `IsIrreducible` includes nonemptiness. The empty base is
excluded by the node's irreducibility and generic point, as in Lean. Repeated
components are excluded by injectivity. Nilpotent bases, arbitrary characteristic,
vertical components away from the generic point, and nonflat finite type families
are allowed. Intersections of distinct components need not be empty, and no
intersection condition is added. Field extensions are tested in the same universe
as the scheme and residue fields, following the published dependency interfaces;
there is no independently smaller test universe. The identity field extension is
included, and geometric irreducibility is tested over arbitrary fields, not only
algebraic closures or finite extensions.

Searches for an exact existing statement:

- `msearch.py ... leanfinder`: “A finite type morphism over an irreducible scheme
  admits a finite separable extension splitting generic components and a neighbourhood
  where all geometric fibres have at most that many irreducible components”. Eight
  hits: `IsFinite`, `finite_appTop_of_universallyClosed`, finiteness of the underlying
  fibre of an IsFinite morphism, `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`,
  `Scheme.PartialMap.fromFunctionField`, `IsFinite.finite_preimage_singleton`,
  Jacobson fibres, and `Scheme.Hom.discrete_fiber`. None gives splitting plus a
  uniform bound for an arbitrary finite type family.
- `msearch.py ... loogle '"GeometricallyIrreducible", "irreducibleComponents"'`:
  zero hits.
- `msearch.py ... grep 'geometric.*component|component.*geometric|055A|055G'
  AlgebraicGeometry`: three hits, in Geometrically/Reduced, Irreducible and Connected.
  Read the returned declarations: reduction under flatness, a component equivalence
  for an already geometrically irreducible open morphism, and a connected-component
  homeomorphism. None supplies the present generic splitting and neighbourhood bound.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, including the item id,
  generic/component and upper-bound patterns, and the proposed declaration name;
  also searched `dag/lean_names_upstream.json`. Existing generic splitting and
  spreading modules give the two proof inputs. The generic constancy parent and
  generic fibre lower-bound sibling have different statements. No exact duplicate
  or name collision was found.

Validation: `scompile.py Q50 lem-trf-generic-split-component-upper-bound` compiled
both the sandbox and library module successfully (3.2 s and 8.5 s), with no errors
or warnings. The declaration uses `sorry` as required by stage 2.

## Second reading by Q50

This second reading was done by an independent maintainer reviewer (cc review
service), who did not write the delivery. It replaces the author's self-check that
was delivered in this section.

Node clauses, the Lean that renders each, and the verdict:

1. f : X → S finite type: `(f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]`.
   This is the conjunction recorded by def-weil-finite-type-morphism. Correct.
2. S irreducible, with generic point η: `[IrreducibleSpace S]`, `(η : S)`,
   `hη : IsGenericPoint η Set.univ`. Correct, and nonemptiness is included.
3. k = κ(η): `S.residueField η`. Fibres are the scheme-theoretic ones, through
   `f.fiberToSpecResidueField` (Mathlib Fiber.lean:46). Correct.
4. L/k a field extension whose spectrum map a is finite and étale:
   `(L : Type u) (_ : Field L) (a : Spec L ⟶ Spec k)`, `IsFinite a ∧ Etale a`.
   Spec is fully faithful on rings, so a is Spec of a ring map k → L, which is
   injective. This is the same form as the proof input
   `exists_finite_etale_geometric_component_extension`
   (lem-sbc-generic-components-split). Correct.
5. n ≥ 0 and an open W ∋ η: `(n : ℕ) (W : Set S)`, `IsOpen W ∧ η ∈ W`. Correct.
6. G = X_η ×_k Spec L has exactly n distinct components A_1..A_n, which cover G:
   `A : Fin n → Set (pullback (f.fiberToSpecResidueField η) a)` with
   `Function.Injective A`, `Set.range A = irreducibleComponents G` and
   `⋃ i, A i = univ`. Correct. The cover clause is redundant but true.
7. For every i and every E/L, the inverse image of A_i in G ×_L Spec E is
   irreducible and nonempty:
   `IsIrreducible ((pullback.fst (pullback.snd _ a) z) ⁻¹' A i)` for all
   `E : Type u`, `[Field E]` and `z : Spec E ⟶ Spec L`. IsIrreducible includes
   nonemptiness, and the projection is G ×_L Spec E → G. Correct.
8. For every s ∈ W and every K/κ(s), (X_s)_K has at most n components: there is an
   injection from the components of `pullback (f.fiberToSpecResidueField s) y` into
   `Fin n`. This also rules out infinitely many components. Correct.
9. When n = 0, the list is empty and the fibres over W are empty: `Fin 0` handles
   the list, and the conjunct `n = 0 → IsEmpty (pullback …)` handles the fibres.
   The conjunct also follows from clause 8, since a nonempty space has a component,
   so it is not stronger than the node. Correct.

Quantifier order is ∃ L a n W A, then the clauses, matching the node. Test fields
live in universe u, as in the recorded dependency interfaces; this is not a silent
restriction relative to the node. No extra hypotheses are added: no Noetherian,
flatness or reducedness assumption.

Edge cases checked:
- empty X, so n = 0 and L = k is allowed;
- vertical components away from η, which the open W handles;
- the identity extension, which is included in the quantifiers;
- arbitrary characteristic.

The source is Stacks Tag 055A, paragraph 2 (via 0551) and the final paragraph
(via 055G), which give exactly this splitting and upper bound.

One definition per notion: there are no new definitions. The Mathlib and project
searches in the worker report are adequate, and the declaration name is not taken
in side-live.

Mismatches: none in the Lean or the node record. Only this report section was
replaced.
