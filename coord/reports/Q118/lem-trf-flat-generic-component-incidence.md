## Worker report

The module `Sheaf.AlgebraicGeometry.FlatGenericComponentIncidence` states
`AlgebraicGeometry.Flat.generic_fibre_component_incidence`, with `sorry` as its only
proof. It introduces no definitions and changes only the item's `lean` record.
The natural-language statement and accepted four-step split are unchanged.

Statement correspondence, hypothesis by hypothesis and clause by clause:

- Schemes X and S: `{X S : Scheme.{u}}`, with explicit arbitrary universe `u`.
  Both lie in the universe of Mathlib's scheme category and its fibre construction.
- Integral base: `[IsIntegral S]`, exactly the recorded declaration of
  `def-pc-integral-scheme`; this includes nonemptiness, reducedness and irreducibility.
- Generic point eta of S: `(η : S) (hη : IsGenericPoint η Set.univ)`.
  No chosen generic-point representative is imposed.
- Flat morphism: `(f : X ⟶ S) [Flat f]`, the recorded stalkwise-equivalent
  flatness class, without any finite-type or finite-presentation assumption.
- Arbitrary base point and fibre component: `(s : S) (C : Set (f.fiber s))`
  and `(hC : C ∈ irreducibleComponents (f.fiber s))`.
- Existence of a generic point of C: the first conjunct
  `(∃ x : f.fiber s, IsGenericPoint x C)`. Membership in C is already implied
  by `IsGenericPoint.mem`, so it needs no separate conjunct.
- Every such generic point: the second conjunct is
  `∀ x : f.fiber s, IsGenericPoint x C → ...`. This is independent of the witness
  in the first conjunct and does not substitute a chosen point for the universal clause.
- Component B of the generic fibre and its generic point z:
  `∃ B : Set (f.fiber η), B ∈ irreducibleComponents (f.fiber η) ∧`
  `∃ z : f.fiber η, IsGenericPoint z B ∧ ...`.
- Ambient specialization, using the actual scheme-theoretic fibre inclusions:
  `f.fiberι s x ∈ closure ({f.fiberι η z} : Set X)`.
- The final component assertion is expressed in the actual subspace
  `Set.inter (closure ({f.fiberι η z} : Set X)) (f ⁻¹' {s})`.
  There exists a subset D of this subspace belonging to its `irreducibleComponents`,
  and `Subtype.val '' D = (f.fiberι s) '' C`. This equality says that D is exactly
  the image of C, including containment of the whole image in the intersection.
  It does not merely assert that a truncated preimage of C is a component, and
  it does not assert that the entire intersection is irreducible.
- There are no local finite type, Noetherian, density or equidimensionality binders.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`
  (lines 238--244), the scheme `T0Space` and `QuasiSober` instances (lines 38--52).
  These serve `def-pc-integral-scheme` and the proof leaf `lem-sc-scheme-sober`.
- `Mathlib.Topology.Sober`: `IsGenericPoint` (lines 36--40),
  `IsGenericPoint.mem`, `IsGenericPoint.eq` (lines 65--80), and
  `QuasiSober.sober` (lines 108--112). This is the recorded generic-point notion
  and the proof leaf's existence/uniqueness interface.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`
  (lines 36--47) and `Flat.iff_flat_stalkMap` (line 106).
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` (lines 104--108),
  defined by maximal nonempty irreducible subsets, and
  `exists_mem_irreducibleComponents_subset_of_isIrreducible`,
  `mem_irreducibleComponent`, `irreducibleComponent_mem_irreducibleComponents`
  (lines 128--159), the proof node `lem-sc-irreducible-components-cover`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `Scheme.Hom.fiberι`,
  `Scheme.Hom.fiberToSpecResidueField` (lines 37--48) and
  `Scheme.Hom.fiberHomeo` (lines 102--104). These are exactly the recorded
  scheme-theoretic fibre and its embedding, not a set-theoretic replacement.
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`:
  `AlgebraicGeometry.Flat.generalizingMap` (lines 133--143), the recorded
  `lem-weil-pbc-flat-generalizations-lift` interface. Its module is a plain proof
  import. The definition of `GeneralizingMap` was read at
  `Mathlib.Topology.Inseparable` lines 356--360: it lifts a generalization of f(x)
  to a generalization of x, so the direction in the proof docstring is correct.

All five statement dependencies are imported publicly through their recorded modules
or Mathlib matches. All additional proof dependencies are covered by the plain
UniversallyOpen import and the already public Properties, Sober and Irreducible modules.
No missing or unusable dependency was found.

Sources read: `literature/stacks-project/more-morphisms.tex`,
`remark-flat-equidimensional` (Tag 0GSK), lines 5312--5340; the second list defers
a proof, so the node correctly labels its incidence argument as agent-written.
Read `morphisms.tex`, `lemma-generalizations-lift-flat` (Tag 03HV), lines 4786--4795;
`schemes.tex`, `lemma-scheme-sober` (Tag 01IS), lines 1929--1949, and
`lemma-fibre-topological` (Tag 01K1), lines 3510--3532.
The theorem docstring carries all four accepted proof steps with their node ids.

Edge cases checked mathematically before writing:

- Empty X or empty fibre: there is no irreducible component C, so the hC premise
  makes the statement vacuous. No nonempty-source or nonempty-fibre hypothesis is added.
- Empty generic fibre with a nonempty special fibre cannot occur for a flat morphism
  to an integral base: going-down lifts every special-fibre point to eta.
- s = eta: take B = C and z = x; the fibre embedding identifies C with the
  intersection of its ambient closure and that same fibre.
- The flat family xy = t over k[t] has an irreducible generic fibre and a reducible
  special fibre. Each of the two special components is a component of the closure
  intersection; the formal statement correctly permits the intersection to be reducible.
- Infinite component sets and non-Noetherian/non-finite-type schemes: sobriety,
  component existence by maximality, and flat generalization lifting require none
  of those finiteness assumptions. B is existentially chosen, never finitely indexed.
- Flatness is necessary: the inclusion of a closed point into an integral affine
  line has a nonempty special fibre and empty generic fibre; it is nonflat.
- No restriction on characteristic or any dimension occurs in the signature.

Searches actually run through `msearch.py` for this group and item:

- LeanFinder: "For a flat morphism to an integral scheme every fibre component occurs
  in the closure of a generic fibre component". Eight hits, headed by
  `AlgebraicGeometry.Flat.generalizingMap`, `AlgebraicGeometry.Flat`, and
  `RingHom.Flat.generalizingMap_comap`. These lift individual points but do not
  give the component-existence and maximality conclusion.
- Loogle: `AlgebraicGeometry.Flat, IsGenericPoint`. Zero hits.
- LeanSearch: "Every irreducible component of a fibre of a flat morphism to an
  integral scheme is an irreducible component of the intersection with the closure
  of a generic fibre component". Eight hits: genericPoints, genericPoints.component,
  Flat.comp, irreducibleSpace_of_isIntegral, Flat.casesOn, Flat.generalizingMap,
  Flat.flat_appLE and Flat.stalkMap. No exact statement.
- Mathlib grep: `generalizingMap|irreducibleComponents|IsGenericPoint`, in
  `AlgebraicGeometry`. Twenty-five hits, including Properties, FunctionField,
  Geometrically/Reduced, IdealSheaf/IrreducibleComponent, Noetherian, Smooth and
  UnderlyingMap. They supply ingredients, no full incidence assertion.
- Project `rg` in both `lean/WeilConjectures` and `lean/Sheaf`:
  `generic.*[Cc]omponent|[Cc]omponent.*generic|flat.*incidence`.
  Read the nearby FlatFibreGenericGeneralization (valuation-base finite-presentation
  generalization stability), FlatFibreComponentClosureDimension (locally finite
  type dimension comparison), FlatDenseGenericFibrePureDimension (the consumer),
  and GenericFiberComponentSection (a connected-component section result).
  None states this unrestricted irreducible-component incidence lemma.
- `grep -rn 'lem-trf-flat-generic-component-incidence' lean/WeilConjectures`
  returned no match. `rg` for `generic_fibre_component_incidence` and
  `genericFibreComponentIncidence` in both project roots and
  `dag/lean_names_upstream.json` returned no match. The chosen declaration is new.

Validation: `scompile.py Q118 lem-trf-flat-generic-component-incidence` compiled the
delivered file successfully as both sandbox and named library module, with no errors
or warnings (3.5 s and 9.0 s). The initial subspace-notation elaboration error was
repaired by writing `Set.inter` explicitly. All universes and variables are explicit;
`autoImplicit` is disabled. No diagnostic commands remain. The record's signature
is copied verbatim from the file, before `:=`.

There is no statement dispute, source correction, new node or dependency repair.
Per the dispatcher's direct-delivery instruction, the maintainer supplies the
independent review; no independent-worker review is claimed here.

## Second reading by Q118

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
