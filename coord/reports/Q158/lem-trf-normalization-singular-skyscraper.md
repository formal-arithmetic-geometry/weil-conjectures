## Worker report

The delivery states `AlgebraicGeometry.Scheme.normalization_singular_skyscraper` in
`Sheaf.AlgebraicGeometry.NormalizationSingularSkyscraper`. Its only theorem has proof `sorry`.
Six auxiliary declarations introduce the exact C_x, its structural A_x-algebra action,
C_x/A_x, Ahat_x, the ideal m_x C_x, and Chat_x already named in this node. They contain real
Mathlib constructions and no postponed proof or choices of unspecified objects.
The source is Stacks `varieties.tex`, Tag 0C1R, read at
`lemma-prepare-delta-invariant`, statement and proof (lines 8819 onward). The module docstring
and theorem docstring identify this source; the latter follows all eleven DAG proof steps
and lists each step's dependency IDs. The mathematical statement is unchanged.

Hypotheses and conclusions, clause by clause:

- Algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Reduced finite-type k-scheme X: `(X : Scheme.{u}) [X.Over (Spec (.of k))] [IsReduced X]`,
  `[LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]`.
  No separatedness, properness, connectedness, integrality or nonemptiness is assumed.
- Every irreducible component has dimension one: `hpure` quantifies over all `Z : Set X`
  with `Z ∈ irreducibleComponents X`, and asserts `topologicalKrullDim Z = 1`.
- Componentwise normalization: all occurrences are the recorded `X.reducedNormalization`
  and `X.fromReducedNormalization`, not an arbitrary finite morphism or a relative
  normalization of another morphism.
- Nonsmooth set S: `hS : S = {x : X | x ∉ (X ↘ Spec (.of k)).smoothLocus}` simply names the
  set in the node. Finiteness is `S.Finite`.
- Closed points with structural residue field k: for every `x : S`,
  `IsClosed ({x.val} : Set X)` and `∃ e : X.residueField x.val ≅ CommRingCat.of k`, with
  `Spec.map e.inv = X.fromSpecResidueField x.val ≫ (X ↘ Spec (.of k))`.
  The equation specifies the structural map, not an unqualified field isomorphism.
- Finiteness of normalization is `IsFinite X.fromReducedNormalization`.
- The exact sequence is an existential `Q`, quotient morphism `q`, and its zero-composite
  proof `hq`, followed by `ShortComplex.mk ... q hq |>.ShortExact`. Its first arrow is
  precisely `SheafOfModules.unitToPushforwardObjUnit` for the normalization map.
- All three modules are coherent: `RingedSpace.IsCoherent X.toRingedSpace` for `Modules.unit X`,
  the normalization's pushed-forward unit, and Q. This is the finite-type-kernels definition,
  rather than assuming only quasi-coherence or finite type.
- The skyscraper decomposition is `Nonempty (Q ≅ ∐ (fun x : S ↦ ...))`, using the actual
  `SheafOfModules.ringedModuleSkyscraper` with value `normalizationQuotientStalk X x.val`.
  Its existing definition has sections `PLift (x ∈ U) → M`, the specified zero group off x,
  and scalar action by germs. The coproduct is the sheaf-module direct sum, also for empty S.
- A_x is literally `X.presheaf.stalk x`. C_x is `normalizationPushforwardStalk X x`, defined
  as the CommRingCat stalk of the ordinary pushforward of the normalization's ring presheaf.
  Its A_x-action is induced by the stalk functor applied to the actual structure-sheaf map
  `X.fromReducedNormalization.c`. It is not a freely chosen ring or module.
- The integral-closure assertion is an A_x-algebra equivalence between this C_x and
  `integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))`. `FractionRing`
  for a commutative ring is its localization at `nonZeroDivisors`, so this includes
  reducible local rings and does not replace total fractions by a field.
- M_x is literally the module quotient of C_x by `(Algebra.linearMap A_x C_x).range`.
  Nonzero is `Nontrivial (normalizationQuotientStalk X x)`.
- Finite length is written in the node's explicit sense: there exist a natural r and
  `F : Fin (r+1) → Submodule A_x M_x` with bottom and top endpoints, strict adjacent
  inclusions, and `IsSimpleModule A_x` for each adjacent quotient. No numerical delta
  invariant or field-vector-space substitute is inserted.
- Ahat_x is Mathlib `AdicCompletion m_x A_x`. Chat_x is
  `AdicCompletion (m_x.map (algebraMap A_x C_x)) C_x` with its ring structure. Since powers
  of the extended ideal are m_x^n C_x, these are exactly the two inverse limits in the node.
- The completed structural arrow `i : Ahat_x →ₐ[A_x] Chat_x` is an existential with its
  normalization at EVERY n: a coordinate represented by b maps to the coordinate represented
  by `algebraMap A_x C_x b`. Completion-coordinate extensionality uniquely determines i.
  The explicit injectivity states the inclusion implicit in the node's quotient notation.
- The ring equivalence `e : Chat_x ≃+* integralClosure Ahat_x (FractionRing Ahat_x)` satisfies
  `e (i a) = algebraMap Ahat_x _ a` for every a. This expresses precisely that Chat_x is the
  integral closure as an Ahat_x-algebra via the specified inclusion, without an extra chosen
  or unbound algebra instance on Chat_x.
- The completed quotient is `Chat_x ⧸ i.toLinearMap.range`, with its structural A_x-action.
  The A_x-linear equivalence `eM` from M_x satisfies, for EVERY c in the actual C_x,
  `eM (Submodule.Quotient.mk c) = Submodule.Quotient.mk (AdicCompletion.of _ _ c)`.
  Thus the asserted isomorphism is the natural one induced by completion of representatives,
  not an unrelated isomorphism of abstract modules.

Dependency declarations used, with signatures/docstrings read:

- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (all polynomials split, equivalently
  every nonconstant polynomial has a root), supplied by def-weil-algebraic-closure's match.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced` (all section rings
  reduced) and its equivalence with the stalk condition.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`. The dependency defines
  finite type as these two conditions.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, maximal irreducible subsets;
  `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, dimension of irreducible-closed chains.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalization`,
  `Scheme.fromReducedNormalization`, and the reduced integral components used in their construction.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` and its `smoothLocus`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`, affine plus
  finite section-ring maps on affine opens.
- `WeilConjectures.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent` (Stacks 01BV),
  used directly, as recorded in the item lean.note. The landed pqf-def-coherent record
  on `CoherentFiniteType` / `IsQuasiCoherentFiniteType` is retained unchanged.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, subalgebra of elements
  satisfying monic equations; `Mathlib.RingTheory.Localization.FractionRing`: `FractionRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`, `of`, `evalₐ`,
  the compatible quotient sequences, ring structure, structural algebra maps and projections.
- `Sheaf.Topology.RingedModuleSkyscraper`: `SheafOfModules.ringedModuleSkyscraper` and its
  recorded functor. Added the already landed def-pc-ringed-module-skyscraper to stmt_deps.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Scheme.Modules.unit`;
  Mathlib `Scheme.Modules.pushforward`, `SheafOfModules.unitToPushforwardObjUnit` and
  `CategoryTheory.ShortComplex.ShortExact` give the actual sequence.

Every available recorded proof-dependency module is imported, with ordinary `import`
for proof-only dependencies. No proof import has been omitted for an import cycle.

Searches (all performed before writing the new declarations):

- msearch.py LeanFinder, query "For a reduced algebraic curve over an algebraically closed
  field, the normalization quotient is a finite sum of skyscraper modules at singular points
  and unchanged by completion": eight hits, mostly Mathlib relative-normalization definitions
  and instances; no match for the theorem.
- msearch.py Loogle, query "AlgebraicGeometry.Scheme.fromReducedNormalization,
  AdicCompletion, integralClosure": no hits, unknown identifier for the side-project name.
- msearch.py LeanSearch, query "normalization of a reduced curve quotient structure sheaf
  skyscraper": eight hits, including generic skyscraper sheaves and relative normalization;
  none gives the module-valued normalization quotient or completion assertions.
- msearch.py grep, query `skyscraper|normalization.*quotient|quotient.*normalization` in
  Mathlib AlgebraicGeometry: zero hits. A second grep for the new declaration names also
  returned zero hits.
- Direct rg over the upstream WeilConjectures/AlgebraicGeometry source found the generic
  skyscraper in Modules/FlatPullbackStalk and a different normalization-exact-sequence lemma
  for etale constant sheaves in Curve/Reductions. Neither states this node.
  The prescribed grep for this exact node id in upstream WeilConjectures returned no match.
- Direct rg over lean/Sheaf found the recorded ReducedNormalization, RingedModuleSkyscraper,
  CurveNormalizationCompletion, and the downstream NodalNormalizationQuotient. The last
  assumes properness, connectedness and split nodes, so it cannot replace this theorem.
- Direct rg over Mathlib, WeilConjectures and lean/Sheaf for all seven new declaration names
  returned no hits. Each helper only names one of this node's own objects using the existing
  stalk, image, quotient or completion construction; no independent new notion is introduced.
- Current upstream coherence was read with the prescribed
  `scompile.py --source WeilConjectures.AlgebraicGeometry.Coherent`, since that current module
  is absent from the older local checkout. The current exact definition was available.

Edge cases checked mathematically against the source and the signature: empty X (no
Nonempty hypothesis, empty S and coproduct); smooth curve (S empty and normalization quotient
zero); reducible curves with crossing components (C_x need not be local or a domain); cusp;
node; and y^2 = x^5, where the nonzero maximal-ideal action on the length-two quotient rules
out replacing M_x by a skyscraper residue-vector-space module. Arbitrary characteristic is
retained; algebraically closed implies perfect. Nonseparated curves are permitted. Each
singular closed local ring is nonzero, whereas generic points and smooth points do not appear
in the finite sum. The filtration allows arbitrary finite lengths, including the syntactic
r = 0 case, which is incompatible with the independently stated Nontrivial conclusion.

The file compiled cleanly twice via scompile.py, including the version with all proof imports
(sandbox 3.6 seconds, library 3.9 seconds). There is no disputed mathematical statement.

## Second reading by Q158

Author's separate second pass with both the DAG statement and complete Lean module open;
the maintainer supplies the independent review required by the direct-delivery brief.
I checked each hypothesis and clause in the correspondence above. The coherence mismatch
was found in the recorded dependency; this item uses the exact upstream predicate directly
and records that in lean.note without rebinding the dependency.
The ordinary pushforward's RING stalk is used for C_x, avoiding any artificial ring structure
on an abstract abelian stalk. The summand is C_x/A_x with the full local-ring action, not just
its length or an arbitrary module. The completion comparison specifies all quotient-level
coordinates and the formula on representatives. The ring equivalence respects Ahat_x and
the quotient equivalence is A_x-linear; these are the source's structural identifications.
The six helpers are literal constructions of objects explicitly named in the node. All
variables and the single universe are bound explicitly, and no let, private definition,
file-local notation, local instance, proved theorem or extra hypothesis is used. All lines
meet the 100-character bound. No statement correction and no new DAG node are needed.

## Returned delivery repair

Addressed L's H13/H4 return on immutable head a8277ef1277b: removed
`dag/nodes/sec-abelian-varieties/pqf-def-coherent.json` from the packet entirely.
The current Q25 binding and its module remain untouched. The item's lean.note now
records its direct use of upstream `AlgebraicGeometry.RingedSpace.IsCoherent`
(Stacks 01BV). The delivered Lean module, theorem signature, mathematical node
statement, and statement dependencies are unchanged from the returned packet.
No dependency modules or new nodes are delivered.

The initial required dry run passed (fb9a727d37), but still staged the rejected
coherence-record replacement, so the explicit maintainer correction was applied.
The already-landed `def-pc-ringed-module-skyscraper` remains in stmt_deps, as the
maintainer confirmed that this is a genuine statement dependency.

Repair validation: scompile.py compiled the unchanged module cleanly in sandbox
(3.5 s) and library (3.9 s) modes. The recorded theorem signature equals the file
verbatim; the mathematical node statement is unchanged from current main. The
only added statement dependency is the existing ringed-module-skyscraper node.
The module has one sorry, at the theorem proof, and all lines meet the width bound.
Re-read current upstream Coherent via scompile.py --source: its predicate is exactly
finite type and finite-type kernels on every open, as required by 01BV.
