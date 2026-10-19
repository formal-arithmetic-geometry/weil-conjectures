## Worker report

The module `Sheaf.Paper.FiniteFieldFiber` defines the global finite-field datum and its
specialized subfield, geometric-fiber, rational-point, counting and coefficient-choice
conventions. It contains no theorem and no `sorry`. The node is unchanged except for `lean`.
Source read: the complete master blueprint file
`sec-nagata-compactification/sk-prop-nagata-sketch-comp-category/def-weil-finite-field-fiber.md`,
order 411, compared with the DAG statement and all thirteen statement dependencies.

Clause-by-clause correspondence:

- The prime, positive exponent and prime power are `FiniteFieldDatum.p`, `.a`, `.q`,
  `.prime : p.Prime`, `.exponent_pos : 1 ≤ a`, `.cardinality_eq : q = p ^ a`.
- The fixed field with q elements is `.k₀`, with `.field_base`, `.finite_base` and
  `.card_base : Nat.card k₀ = q`. It may be any such field, not just GaloisField.
- The fixed algebraic closure and structure homomorphism are `.k`, `.field_closure`,
  `.algebra_closure`, `.isAlgClosure : IsAlgClosure k₀ k`, and `algebraMap D.k₀ D.k`.
  The structure packages exactly the stated tuple and its required structures.
- For each `n : ℕ` with `hn : 1 ≤ n`, `extensionSubfield` chooses the subfield from
  `FiniteField.exists_unique_subfield_of_closure`. The theorem's clauses identify it
  as the roots of `x ^ (q ^ n) = x`, give cardinality `q ^ n`, uniqueness and inclusion
  of the image of k₀. `extensionEmbedding` selects the theorem's corestriction map;
  its composite with the injective subtype map is prescribed, determining it uniquely.
  The map supplies the k₀-algebra structure via `RingHom.toAlgebra` when needed.
  Neither choice is from a mere unconstrained existence assertion.
- For arbitrary `S : Scheme`, the closed-point convention is exactly the existing
  `closedPoints S`, and for `s : closedPoints S`, its residue field is
  `S.residueField s.val`. These notions are documented, not defined a second time.
- A k₀-scheme is `Y₀ : Over (Spec (CommRingCat.of D.k₀))`. Its finite-type assumption
  is `[LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]` on each relevant definition.
  Bundled Over objects are expressly permitted by brief-stage2 §3.
- `geometricFiber` applies `Over.pullback` along
  `Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))`. Its `.left` is the pullback
  `Y₀ ×_{k₀} k`, and its `.hom` is `pullback.snd`, the required `a_Y`.
- `extensionPoints Y₀ n hn` is the actual hom type in `Over (Spec D.k₀)` from the
  spectrum of the chosen subfield, using precisely `extensionEmbedding`, to Y₀.
  Thus its morphisms commute with the stated k₀-structure maps.
- `pointCount` is `Nat.card (D.extensionPoints Y₀ n hn)`. No finiteness assertion has
  been added; the DAG explicitly leaves that assertion to lem-weil-point-counts-finite.
- `CoefficientDatum` fixes `l`, `[Fact l.Prime]`, `different : l ≠ D.p`, and `Qbar`
  with field, `Algebra (Padic l) Qbar`, and `IsAlgClosure (Padic l) Qbar` structures.
  This is any fixed algebraic closure, with no extra restriction on its choice.
- The existing `Padic l` and `PadicInt l` render Q_l and Z_l; the latter is the subtype
  of elements with norm at most one, equivalent to nonnegative valuation.
- For a field E with `[Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`, use the
  dependency's `Padic.coefficientExtensionIntegers l E`,
  `Padic.coefficientExtensionUniformizer l E`, and `Padic.coefficientExtensionRing l E n`
  for O_E, the fixed uniformizer, and A_{E,n}. These exact existing conventions are
  explicitly recorded in the module; no second valuation ring or quotient is introduced.
  The n ≥ 1 range uses these definitions at positive n.

Dependency declarations read and used:

- `Mathlib.FieldTheory.Finite.GaloisField`: `GaloisField` supplies a model for the finite
  base field; the datum accepts arbitrary models of the same specified cardinality.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure`.
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure` supplies a
  possible fixed choice; the datum does not require that particular construction.
- `Sheaf.FieldTheory.UniqueSubfieldOfClosure`:
  `FiniteField.exists_unique_subfield_of_closure`, its full signature and docstring.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over` and the bundled `CategoryTheory.Over`
  form from `Mathlib.CategoryTheory.Comma.Over.Basic` (including its hom type).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: the recorded general base-change
  convention is `Over.pullback`, with `Limits.pullback` and its second projection.
  Read the entire module including `Scheme.Hom.geometricFiberAt`; that definition is
  at an arbitrary point, whereas this item changes the base finite field directly.
- `Mathlib.NumberTheory.Padics.PadicNumbers`: `Padic`;
  `Mathlib.NumberTheory.Padics.PadicIntegers`: `PadicInt`.
- `Sheaf.NumberTheory.Padics.CoefficientExtension`: all recorded definitions, especially
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal`, `coefficientExtensionRing`; the entire module was read.

Edge cases checked before writing: a = 0 and n = 0 are excluded exactly by the positive
bounds; p = 2 is allowed; no unnecessary restriction on l other than prime and l ≠ p;
empty Y₀ is allowed and its point set is empty (count zero); disconnected and nonreduced
finite-type schemes are allowed; schemes need not be smooth, separated or proper; E may
be Q_l itself. No cardinality is asserted for an infinite point set. All fields and schemes
can be taken in any common universe u; no small universe is fixed, and there is no
quantification over test objects in an independent smaller universe. Every universe and
variable is explicitly bound. No statement correction, disputed statement or new node.

Searches performed with msearch.py and direct source searches:

- LeanFinder: "global finite field datum finite field algebraic closure geometric fiber
  l adic coefficients": eight unrelated function-field/isocrystal results, no datum.
- Loogle: "GaloisField, AlgebraicClosure": zero hits.
- Mathlib grep: `FiniteFieldDatum|finiteFieldDatum|finite.field.datum`: zero hits.
- LeanSearch: "finite field algebraic closure global datum geometric fiber": unavailable,
  Internal Server Error; this is an unavailable search, not a negative mathematical result.
- Direct rg of the upstream WeilConjectures tree, project lean/Sheaf and upstream name
  index for the datum, blueprint id and proposed declaration suffixes: no datum exists.
  The blueprint-id matches are dependency source docstrings, not a duplicate datum.
- Broader source search found upstream `Scheme.Hom.geometricFiber` in
  `WeilConjectures.AlgebraicGeometry.GeometricFrobenius`: it fixes the specific Mathlib
  `AlgebraicClosure k`; it cannot represent an arbitrary fixed closure D.k without a
  comparison isomorphism. `PoincareDualitySetting.geometricFiber` additionally requires
  a smooth, separated, geometrically connected model. Neither is this node's general datum.
- Read `Comparator/Weil/Definitions.lean`: `Scheme.Hom.fieldPoints` and `.pointCount`
  use a splitting-field model `FiniteField.galoisExtension`, not the specified subfield
  of the fixed closure. The item instead specializes its dependency's Over hom type
  at that actual subfield; its count is Nat.card of that type. No alternative finite
  extension model or comparison theorem is substituted.

Validation: scompile.py compiled the delivered module cleanly on the server (2.0 seconds,
60-second per-file cap, nice 19, two threads). The tool also compiled the published
UniqueSubfieldOfClosure side dependency in its private overlay. No local compiler was run.

## Second reading by NB

Independently read the sandbox node and all seven declarations against the complete
master blueprint source, order 411, and the statements and recorded declarations of
all thirteen dependencies. This source is a blueprint definition, not a Stacks lemma;
it has no additional ambient hypotheses. No statement correction, new node, or dependency
module is part of this delivery. The Lean and node record need no changes.

Object/hypothesis/clause checklist (each verdict is pass):

1. A prime p, positive integer a, q = p^a: `FiniteFieldDatum.p`, `.a`, `.q`,
   `.prime`, `.exponent_pos`, `.cardinality_eq`. Naturals with `1 ≤ a` express precisely
   the positive-integer range. There is no extra characteristic hypothesis.
2. A fixed field k₀ with q elements: `.k₀`, `.field_base`, `.finite_base`, `.card_base`.
   This admits every field of that cardinality, not just the `GaloisField p a` model.
   Read the dependency's `GaloisField` signature and its cardinality convention.
3. A fixed algebraic closure k and inclusion iota: `.k`, `.field_closure`,
   `.algebra_closure`, `.isAlgClosure`; iota is `algebraMap D.k₀ D.k`. Read
   `IsAlgClosure` itself: it requires algebraicity as well as algebraic closedness.
   Its torsion-free parameter is inferred for field extensions, not an extra hypothesis.
4. For every positive n, the unique subfield of size q^n containing iota(k₀):
   `extensionSubfield D n hn` chooses exactly the witness of
   `FiniteField.exists_unique_subfield_of_closure`. Read the full signature: root-set
   equality, cardinality, uniqueness among subfields, containment, and the n = 1 image
   characterization all concern that same witness. `extensionEmbedding` chooses its
   corestriction, whose composite with the subtype embedding equals iota. Both choices
   are determined by the theorem up to equality, so neither is hollow under H5.
5. Any scheme S, its closed points and residue fields: the module explicitly reuses
   `closedPoints S` and `S.residueField s`. Read `closedPoints` as the predicate
   `IsClosed {s}`, and `Scheme.residueField` as the residue field of the stalk.
   For `s : closedPoints S`, the latter takes `s.val`. No duplicate definition is needed.
6. A k₀-scheme Y₀ with finite-type structure morphism:
   `Y₀ : Over (Spec (CommRingCat.of D.k₀))`, `[LocallyOfFiniteType Y₀.hom]`,
   `[QuasiCompact Y₀.hom]`. Read both property-class signatures and `Scheme.Over`;
   the bundled Over form is allowed and represents exactly the structure morphism.
   There is no smoothness, separation, connectedness, reducedness or properness premise.
7. Y = Y₀ × k and a_Y its projection to Spec k: `D.geometricFiber Y₀` applies
   `Over.pullback` to `Spec.map` of iota. Read `Over.pullback.obj`: it is
   `Over.mk (pullback.snd g.hom f)`. Thus `.left` is precisely the specified fiber
   product and `.hom` is its second projection, with the correct contravariant direction.
   Read `BaseChangeConventions` and its geometricFiberAt signature; that declaration
   uses a point's residue field and is not this specialization at the chosen base field.
8. Y₀(F_{q^n}) = Hom over k₀ from Spec of that actual subfield:
   `D.extensionPoints Y₀ n hn` is the Over hom from
   `Over.mk (Spec.map (CommRingCat.ofHom (D.extensionEmbedding n hn)))` to Y₀.
   The Over hom's commutativity equation enforces exactly the base-field condition.
   This uses the recorded field-valued-points convention, not an unrelated map set.
9. Its number of elements: `D.pointCount Y₀ n hn` is `Nat.card` of exactly that hom
   type. The node leaves finiteness to lem-weil-point-counts-finite; no extra finiteness
   hypothesis or unproved finiteness assertion is inserted here.
10. A choice of prime l distinct from p and algebraic closure of Q_l:
    `CoefficientDatum D` has `.l`, `.prime : Fact l.Prime`, `.different : l ≠ D.p`,
    `.Qbar`, `.field`, `.algebra`, `.isAlgClosure`. These are choices for any l ≠ p,
    not a restriction to a particular closure. The existing `Padic l` and `PadicInt l`
    supply Q_l and its valuation ring; their definitions were opened independently.
11. Every finite extension E/Q_l, its integers, chosen uniformizer and quotients at
    positive levels: the module documents direct use of
    `Padic.coefficientExtensionIntegers l E`, `coefficientExtensionUniformizer l E`,
    `coefficientExtensionRing l E n`. Read all these definitions in the dependency
    module: binders are `[Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`,
    the ideal is `Ideal.span {uniformizer} ^ n`, and the quotient is of those integers
    by that ideal. Thus the quotient is O_E/(varpi_E^n), not a residue-field substitute.
    No second coefficient-ring definition is introduced.

Edge cases: a = 0 and extension n = 0 are excluded by exactly the source's positivity
conditions. n = 1 is allowed and the dependency identifies its subfield with iota(k₀).
p = 2 is allowed; l = p is excluded, with all other primes admitted. The empty scheme,
nonreduced schemes and disconnected schemes satisfy the same binders when finite type;
empty Y₀ has no field-valued points, and its count is zero. E = Q_l is allowed. There
is no index set or nonzero-module premise. The coefficient dependency's level zero is
an additional defined value, not a replacement for any positive level. `universe u` is
explicit and arbitrary, and all field/scheme objects may inhabit a common sufficiently
large universe; there is no quantification over a smaller test universe and no unbound
variable or universe. No extra mathematical case is excluded.

Independent searches (other queries than the author's):

- LeanFinder via msearch: "finite field with chosen algebraic closure and rational points
  over finite extensions": eight hits, chiefly `FiniteField.Extension` constructions
  and unrelated function-field/model-theory results. These do not bundle the datum or
  specify subfields of its chosen closure.
- Loogle via msearch: `IsAlgClosure, Subfield`: zero hits.
- Grep via msearch: `FiniteFieldDatum|CoefficientDatum|extensionSubfield`: zero hits.
- Direct rg in Mathlib FieldTheory, upstream WeilConjectures and project lean/Sheaf,
  using `finite.field`, `geometricFiber`, `fieldPoints`, `pointCount` and the proposed
  datum names: no existing global datum. Opened `Scheme.Hom.geometricFiber` and its
  structure map (the specific `AlgebraicClosure k` model), and
  `PoincareDualitySetting.geometricFiber` (requires a smooth, separated,
  geometrically connected model). Neither has the required generality and chosen closure.
- Opened `Comparator/Weil/Definitions.lean`: clarification of the worker report:
  `Hom.fieldPoints` itself accepts arbitrary field extensions; it is `Hom.pointCount`
  that selects the splitting-field model `FiniteField.galoisExtension`. The present
  module follows the recorded Over-hom convention directly and specializes it to the
  actual chosen subfield. This is not a second general field-valued-points construction.

Mismatch/changes: none in the Lean or node; clarified the worker report's description
of upstream `Hom.fieldPoints` above. Appended this independent reading only. H4/H5/H6/H8/H9
checks pass: no private copies, no data sorry, no theorem proofs, source docstrings on
every declaration, correct module and namespace. The node's `lean.statement` is verbatim
`structure FiniteFieldDatum`, the header before `where`.

Validation: reran scompile.py for the delivered module. The server compiled its
UniqueSubfieldOfClosure side dependency in 1.0 s and FiniteFieldFiber in 2.0 s, cleanly,
with nice 19, two threads, and a 60-second limit per file. No local compiler was used.
