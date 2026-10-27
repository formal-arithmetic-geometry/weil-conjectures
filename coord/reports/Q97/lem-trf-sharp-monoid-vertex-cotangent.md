## Worker report

Group Q97, stage 2, item lem-trf-sharp-monoid-vertex-cotangent, 2026-10-23.
The module Sheaf.RingTheory.SharpMonoidVertexCotangent states
AlgebraicGeometry.Monoscheme.sharp_monoid_vertex_cotangent, with proof `sorry`.
Its three construction helpers have real data: the monoid algebra, its displayed
ideal generators, and their ideal span. They belong to this very vertex-cotangent
notion and are listed in lean.declarations. No independent notion or new DAG node
is introduced. The theorem's docstring carries all six steps of the accepted proof.
The item's statement, dependencies, proof, and maintainer fields are preserved.

The previous worker's refusal concerned stage-1 re-splitting. I checked the live
node (status split, reviewed stage 1 PASS, no lean), the stage-2 queue row, and the
explicit stage handoff at the start of coord/brief-stage2.md. This is stage 2 and
requires no re-split. There is no released repair note for this item.

Source read: the local ILO PDF, physical pages 110--111, printed pp.104--105,
Exposé VIII proof of Lemma 3.2.12(ii). It identifies I/I² with the vector space on
indecomposables, proves their generation, and splits off the torus beforehand.
The accepted DAG expands the direct Laurent-coordinate and localization argument;
that full accepted statement, including unsaturated monoids, is what is stated here.

Hypotheses and objects, clause by clause:

- `k : Type u` and `[Field k]` give an arbitrary field, in every characteristic.
- `R : Type v` and `[CommMonoid R]` present the additive monoid multiplicatively,
  exactly as the owning FineFan module does. Thus one means the node's zero.
  Independent universes u and v place no size equality on the ring and monoid.
- `hR : FineFan.IsFine R` is the recorded conjunction of finite generation and
  injectivity of `Algebra.GrothendieckGroup.of`, hence fineness and integrality.
- `hsharp : FineFan.IsSharp R` is the recorded condition that every unit is one.
- `htf` says `0 < n → g ^ n = 1 → g = 1` in the actual Grothendieck group,
  precisely torsion-free group completion. No saturation hypothesis is imposed.
- `t : ℕ` is arbitrary finite torus rank, including zero.
- `Irreducible a` is Mathlib's nonunit that cannot factor into two nonunits.
  Under the displayed sharpness hypothesis, units are exactly one, so it is
  exactly the node's nonzero indecomposable atom. No second atom predicate is defined.
- `sharpVertexAlgebra k R t` is `MonoidAlgebra k (R × Multiplicative (Fin t → ℤ))`.
  Its basis element `(q,n)` is e^q y^n, with product `(qr,n+m)`. This is the
  finite-formal-sum definition of the Laurent extension k[R][y_j^±1], using the
  same `MonoidAlgebra` as the recorded `Monoscheme.monoidAlgebra` functor.
- `sharpVertexGenerator` has domain `{q : R // q ≠ 1} ⊕ Fin t`. Its left value
  is `MonoidAlgebra.single (q,1) 1`, exactly e^q; its right value is the single
  monomial at `(1, ofAdd (Pi.single j 1))` minus one, exactly y_j - 1.
- `sharpVertexIdeal` is the ideal span of the range of that generator map. This
  is exactly m = (e^q : q≠0) + (y_j-1); the span of a disjoint indexed family is
  the sum of the two displayed generated ideals.

Conclusions, clause by clause:

- `{a : R | Irreducible a}.Finite` gives finiteness of A.
- `Submonoid.closure {a : R | Irreducible a} = ⊤` gives generation of R by A.
- `(sharpVertexIdeal k R t).IsMaximal` is maximality of the displayed ideal.
- `Nonempty ((B ⧸ m) ≃ₐ[k] k)` gives its residue field k as a k-algebra.
  In particular this equivalence respects the given coefficient inclusion.
- `∀ [m.IsPrime], ...` permits forming Mathlib's localization. This is inside
  the conclusion, after asserting maximality. It adds no assumption: every
  instance exists by the asserted maximality, and the assertion holds for any
  proof of it. This avoids a circular definition or a postponed helper theorem.
- `∃ e : m.Cotangent ≃ₗ[k] (m.map (algebraMap B (Localization.AtPrime m))).Cotangent`
  gives the requested k-linear isomorphism. `Ideal.Cotangent` is Mathlib's m/m²;
  its standard k-action is the restriction of the coefficient action.
- `e.toLinearMap = Ideal.mapCotangent ... (IsScalarTower.toAlgHom k B ...) ...`
  pins this isomorphism to the natural localization map. `Ideal.le_comap_map`
  supplies the canonical membership inclusion. This is not a bare arbitrary
  equivalence substituted for the required natural map.
- `b : Module.Basis ({a // Irreducible a} ⊕ Fin t) k m.Cotangent` is the global
  basis. For each atom, its image under the standard injective
  `m.cotangentToQuotientSquare` is the class of e^a modulo m². For each torus
  index it is the class of y_j-1. The standard injection characterizes precisely
  these classes without requiring a separate theorem merely to bind an element
  of the ideal subtype.
- `c` is a basis of the localized ideal's cotangent module on the identical index
  set; `∀ i, c i = e (b i)` says its vectors are the images of those exact
  monomials and coordinate differences, so the same family is a local basis.
- The last equality is `Module.finrank k (...) = Nat.card {a // Irreducible a} + t`,
  precisely the asserted local cotangent dimension. Finiteness of the atom type
  was already asserted, so Nat.card here is its actual finite cardinality.

Dependency declarations opened and used:

- Sheaf.AlgebraicGeometry.FineFanBlowup: `AlgebraicGeometry.FineFan.IsFine`,
  `AlgebraicGeometry.FineFan.IsSharp`, including their full signatures and docstrings.
  The completion is `Algebra.GrothendieckGroup` from that same interface.
- Sheaf.AlgebraicGeometry.MonoschemeToricRealization:
  `AlgebraicGeometry.Monoscheme.monoidAlgebra`, whose object construction is
  `CommRingCat.of (MonoidAlgebra k P)` and whose maps are monomial substitutions.
  This recorded definition explains the algebra chosen here; no duplicate
  realization or formal-sum ring is constructed.
- Mathlib.RingTheory.Localization.AtPrime.Basic: `Localization.AtPrime`, whose
  complete signature uses `[P.IsPrime]` and abbreviates `Localization P.primeCompl`.
  Read its source and the recorded residue-field/fibre-ring dependency entry.
  The fibre-ring clause is not needed by this item.
- Mathlib.RingTheory.Ideal.Cotangent: `Ideal.Cotangent`, `Ideal.mapCotangent`,
  `Ideal.toCotangent`, and `Ideal.cotangentToQuotientSquare` (including the latter's
  injectivity theorem). These give the exact canonical quotient and map.
- Mathlib.Algebra.Group.Irreducible.Defs: `Irreducible` and its full two-field
  definition. Under sharpness this is exactly the nonidentity atom predicate.

Edge cases checked before drafting: the trivial R has no irreducibles, and only
the Laurent coordinate vectors remain; t=0 removes the torus family; when both
are trivial B=k and both cotangent spaces have empty bases and dimension zero.
For R=N, t=0 there is one atom and one cotangent vector; for R=N² there are two.
For the unsaturated additive submonoid generated by 2 and 3, both are atoms,
giving cotangent dimension two without adding saturation. In characteristic p,
y^p-1 has zero linear term, as required by the integer coefficient formula; it
does not remove the basis vector y-1. No positive-characteristic exclusion or
nonempty-index requirement is imposed. The prime-instance quantifier is
nonvacuous because the theorem separately asserts maximality.

Searches made (the recorded logs are searches.jsonl in this sandbox):

- msearch LeanFinder: “Monoid algebra sharp vertex cotangent basis irreducible
  monomials Laurent torus coordinates”; eight hits, led by
  Algebra.Generators.basisCotangentAway_apply and cotangentSpaceBasis, concerning
  presentations and differentials, not this monomial-vertex basis theorem.
- msearch LeanSearch: “The irreducible monomials form a basis of the cotangent
  space at the vertex of a sharp monoid algebra.”; eight hits. Generic polynomial
  and monoid-algebra bases and presentation cotangents do not state this item.
- msearch Loogle: `"MonoidAlgebra", "Cotangent"`; zero hits.
- msearch grep in Algebra/AffineMonoid:
  `cotangent.*monoid|monoid.*cotangent|finite_irreducible|closure_irreducible`;
  four lines, including finite_irreducible and Submonoid.closure_irreducible.
  Opened the full source: these give the atom finiteness/generation subclaims
  with their standard finite-generation/cancellation/unit instances, not the
  complete theorem, and no second theorem for those subclaims was written.
- rg of lean/WeilConjectures and lean/Sheaf for
  `sharp.*[Vv]ertex|vertex.*[Cc]otangent|[Cc]otangent.*[Aa]tom`: only the existing
  ToricMonoidComparison proof docstring discusses this argument, with no exact
  statement. Also ran the item-id grep in WeilConjectures (no hit).
- Read Mathlib's Ideal/Cotangent source and searched its map API, using
  Ideal.mapCotangent rather than inventing a canonical quotient comparison.

There is no statement correction or mathematical dispute.

## Dependency modules

No dependency delta remains in the final delivery. Both recorded modules were
legacy non-module files when this task began, and the first server compile
confirmed Lean rejects them from a required module-mode statement. I validated
format-only migrations in the sandbox. During validation, Q120 and then Q109
landed the identical migrations. I read the live source and records again and
replaced both dependency copies with those exact current versions, preserving
the published ownership and notes. These copies are supplied to scompile solely
because its last verified build still has legacy artifacts; they contribute no
new definitions or changes to the delivery. Only the item and report are new.

`def-trf-fine-fan-blowup`: the final compile input is the current landed module
and node record, byte for byte. It preserves the full recorded fine-fan and
saturated-blowup interface, including the exact IsFine and IsSharp predicates.

`def-trf-monoscheme-toric-realization`: the final compile input is likewise the
current landed module and node record, byte for byte. It preserves the recorded
finite-formal-sum monoid algebra and all monoscheme realization declarations.
No smaller private copy or specialization of this definition is introduced.

## Second reading by Q97

This is an explicit self-check by the dispatched worker; no independent agent
was started because the dispatcher expressly forbids starting other agents.
The maintainer's independent review remains the independent reading.

I reopened the item and the complete statement. The field, fine, sharp and
completion torsion hypotheses each occur with their original objects. Torus
rank is an arbitrary natural number. I checked every conjunct and basis formula
against the node, including the localization-map equality and the explicit local
dimension. Irreducible agrees with atom only because the same statement assumes
sharpness; that hypothesis is present. The algebra uses integer exponent vectors,
not natural ones, so negative Laurent powers are retained. The basis-index sum
has no nonempty hypothesis. The equality after cotangentToQuotientSquare pins
the atom and torus classes and uses the standard injective map. The local basis
is the image under the exact natural map. I diagnosed both old-format dependency interfaces. Both migrations landed concurrently and are reused byte for byte, without
duplicating either notion or changing either published record.
I also repaired the pattern-match branch syntax from ↦ to => on first compile.
The dependency migrations preserve their entire notions, not just the part this
item needs. No item statement change, new hypothesis or omitted clause remains.

Validation: the first complete three-file server compile was clean (5.3, 9.4,
and 2.0 seconds for the separate sandbox files). The first delivery dry run
passed preflight and compilation at 5f6f7ee4664 without pushing. Its fresh base
exposed the concurrent Q120 FineFan migration, which prompted removing the
redundant dependency migration before repeating the dry run. The two-file
retry revealed the old published FineFan artifact, so the exact current FineFan
source and node were restored as compile inputs, with no change to either. The
final delivery delta therefore has only the item and the monoscheme dependency
module, while three files are checked separately in the private compile.

Final parallel-landing refresh: the later Q109 landing migrated both dependencies.
The initial push a93c0f84a08 crossed that landing and still carried redundant
format/record deltas; before completing this task I refreshed both owning sources
and node records to the exact live versions and repeated preflight and delivery.
The replacement packet preserves their ownership and contains only the new item
statement, its lean record and this report. The three supplied files are still
compiled individually to work against the old published artifacts.
