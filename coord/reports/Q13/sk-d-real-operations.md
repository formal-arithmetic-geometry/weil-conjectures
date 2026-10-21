## Worker report

The item is a definition sketch covering several existing notions, just as its
statement dependency `sk-d-linear` is. No new module, definition or theorem is
introduced. The `existing: true` record is anchored at
`AlgebraicGeometry.WeilGroup.detLine` in
`WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra`.
Its `declarations` and `note`, together with the following source map, record the
whole sketch; the determinant declaration alone is not asserted to be the whole
item. The record deliberately uses an already existing declaration rather than
introducing an artificial tuple packaging existing objects.

Read the current main-20261015 blueprint unit `_section.md`, the whole item,
all four statement-dependency statements and Lean records, and the actual
signatures and docstrings of the declarations below. No repair note exists for
this item. The example CompactObject module is withdrawn; its node now points
to the upstream module, which was also read. No statement correction is needed.

Every hypothesis and clause maps as follows. In these expressions `k` is the
coefficient field and `G = W.carrier`, where `W` is the actual presented Weil
group supplied by `sk-d-real-weil`; for the named Weil-line abbreviations
`k = PadicAlgCl l`, the standard realization of Qbar_l. The representation
operations themselves are generic in the coefficient field and in independent
group/vector universes. Their use does not replace the geometric Weil group
by an arbitrary unrelated group.

| Node clause | Existing Lean rendering and source |
| --- | --- |
| Weil representations of `sk-d-real-weil` | `Representation k W.carrier V`; `W : AlgebraicGeometry.WeilGroup p` is the actual Weil-group presentation reused by `Sheaf.Paper.RealWeilSheaves`, not a new group. `Fact l.Prime`, the finite base field and its curve structure are exactly the standing source data. |
| Ordinary direct sum | `Representation.directSum` in `Mathlib.RepresentationTheory.Basic` acts componentwise on the direct sum. For a binary sum the existing `Representation.prod` uses `(ρ g).prodMap (σ g)`, the equivalent binary direct sum. |
| Diagonal tensor action | `Representation.tprod` in the same module has action `TensorProduct.map (ρ g) (σ g)`, hence sends `v ⊗ w` to `ρ g v ⊗ σ g w`. |
| Exterior action | `Representation.exteriorPower ρ r` in `WeilConjectures.Mathlib.RepresentationTheory.Basic` has action `_root_.exteriorPower.map r (ρ g)` on `↥(⋀[k]^r V)`, so applies `ρ g` to each wedge factor. |
| Dual inverse action | `Representation.dual ρ` in `Mathlib.RepresentationTheory.Basic` sends a linear form `f` to `f ∘ₗ ρ g⁻¹`, exactly `(gλ)(v)=λ(g⁻¹v)`. |
| Determinant is the top exterior power | `AlgebraicGeometry.WeilGroup.detLine W l ρ` in `RealSheaves.LinearAlgebra` is definitionally `ρ.exteriorPower (Module.finrank (PadicAlgCl l) V)`. For arbitrary coefficient/vector universes use that same generic exterior-power expression, not a separate determinant construction. |
| Nonzero irreducible and no proper nonzero invariant subspace | `Representation.IsIrreducible` in `Mathlib.RepresentationTheory.Irreducible` is `IsSimpleOrder (Subrepresentation ρ)`. `Representation.isIrreducible_iff` in `WeilConjectures.Mathlib.RepresentationTheory.Irreducible` states precisely `Nontrivial V ∧ ∀ U : Submodule k V, (∀ g, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤`. |
| Constituent is an irreducible subquotient up to isomorphism | `Representation.IsConstituent σ ρ` in the latter module is `σ.IsIrreducible ∧ ∃ N M : Subrepresentation ρ, N ≤ M ∧ Nonempty (σ.asModule ≃ₗ[MonoidAlgebra k G] (M.asSubmodule ⧸ Submodule.comap M.asSubmodule.subtype N.asSubmodule))`. The k[G]-linear equivalence is exactly an equivariant linear equivalence, via the existing `Representation.Equiv.asModuleLinearEquiv` and `.ofAsModuleLinearEquiv`. `Subrepresentation` already asserts stability, and `N ≤ M` is explicit. |
| Finite-dimensional constituents are successive quotients | `Representation.exists_compositionSeries` applies with `[FiniteDimensional k V]`. The dependency's `Representation.CompositionSeries.factor s i` is exactly `(s.series i.succ).subquotient (s.series i.castSucc)` and `.isIrreducible_factor` asserts simplicity. Conversely `Subrepresentation.exists_equiv_of_isIrreducible_subquotient` in `WeilConjectures.RepresentationTheory.CompositionFactors` identifies every irreducible subquotient with a factor of any such series, using the chain endpoint conditions and covering steps. `Representation.CompositionSeries.exists_chain` in that module converts the recorded series to this chain interface. |
| Multiplicity retained | The index is `Fin s.length`, with a separate index for every step even when two factors are isomorphic. `.jordanHolder` in `WeilConjectures.RepresentationTheory.CompositionSeries` gives a bijection of the factor index sets and an equivariant isomorphism for every pair. Thus it preserves repetitions. The Prop `IsConstituent` is not being used as a multiplicity counter. |
| Their direct sum is a semisimplification | `Representation.CompositionSeries.semisimplification s` in the same module is `Representation.directSum (fun i ↦ s.factor i)` on exactly the quotient spaces above. `.nonempty_semisimplification_equiv` gives independence up to equivariant isomorphism, as in the recorded dependency. |
| Arbitrary subgroup I, invariant vectors | For `I : Subgroup W.carrier`, `(ρ.comp I.subtype).invariants` in `Mathlib.RepresentationTheory.Invariants` has carrier `{v | ∀ g : I, ρ g v = v}`. No normality is required. |
| Coinvariant quotient by the coefficient-linear span | `(ρ.comp I.subtype).Coinvariants` in `Mathlib.RepresentationTheory.Coinvariants` is the quotient by `Coinvariants.ker`, which is definitionally `Submodule.span k (Set.range (fun gv : I × V ↦ ρ gv.1 gv.2 - gv.2))`. This is exactly the displayed span, not a quotient by the mere set of differences. No whole-Weil action on the quotient is asserted. This module must be imported explicitly; it is not re-exported by the anchor module. |
| b is nonzero, constant line action | `AlgebraicGeometry.WeilGroup.constLine W l b` in `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic` takes `b : (PadicAlgCl l)ˣ`, and its action is `(b ^ Multiplicative.toAdd (W.deg g) : (PadicAlgCl l)ˣ) • (1 : Module.End _ _)`. On z this is exactly `b^(deg g) z`; the integer degree is written multiplicatively only for the homomorphism API. The definition contains real action data. |
| Tate line for every integer n | `AlgebraicGeometry.WeilGroup.tateLine W l n` in the same module is `W.constLine l (Units.mk0 ((Nat.card K : PadicAlgCl l) ^ (-n)) ...)`. `Nat.card K` is q, and the proof argument states its integer power is nonzero. Thus this is exactly `B_(q^(-n))`, with the geometric Frobenius convention of the source. |

The four statement dependencies are used without replacement:

- `sk-d-real-weil`: `Sheaf.Paper.RealWeilSheaves`, especially the underlying
  `AlgebraicGeometry.WeilGroup`, `IsLisseInEveryBasis`, and the finite-dimensional
  compatibility theorem with the original `IsLisse`. The new constructible-pair
  structure of that node is not needed for these representation operations.
- `sk-d-linear`: its recorded `Representation`, `Subrepresentation`, subquotient,
  direct sum, tensor and exterior-power declarations. The record's importing
  module is `WeilConjectures.RepresentationTheory.CompositionSeries`.
- `def-mg-weil-composition-series`: precisely
  `Representation.CompositionSeries` and `.factor` in that module.
- `def-mg-weil-semisimplification`: precisely
  `Representation.CompositionSeries.semisimplification` in that module.

The three theorem proof dependencies are also the recorded declarations in
`WeilConjectures.RepresentationTheory.CompositionSeries`:
`Representation.exists_compositionSeries`,
`Representation.CompositionSeries.jordanHolder`, and
`Representation.CompositionSeries.nonempty_semisimplification_equiv`.
No version specialized to monodromy data is copied. Specializing these generic
interfaces to the Weil representation imposes no additional mathematical
hypothesis. All construction data are already real definitions, and no new
`sorry`, proof or axiom is introduced in this delivery.

Edge cases checked against the definitions and source:

- For V=0 there are no irreducible subquotients, the series has length zero and
  its semisimplification is the empty direct sum. Irreducibility explicitly
  excludes the zero representation.
- A simple rank-one representation is its sole factor; repeated isomorphic
  rank-one factors remain repeated in `Fin s.length`. A nontrivial unipotent
  rank-two representation need not be isomorphic to its semisimplification;
  no such claim is made.
- r=0 gives the usual zeroth exterior power, including det(0); r larger than
  rank gives the zero exterior power. Negative exterior indices are not part
  of the source.
- N=0 and M=V are allowed, as are zero subquotients before imposing
  irreducibility. The condition N≤M is present.
- I may be trivial, the whole group, or nonnormal. For trivial I the span of
  differences is zero and every vector is fixed. No full-group action is
  required on either space for nonnormal I.
- b=1 gives the trivial character. b need not be an integral unit; all nonzero
  elements of Qbar_l are allowed. Negative degree is handled by integer powers.
- n=0 gives the trivial Tate line; n=1 gives geometric Frobenius eigenvalue
  q^(-1), and negative n is also allowed. q is nonzero in characteristic zero.
- Generic algebraic APIs have independent group/coefficient/vector universes.
  The same-universe `detLine` abbreviation is only an attachment anchor;
  the underlying exterior-power formula covers all sizes without identifying
  universes, and no new hypothesis is added.

Searches actually run (msearch search transcripts are retained by the tool):

- LeanFinder: `Weil representations direct sum tensor exterior dual constituents
  composition series invariants coinvariants constant Tate character` returned
  eight mostly coinvariant-tensor results, including
  `Rep.coinvariantsTensorFreeLEquiv`; no single packaged definition.
- Loogle: `Representation.IsConstituent, Representation.dual,
  Representation.Coinvariants` returned zero hits because the project-only
  `Representation.IsConstituent` is unknown to the Mathlib service. This does
  not mean it is absent upstream: its actual source was found and read.
- LeanSearch: `Weil representation constituents subquotients composition series
  constant Tate lines` returned eight hits, including `CompositionSeries`,
  `Rep.quotient` and `Subrepresentation.instLattice`; no packaged definition.
- msearch grep: `def IsConstituent|def dual|def Coinvariants|def invariants|def
  prod|def tprod` in RepresentationTheory returned the exact Mathlib basic
  operations, invariant and coinvariant definitions among other hits.
- Local `rg` and the prescribed `grep -rn sk-d-real-operations` on
  `lean/WeilConjectures` found `RealSheaves.Basic`'s constant/Tate lines and
  `Mathlib.RepresentationTheory.Irreducible`'s exact constituent predicate.
  The further `rg` queries found `RealSheaves.LinearAlgebra.detLine`, the
  composition-series module, and `CompositionFactors`'s correspondence theorem.
- `rg` for `IsConstituent|constLine|tateLine|detLine` in `lean/Sheaf` returned
  no alternative declarations. Mathlib source searches located the exact
  invariant/coinvariant spans, the inverse dual, and component/diagonal actions.

These individual exact matches jointly realize all clauses of this definition
sketch, with the same objects and formulas. A new definition for any of them
would violate one definition per notion. The existing-record choice follows
that already used for `sk-d-linear`, with the extra modules explicitly named
rather than falsely asserting the anchor module exports everything.

Validation: `scompile.py Q13 sk-d-real-operations` checked a sandbox-only probe
importing the anchor, `Mathlib.RepresentationTheory.Coinvariants`, and
`WeilConjectures.RepresentationTheory.CompositionFactors`. All nineteen
attachment declarations, coinvariants and its span, and the irreducible
subquotient correspondence checked successfully against the live server
library, with no errors or warnings. The probe introduces no declarations and
is not a delivered module. The delivery wrapper independently checks all
recorded declarations using only the recorded anchor import.

The first dry run requested the upstream branch marker `slopmaster2` for the
WeilConjectures attachment and printed the canonical existing-signature form
`abbrev detLine : Representation (PadicAlgCl l) W.carrier
↥(⋀[PadicAlgCl l]^(Module.finrank (PadicAlgCl l) V) V)`. Both metadata
fields were aligned with that existing-declaration reader; no Lean or
mathematical statement was changed.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
