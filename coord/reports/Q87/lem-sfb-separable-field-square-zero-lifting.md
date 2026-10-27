## Worker report

The delivery states `Algebra.exists_lift_of_isSeparableExtension` in
`Sheaf.FieldTheory.SeparableFieldSquareZeroLifting`. Its only theorem has proof `sorry`.
No definition is introduced, no node statement is corrected, and only the item's `lean`
field changes. The module docstring and theorem docstring cite the source and the item;
the theorem docstring gives all four accepted proof steps and their DAG dependencies.

Read Stacks `algebra.tex`, Tag 0322 (`proposition-characterize-separable-field-extensions`),
Tag 0320 (`lemma-formally-smooth-extensions-easy`), Tag 031Z
(`lemma-characterize-formally-smooth-field-extension`), and Tag 00TI
(`definition-formally-smooth`). These sources impose no algebraicity, finite generation,
or characteristic restriction on the separable extension in the item.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Fields k and L | `(k : Type u) (L : Type v) [Field k] [Field L]` |
| Extension k ⊆ L | `[Algebra k L]`; the structure map from a field to a field is injective |
| Every intermediate field finitely generated as a field is separably generated | `(hsep : IsSeparableExtension k L)` in namespace `Algebra`; the recorded definition is exactly `∀ F : IntermediateField k L, F.FG → IsSeparablyGenerated k F` |
| Every commutative k-algebra D | `(D : Type w) [CommRing D] [Algebra k D]` |
| Ideal J ⊆ D | `(J : Ideal D)` |
| J² = 0 | `(hJ : J ^ 2 = ⊥)`, where the bottom ideal is the zero ideal |
| Every k-algebra homomorphism g : L → D/J | `(g : L →ₐ[k] D ⧸ J)` |
| There is a k-algebra homomorphism f : L → D | `∃ f : L →ₐ[k] D, ...` |
| q ∘ f = g, with the quotient map q | `(Ideal.Quotient.mkₐ k J).comp f = g` |
| No algebraicity, finite generation, or characteristic hypothesis | None occurs in the signature; all three universes u, v, w are explicitly declared and independent |

There is no separate quotient map binder: the equation uses exactly the canonical map,
not an arbitrary surjection. The quotient algebra structure is Mathlib's structure induced
from the map k → D → D/J. `AlgHom` includes preservation of that structure map.
Every type, structure, ideal, homomorphism and universe in the signature is explicitly bound;
there are no auto-bound implicits, file-local notation, helper instances, or hidden choices.
The arbitrary test algebra is a parameter of the universally polymorphic theorem, not a
quantifier fixed to a smaller universe inside a formal-smoothness predicate.

Dependency declarations read and used:

- `def-weil-pbc-separable-field-extension`: public import
  `WeilConjectures.FieldTheory.SeparableExtension`, declarations
  `Algebra.IsSeparableExtension` and `Algebra.IsSeparablyGenerated` (lines 34–46).
  The latter uses a transcendence basis and `Algebra.IsSeparable` over its generated
  intermediate field. This is the general separability notion, not just algebraic separability.
- `def-weil-pbc-algebra-hom-quotient`: public import
  `Mathlib.RingTheory.Ideal.Quotient.Operations`, declarations `Ideal.Quotient.algebra`
  (line 354) and `Ideal.Quotient.mkₐ` (line 370); `AlgHom` in
  `Mathlib.Algebra.Algebra.Hom` (line 30). Their signatures and docstrings were read.
- Proof-only import `Mathlib.RingTheory.Smooth.Field` exposes
  `Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable` (lines 44–51),
  the recorded match for `lem-sfb-separably-generated-field-h1-zero`, together with
  `Algebra.FormallySmooth.subsingleton_h1Cotangent` from `Smooth.Basic` (line 72).
  The local pinned source has no `EssFiniteType` assumption here, although the remote
  semantic-search index printed a stale signature with that assumption.
- Proof-only import `WeilConjectures.RingTheory.H1CotangentFiniteSubfields`, declaration
  `Algebra.subsingleton_h1Cotangent_of_finite_subfields`: any two universe levels, fields
  k and L with an algebra structure, and vanishing for every `E.FG` imply vanishing for L.
  Read its entire statement and finite-support proof docstring.
- Proof-only import `Mathlib.RingTheory.Kaehler.Basic`, declarations
  `KaehlerDifferential` (line 153), `KaehlerDifferential.D` (line 198), and
  `KaehlerDifferential.linearMapEquivDerivation` (line 327), as recorded for
  `def-weil-pbc-kahler-differentials`.
- Proof-only imports `Mathlib.LinearAlgebra.Basis.VectorSpace` and
  `Mathlib.Algebra.Module.Projective`: `Module.Free.of_divisionRing` (line 156) and
  `Module.Projective.of_free` (line 161), the recorded matches for
  `lem-weil-pbc-vector-space-projective`; neither requires finite dimension.
- The recorded lifting match `Algebra.FormallySmooth.comp_surjective` in
  `Mathlib.RingTheory.Smooth.Basic` (line 80, imported by `Smooth.Field`) takes
  `[FormallySmooth k L]`, an ideal with square zero, and yields precisely the displayed
  surjectivity of composition with the quotient algebra map. The `FormallySmooth` class
  fields are exactly differential-module projectivity and cotangent-homology vanishing.

Edge cases checked mathematically before writing:

- L = k and the finitely generated intermediate field E = k are included. The lift for
  L = k is the structure map; the empty transcendence basis is allowed by the definition.
- Arbitrarily large purely transcendental and separable algebraic extensions are included.
  No whole-extension separating basis or finite dimensionality is assumed.
- J = 0 is allowed and asks for the ordinary lift through D/0 ≅ D.
- D may be the zero ring; its unique maps satisfy the asserted equation. J = ⊤ can satisfy
  J² = 0 only in this zero-ring case, so it creates no omitted nonzero-ring obstruction.
- In positive characteristic an inseparable extension such as
  F_p(s) ⊆ F_p(s)(s^(1/p)) fails `hsep`, as it should. Separability is a substantive
  hypothesis, not an automatically inhabited structure.
- A nonzero square-zero ideal, for instance (ε) in a dual-number algebra over L, is allowed.
  Existence is asserted without uniqueness, appropriate for transcendental extensions.
- All universe levels and all characteristics are unrestricted.

Searches actually run (msearch logs are in the sandbox):

1. LeanFinder: “An arbitrary separable field extension, meaning every finitely generated
   intermediate field is separably generated, lifts algebra maps across square-zero ideals”.
   Eight hits: separably closed-field lifting, the separably generated formal-smoothness
   theorem, algebraic formal étaleness, and generic infinitesimal extensions. No exact match.
2. Loogle: `"FormallySmooth", "IsSeparableExtension"`. Zero hits.
3. msearch grep: `IsSeparableExtension|separable.*[Ll]ift|[Ll]ift.*separable` in
   Mathlib/RingTheory. One unrelated separable-closure lift in `Trace/Basic.lean:288`.
4. LeanFinder: “there exists a k-algebra homomorphism lifting a map from a separable field
   extension to a square-zero quotient”. Eight hits include
   `Algebra.FormallySmooth.exists_lift`, requiring formal smoothness already, and
   `TrivSqZeroExt.lift`; none derives lifting from the general predicate `hsep`.
5. `rg` with the same separability/lifting pattern in `lean/WeilConjectures` and
   `lean/Sheaf`: read the defining `SeparableExtension` module and relevant hits;
   `HenselianSeparablyGeneratedResidueSection.lift_separable_field` is private and has
   algebraic separability and a henselian local target. `FgSeparableSmooth` is restricted
   to essentially finite type. `SeparableSmoothColimit` is an ind-smooth presentation,
   not this lifting statement. None is an exact reusable declaration for the item.
6. `grep -rn` for the exact item id in `lean/WeilConjectures`: no hits.
7. `rg` in `dag/lean_names_upstream.json` for the id and `IsSeparableExtension`: found
   the existing separability definition, no lifting attachment. A duplicate-name search
   for `exists_lift_of_isSeparableExtension|SeparableFieldSquareZeroLifting` in both
   project source trees and the upstream name index returned no hits.

8. LeanSearch: “An arbitrary separable field extension lifts algebra maps through
   square-zero quotient ideals”. Eight hits include `FormallySmooth.lift`,
   `FormallyEtale.of_isSeparable`, `AlgHom.kerSquareLift` and square-zero derivation
   equivalences. They do not give the general separability-to-lifting implication.

No disputed statement or dependency fault was found. No new nodes or dependency repairs
are needed. The supplied CompactObject example is now a withdrawn module; its node points
to the upstream definition. The delivered file follows the required module-mode header,
public statement imports, plain proof imports, source docstrings and public section.

Validation: the prescribed `scompile.py` compiled both its sandbox check and the module
against the server's published library cleanly (1.4 seconds each). The prescribed `deliver2.py --no-push` then passed server preflight and its
repeated per-file compile, printing OK for dry-run commit `73fd0cdd18d`.

## Second reading by Q87

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
