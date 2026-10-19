## Worker report

The module `Sheaf.AlgebraicGeometry.GenericPointGeometricIrreducibility` states
`AlgebraicGeometry.geometricallyIrreducible_iff_genericResidueField`, with `sorry` as its
entire proof. It introduces no definition. The DAG statement is unchanged. Source checked:
`literature/stacks-project/varieties.tex`, Tag 054Q,
`lemma-geometrically-irreducible-function-field`, equivalence (1) and (2), together with
its proof (lines 1446–1490). This is a supporting node, not the blueprint unit statement.
No repair note exists for this item.

Each hypothesis and clause is rendered as follows:

| Node text | Lean rendering |
| --- | --- |
| Let k be a field | `(k : Type u) [Field k]` |
| X a k-scheme | `(X : Scheme.{u}) [X.Over (Spec (.of k))]`; its structure map is `X ↘ Spec (.of k)` |
| X irreducible | `[IrreducibleSpace X]`, including nonemptiness |
| ξ its generic point | `(ξ : X) (hξ : IsGenericPoint ξ (Set.univ : Set X))` |
| Closure of {ξ} is all of X | `IsGenericPoint` is exactly `closure {ξ} = Set.univ` |
| Its residue field κ(ξ) | `X.residueField ξ`, the quotient of its local stalk by its maximal ideal |
| Induced k-algebra structure | The spectrum has structure map `X.fromSpecResidueField ξ ≫ X ↘ Spec (.of k)` |
| X geometrically irreducible over k | `GeometricallyIrreducible (X ↘ Spec (.of k))` |
| If and only if Spec κ(ξ) is geometrically irreducible over k | `↔ GeometricallyIrreducible (X.fromSpecResidueField ξ ≫ X ↘ Spec (.of k))` |
| No reducedness or finite-type hypothesis | Neither is a binder or implicit assumption of the theorem |

The right-hand morphism has domain `Spec (X.residueField ξ)`. It is the canonical map,
not a quantified or chosen map. In Mathlib's `ResidueField.lean`,
`Scheme.fromSpecResidueField` is `Spec.map (X.residue ξ) ≫ X.fromSpecStalk ξ`, and
`Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField` identifies its composite with
any structure map with the induced residue-field map. Thus this expression uses exactly
the induced field extension of the node; it needs no new algebra instance or bridge.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` is a convention-only node, explicitly fixing no
  additional notion. Schemes and morphisms are Mathlib's `AlgebraicGeometry.Scheme` and
  `Scheme.Hom` (available through the public imports).
- `def-weil-irreducible-components` has Mathlib match `irreducibleComponents` in
  `Mathlib.Topology.Irreducible`. Its irreducibility notion is Mathlib's `IsIrreducible` /
  `IrreducibleSpace`, whose definitions were read; no component is needed in this statement.
- `def-sc-generic-point`: `IsGenericPoint` from `Mathlib.Topology.Sober`, publicly imported.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`, from
  `Mathlib.AlgebraicGeometry.ResidueField`, publicly imported. The same module supplies
  the canonical `Scheme.fromSpecResidueField` used in the signature.
- `def-pc-geometrically-irreducible`: `AlgebraicGeometry.GeometricallyIrreducible`, from
  `Mathlib.AlgebraicGeometry.Geometrically.Irreducible`, publicly imported. Its definition
  and `AlgebraicGeometry.geometrically_iff_of_commRing` in
  `Mathlib.AlgebraicGeometry.Geometrically.Basic` were read: over `Spec k` it quantifies over field extensions and irreducibility of base changes.

The stated proof dependencies are imported without `public`:
`WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism`,
`Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso`,
`Mathlib.AlgebraicGeometry.FunctionField`, and
`WeilConjectures.Topology.PresheafModuleStalkFunctor`. Mathlib's integral-scheme and
scheme declarations are already supplied by those imports. The two new proof nodes
`lem-zl-geometric-irreducibility-affine-local` and
`lem-zl-geometric-irreducibility-subalgebra-colimit` have no recorded Lean declaration
or Mathlib match, so there is no module to import for them yet; they are referenced in
full in the proof docstring. They are not needed to type this statement. The maintainer
can add their imports when they are stated. Live source for the reduction and presheaf
stalk modules was read using `scompile.py --source`, since the older checkout lacks them.
The docstring carries all five proof steps, including reduction, the generic stalk's
affine-neighbourhood colimit, both implications, and transfer back to X.

Edge cases checked before writing:

- The empty scheme is excluded exactly by irreducibility and by the specified point ξ;
  it is not accidentally counted as irreducible.
- Nonreduced schemes remain allowed: for `Spec (k[ε]/(ε²))`, the generic residue field
  is k, and every field base change stays topologically one point, so both sides hold.
- The assertion detects failure: `Spec ℂ` over ℝ has generic residue field ℂ, and after
  extension to ℂ both sides fail irreducibility. The conclusion is not automatic for fields.
- Purely inseparable extensions in positive characteristic are allowed. No separability,
  perfectness or characteristic-zero assumption appears.
- Schemes of arbitrary type, including infinite-dimensional affine schemes and schemes
  without a finite-type or separatedness assumption, remain allowed; the source proof
  uses affine neighbourhoods, not a finite cover.
- `ξ` is an arbitrary specified generic point; no additional choice or equality to
  Mathlib's chosen generic point is imposed.
- Universe `u` is explicit, with k and X in Mathlib's common universe convention; no
  independent smaller universe is used for test extensions. All variables are bound.

Searches actually run (using `msearch.py Q109 lem-zl-generic-point-geometric-irreducibility`):

- `leanfinder`: “Irreducible scheme over a field geometrically irreducible if and only if
  residue field at its generic point is geometrically irreducible”. Eight hits, including
  `Scheme.SpecToEquivOfField`, `Scheme.instFieldCarrierResidueField`, and integral-scheme
  results; no equivalent criterion.
- `loogle`: `AlgebraicGeometry.GeometricallyIrreducible, AlgebraicGeometry.Scheme.residueField`.
  Two hits, `instGeometricallyIrreducibleFiberToSpecResidueField` and
  `GeometricallyIrreducible.iff_geometricallyIrreducible_fiber`; both concern fibres over
  points of the base, not the residue field at the generic point of X.
- `grep`: `geometricallyIrreducible.*(function|generic|residue)|geometrically_irreducible.*(function|generic|residue)`.
  Two hits, both the base-fibre results above in `Mathlib/AlgebraicGeometry/Geometrically/Irreducible.lean`.
- `leansearch`: “Geometric irreducibility of an irreducible scheme is equivalent to
  geometric irreducibility of its generic residue field”. Eight hits, giving integral,
  residue-field and generic-point infrastructure, but no exact result.
- `rg` with the same geometric-irreducibility/generic/residue/function patterns in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no matching criterion.
- `grep -rn 'lem-zl-generic-point-geometric-irreducibility'` in the upstream
  `WeilConjectures` tree: no match.
- A second `rg` search for geometric irreducibility next to residue fields, and for
  `geometricallyIrreducible_iff`, in both project algebraic-geometry trees: no match.
- Exact proposed module/declaration names searched in Mathlib, upstream, `lean/Sheaf`
  and `dag/lean_names_upstream.json`: no collision.

No statement correction, new node, dependency repair, or disputed mathematical claim
was needed. Only the item's `lean` record changes in its JSON copy.

## Second reading by Q109

This is a final self-check; the dispatcher's brief forbids other agents and assigns the
independent review to the maintainer. Rereading the source, node and signature together:
all hypotheses and both sides match the table above. In particular, the right side is
geometric irreducibility over the original k, not over κ(ξ), and the theorem does not
replace irreducibility by integrality or add reducedness. The generic-point hypothesis
is explicit and the residue-field structure is canonical. No mismatch was found.

Validation: `scompile.py Q109 lem-zl-generic-point-geometric-irreducibility` compiled
this module cleanly in both wrapper passes (15.2 s sandbox, 29.7 s library), with no
compiler errors or warnings. The delivered Lean file has no line over 100 characters.
