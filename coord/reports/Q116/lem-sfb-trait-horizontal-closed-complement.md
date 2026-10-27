## Worker report

The module `Sheaf.AlgebraicGeometry.TraitHorizontalClosedComplement` states
`AlgebraicGeometry.trait_horizontal_closed_complement`, with its sole proof `sorry`.
The node is unchanged except for `lean`. No new notions or dependency repairs are needed.

The primary BLR scan was opened online at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf,
PDF p.168 / printed p.162, §6.5 Theorem 1 proof. The paragraph beginning with the
reduction to affine generic fibre removes the schematic closure of the generic
complement and asserts the resulting open is dense over the trait. The Lean
statement renders exactly the isolated node, without imposing the surrounding
descent data. The module docstring carries all eight proof steps and their nodes.

Hypotheses and objects, clause by clause:

- The DVR is `{R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`.
  `Spec (.of R)` is T. The zero prime is `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)`.
  `f.fiber` at that prime is Y_F, using the canonical residue field at zero,
  canonically Frac(R). Likewise `f.fiber (IsLocalRing.closedPoint R)` is Y_k,
  using the canonical residue field at the maximal prime, canonically R/m.
  This is the existing fibre convention, not another definition or an extra hypothesis.
- `{Y : Scheme.{u}} (f : Y ⟶ Spec (.of R))` supplies the scheme and morphism.
  `[Smooth f]`, `[IsSeparated f]`, `[LocallyOfFiniteType f]`, `[QuasiCompact f]`
  give smooth, separated and finite type. `IsSeparated` means precisely that
  `pullback.diagonal f` is a closed immersion. Finite type is the conjunction of
  the last two classes; no relative dimension is specified.
- `{ZF : Scheme.{u}}` and `i : ZF ⟶ f.fiber ...` with `[IsClosedImmersion i]`
  give the actual closed subscheme, including its possible nonreduced structure.
  `hthin` says for every C in `irreducibleComponents` of the generic fibre,
  `¬ C ⊆ i.ker.support`. For a closed immersion that support is its closed image.
- The composite `i ≫ f.fiberι ...` is the map ZF → Y. Its scheme-theoretic image
  is Mathlib's `Scheme.Hom.image`, defined as its kernel ideal's subscheme.
  Its underlying closed subset is exactly `.ker.support`. The displayed use of
  that support therefore refers to the schematic closure specified in the node;
  it is not an independently chosen topological closure or a reduced replacement.
- The open complement is `.ker.support.compl`, Mathlib's open complement of a
  bundled closed set. Its canonical open subscheme and inclusion are given by
  `.toScheme` and `.ι`; no existential choice or additional definition is needed.

Conclusions, clause by clause:

- The first conjunct is equality of open subsets on Y_F: the inverse image
  `f.fiberι ... ⁻¹ᵁ (composite).ker.support.compl` equals `i.ker.support.compl`.
  Base change of an open subscheme is the open subscheme of the inverse-image
  open, so this is exactly the prescribed generic fibre Y_F minus |ZF|.
- The second conjunct quantifies over every `t : Spec (.of R)`, every
  `Ω : Type u`, `[Field Ω]`, `[Algebra ((Spec (.of R)).residueField t) Ω]`, and
  `[IsAlgClosed Ω]`. There is no algebraicity requirement: arbitrary
  algebraically closed extensions, including transcendental ones, are covered.
  The map from Spec Ω is `Spec.map (CommRingCat.ofHom (algebraMap ... Ω))`
  followed by `fromSpecResidueField t`. The scheme is the actual `pullback f`
  along that map. `Dense` of the inverse image of the open complement under
  `pullback.fst` states its density in this geometric fibre.
- The last conjunct quantifies over all components of `f.fiber (closedPoint R)`
  and says no such component lies in the inverse image of the schematic image
  support under `f.fiberι (closedPoint R)`. This is precisely the final
  closed-fibre exclusion, in its correct ambient fibre rather than in Y.

Universes and edge cases were checked before drafting. Everything is universally
polymorphic in u, with schemes and extension fields in that common ambient
universe, as in the recorded base-change interface. There is no independent
smaller test universe. No `Nonempty`, connectedness, equidimensionality, integral
scheme, perfection, completeness or excellence hypothesis occurs. Empty Y and
empty ordinary/geometric fibres give vacuous component conditions and density
on the empty space. Empty ZF has unit kernel ideal, empty image support, and
whole open complement. If ZF is the whole of a nonempty generic component,
`hthin` fails as it should. Relative dimension zero and mixtures of relative
dimensions are allowed. Nonreduced closed ZF is allowed; the schematic closure
still uses its full ideal. A vertical closed subscheme is not incorrectly
substituted for the closure of a generic subscheme.

Dependency declarations read and reused:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic` (Mathlib match).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`;
  its recorded convention explicitly uses `Limits.pullback` for base change.
  `Scheme.Hom.fiber`, `fiberι` are the corresponding canonical point pullbacks
  in `Mathlib.AlgebraicGeometry.Fiber`. The module's `geometricFiberAt` asks
  for an algebraic closure, whereas the present statement correctly uses its
  documented general pullback convention for arbitrary algebraically closed extensions.
- `def-weil-irreducible-components`: `irreducibleComponents`,
  `Mathlib.Topology.Irreducible` (Mathlib match).
- `def-nagata-scheme-theoretic-image`: `Scheme.Hom.image`,
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`, defined by `.ker.subscheme`;
  `.ker.support` is the underlying closed subset of exactly this subscheme.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`; canonical open complements use
  the standard opens `.toScheme`/`.ι` and `Closeds.compl`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, same Scheme module above.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its
  publicly imported `Morphisms.QuasiCompact`.

Proof-only project imports preserve the recorded plan:
`Sheaf.AlgebraicGeometry.RegularNormalDecomposition`
(`regular_normal_and_normal_decomposition`),
`WeilConjectures.AlgebraicGeometry.GenericFibreAffineRingModels`
(`generic_fibre_affine_ring_models`), and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`
(`Scheme.Hom.ker_morphismRestrict`). Mathlib proof facts are available from
ClosedImmersion, Affine, Properties, DiscreteValuationRing.Basic, Sober and
Irreducible. The two proof nodes `lem-sfb-smooth-trait-volume-infrastructure`
and `lem-sfb-smooth-fibrewise-dense-open-base-change` currently have no Lean
record or Mathlib match and are therefore not imported. They are not needed
to type the statement. No import cycle is introduced.

Searches (using the prescribed `msearch.py Q116 <item> ...`):

- leanfinder: “A closed subscheme of the generic fibre of a smooth scheme over
  a discrete valuation ring has closure containing no fibre component”. Eight
  results: valuative-criterion specializing maps, an immersion's coborder,
  closed-point specialization, and residue closed immersions. None is the item.
- loogle: `AlgebraicGeometry.Scheme.Hom.image, Dense, irreducibleComponents`:
  zero hits.
- grep in Mathlib AlgebraicGeometry:
  `trait.*(closure|complement)|horizontal.*closed|image.*support`: four hits
  concerning general image support / vanishing ideals, no trait-thin theorem.
- rg in both `lean/WeilConjectures` and `lean/Sheaf`:
  `trait.*(closure|complement)|horizontal.*closed|lem-sfb-trait-horizontal-closed-complement`:
  unrelated horizontal squares, curve preparation and supported cup products,
  with no declaration carrying this statement or this node id.
- rg for the new name `trait_horizontal_closed_complement` in Lean and
  `dag/lean_names_upstream.json`: no existing declaration.

No STATEMENT-DISPUTED issue or node fault was found. The example Sheaf compact
module is withdrawn; its node points to the actual upstream CompactObject
module, whose header/public-section convention was read instead.

## Second reading by Q116

A separate rereading by the same worker checked the source node and final
signature together; this is not represented as another person's independent
review. The assignment prohibits starting other agents, and the maintainer's
independent delivery review remains the independent check. The three conjuncts
were matched in order with the generic-fibre, all-geometric-fibres, and special
component clauses. The closed-subscheme support uses the full scheme-image
ideal, the geometric extension has `IsAlgClosed` rather than `IsAlgClosure`,
and all emptiness cases remain admitted. No statement mismatch was found.

Validation: `scompile.py` compiled the module successfully in both sandbox and
library contexts (2.2 s and 2.8 s), with no errors or unexpected warnings.
The final direct-import additions are also validated by the delivery dry run.
