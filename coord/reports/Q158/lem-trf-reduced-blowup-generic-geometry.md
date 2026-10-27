## Worker report

The module `Sheaf.AlgebraicGeometry.ReducedBlowupGenericGeometry` states
`AlgebraicGeometry.Scheme.IdealSheafData.reducedBlowup_generic_geometry`.
It has exactly one theorem, whose whole proof is `sorry`, and no new definitions.
The item's mathematical statement, proof plan and dependency lists are unchanged.
The existing upstream full-coherence definition is used directly. The live Q25
dependency record is preserved; see the return repair below and the item lean.note.

Hypothesis and clause correspondence:

- The scheme is `S : Scheme.{u}`. Its rational structure morphism is
  `q : S ⟶ Spec (.of (ULift.{u} ℚ))`. `ULift` only places the same field Q in
  the scheme universe; it does not restrict the universe or change the field.
- Reducedness is `[IsReduced S]`, the recorded Mathlib notion (reduced rings of
  sections, equivalently reduced stalks).
- Finite type over Q is `[LocallyOfFiniteType q] [QuasiCompact q]`, exactly the
  conjunction specified by def-weil-finite-type-morphism.
- The quasi-coherent ideal is `J : S.IdealSheafData`, the existing affine-local
  ideal-sheaf data with compatibility under localization. Its actual module is
  the canonical `J.toModules`, the kernel of O_S -> (subschemeι)_* O_V(J).
  Coherence is `hJ : RingedSpace.IsCoherent S.toRingedSpace J.toModules`, including
  finite type and finite-type kernels of maps from finite free modules on every
  open, not merely finite presentation or finite generation.
- `U = S minus V(J)` is the existing open `J.support.compl`. The hypothesis
  `hcentre : ∀ C ∈ irreducibleComponents S,
  Dense {x : C | x.1 ∈ J.support.compl}` states density in each component's
  subspace topology, rather than merely nonemptiness or a choice of one component.
- The ordinary blowup and its map are exactly the recorded `J.blowup` and
  `J.blowupMap`, constructed by gluing the affine blowups. They are neither the
  normalized blowup nor a freely chosen proper birational scheme.
- The first three conclusion factors are `IsReduced J.blowup`,
  `IsLocallyNoetherian J.blowup`, and
  `(irreducibleComponents J.blowup).Finite`.
- The next factors `LocallyOfFiniteType (J.blowupMap ≫ q)` and
  `QuasiCompact (J.blowupMap ≫ q)` assert finite type over the specified Q.
- `IsProper J.blowupMap` and `Surjective J.blowupMap` assert properness and
  surjectivity of that very map, with the recorded Mathlib predicates.
- `IsIso (J.blowupMap ∣_ J.support.compl)` asserts the isomorphism b^{-1}U -> U.
- `∀ C ∈ irreducibleComponents J.blowup,
  Dense {x : C | J.blowupMap x.1 ∈ J.support.compl}` asserts density of b^{-1}U
  in every blowup component, again in the component's subspace topology.
- `Set.BijOn J.blowupMap (genericPoints J.blowup) (genericPoints S)` asserts that
  b itself takes generic points to generic points, injectively and onto. Mathlib
  defines these sets by closure of the singleton being an irreducible component.
  For schemes, `genericPoints.equiv` identifies them with the component sets.
- `∀ x ∈ genericPoints J.blowup, IsIso (J.blowupMap.residueFieldMap x)` asserts
  that the induced map kappa(b(x)) -> kappa(x) is an isomorphism. This uses the
  actual morphism on residue fields, not an arbitrary field isomorphism.
- The last factor spells out the equivalent birationality clause. `C` and `D`
  are closed subsets which are components of the blowup and S. They correspond
  precisely when some x is generic for C and b(x) is generic for D, using the
  recorded `IsGenericPoint`. `vanishingIdeal C` and `vanishingIdeal D` cut out
  the canonical reduced induced component schemes (Mathlib's existing
  construction, also used in lem-weil-pbc-reduced-induced-closed-subscheme).
  The existential V and U are opens of those schemes, both `Dense`. The scheme
  isomorphism `e : V.toScheme ≅ U.toScheme` satisfies
  `e.hom ≫ U.ι ≫ (vanishingIdeal D).subschemeι =
  V.ι ≫ (vanishingIdeal C).subschemeι ≫ J.blowupMap`, so it is induced by b
  over S. The generic-point bijection supplies exactly one corresponding D
  for each component C; the final implication covers every such pair.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`;
  this is sectionwise reducedness, equivalent to the node's stalk condition.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; the quasi-compact factor is
  `AlgebraicGeometry.QuasiCompact` from Morphisms.QuasiCompact.
- `WeilConjectures.AlgebraicGeometry.Coherent`:
  `AlgebraicGeometry.RingedSpace.IsCoherent`, and its public Mathlib imports
  `SheafOfModules.IsFiniteType` and `SheafOfModules.IsQuasicoherent`.
  The IsCoherent docstring and full definition were read: finite type plus
  finite-type kernels for all opens, natural numbers n and finite-free maps.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`:
  `AlgebraicGeometry.Scheme.IdealSheafData.toModules`, its kernel construction
  and `range_toModulesι_app`, which identifies its affine sections with J's ideals.
- `WeilConjectures.Blowup.Gluing`:
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup` and `.blowupMap`, respectively
  the glued scheme and the glued structural map.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` (maximal irreducible sets).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, `genericPoints` and its component
  equivalence. `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` (induced by the local homomorphism on stalks).
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` / `Subscheme`:
  `Scheme.IdealSheafData.vanishingIdeal`, `.subscheme` and `.subschemeι`.

The proof-only imports include the recorded modules `WeilConjectures.Blowup.Proper`
(`isProper_blowupMap`), `.Complement`
(`isIso_blowupMap_restrict_support_compl`), `.Density`
(`IsAdmissible.isSchemeTheoreticallyDominant_preimage_ι`),
`Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`,
`Mathlib.Topology.NoetherianSpace`, and
`WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
(`reduced_induced_closed_subscheme`). Other proof dependencies occur in the
already publicly imported FiniteType, Noetherian, Properties, Irreducible,
Sober, Proper and UnderlyingMap modules. No import cycle was omitted.
The theorem's docstring follows all seven DAG proof steps in order and names
all their dependencies. No proof is supplied at stage 2.

Sources read: Stacks divisors.tex, lemma-blow-up-reduced-scheme (0808),
lemma-blow-up-and-irreducible-components (0BFM),
lemma-blowing-up-gives-effective-Cartier-divisor (02OS), and
lemma-blowing-up-projective (02NS), including their proofs. Also read the current
blueprint `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`
`lem-trf-local-term-locality.proof.md`. This item supplies the ordinary-blowup
geometry in the DAG's normalized-blowup proof; it does not change the unit.

Edge cases checked before finalizing the statement:

- Empty S: no nonemptiness hypothesis, no selected component or generic point;
  the component quantifiers and generic-point bijection admit empty sets.
  Coherence and the density hypothesis are valid on the empty scheme.
- Unit ideal: support is empty, the complement is all of S, and the ordinary
  blowup is S. Every conclusion specializes to the identity-map assertion.
- Zero ideal on nonempty S: complement is empty and fails density on every
  nonempty component; this case is correctly excluded by the stated source
  hypothesis. On empty S it is allowed.
- Reducible schemes and intersecting components: density is inside each
  component, with no disjointness assumption. The last clause uses the reduced
  induced structures even when components meet.
- No normality, regularity, integrality, separatedness of S over Q, or
  nonempty centre/complement assumption was introduced. The only size
  parameter is the arbitrary explicitly declared u; Q is lifted to it.

Searches for reuse (2026-10-23):

- `msearch.py ... leanfinder "Blowup of reduced finite type scheme preserves
  generic points and residue fields and is proper surjective and birational"`:
  8 hits about residue-field preimmersions, normalization, rational maps and
  Spec-to-field equivalences. None states this ordinary-blowup package.
- `msearch.py ... loogle '\"blowup\", \"IsReduced\"'`: 0 hits.
- `msearch.py ... grep
  'blow.?up.*(reduced|generic|birational)|(reduced|generic|birational).*blow.?up'`:
  0 Mathlib hits.
- `msearch.py ... leansearch "Blowup of a reduced scheme is reduced and induces
  bijection of generic points outside its center"`: 8 general reduced-scheme
  declarations, no ordinary-blowup theorem with this statement.
- `rg` of the blowup/reduced/generic/birational pattern over both
  `lean/WeilConjectures` and `lean/Sheaf`: existing normalized-blowup calculus and
  finality, smooth-centre blowups and several different geometric results.
  Read NormalizedBlowupCalculus and NormalizedBlowupFinality; neither asserts
  this ordinary-blowup package. The latter cites this item only in its proof
  docstring, not as a declaration.
- The item-id search over `lean/WeilConjectures` and `lean/Sheaf` found only that
  finality docstring. The proposed full declaration name was absent from
  Mathlib, both project source roots and `dag/lean_names_upstream.json`.
- Coherence search located the exact existing upstream
  `AlgebraicGeometry.RingedSpace.IsCoherent`; it is reused via the dependency
  import explained by the item lean.note, never duplicated.

Validation: the final module compiles through the prescribed server
`scompile.py`, both its sandbox and library-module checks. No error or
unexpected warning. All variables and the universe are explicitly bound;
`autoImplicit` is false; lines are at most 100 characters.
There is no statement dispute and no correction to the item's statement.

## Return repair (H13)

The returned immutable head `6ce721f2a13d` replaced the live Q25 primary record
of `pqf-def-coherent` with a different existing declaration. That replacement
would drop a declaration used by 16 live Sheaf modules. The initial saved-packet
dry run passed mechanically, but it retained this review defect.

Removed `dag/nodes/sec-abelian-varieties/pqf-def-coherent.json` from the sandbox
packet, so it is absent from the delivery commit. The current main-branch record
continues to name `Sheaf.AlgebraicGeometry.CoherentFiniteType` /
`AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`; it is not modified.
The item gains `lean.note`, explaining why the already imported upstream
`RingedSpace.IsCoherent` is the faithful full-coherence notion of Stacks 01BV,
while the Q25 predicate records quasi-coherence and finite type. The item uses
that existing definition directly and introduces no replacement notion.

The reviewed item module is byte-identical to the saved returned module:
SHA256 `58ed22c046a1d8b5a8282451fe4f7719bef2d6a4f4f4c629e694e44de62f1f02`.
Its hypotheses, conclusions, imports, docstrings and sorry-only proof are
unchanged. Compared the sandbox item with current main: its non-lean fields
are unchanged. No new nodes or dependency modules are delivered.

## Second reading by Q158

Author's final consistency check; independent review is left to the maintainer,
as required by the dispatched-worker brief (no other agents were started).
I reread the complete node, its dependencies and the final module together.
Every input hypothesis and output factor is matched above. In particular,
I checked that the residue-field assertion concerns the actual induced map,
the map on generic points is BijOn rather than only MapsTo, the finite-type
conclusion uses the same rational structure morphism, and the birational
isomorphism commutes with b on the reduced induced components. The first draft
used the dependency's quasi-coherent finite-type predicate, which is equivalent
here because S is locally Noetherian; I replaced it with the existing full
coherence predicate to match the source literally. The returned record replacement
is now removed, and the item lean.note explains the direct upstream use. The
reviewed module is preserved byte for byte. The final version compiles. No weakened conclusion or added
mathematical hypothesis was found. The empty and unit-ideal cases remain
included. No new nodes were needed.
