## Worker report

This delivery states `lem-trf-curve-integral-filtration-multiplicity-profile` in
`Sheaf.AlgebraicGeometry.CurveIntegralFiltrationMultiplicityProfile`. All seven declarations
are in `AlgebraicGeometry.Scheme.Modules`; every proof is `by sorry`. No construction is
postponed and the natural-language statement is unchanged. The H2 repair adds one
definition node bound to the existing Mathlib vanishing-ideal declaration, without
introducing a Lean definition.

Read the entire target statement and its nine proof steps, all fifteen original statement
dependency nodes and their declaration records, the relevant declaration source/docstrings,
and the current Stacks source: coherent.tex `lemma-coherent-filter` (01YF), and varieties.tex
the multiplicity paragraph preceding `lemma-degree-in-terms-of-components` (0AYW) and its
proof. The current blueprint's `sk-i-curve-zero/_section.md` and
`lem-trf-local-term-locality.proof.md` confirm that this is a supporting extracted node,
not a replacement of a unit statement. The source of the present algebraic refinement is
01YF plus the generic length calculation, as its node explicitly records.

### Hypotheses and clause correspondence

All assertions have explicit `k : Type u`, `[Field k]`, `X : Scheme.{u}`,
`f : X ⟶ Spec (CommRingCat.of k)`, `[IsProper f]` and
`hdim : topologicalKrullDim X ≤ 1`. There is no assumption of reducedness, integrality,
pure dimension, connectedness, algebraic closure, or nonemptiness of X. Additional binders
in the later declarations name exactly the components, modules or arbitrary filtrations
whose properties the corresponding clauses discuss.

1. `curve_integral_filtration_components` concludes `IsNoetherian X`, namely the existing
   class extending `IsLocallyNoetherian X` and `CompactSpace X`, followed by
   `RingedSpace.IsCoherent X.toRingedSpace (SheafOfModules.unit X.ringCatSheaf)`.
   CompactSpace is the open-cover finite-subcover condition in the node. Coherence uses
   the full finite-type-and-finite-type-kernel predicate, not merely the conjunction of
   quasi-coherence and finite type.
2. The same theorem supplies `∃ (t : ℕ) (T : Fin t → Closeds X)`, with `Function.Injective T`
   and `Set.range (fun i ↦ (T i : Set X))` equal to the set of irreducible components of
   dimension one. Thus the list is exhaustive, finite and without repetitions; it may be
   empty. A closed set has its unique closed-set wrapper, so injectivity is also injectivity
   of underlying component subsets.
3. `curve_integral_filtration_component_geometry` is universal in a closed component T,
   with precisely `hT : (T : Set X) ∈ irreducibleComponents X` and `hTdim : dim T = 1`.
   This lets it apply to every member of the preceding list. Its component scheme C is
   the existing `(IdealSheafData.vanishingIdeal T).subscheme`, and j is its `.subschemeι`.
   These are the canonical reduced induced closed subscheme and closed immersion,
   already constructed by the imported API. Its conclusions give `IsIntegral C`,
   `IsProper (j ≫ f)` and `topologicalKrullDim C = 1`.
4. `∃! ξ : C, IsGenericPoint ξ Set.univ` supplies the unique generic point of C.
   The universal generic-point conclusion gives `closure {j ξ} = T`, so the point is
   viewed in X exactly as the node specifies. The closed immersion is injective, so
   uniqueness on C gives uniqueness of this point on its component in X as well.
5. For every affine open `U : X.affineOpens`, the explicit condition
   `(U.1 : Set X) ∩ (T : Set X) ≠ ∅` means that U meets the component. The conclusion
   `(vanishingIdeal T).ideal U |>.IsPrime` and its displayed zero-locus equality identify
   the defining ideal with the prime of that irreducible closed subset. `.subscheme`
   is actually defined by this ideal on the affine chart; this is not just an assertion
   about an unrelated prime or an arbitrary closed immersion.
6. `curve_integral_filtration_exists` takes any `F : X.Modules` with its full coherence
   hypothesis and concludes the existing `HasCoherentIntegralFiltration F`. Its definition
   was read in full: `∃ m`, a monotone chain `c : Fin (m+1) → Subobject F`, bottom at 0,
   top at `Fin.last m`, coherence of each term, and for each `j : Fin m` an integral
   closed immersion `i : Z ⟶ X` and `I : Z.IdealSheafData`, `I ≠ ⊥`, coherence of
   `I.toModules`, and a module isomorphism from the actual cokernel of `Subobject.ofLE`
   to `(pushforward i).obj I.toModules`. Thus all endpoint, inclusion, quotient,
   nonzero-ideal and pushforward clauses are present verbatim via the existing predicate.
7. `curve_integral_filtration_factor_geometry` is universal in an integral closed
   immersion `h : Z ⟶ X`, so applies in particular to every factor of every filtration.
   It concludes `IsProper (h ≫ f)` and `IsNoetherian Z`. Its disjunction says either
   `dim Z = 0`, there is a single point (`∃ z, ∀ w, w = z`) and its image is closed in X,
   or `dim Z = 1` and there is exactly one `T : Closeds X` which is a one-dimensional
   component with image `Set.range h`. It gives a unique isomorphism
   `Z ≅ (vanishingIdeal T).subscheme` whose composite with the canonical immersion is h.
   This is equality as reduced closed subschemes over X (isomorphism over X), not
   literal equality of separately bundled schemes. Together with the injective
   exhaustive component enumeration it is exactly the unique-C_i assertion.
8. `curve_integral_filtration_stalk_count` takes an arbitrary F and arbitrary filtration
   data, not a chosen existence witness: `s`, `c`, monotonicity `hc`, bottom `hbot`, top
   `htop`, term coherence `hcoh`, the schemes `Z`, maps `h`, `hclosed`, `hintegral`, ideals
   `I`, `hnonzero`, `hIcoh`, and quotient isomorphism hypotheses `hquot`. These are exactly
   the conditions in the preceding filtration predicate. It takes an arbitrary
   one-dimensional component T and its generic point `ξ : X` with `hξ : IsGenericPoint ξ T`.
9. In that theorem each quotient Q_a is written as
   `cokernel (Subobject.ofLE (c a.castSucc) (c a.succ) (hc a.castSucc_le_succ))`.
   For `Set.range (h a) ≠ T`, its stalk is `Subsingleton`, the zero module condition.
   For equality, the stalk is isomorphic in `ModuleCat (X.presheaf.stalk ξ)` to the
   residue field with the canonical action, explicitly
   `(ModuleCat.restrictScalars (X.residue ξ).hom).obj
     (ModuleCat.of (X.residueField ξ) (X.residueField ξ))`.
   This is an R-linear isomorphism, not only an additive-group equivalence or a
   dimension assertion. The same implication states that the quotient stalk's
   `Module.length (X.presheaf.stalk ξ)` is 1.
10. The component geometry theorem states surjectivity of the actual `j.stalkMap ξ`
    onto the component local ring. Its ring equivalence `e` from that local ring to
    `X.residueField (j ξ)` satisfies `e (j.stalkMap ξ r) = X.residue (j ξ) r` for every r.
    Thus the residue-field identification is normalized by the canonical quotient map;
    it cannot be an arbitrary field isomorphism. Factor classification transports
    this to any factor with equal support, exactly as in proof Steps 5--6.
11. The stalk-count theorem concludes the equality of `length_R F_ξ` with
    `(Nat.card {a : Fin s // Set.range (h a) = T} : ℕ∞)` and separately `length_R F_ξ < ⊤`.
    Fin s corresponds to the node's indices 1 through s via a ↦ a+1.
    The finite subtype uses propositional support equality without a decidability
    assumption. The final implication explicitly specializes the count to
    `Module.length R R` when `F = SheafOfModules.unit X.ringCatSheaf`.
12. `curve_integral_filtration_multiplicity` states `∃ m : ℕ, 0 < m ∧ length_R R = m`.
    Together with the explicit structure-module specialization just described, this
    gives precisely that each m_i is a positive integer equal to the factor count.
13. `curve_integral_filtration_zero_cases` says every `IsZero F` admits the chain on
    `Fin (0+1)` with its sole term both bottom and top and coherent. There are no factor
    indices (`Fin 0`), so this is exactly the allowed length-zero filtration. For an
    empty X it explicitly concludes `IsZero (SheafOfModules.unit X.ringCatSheaf)` and
    equality of the one-dimensional component set with the empty set. The earlier
    enumeration can therefore be chosen with t=0, and the same zero chain applies.

The presentation separates universally reusable clauses of this one node into named
statements rather than encoding a new profile or a duplicate filtration structure.
All seven names are listed in `lean.declarations`, each tagged with this node and a
source/proof docstring. The primary `lean.statement` is copied verbatim from the first
signature; the remaining clauses are the other recorded declarations.

### Dependency declarations and imports

All original statement-dependency records were used with their supplied notions:

- `Field` (Mathlib.Algebra.Field.Defs, reached by the geometry imports).
- `AlgebraicGeometry.IsProper` (Mathlib.AlgebraicGeometry.Morphisms.Proper).
- `topologicalKrullDim` (Mathlib.Topology.KrullDimension).
- `IsLocallyNoetherian` and `IsNoetherian` (Mathlib.AlgebraicGeometry.Noetherian).
- `RingedSpace.IsCoherent` exposed by the repaired
  Sheaf.AlgebraicGeometry.CoherentFiniteType, originating in
  WeilConjectures.AlgebraicGeometry.Coherent. The source was read and its full kernel
  condition was used. No dependency repair is needed here.
- `irreducibleComponents` (Mathlib.Topology.Irreducible), `IsReduced` and `IsIntegral`
  (Mathlib.AlgebraicGeometry.Properties), `IsClosedImmersion`
  (Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion), and `Spec`
  (Mathlib.AlgebraicGeometry.Scheme), through their public dependency imports.
- `SheafOfModules` / `Scheme.Modules`, with the recorded general-site module
  Sheaf.CategoryTheory.RingedSiteModules publicly imported; the scheme specialization
  is exactly the Mathlib module category, not a private category.
- `Scheme.Modules.pushforward` (Mathlib.AlgebraicGeometry.Modules.Sheaf), exposed by
  the recorded Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction import for
  def-pc-module-pullback. No new pullback or pushforward is defined.
- `Scheme.residueField` and `Scheme.residue` (Mathlib.AlgebraicGeometry.ResidueField).
- `PresheafOfModules.moduleStalkFunctor` (recorded presheaf-level dependency, public
  import WeilConjectures.Topology.PresheafModuleStalkFunctor). For scheme modules its
  documented sheaf specialization is `RingedSpace.moduleStalkFunctor` from
  WeilConjectures.Algebra.Homology.ModuleStalkFunctor, which uses the same existing
  stalk carrier and canonical local-ring action.
- `Module.length` (Mathlib.RingTheory.Length) and `ModuleCat.restrictScalars`
  (Mathlib.Algebra.Category.ModuleCat.ChangeOfRings).

The item's stmt_deps additionally names the recorded nodes
`def-weil-pbc-coherent-integral-filtration` for the existing predicate,
`def-pc-module-stalk-functor` for the sheaf-level stalk packaging,
`def-sbc-closed-immersion-ideal-sheaf` for the module inclusion of an ideal,
`def-weil-pbc-scheme-reduction` for `IdealSheafData.subscheme` and `.subschemeι`, and
`def-sbc-ideal-sheaf-powers` for `Scheme.IdealSheafData`. Their statements, records and
exact declaration sources were read. It also cites the new definition node
`def-trf-vanishing-ideal-reduced-closed-subscheme`, bound to the existing
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal` in
Mathlib.AlgebraicGeometry.IdealSheaf.Basic. These definition modules are public imports.
The theorem node `lem-weil-pbc-reduced-induced-closed-subscheme` is absent from stmt_deps;
it remains in proof_deps, with a plain import of its module.

Recorded proof dependencies with Lean statements are imported as plain proof imports:
WeilConjectures.AlgebraicGeometry.Modules.Invertible (`IsInvertible`),
CoherentFiltrationIntegralSubschemes (`exists_coherent_filtration_integral_subschemes`),
ClosedPushforwardStalks (`closedImmersion_pushforward_stalks`),
CoherentFiniteTypeLocallyNoetherian (`isCoherent_iff_isQuasicoherent_and_isFiniteType`),
IntegralIdealGenericStalk (`integral_ideal_generic_stalk`), and
WeilConjectures.Algebra.Homology.ModuleStalkExact (`module_stalk_exact`).
ReducedInducedClosedSubscheme is a plain proof import; the canonical construction
used by the statement comes directly from the public Mathlib ideal-sheaf imports. Mathlib proof leaves are already reached by the geometry/length imports.
The proof dependency `lem-trf-proper-field-invertible-coherent` has no recorded module,
so there is no module to import for it; its mathematical application is retained in the
proof docstrings. Its missing proof statement does not affect elaboration of this node.

### Edge cases checked

- Empty X: dimension is bottom, not 0; no integral component exists, the enumeration
  is empty, the structure module is zero and the zero-length filtration is permitted.
- F=0 and s=0: Fin 0 has no quotients; bottom=top is permitted. Generic counts and
  stalk lengths are 0, with no asserted positivity for arbitrary F.
- A zero-dimensional proper scheme (including Spec k): there are no dimension-one
  components, but integral factors may be closed points; the generic assertions have
  no component instance and the general filtration existence remains present.
- An integral proper curve: the unique component has multiplicity 1, and nonzero
  ideal factors have its generic field as the ambient residue-field module.
- A curve plus an isolated point, two components meeting, and point-supported factors:
  point factors have zero stalk at every curve generic point, and a factor on one
  component has zero stalk at the other generic points. No disjointness is assumed.
- A square-zero thickening of a proper integral curve: X is allowed nonreduced;
  the generic ambient ring need not be a field and may have length 2. The component
  local ring is its residue field, and two supported factors give count 2. No reduction
  or arbitrary field action has replaced this local-ring length.
- Affine opens disjoint from a component impose no primality condition; opens meeting
  it have nonempty irreducible intersection and a proper prime defining ideal.
- All characteristics are allowed and no extra coefficient, small-index-universe,
  dimension-equality or generic nonemptiness assumption was imposed.

### Searches for existing statements and notions

Executed through msearch.py with group NW and this item:

- LeanFinder: `The length of a coherent sheaf at a generic point equals the number of
  factors on that component in an integral ideal filtration`: 8 hits, on module support
  dimension and regular sequences, not the target's coherent filtration/stalk count.
- Loogle: `Module.length, AlgebraicGeometry.Scheme.Modules, irreducibleComponents`:
  successful query, 0 hits.
- Mathlib grep: `filtrat.*length|length.*filtrat|multiplicity.*component`, subdirectory
  RingTheory: successful query, 0 hits.
- LeanSearch: `generic stalk length of coherent integral ideal filtration on a proper
  curve`: 8 hits including Ideal.Filtration, its stability API and Module.rankAtStalk;
  none is the target's coherent integral-ideal filtration multiplicity statement.

Local rg searches in both lean/WeilConjectures and lean/Sheaf for filtration, generic
multiplicity/profile, topologicalKrullDim and the exact item ID found the upstream
CoherentIntegralFiltration predicate and CoherentFiltrationIntegralSubschemes theorem,
which were opened and reused. The exact item ID and all seven proposed declaration names
had no existing declaration. The full target is not any of the general filtration,
reduced-induced-scheme, closed-pushforward-stalk, generic-ideal or module-length inputs.
The withdrawn CompactObject example was also read, then the actual currently recorded
WeilConjectures.CategoryTheory.CompactObject source for its module/docstring conventions.

### Validation and faults

Compilation uses only the prescribed scompile.py wrapper against the published live
library. The initial full statement compiled successfully against current server sources
(2.5 s reported for the server confirmation). The wrapper's internal cache attempt
reported OSError 28 (no space left), then its automatic server-source confirmation
returned success; no infrastructure workaround or launcher edit was made. The final
structure-sheaf-specialization and zero-case signatures also passed scompile.py, and
deliver2.py --no-push returned OK after both preflight and compilation. The completed
module declaration index is included in the final validation run.

No STATEMENT-DISPUTED finding, statement correction, dependency module, private Lean
definition, auto-implicit variable or non-sorry proof is present. The one new definition
node records an existing Mathlib construction, as detailed below.


## Repair of H2 at returned head d1708de228f8

The independent review accepted all seven statement signatures and returned only the
statement/proof dependency classification. Rebuilt the item's node from current main
(the current shared node has no Lean record and only the original fifteen statement
dependencies), retaining exactly the delivered Lean record and the authorized added
notion dependencies. The natural-language statement, proof steps and proof dependencies
are byte-identical to current main and to the returned sandbox statement. All seven
Lean signatures are unchanged from the returned delivery.

Removed `lem-weil-pbc-reduced-induced-closed-subscheme` from the proposed stmt_deps and
changed its module from public import to plain proof import. Added public imports of
Mathlib.AlgebraicGeometry.IdealSheaf.Basic and .Subscheme, and cited the existing
`def-weil-pbc-scheme-reduction` and `def-sbc-ideal-sheaf-powers` nodes as requested.
The latter's exact `IdealSheafData` source defines the affine ideals and their basic-open
compatibility; the former's declarations construct the ideal's subscheme and inclusion.

The return also requests a definition node for vanishingIdeal, now supplied as
`def-trf-vanishing-ideal-reduced-closed-subscheme`. This is a definition-node attachment,
not a restatement of the proof theorem or a copy of the construction. The mathematical
properties of reduced induced closed schemes remain the role of the existing proof
node. No unchanged re-push is being made.

## New nodes

`def-trf-vanishing-ideal-reduced-closed-subscheme` defines, for any scheme X and closed
subset T, the vanishing ideal by its affine prime-ideal intersection and names the
reduced induced closed subscheme as the existing subscheme of that ideal, with its
canonical inclusion. The source is schemes.tex Tag 01J3, the ideal construction in the
proof of `lemma-reduced-closed-subscheme`, and Tag 01J4,
`definition-reduced-induced-scheme`, both read in full. On an empty intersection the
intersection of prime ideals is the whole affine ring, giving the empty closed scheme;
on all of X it is the nilradical, giving X_red. No Noetherianity or nonemptiness is added.

The record has `existing: true` and exactly the source declaration
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal` in
Mathlib.AlgebraicGeometry.IdealSheaf.Basic, whose source at lines 559--599 was read.
Its affine ideal is `PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' T)`, exactly the
intersection in the node. Its `.subscheme` and `.subschemeι` are the existing construction
recorded by def-weil-pbc-scheme-reduction, which the new node cites. It also cites
`def-pc-scheme`, `def-weil-affine-spectrum`, and `def-sbc-ideal-sheaf-powers` for the
notions in its statement. It adds no module and no sorry, and is cited by the item.

Searches executed in this repair (also recorded in its mathlib_searches):

- LeanSearch, `vanishing ideal sheaf of a closed subset of a scheme reduced induced
  closed subscheme`: eight hits, including the exact vanishingIdeal construction,
  its affine formula, support and Galois-connection lemmas. Exact match.
- LeanFinder, `AlgebraicGeometry Scheme IdealSheafData vanishingIdeal closed subset`:
  eight hits, including the same exact construction and affine formula. Exact match.
- Mathlib grep, `def vanishingIdeal|reduced induced scheme structure` in
  AlgebraicGeometry: three hits, including Basic.lean:563 and :565. The projective
  spectrum hit is a different construction.
- Scanned DAG definition statements for vanishing ideal / vanishingIdeal / reduced
  induced closed, and searched the entire blueprint with blueprint_refs.py search
  `vanishing ideal` (none) and `reduced induced` (four users, no definition). There is
  a general theorem node, but no general definition node to cite for this construction.
- rg of lean/WeilConjectures and lean/Sheaf found the Mathlib construction used by the
  reduced-induced theorem and several specialized constructions; none supplies a
  different definition to introduce. The requested new node attaches the existing
  Mathlib definition without writing it again. The upstream reducedness instance in
  IdealSheaf/Subscheme.lean was also read, separating that property from the definition.

Repair validation uses the prescribed scompile.py followed by deliver2.py --no-push,
which additionally compiles an existing-declaration probe for the new Mathlib binding.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
