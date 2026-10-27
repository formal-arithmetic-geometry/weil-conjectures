## Worker report

The module `Sheaf.RingTheory.TraitTestMixedRegularPairModels` states
`RingTheory.exists_trait_test_mixed_regular_pair_models`, with its sole proof `sorry`.
It introduces no definition and changes only the item's `lean` field. All objects are
bound explicitly, with `set_option autoImplicit false` and universe `u`.

Hypothesis-by-hypothesis correspondence:

- The local ring `(B,m)` is `B : Type u`, `[CommRing B]`, `[IsRegularLocalRing B]`.
  The latter includes locality and Noetherianity. Its maximal ideal is the existing
  `IsLocalRing.maximalIdeal B` and its residue field is `IsLocalRing.ResidueField B`;
  using that canonical field loses no separately named residue-field identification.
- Completeness is `[IsAdicComplete (IsLocalRing.maximalIdeal B) B]`; strict
  henselianity is `[IsStrictlyHenselianLocalRing B]`.
- Mixed characteristic `(0,p)` is `[CharZero B]`, `hp : p.Prime`, and
  `[CharP (IsLocalRing.ResidueField B) p]`. Prime positivity is included in `hp`.
- Dimension is `hd : 1 ≤ d` and `hdim : ringKrullDim B = (d : WithBot ℕ∞)`.
- The invertible prime is `hℓ : ℓ.Prime` and `hℓB : IsUnit (ℓ : B)`.
- The ordered generators are `t : Fin d → B`; `ht` states that their generated
  ideal, `Ideal.ofList (List.ofFn t)`, equals the maximal ideal. `htreg` is the
  recorded regular-sequence predicate on exactly this ordered list.

Conclusion-by-conclusion correspondence:

- The existential `C : Type u`, commutative ring and domain structures, and
  `IsDiscreteValuationRing C` give the DVR. Mathlib defines a DVR as a local PID
  which is not a field, equivalent to the node's Noetherian local dimension-one
  domain with principal maximal ideal. No nonramification condition is imposed.
- The subsequent existential classes give characteristic zero, strict henselianity,
  maximal-ideal adic completeness, and residue characteristic `p` for `C`. An
  existential ring equivalence identifies its residue field with that of `B`.
  `IsUnit (ℓ : C)` is the required invertibility.
- The index `I : Type u` has a preorder, a `Nonempty` instance and
  `IsDirected I (· ≤ ·)`, the project's directed-set convention. Its universe
  matches the rings' universe. `A : I ⥤ CommAlgCat.{u} C` is the directed algebra
  system. The existential `Algebra C B` and the algebra-valued natural
  transformation `ι` encode the induced structure of its limit: any compatible
  ring colimit of a nonempty directed C-algebra diagram carries precisely such a
  structure, so this is not an additional hypothesis on the input `B`.
- `s : (i : I) → Fin d → A.obj i` is the marked tuple. The first conjunct is its
  preservation by every transition map, including identities and arbitrary arrows.
- For every index the algebra clause asserts `IsRegularRing`, `IsDomain`,
  `Algebra.FiniteType C`, `Module.Flat C`, and regularity of the displayed list.
  Thus it includes the regular Noetherian integral finitely generated flat algebra
  and its regular sequence. `IsRegularRing` includes Noetherianity.
- The actual quotient is `A.obj i ⧸ Ideal.ofList (List.ofFn (s i))`. The same clause
  gives its `IsRegularRing` and `CharP ... p`, hence the required regular
  Noetherian characteristic-p quotient.
- `Q : I ⥤ CommRingCat` represents the quotient diagram; `eQ i` is an explicit
  isomorphism to the actual quotient. The equation
  `(eQ i).toRingHom.comp (q.app i).hom = Ideal.Quotient.mk ...` fixes `q` as the
  quotient map under that identification. Naturality of `q` forces the transitions
  to be the induced quotient transitions: this is not an arbitrary map or quotient.
  This avoids building another copy of the canonical quotient functor or inserting
  unrecorded helper theorems.
- The two `Nonempty (IsColimit ...)` conjuncts assert the universal properties
  with respective vertices `B` and its residue field, so are exactly the two ring
  colimit isomorphisms, with their compatible coprojections. The first is a
  colimit in rings, explicitly obtained by applying the forgetful functor to the
  C-algebra cocone; it is not merely a colimit in C-algebras.
- `ι.app i (s i r) = t r` is the marked-element condition.
  `(ν.app i).hom.comp (q.app i).hom = (IsLocalRing.residue B).comp ...` is precisely
  compatibility of the quotient diagram with `B ↠ k`. With the two colimit
  properties it makes the limiting pair `Spec k ↪ Spec B` the specified residue
  inclusion, rather than an unspecified morphism between the same limiting objects.
- The final clause gives `IsIntegral` and `IsRegularScheme` for `Spec (A.obj i)`;
  `Flat`, `LocallyOfFiniteType`, and `QuasiCompact` apply to its structural Spec
  map to `Spec C`. The last two predicates are the recorded definition of finite type.
- Quasi-projectivity is the displayed existential immersion into
  `ProjectiveSpace (ULift.{u} (Fin (n+1))) (Spec C)` commuting with structure maps.
  These are n+1 homogeneous coordinates, so this is finite-dimensional projective
  n-space. `IsImmersion` is Mathlib's locally closed immersion. The existing
  `IsQuasiProjective` API is restricted to field bases and cannot apply to the DVR;
  the node already writes this clause explicitly, and we render it inline without
  adding a duplicate quasi-projectivity definition.
- The final two conjuncts say that the actual quotient spectrum is regular and
  that its canonical quotient closed immersion has codimension function `fun _ => d`,
  using the dependency's exact `IsRegularClosedImmersionWithCodimension`.
  Its defining equations are the same actual quotient equations, not a second
  freely chosen closed subscheme.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`:
  `AlgebraicGeometry.IsRegularScheme`; its ring clauses use Mathlib's
  `IsRegularLocalRing` and `IsRegularRing` (`RegularLocalRing.Defs`).
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` (the companion to
  the node's `AdicCompletion` declaration).
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.AlgebraicGeometry.ResidueField`: the recorded scheme residue-field
  definition is itself `IsLocalRing.ResidueField` of the stalk. For this local-ring
  statement we use that same Mathlib local-ring field and `IsLocalRing.residue`,
  read in `RingTheory.LocalRing.ResidueField.Defs`; no second definition is supplied.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` and the
  proof dependency `Flat.SpecMap_iff`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  `locallyOfFiniteType_iff`; `QuasiCompact` is the recorded companion predicate.
- `Sheaf.AlgebraicGeometry.RegularClosedImmersionCodimension`:
  `AlgebraicGeometry.IsRegularClosedImmersionWithCodimension`.
- The supporting existing APIs are `CommAlgCat`, `Ideal.Quotient.mk`,
  `IsDiscreteValuationRing`, `ProjectiveSpace`, `ProjectiveSpace.over` and `IsImmersion`.

Proof imports also include the recorded regular-system-of-parameters module, the
Mathlib affine-scheme and Noetherian modules (including `IsAffineOpen.isLocalization_stalk`
and `IsLocallyNoetherian.component_noetherian`), closed immersions and `Limits.HasLimits`
(`IsColimit`, the universal property underlying `colimit`). Proof nodes whose modules
are already public statement imports need no second import line.

The proof-only dependency `lem-per-complete-mixed-regular-pair-approximation` has a
stale Lean record: its note explicitly says that
`Sheaf.RingTheory.CompleteMixedRegularPairApproximation` was deleted on 2026-10-20.
The local file is absent and `scompile.py --source` returned
`Module source unavailable: Sheaf.RingTheory.CompleteMixedRegularPairApproximation`.
Consequently that unavailable proof module is not imported. Its full recorded
signature and node statement were read, and the mathematical proof plan continues
to cite that DAG node. This delivery does not need its theorem to type the item,
restate that theorem, or change its record. The remaining proof modules are imported.

Edge cases checked before writing:

- `d=0` is intentionally excluded by the node's `d≥1`; `d=1` includes both an
  unramified DVR and a ramified DVR with `p = unit * uniformizer^e`. No smoothness
  of `C → B` or of the models is asserted, so the ramified case is retained.
- Higher-dimensional complete regular local rings, such as a power-series
  extension of a complete strictly henselian DVR, retain arbitrary ordered regular
  generators of their maximal ideal. No single distinguished parameter is fixed.
- `p` must be prime positive; `ℓ=p` is excluded already by the input's unit condition
  because `p=0` in the residue field. No equal-characteristic case is added.
- The index is genuinely nonempty, all transitions are quantified, and a singleton
  index is permitted. All rings and the small index use the same universe `u`;
  no independent smaller test-object universe or universe equality is imposed.
- The actual quotient cannot be zero because its equations form a regular sequence;
  `CharP ... p` therefore has its intended nonzero-ring meaning. Regularity is
  Noetherian regularity, not only an unqualified condition on stalks.
- Projective dimension zero is allowed, and `ULift` changes only the coordinate
  index's universe. The codimension predicate is the recorded sourcewise one,
  so there is no extra nonemptiness/local-constancy hypothesis on source points.

Searches performed:

- `msearch.py leanfinder`, query `complete mixed characteristic regular local ring simultaneous regular pair finite type models over a complete discrete valuation ring`:
  eight hits, characteristic splitting, HenselianLocalRing, BDeRham and tilt
  constructions; no simultaneous marked-pair approximation theorem.
- `msearch.py loogle`, query `IsRegularLocalRing, IsDiscreteValuationRing`:
  zero hits.
- `msearch.py grep`, query `regular.*approximation|mixed.*pair|QuasiProjective`
  in Mathlib's `AlgebraicGeometry`: zero hits.
- `msearch.py leansearch`, query `simultaneous approximation of a mixed characteristic complete regular local ring and its regular parameter quotient by finite type flat regular algebras over a complete discrete valuation ring`:
  eight hits, including smooth-flatness, adic lifting and completion-flatness;
  none states the item.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, patterns
  `regular pair|regular.*models|MixedRegularPair|trait-test-mixed` and
  `mixed.regular.pair|MixedRegularPair|trait-test-mixed`: no matching existing
  statement. Hits concern unrelated depth-two regular pairs and log regular models.
- `grep -rn lem-per-trait-test-mixed-regular-pair-models lean/WeilConjectures`:
  no matches. `rg` in `dag/lean_names_upstream.json` found no matching attachment.
- Searched and read projective-space/quasi-projectivity APIs: the field-only
  `IsQuasiProjective` is in `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective`;
  the arbitrary-base `GabberModification.QuasiProjective` has the same explicit
  immersion formula but belongs to a large log-modification interface. The item
  renders its own explicit formula with the shared `ProjectiveSpace` and `IsImmersion`.

Source check: read ILO printed pp.254–255 (PDF pp.260–261) using `pdftotext`.
XVI 3.7 reduces to integral regular quasi-projective flat schemes over a strictly
henselian mixed-characteristic trait, as the node's source says. The node expressly
labels the simultaneous approximation assertion an agent-formulated algebraic input,
not a verbatim theorem of those pages. The latest blueprint ancestor proof was also
read; its recorded ancestry is stale as already noted by the stage-1 reviewer.
No source-based statement correction is needed here. No STATEMENT-DISPUTED claim is made.

Validation: the statement compiled with `scompile.py` after correcting parentheses
around the projective-space structure morphism; final compilation and delivery
preflight use the prescribed wrappers only. No source in the shared repository was edited.

## Second reading by Q41

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
