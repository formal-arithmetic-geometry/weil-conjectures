## Worker report

The module `Sheaf.AlgebraicGeometry.AdmissibleFiniteTypeFieldQuotient` states the quotient
existence theorem and the two admission clauses of
`lem-sfb-admissible-finite-type-field-quotient`. All three theorem proofs are `sorry`.
There is no statement correction and no disputed statement.

Hypotheses and clauses, in the order of the node:

- The field is `(e : Type u) [Field e]`. The scheme over it is `V : Scheme.{u}` with
  structure map `p : V ⟶ Spec (.of e)`. Explicit structure maps are used because this
  statement concerns several morphisms over the field. Separation and local finite type
  are `[IsSeparated p] [LocallyOfFiniteType p]`.
- The finite group is `(H : Type v) [Group H] [Finite H]`, its automorphism action is
  `a : H →* Aut V`, and being over e is `ha : ∀ g, (a g).hom ≫ p = p`.
- `horbit` says, for each underlying point x, that some `W : V.affineOpens` contains
  `(a g).hom x` for every g. There is no hypothesis on stabilizers or the characteristic.
- The existential `Q`, `b`, `q` supplies the e-scheme and e-morphism through `q ≫ b = p`.
  `IsAdmissibleFiniteSchemeQuotient a q` is the landed definition, read in full: its
  conjuncts supply finite q, invariance, `Topology.IsQuotientMap q`, ordinary point fibres
  exactly the H-orbits, and injectivity of `q.app U` with image precisely invariant
  sections for EVERY open U. `Surjective q` states surjectivity explicitly.
- Geometric fibres use `pullback q t`, a scheme, for every algebraically closed field Ω
  and geometric point `t : Spec (.of Ω) ⟶ Q`. They are nonempty and the induced action is
  transitive on their underlying points x,y. The morphism l for a group member g is pinned
  to that action by BOTH equations with `pullback.fst` and `pullback.snd`; it is uniquely
  determined by these equations. Thus no arbitrary action or arbitrary map replaces the
  induced action. In particular this applies to the algebraic closure of each residue
  field specified in the geometric-fibre dependency. The test-field universe is u,
  matching Scheme.{u}; it is not an independent potentially smaller universe.
- The universal property quantifies over every scheme Z and invariant scheme morphism
  f, with `∃! r : Q ⟶ Z, q ≫ r = f`. This is in schemes, not just affine schemes or
  e-schemes. Its field-compatible specialization is also explicitly used below.
- `LocallyOfFiniteType b` and `IsReduced V → IsReduced Q` are the two permanence clauses.
- For every invariant open W, the next conjunct supplies an open O of Q with
  `q ⁻¹ᵁ O = W`, the restricted action `aW` and map r. The equations with W.ι and O.ι
  characterize their actual restrictions. It asserts `IsAdmissibleFiniteSchemeQuotient
  aW r` and the full categorical property on this restriction. This includes the empty
  and full invariant opens. Local finite type and reducedness restrict automatically;
  the geometric orbit assertion is likewise the restriction of the one above.
- For EVERY invariant affine W, the next conjunct gives an affine O with that preimage
  and an isomorphism `O.toScheme ≅ Spec (.of (finiteQuotientInvariantSections a W))`.
  The displayed diagram identifies the restricted q with Spec of the invariant-subring
  inclusion, using the canonical `hW.isoSpec` on W. Thus this states the canonical
  `Spec R → Spec R^H` formula, not only an abstract isomorphism of schemes.
- The helper `finiteQuotientInvariantSections` constructs this subring as the intersection
  of the equalizers of the actual pullback and restriction homomorphisms on common
  subopens. On an invariant open, testing the whole open is equivalent to fixed sections.
  This is a concrete ancillary construction for the invariant-ring clause of this node;
  it does not replace the landed quotient definition, create a second action notion, or
  postpone data. It contains no proof hole and needs no new independent definition node.
- Finally, every B with structure map c and invariant e-map v has a factor r satisfying
  both `q ≫ r = v` and `r ≫ c = b`. For every U, `IsFinite (v ∣_ U)` implies
  `IsFinite (pullback.snd r U.ι)`, exactly `Q ×_B U → U`. B has no Noetherian, separated,
  finite-type or affine hypothesis. Uniqueness of r is already the preceding universal
  property; it is not replaced by a freely chosen map.
- `orbit_in_affine_of_quasiProjective` states the quasi-projective finite-type admission
  clause with `[LocallyOfFiniteType p] [QuasiCompact p]` and `IsQuasiProjective p`.
  The latter is the existing upstream finite-coordinate projective-space immersion
  predicate, not a new definition. Empty coordinates give the empty scheme, which also
  embeds into P^0, so the finite-coordinate convention includes exactly the stated cases.
- `orbit_in_affine_subgroup` says the same orbit condition for `a.comp K.subtype` for
  EVERY subgroup K. Its more general context reflects the node proof's observation that
  this follows for every admissible action, independent of quasi-projectivity.
- No projectivity of Q, no quasi-compactness of V in the main theorem, and no faithfulness,
  freeness or tameness are asserted or assumed.

Dependency interfaces read and used:

- `Field`, from Mathlib's algebra field definitions.
- `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`, and `Scheme.Hom.appLE`, from
  `Mathlib.AlgebraicGeometry.Scheme`; affine opens and `IsAffineOpen.isoSpec` from
  `Mathlib.AlgebraicGeometry.AffineScheme` (available through the public dependencies).
- `AlgebraicGeometry.IsSeparated`, from `Mathlib.AlgebraicGeometry.Morphisms.Separated`,
  via the recorded `Mathlib.AlgebraicGeometry.Morphisms.Proper` dependency.
- `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`, from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its imports.
- `AlgebraicGeometry.IsFinite`, from `Mathlib.AlgebraicGeometry.Morphisms.Finite`;
  `AlgebraicGeometry.Surjective`, from `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.
- `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, publicly available through
  the scheme pullback/fibre imports. These render both geometric fibres and Q times_B U.
- `AlgebraicGeometry.IsReduced`, from `Mathlib.AlgebraicGeometry.Properties`.
- `AlgebraicGeometry.IsHProjective`, from the recorded
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, supplies the node's projective
  convention; the actual quasi-projective clause uses the existing immersion predicate
  rather than incorrectly substituting projectivity.
- Added the landed statement dependency `def-per-admissible-finite-scheme-quotient`, using
  `AlgebraicGeometry.IsAdmissibleFiniteSchemeQuotient` from
  `Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient`.
- Added the landed statement dependency `def-sc-quasi-projective`, using
  `AlgebraicGeometry.IsQuasiProjective` from
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective`.

The module imports the recorded non-Mathlib proof modules
`FiniteFreeAlgebraSpectrum`, `AffineGroupoidOrbitFibres`, `GradedPrimeAvoidance`, and
`ProjStandardOpenBasis` as plain proof imports, alongside the relevant Mathlib proof modules.
The theorem docstrings carry all ten proof steps with their DAG references: invariant affine
cover; affine groupoid; orbit space and invariant sheaf; localization including zero divisors;
finiteness; Artin--Tate and reducedness; categorical locality and restriction; image algebra
for an arbitrary base; Noetherian submodule finiteness; quasi-projective and subgroup admission.

Edge cases checked: V empty (Q and all fibres over existing geometric points are treated
correctly; there are no geometric points of empty Q); trivial and nonfaithful actions;
nonreduced rings and localization with zero divisors; characteristic dividing |H|; schemes V
not quasi-compact; arbitrary non-Noetherian B; U empty or full; W empty or full; trivial or
whole subgroup; finite fields in graded prime avoidance; and empty projective coordinate sets.
No averaging or generic freeness is used.

Searches performed:

- `msearch.py ... leanfinder "A finite group acting on a separated locally finite type
  scheme over a field with affine orbit neighbourhoods admits a finite geometric
  categorical quotient"`: eight hits, consisting of finite-set/Galois-category quotients
  and the affine finite-morphism criterion; none states this theorem.
- `msearch.py ... loogle '"Scheme", "quotient"'`: three hits, all
  `Scheme.Hom.liftQuotient` and its composition lemmas, concerning ideal quotients.
- `msearch.py ... grep 'quotient|invariant' AlgebraicGeometry`: 25 hits (Proj, ideal
  quotients, quotient topology and unrelated elliptic-curve material), no theorem match.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib for admissible actions,
  geometric quotients, affine orbit neighbourhoods, invariant rings and candidate names;
  the exact node-id search in WeilConjectures returned none. Located and reused the
  landed quotient predicate and upstream quasi-projectivity. `GaloisCoverAction` was
  inspected and rejected as an encoding because it requires etaleness and free action.
- DAG searches found `def-per-admissible-finite-scheme-quotient` and
  `def-sc-quasi-projective`; their records and full source declarations were inspected.
  No duplicate definition node is added.

Source check: read ILO IX 1.4, printed pp.132--133 (PDF pages 138--139), including the
projective-admissibility and subgroup quotient use; Stacks groupoids.tex
`lemma-find-invariant-affine` and properties.tex `lemma-ample-finite-set-in-affine`, case (4).

Validation: `scompile.py NE lem-sfb-admissible-finite-type-field-quotient <module>` passed
both the sandbox and actual library-module checks (2.0 s and 2.3 s) without warnings.
The initial probe's ambiguous pullback carrier and abbreviated ring-hom constructor were
corrected by explicit `Scheme.{u}` and `CommRingCat.ofHom`. Final dry-run results are below.

## Second reading by NE

The dispatcher brief reserves independent review to the maintainer and explicitly forbids
starting other agents. This section records the worker's self-check, not an independent reader.
I reopened the node and module and matched every hypothesis and clause as listed above.
The existing quotient predicate was checked for EVERY open, not merely affine opens.
The additional geometric-fibre assertion uses actual scheme pullbacks, with action maps
specified by both projections. The affine formula fixes the quotient map, not merely the
object. The restriction statement supplies the restricted action and map with compatibility
equations, and the arbitrary-base finiteness clause includes the e-structure equations.
The quasi-projective and subgroup admission clauses are separate declarations of the same
node. No statement change, extra hypothesis on the base, or omitted clause was found.

Delivery dry run: `deliver2.py NE lem-sfb-admissible-finite-type-field-quotient --no-push`
returned `OK (dry run): commit 24ddf0312c3 passes the preflight and compiles; nothing pushed`.
This includes recompilation after adding the explicit Artin--Tate and integral-adjoining
proof imports. Also read ILO X 2.3 Step 2, printed p.151 (PDF p.157), where the arbitrary
Sylow subgroup quotient X2/L and its finite surjective map are used.
