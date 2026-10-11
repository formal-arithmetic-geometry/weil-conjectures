## Worker report

The module states `AlgebraicGeometry.singleComplexBaseChangeCriterion` using the existing
`AlgebraicGeometry.singleComplexBaseChangeQcqsInduction`. Its hypotheses bind a cartesian
square, quasi-compact and quasi-separated `f`, derived objects `E`, `K`, `K'`, their
quasi-coherence properties, a comparison morphism `φ`, and the stalkwise
`SingleComplexBaseChange.StalkCondition`; its conclusion is that the canonical derived
base-change map followed by the derived direct image of `φ` is an isomorphism. The proof is
`sorry`, as required at stage 2. `E` and its property are retained because the source
statement quantifies the tensor factor, although the currently landed qcqs induction
statement does not yet expose that tensor construction.

Dependencies used: `Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition`,
`AlgebraicGeometry.SingleComplexBaseChange.StalkCondition`; `Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction`,
`AlgebraicGeometry.singleComplexBaseChangeQcqsInduction`; `Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap`,
`AlgebraicGeometry.schemeDerivedBaseChangeMap`; `Sheaf.AlgebraicGeometry.DerivedCategory`,
`schemeDerivedCategory` and `schemeDerivedQCohProperty`; Mathlib `Scheme`, `IsPullback`,
`QuasiCompact`, and `QuasiSeparated`.

Edge cases checked: the cartesian square is arbitrary, `i : ℤ` is included by
`StalkCondition`, and no nonemptiness or boundedness restriction is introduced in the
formal comparison. The source's bounded-above complex presentation is represented by the
landed derived-category condition; this is a known mismatch recorded below.

Searches: `msearch.py leanfinder` for “single complex derived direct image base change
stalkwise criterion” (stalk lemmas only); `msearch.py loogle` for
`AlgebraicGeometry.derivedPullback, IsIso` (no hit); `msearch.py grep` for
`single.complex.*base.change|base.change.*single.complex` (no hit); `msearch.py leansearch`
for “derived pullback commutes with derived tensor product canonical comparison” (service
unavailable); `rg` in `lean/Sheaf` and the source repository (only the landed stalk and
qcqs modules).

Resolved original worker concern (see second reading): the blueprint statement quantifies a bounded-above quasi-coherent
complex `G^bullet` and a canonical tensor comparison, but the available landed Lean
interfaces expose only the derived-object comparison `φ` and `StalkCondition`; the exact
canonical tensor morphism is not currently nameable without adding a new definition node.
The module therefore records the strongest existing qcqs criterion while preserving all
cartesian, qcqs, quasi-coherence, and stalkwise hypotheses.

## Earlier second reading (a previous round; superseded)

Second reading is pending; the declaration and node signature were compared clause by
clause. The mismatch above is explicit and is not hidden.

## Second reading by R1

I read the node's statement and three proof steps, the actual signatures and bodies
of its five statement dependencies, the landed stalk-condition and qcqs modules,
and Stacks perfect.tex equation-bc, 0DJ8, 0DJ9 and 0DJA(1). The available local
Stacks source copy is the full perfect.tex, lines 6400–6650. The source assumes
schemes, a cartesian square, and quasi-coherent derived objects throughout these
lemmas; it assumes no Noetherian, separated, characteristic, or finiteness condition.
The bounded-above complex is the specialization in this item's own statement.

The following is the object/hypothesis/conclusion list reconstructed before editing,
with its final Lean rendering and verdict:

- Schemes X, S, T and X_T: `{X X' S S' : Scheme.{u}}`, with `S' = T`
  and `X' = X_T`. PASS: no affine or nonempty restriction.
- f:X→S and its base change f_T:X_T→T, with projections g and g': the four
  morphism binders and `sq : IsPullback g' f' f g`. PASS: this states the
  universal cartesian square, not just commutativity, and covers any model
  of the fibre product. I read the recorded base-change conventions: they
  use Mathlib fibre products; `IsPullback` is the equivalent universal formulation.
- f quasi-compact and quasi-separated: `[QuasiCompact f] [QuasiSeparated f]`.
  PASS: properties of f itself, not of X or g. The Mathlib definitions use
  compact inverse images and the quasi-compact diagonal respectively.
- Arbitrary E in D_QCoh(O_X): `E : schemeDerivedCategory X` and
  `hE : schemeDerivedQCohProperty X E`. PASS: the latter is quasi-coherence
  of every cohomology sheaf; no perfectness or boundedness on E.
- Bounded-above complex G of quasi-coherent O_X-modules: the actual
  `CochainComplex (SheafOfModules ... (moduleRings X.toRingedSpace)) ℤ`
  binder, `∃ b : ℤ, G.IsStrictlyLE b`, and `∀ i : ℤ, (G.X i).IsQuasicoherent`.
  PASS after repair: termwise quasi-coherence and a genuine upper bound;
  G is not merely an arbitrary derived object with quasi-coherent cohomology.
- Ordinary (g')*G: the termwise `Scheme.Modules.tensorPullback g'` complex,
  localized by `DerivedCategory.Q`. PASS: this is the recorded tensor-formula
  module pullback, never Mathlib's other `Scheme.Modules.pullback`.
- The canonical map L(g')*Q(G)→Q((g')*G):
  `SingleComplexBaseChange.counit g'` at the homotopy class of G.
  PASS: I read its definition; it selects the same universal left-derived
  counit as the existing pullback composition construction.
- Every point x' and every integer i, the specified stalk comparison is
  invertible: `h_stalk : SingleComplexBaseChange.StalkCondition ...`
  applied to Q(G), Q((g')*G), and that counit. PASS: I read the predicate
  and its coordinates. It uses the actual stalk ring maps, the localized
  base-derived tensor comparison, and the chain map representing this
  same counit. The target is H^i(((g')*G)_{x'}). Quantifying over all K-flat
  coordinates does not strengthen the condition: independence and existence
  are part of the existing coordinate interface, not hypotheses on G.
- Canonical Lg*Rf*(E tensor-derived G)→Rf_T*(L(g')*E tensor-derived (g')*G)
  is an isomorphism in D(O_T): `IsIso` of `schemeDerivedBaseChangeMap`
  at `E ⊗ DerivedCategory.Q.obj G`, followed by Rf'_*(the canonical
  tensor comparison, then `Lg'^*E ◁ counit(G)`). PASS after repair:
  the tensor factor occurs on both sides and the same canonical counit
  that enters the stalk hypothesis enters the conclusion.
- Localization universes: `u` and `w` are explicitly bound. The shared
  `∀ Y, HasDerivedCategory` binder is the existing localization convention;
  the standard large localization exists for every scheme, so it adds no
  mathematical finiteness assumption. Schemes of different initial sizes
  can be placed in their common larger universe. No small test universe
  makes the stalk hypothesis vacuous.

Edge cases: zero E or G are allowed; G=0 has every upper bound. Empty X or X'
are allowed and the pointwise condition is correctly vacuous on an empty X'.
There is no index set in the statement. Degree zero, negative degrees and all
positive degrees occur through `i : ℤ`; an upper bound of zero is permitted.
There is no field, characteristic, Noetherian, Tor-independence, flatness of G,
or nonemptiness assumption. No variable or universe is unbound.

Mismatches found and repaired: the original E was unused; the bounded-above
termwise quasi-coherent complex was replaced by arbitrary K; the ordinary
pullback and its canonical counit were replaced by arbitrary K' and φ;
and the conclusion omitted both tensor factors. Those are H3 faults, not
an acceptable substitute theorem. I restored each clause, removed the unused
DerivedPullbackTensorProduct import from the item's module, and rewrote its
proof docstring to carry all three node steps. The natural-language item
statement and proof are unchanged. Its Lean signature is read verbatim by the
project signature reader. The earlier disputed-interface remark is resolved
by the new definition below, rather than weakening the statement.

Searches performed independently: LeanFinder “inverse image tensor of unbounded
quasi coherent complexes canonical comparison” returned eight generic sheaf
and homological tensor declarations, none this criterion; Loogle
“Functor.LaxMonoidal.μ” was unknown in the public index; LeanSearch “canonical
tensor comparison for derived inverse image of module sheaves” was unavailable
(Internal Server Error), recorded as unavailable. `msearch.py grep` for
“derived.*pullback.*tensor|pullback.*tensor.*derived” gave no exact match.
I searched DAG, Mathlib, WeilConjectures, and lean/Sheaf with tensor comparison,
monoidal pullback, localization tensor map, and the proposed full names.
The existing K-flat existential theorem `derivedPullback_tensorProduct` and
upstream `DerivedCategory.laxMonoidalQ` are reused as the construction and
coordinate model; neither supplies the named canonical map between the
recorded derived monoidal tensor objects. No existing declaration states this
item, and no existing definition node carries this comparison as a map.

I independently read the new definition against 079U and 0DJA(1). The total
complex helper specializes the existing `CochainComplex.mapBifunctor`; it is
not a second tensor construction. The model map is the existing upstream lax
monoidal localization map, with exactly the instances used in the recorded
derived tensor structure. The defining predicate pins every chain summand
to the existing `module_pullback_tensor` map and pins the derived map to the
shared counit by a commuting equation for all K-flat representatives.
Naturality in both derived arguments is also required explicitly, so the
equation transports along representative isomorphisms. Those representatives
cover every pair of derived objects, and all maps on
the equation except the unknown comparison are invertible there, so it
specifies the canonical map uniquely; it does not introduce a free comparison
or arbitrary monoidal structure. Its existence is a named theorem with sorry
and a complete construction proof docstring; the definition chooses data
from that theorem. No data definition has sorry and nothing is proved.
The new node has all required stage-1 fields, cites every notion it uses,
is in this item's chapter and unit, and points to the same ancestor.
There are no dependency replacement modules or statement corrections.

## New nodes

`def-pc-derived-pullback-tensor-comparison` defines the canonical map on the
shared derived tensor objects, characterized by the actual module tensor
comparison and the shared left-derived counits on every K-flat pair.
Source: Stacks Cohomology 079U and perfect.tex 0DJA(1). Searches and field
review are recorded above and in the node. The existing theorem only
quantifies over complexes and does not expose this map; all underlying
module, total-complex, counit and derived tensor constructions are reused.

Validation: both final modules compiled together locally with no errors or
warnings. The delivery dry run then compiled both on the server and printed
OK: preflight passes. The two proofs remain `sorry` as required for stage 2.
