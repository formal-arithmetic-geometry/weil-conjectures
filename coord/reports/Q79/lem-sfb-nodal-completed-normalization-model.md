## Worker report

This repairs immutable head `237aacc27e99`. The original Lean statement was wrong and incomplete;
its earlier second reading was also wrong. The DAG's mathematical statement is unchanged. The
sandbox node is regenerated from current main, with changes only to `lean` and added definition
statement dependencies. No dependency module or new node is delivered.

The module states `AlgebraicGeometry.Scheme.nodal_completed_normalization_model` with one `sorry`.
Its helper `nodalNormalizationBranchResidue` is real data: transport the pushforward stalk along
`ν(y) = x`, use `presheaf.stalkPushforward` to the normalization's local ring, apply its actual
`Scheme.residue`, and then the specified residue-field identification. It contains no `sorry`.

For the correspondence below, A denotes `C.presheaf.stalk x.val`, B denotes the existing canonical
`normalizationPushforwardStalk C x.val`, m denotes `IsLocalRing.maximalIdeal A`, and I denotes
`m.map (algebraMap A B)`. The file writes all completion types in full: Â is `AdicCompletion m A`,
and Bhat is `AdicCompletion I B`. These are explanatory abbreviations in this report only.

Hypotheses, in the node's order:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Nonempty proper reduced k-scheme: `(C : Scheme.{u})`, its `Over (Spec (.of k))` instance,
  `[IsProper (C ↘ Spec (.of k))]`, `[IsReduced C]`, and `(hC : Nonempty C)`.
- Pure dimension one: `(hpure : C.IsPureDimension 1)`, exactly the recorded definition.
- Smooth except at nodes: `hnodal` quantifies over every point outside the structure morphism's
  `smoothLocus` and requires the stated completed ring isomorphism to the quotient by uv.
- Reduced normalization: every occurrence uses `C.reducedNormalization` and its canonical
  `C.fromReducedNormalization`, as defined in the recorded dependency.
- S: `hS` identifies the supplied set with exactly the nonsmooth locus.

Conclusion clauses, in the node's order:

- Noetherian C: `IsNoetherian C`, the class combining locally Noetherian and compact space.
- Finite closed k-points S: `S.Finite`; for each `x : S`, `IsClosed {x.val}` and a residue-field
  isomorphism `r` whose `Spec.map r.inv` equals the structural map from that residue field.
- Finite normalization: `IsFinite C.fromReducedNormalization`.
- Finitely many smooth projective connected components: `Finite (irreducibleComponents C)` and,
  for each actual index Z, connectedness of `(C.reducedNormalizationComponent Z).normalization`
  and smoothness/projectivity of its canonical inclusion into the normalization followed by ν
  and the structure morphism. `reducedNormalization` is definitionally the coproduct of precisely
  these schemes. Connected nonempty coproduct summands are its connected components. There is no
  independently quantified family and no empty-index loophole.
- Isomorphism over C minus S: `IsIso (pullback.snd ν smoothLocus.ι)`. By `hS`, that open is C minus
  S.
- B canonically equals the pushforward stalk: B is that actual stalk, with its canonical A-algebra
  structure; the conclusion supplies an A-algebra equivalence to `integralClosure A (FractionRing
  A)`.
  Such an A-algebra identification is unique: integral-closure elements are fractions a/s with s
  regular, so an A-algebra map must fix each one. No product decomposition of uncompleted B is used.
- B finite over A and dimension A = 1: `Module.Finite A B` and `ringKrullDim A = 1`.
- Every chosen nodal presentation: the entire local model follows `∀ α : Â ≃+* k[[u,v]]/(uv)`.
  A particular α is not silently selected from `hnodal`.
- Canonical completed inclusion: the A-algebra homomorphism `i : Â →ₐ[A] Bhat` is specified at
  every quotient level. Whenever a has representative b modulo m^n, `i a` has representative
  `algebraMap A B b` modulo I^n. Quotient representatives exist, so this determines i everywhere.
- Normalization of Â: an equivalence `E : Bhat ≃+* integralClosure Â (FractionRing Â)` carries
  `i a` to the canonical algebra-map image of a. Together with `e : Bhat ≃+* P`, this identifies
  the normalization with P compatibly with the inclusion.
- Axis formula: for every multivariate series h, `e (i (α.symm (Quotient.mk _ h)))` is the pair
  whose nth coefficients are `MvPowerSeries.coeff (Finsupp.single 0 n) h` and the analogous
  expression for variable 1. These are precisely h(u,0) and h(0,v).
- Exact image: the range of `e ∘ i` is equivalent to equality of the two constant coefficients.
- Total fractions: only `FractionRing Â`, not `FractionRing A`, has an equivalence q to
  `LaurentSeries k × LaurentSeries k`. Its restriction on every a in Â is the Laurent inclusion
  of the two coordinate series `e (i a)`. The universal property determines q on fractions.
- Canonical tensor/completion identification as Â-algebras: `tensor` is an actual `AlgEquiv`
  from `Â ⊗[A] B` to P for the action `(e.toRingHom.comp i.toRingHom).toAlgebra` on P. Its value
  on every a tensor b is `e (i a * AdicCompletion.of I B b)`. Composing with e inverse identifies
  the tensor with Bhat = lim B/I^n. Since I=mB, I^n=m^nB. Swapping tensor factors gives the node's
  B tensor Â convention with exactly the right-factor Â-action.
- Two maximal ideals, two points, and residues: y is an equivalence from `Fin 2` to the actual
  fibre set `{y | ν y = x}`; M is an equivalence from `Fin 2` to all maximal ideals of B.
  For each branch its actual point-residue map is surjective, has kernel `(M a).val`, and agrees
  with the quotient isomorphism `res a : B/(M a).val ≃+* k` on every representative b. Finally the
  two maps equal the two constant-term projections after the canonical completion of b and e.
  Thus the residue maps, ideals and points are linked, not merely separately counted. For a
  ring presentation α that twists coefficients, the residue-field identifications may twist
  accordingly; the global assertion about S uses the structural k-point identifications.
- Finite inverse images on each C_a: for every actual summand and every finite set T of smooth
  closed points, the inverse image of `S ∪ T` under its canonical map to C is finite. Taking
  T empty gives the assertion for S alone.

Dependency declarations read and used:

- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsReduced`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Smooth` and
  `smoothLocus`.
- `def-weil-field`, `def-weil-algebraic-closure`: Mathlib `Field`, `IsAlgClosed`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `IsProper`.
- `def-weil-finite-integral-morphism`: Mathlib morphism `IsFinite`.
- `def-weil-pure-dimension`: `Sheaf.AlgebraicGeometry.PureDimension`, `Scheme.IsPureDimension`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`, `IsLocallyNoetherian`; `IsNoetherian`
  extends it by compactness.
- `def-weil-pbc-reduced-normalization`: `Sheaf.AlgebraicGeometry.ReducedNormalization`,
  `reducedNormalizationComponent`, `reducedNormalization`, `fromReducedNormalization`.
- Added existing `def-trf-normalization-pushforward-stalk`: the existing definition and algebra
  instance `normalizationPushforwardStalk` and `normalizationPushforwardStalkAlgebra`, physically
  in `Sheaf.AlgebraicGeometry.NormalizationSingularSkyscraper`. No theorem is used to define B.
- Added existing `def-pc-projective-morphism`:
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `IsProjective`. Added existing Mathlib leaf `def-weil-pbc-laurent-series`: `LaurentSeries`, with
  its canonical `PowerSeries` inclusion. These notions already occur in the node's statement.
- `def-weil-pbc-adic-completion`: Mathlib `AdicCompletion`, `of`, `evalₐ`, and algebra instances.
- `def-weil-pbc-integral-closure`: Mathlib `integralClosure`.
- `def-weil-pbc-krull-dimension-ring`: Mathlib `ringKrullDim`.
- `def-weil-pbc-multivariate-power-series`: Mathlib `MvPowerSeries`, `PowerSeries`, coefficients.
- `def-weil-module-base-change`: Mathlib tensor product with the commuted tensor-factor order.

The module imports the stated project proof dependencies with ordinary `import`; the theorem
proof docstring reproduces all thirteen node proof steps and names their inputs. The structural
maps, finite-quotient formulas, axis coefficients, tensor formula and actual residues together
make the resulting comparisons canonical; they are not arbitrary existential equivalences.

Edge cases: smooth P¹ has S empty, so the local clauses are vacuous while global component
geometry remains present. A disconnected union has all its actual coproduct summands covered.
A reducible transverse node has two components; an irreducible nodal cubic has two points over
its self-node on the same component. For that cubic Q(A) is a field, a direct counterexample to
the rejected qA clause; the repaired product concerns only Q(Â). Zero branch series are included
in the axis and range formulas. Characteristic two changes none of the coefficient, idempotent,
regular-denominator or residue arguments. All universes are explicit; all compiler probes and
compiles use module mode and the required wrapper.

Searches retained from the first delivery: msearch LeanFinder on the completed normalization
model (only relative normalization APIs), Loogle on scheme normalization/completion (no exact
match), and grep on nodal/equal-constant/completed normalization (no exact item match). Repair
searches: `rg` in DAG, Mathlib, WeilConjectures and Sheaf located the already landed definition
owner `def-trf-normalization-pushforward-stalk` and its source. Blueprint search for normalization
stalk found zero matches. msearch LeanSearch on the pushforward normalization stalk and adic
completion returned general stalk maps; LeanFinder on normalization stalk and maximal-ideal
completion returned general affine stalk/localization APIs; msearch grep of AlgebraicGeometry
for the three normalization-stalk aliases returned no hits. The actual project definitions are
reused, and the completion aliases without definition owners are not used. A search for the new
helper name found no existing declaration; it is simply the composed canonical maps of this
node, not a second independent normalization construction.

## Repair of returned head 237aacc27e99

1. Removed qA entirely. q now concerns only the total fraction ring of Â, with its canonical
   extension formula. Removed both zero-preservation tautologies.
2. Removed the arbitrary finite family. Used the actual componentwise normalization summands,
   their finite index type, their canonical maps, and their connectedness/smoothness/projectivity.
3. Added every omitted clause: Noetherianity; structural closed k-points; normal-open isomorphism;
   finite B; exactly two maximal ideals and fibre points with residues; completed tensor algebra
   equivalence; finite preimages on every actual normalized component.
4. Pinned i on every quotient, e on all axis restrictions for every α, and the tensor map on every
   pure tensor. Replaced arbitrary residue maps with actual point-residue maps, with kernels,
   quotient identifications and agreement with constant terms. No tautological conjunct remains.
5. H2: cite the already landed definition owner of the pushforward stalk, and use Mathlib's full
   completion types. No theorem node is added to statement dependencies.
6. H4: replaced the hand-written `hpure` with `C.IsPureDimension 1`.
7. Replaced the incorrect original second reading with the clause-by-clause reading below.

## Second reading by Q79

I reread the node, its thirteen proof steps, the repaired Lean, and the recorded definitions.
The first reading missed the false uncompleted fraction-ring product, arbitrary empty component
family, omitted conclusions, arbitrary comparison maps and dependency ownership; the return
identified these correctly. This rereading is a self-review, not a claim of another agent's
independent review; the dispatcher explicitly forbids starting agents.

The repaired field, nonempty proper reduced scheme, recorded pure-dimension predicate and
completed node hypothesis agree with the node. The indices of the global component clause are
literally `irreducibleComponents C`, and its schemes and inclusions are literally the summands
used by `reducedNormalization`. Thus v=0 can no longer satisfy an unrelated conclusion. The open
restriction uses exactly the smooth locus whose complement is S, and the finite-preimage clause
uses those same actual inclusions. Noetherianity, closed structural k-points, finite ν, finite B,
and local dimension one are separate, explicit conjuncts.

For each node the ring B has the definition-owned canonical stalk algebra; an A-algebra
identification with the actual integral closure prevents replacement by an arbitrary unrelated
normalization. All model clauses are inside `∀ α`. The quotient-by-quotient formula pins i;
coefficient restriction on quotient representatives pins e after α; E identifies the genuine
integral closure; the explicit completed-base action in the AlgEquiv and its pure-tensor formula
pin tensor. The q formula extends this same embedding only for completed total fractions. The
actual stalk-to-residue maps at y are tied simultaneously to M's maximal kernels, quotient
isomorphisms, and constant terms. These replace every arbitrary/tautological map of the rejected
version. I checked the nodal cubic and S empty specifically against the repaired clauses.

The sources read are curves.tex 0E68 and 0C4A Case I, varieties.tex 0C1R and 0C3V, and the
recorded componentwise-normalization definitions. The completed replacement is necessary because
0E68's uncompleted product calculation does not hold for the irreducible nodal cubic, as the DAG
already explains. The node statement itself needs no correction. The full repaired module
compiled cleanly with scompile.py; only the expected sorry proof remains. Independent acceptance
is left to the maintainer's review.
