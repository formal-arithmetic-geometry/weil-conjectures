## Worker report

Module: `Sheaf.Paper.FiniteRegularReductionDualizing`; declaration:
`AlgebraicGeometry.Etale.RegularReductionDualizing.finiteRegularReductionDualizing`.
The single theorem has `sorry` as its entire proof. All helper data are fully written
abbreviations, concrete composites, or a proposition collecting exactly the model and
its normalized coefficient tower. No object is chosen from an unnormalized existence.

Hypothesis and clause correspondence, with the node and source open:

- A field k: `(k : Type u) [Field k]`.
- A prime ell invertible in k: `(l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]`.
- A k-scheme and its structure morphism: `(X : Scheme.{u})`,
  `[X.Over (Spec (.of k))]`, and `X ↘ Spec (.of k)` throughout.
- Separated finite type: `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`
  instances on that structure morphism. No properness of X is assumed.
- Nonempty and irreducible: `[IrreducibleSpace X]`, whose parent field
  `toNonempty` supplies the required nonemptiness. There is no second nonempty binder.
- Regular reduction: `IsRegularScheme X.nilradical.subscheme`; this is the
  dependency's locally Noetherian and stalkwise regular predicate on the actual
  nilradical closed subscheme, not regularity of X itself.
- d = dim |X|: `∃ d : ℕ, topologicalKrullDim X = (d : WithBot ℕ∞) ∧ ...`.
  This asserts finiteness rather than assuming a dimension or silently truncating it.
- Every positive n: the Lean index n is the paper's n-1, so n=0 is Z/ell and all
  coefficients are `FiniteReduction.Coeff l (n+1)`. The two existing ULift layers
  are only universe transports of ZMod (ell^(n+1)); no coefficient ring is redefined.
- Small etale bounded constructible category: the constructibility conjunct of `Model` uses exactly
  `DerivedCategory.isBoundedConstructible`. The isomorphism is written in the
  ambient category and its object is proved bounded constructible; the full
  subcategory therefore has this same isomorphism. The target is likewise bounded
  constructible, by local rank one and its single cohomological shift.
- a_n^! of the base coefficient unit: `dualizingComplex (ModuleCat ...) a`, whose
  definition is the actual `rightDerivedUpperShriek` applied to the monoidal unit.
  Its adjunction is the ordinary compact-support adjunction. On the bounded
  constructible objects here Yoneda identifies it with the finite adjoint in
  `lem-per-adic-exceptional-projection`, with the same counit, as node proof step 6
  explains. It is not an arbitrary dualizing object.
- Lambda_X(0), roots with exponent action, and positive tensor powers: `twist` is
  only an abbreviation for the existing `Scheme.finiteEtaleTateTwist`. Its zero
  case is the constant coefficient sheaf; degree one is extension of the actual
  roots-of-unity ZMod module by the canonical size-lift coefficient map, and its
  higher cases are the ordinary sheaf tensor powers. Thus this is exactly the
  exponent action, not a newly supplied rank-one sheaf.
- a_n^! Lambda_k ≅ Lambda_X(d)[2d]: the existential family `theta` of `Model`, with literal
  `twistComplex ... d` and cohomological shift `(2 * d : ℤ)`.
- Locally free of rank one: the etale-cover conjunct of `Model` gives an etale cover on which the
  sheaf is isomorphic to the constant free module of rank one.
- Actual derived scalar reduction: `quotient` reuses `FiniteReduction.quotient`.
  `dualizingReduction` is precisely `ExceptionalCoefficients.mateMap` evaluated
  on the base unit, followed by the canonical scalar-unit isomorphism. Thus the
  square is about the counit-normalized reduction, not some isomorphism of the
  same endpoints.
- Ordinary tower on the right: the existential family `sheafReduction` of `Model` is ordinary scalar extension
  of the very same Tate sheaves. Its zero case is fixed by the canonical scalar
  unit (the zero-reduction equation); degree one is fixed by `roots : CoefficientLineComparison`
  (the degree-one equation); other degrees are tensor powers under the actual ordinary
  scalar tensorator (the tensor-reduction equation). The witness describes all powers so
  that the d-th power in the conclusion has its canonical tensor reduction.
- Root transition u -> u^ell: `CoefficientLineComparison.roots_power` prescribes
  exponent N/M, here ell^(n+2)/ell^(n+1)=ell; `generators` fixes the scalar action
  on every root/scalar generator. This excludes rescaling the transition by an
  arbitrary unit. No compatible roots in k are assumed.
- No higher Tor: the scalar-counit `IsIso` conjunct of `Model` asserts invertibility of the actual
  derived-to-ordinary scalar counit on the rank-one sheaf. The function
  `shiftedTwistReduction` retains this counit and shift commutation explicitly.
- Chosen simultaneously and compatibly: the final coefficient-square conjunct of `Model` says that
  scalar extension of theta_(n+1), followed by ordinary twist reduction and the
  shift comparison, equals the canonical exceptional reduction followed by theta_n.
  Applying shift -2d gives precisely the ordinary rank-one sheaf tower asserted
  in the node. Iterated squares follow by composition with the canonical scalar
  associators, so there is no independent arbitrary choice of long transition maps.
- Normalization: `dualizingComplex` is applied to the coefficient unit at Spec k.
  This fixes the relative normalization, whose dimension function is
  x -> trdeg_k kappa(x), by ILO XVII 4.1.2/4.1.3. There is no auxiliary absolute
  dualizing complex or unspecified shift. The proof docstring explicitly matches
  this with d - dim O_(X_red,x).
- No perfectness, smoothness, geometric regularity, or separable generation binder
  appears. A purely inseparable finite extension is included.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; QuasiCompact from its recorded module.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsSeparated` (the node's separated
  clause; no IsProper hypothesis is used).
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Mathlib.Topology.Irreducible`: `IrreducibleSpace`, supplied by the node's
  `mathlib_match` (`irreducibleComponents` and its IsIrreducible definition).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.Paper.AdicExceptionalProjection`: `exists_system` and its imports;
  the actual ordinary etale exceptional adjunction is the finite adjoint underlying
  that system, before its specified pro-etale transport.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.nilradical`,
  `Scheme.IdealSheafData.subscheme`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`: `Scheme.finiteEtaleTateTwist`.
- `Sheaf.Paper.FiniteSmoothCoefficientArrows`: `CoefficientLineComparison`,
  `scalarSingleMap`, `scalarShiftIso`, `scalarZeroLineIso`. These definitions have
  no smoothness assumption; their module name does not restrict their domain.
- `Sheaf.Paper.FiniteReductionConstructibility`: `FiniteReduction.Ring`, `Coeff`,
  `quotient`, owned by the new definition node `def-per-finite-reduction-coefficients`.
- `Sheaf.Paper.ExceptionalCoefficientComparison`: `ExceptionalCoefficients.mateMap`
  and `unitIso`, and its ordinary scalar-extension tensorator.

The five added statement dependencies consist of four already landed nodes for
the reduction, Tate sheaf and comparison interfaces and the new definition-only
ownership node `def-per-finite-reduction-coefficients`. The four landed dependency
node files are unchanged. The constructibility theorem is not a statement dependency:
its plain coefficient definitions are supplied by the new definition node. All recorded proof-dependency modules that exist are imported;
the potential-dualizing proof nodes currently have no recorded Lean modules and
are named in the eight-step proof docstring. No new prerequisite theorem is needed
to type the statement.

Edge cases checked before writing: d=0 gives the coefficient sheaf without a
positive twist, and shift zero; n=0 is the first allowed exponent, not Z/1.
Spec of a finite purely inseparable extension has d=0 and is covered. A regular
non-smooth curve over an imperfect field has d=1 and is not excluded. Nilpotent
thickenings are allowed by imposing regularity only on the reduction. The empty
scheme is excluded exactly by IrreducibleSpace. Roots of unity need only become
free on an etale cover; roots in k are never required.

Searches made (2026-10-18 UTC):

- msearch.py leanfinder, query "Finite etale normalized dualizing complex on a
  scheme with regular reduction is a Tate twist shifted by twice the dimension":
  eight unrelated etale-locus/normalization declarations; no exact match.
- msearch.py loogle, query `"dualizing", "regular"`: no hits.
- msearch.py grep, query `dualizing|regularReduction`, Mathlib/AlgebraicGeometry:
  no hits.
- msearch.py leansearch, query "Normalized dualizing complex regular reduction
  finite coefficients Tate twist": unrelated normalization, module duality and
  tactic declarations; no exact match.
- rg in WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  `lem-per-finite-regular-reduction-dualizing`, `regularReduction`,
  `regular_reduction`, `finiteRegular.*Dual`, and `finite_regular.*dual`:
  no existing statement. Searches for coefficient/root/twist reduction located
  the reused FiniteSmoothCoefficientArrows and FiniteReduction interfaces.
- Read ILO XVII the project server and the proof of the project server (regular connected case), and
  Bhatt--Scholze 6.7.20 from the locally supplied PDFs via pdftotext. The sources
  confirm the arbitrary-field normalization and compatible derived reductions.

No statement correction or disputed mathematical claim. The only postponed proof
is the named item theorem; all helper definitions have real data.

## Second reading by NR

Self-rereading, not an independent agent review: the dispatcher explicitly forbids
starting other agents and assigns the independent review to the maintainer.
Compared the node and final file clause by clause as above. In particular checked
that regularity is on X_red, irreducibility supplies nonemptiness, the prime-power
index starts at exponent one, the target is the literal ordinary Tate sheaf with
shift 2d, and the square uses the canonical exceptional counit transpose.
Checked that the degree-one reduction is fixed on all roots and scalars, and that
the zero case uses the canonical coefficient unit. The shift transport retains
the derived/ordinary scalar counit, so the statement cannot identify the two
reductions without asserting its invertibility. There are no extra field or
smoothness hypotheses and no proof-data definitions with sorry.

Compilation repair: the original large witness structure spent more than 60 s in
kernel checking its generated declarations. The final `Model` is the equivalent
existential proposition, with no generated structure projections or recursor.
The tensor equation uses `HEq` for the same morphisms with definitionally equal
recursive-tensor endpoints, avoiding expensive endpoint coercion during elaboration.
All canonical maps, witness families and equations are retained. The final node
record is extracted from the resulting theorem signature, including its proposition.


## New nodes

`def-per-finite-reduction-coefficients` owns the unchanged published definitions
`AlgebraicGeometry.FiniteReduction.Ring`, `Coeff` and `quotient` in
`Sheaf.Paper.FiniteReductionConstructibility`, with `existing: true`. Its statement
specifies both universe lifts of ZMod (ell^r) and the canonical quotient for m <= r.
The source is Bhatt--Scholze, proof of Lemma 6.7.20, whose finite coefficient tower
uses exactly these rings and maps. `Ring` is the first lift, `Coeff` the second;
`quotient` is exactly twice-lifted `ZMod.castHom (pow_dvd_pow l h)`. This requires
no primality or invertibility assumption at the definition level. For prime ell
and positive exponents it is precisely the finite tower in the item. The zero
exponent gives Z/1, equal levels give the canonical identity, and ell=0 with a
positive exponent uses ZMod 0 = integers. These extra definitional cases do not
add cases to the item's theorem, which still assumes a prime and uses n+1.

Searches on 2026-10-18 UTC: msearch LeanSearch for "The coefficient rings ZMod
(l^r) and the canonical quotient ring homomorphism ZMod (l^r) to ZMod (l^m) for m
less than or equal to r" found ZMod.castHom and ideal quotient maps; LeanFinder
for "Canonical quotient ring homomorphism ZMod (l^r) to ZMod (l^m) for m ≤ r with
universe lifts" found ZMod.castHom and PadicInt quotient compatibility; Mathlib
grep `def castHom|abbrev Ring|def quotient` in Data/ZMod found castHom and
quotient equivalences. The exact search records are preserved in the new node.
Upstream rg for `FiniteReduction|ZMod.castHom` found uses of ZMod.castHom but no
FiniteReduction definitions; project rg found the exact three helpers in the
published module. DAG rg for their full names found only the constructibility
and exceptional-coefficient theorem records, with no owning definition node.
`blueprint_refs.py search 'coefficient quotient'` found five unrelated blueprint
nodes. Thus this is ownership of existing data, with no new Lean module or copy.

## Repair of returned delivery 42936c8367b4

H2/H12: replaced `lem-pur-finite-reduction-constructibility` in the saved item's
added statement dependencies with `def-per-finite-reduction-coefficients` and
supplied its existing-definition record listing Ring, Coeff and quotient.
The item Lean module is retained byte-for-byte; its mathematical statement,
proof plan and all other item fields are unchanged. Compared the saved packet
with the refreshed current base: only `lean` and the authorized added
`stmt_deps` differ. The initial saved-packet dry run passed at 3526ff5a72;
this repair additionally resolves the independent review's ownership defect.
`lem-pur-exceptional-coefficient-comparison` is retained: its `unitIso` is
`unitIso_existsUnique.choose`, so its theorem supplies uniquely normalized data.

Additional self-reading by NR: opened the new node beside the three published
signatures and concrete bodies. The two lifts and the direction m <= r match;
the quotient is concrete data, not chosen from the constructibility theorem.
The new node's primary signature is verbatim from the published definition, and
all three declaration names are recorded. The existing full clause-by-clause
reading above remains applicable because the delivered Lean bytes are unchanged.
This is an author's self-check; independent review remains with the maintainer.
