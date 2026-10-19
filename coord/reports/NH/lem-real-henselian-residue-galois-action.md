## Worker report

Item: lem-real-henselian-residue-galois-action, group NH, stage 2.
The single module `lean/Sheaf/RingTheory/HenselianResidueGaloisAction.lean` states
`HenselianLocalRing.exists_residue_galois_action`; its only proof is `sorry`.
There are no new definitions, new DAG nodes, dependency repairs, or statement changes.
The current node has a reviewed stage-1 split from NC but no Lean record. Thus the
previous worker's stale-stage-1-assignment diagnosis does not resolve this stage-2 item.

Hypotheses, in the order of the node:

- A finite field k0 = F_q: `(k0 : Type u) [Field k0] [Finite k0]`. The value q is its
  cardinality and is not separately used in the claim; arbitrary finite fields are
  precisely the fields in def-weil-finite-field-q-elements (GaloisField and
  FiniteField.ringEquivOfCardEq).
- A henselian local commutative k0-algebra R: `(R : Type v) [CommRing R]
  [HenselianLocalRing R] [Algebra k0 R]`. The inherited `IsLocalRing R` gives its
  canonical maximal ideal and residue field.
- Finite residue field kappa: `[Finite (IsLocalRing.ResidueField R)]`.
- A field K and a unital k0-algebra map R -> K: `(K : Type w) [Field K]
  [Algebra k0 K] [Algebra R K] [IsScalarTower k0 R K]`. `Algebra R K` gives the map
  and the tower says it respects k0. Neither injectivity nor locality of this map
  is assumed.
- A chosen algebraic closure Omega/K: `(Ω : Type z) [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω]`.
- The induced R- and k0-algebra maps into Omega are written as compatible algebra
  structures and scalar towers. These only express the specified composites, not
  additional mathematical hypotheses. All four universe variables are explicit
  and independent.

Conclusions, clause by clause:

- B is the integral closure of the image of R in Omega: throughout it is the
  existing `integralClosure R Ω`, whose elements are precisely the integral
  elements for `algebraMap R Ω`. This definition applies to noninjective maps.
- B is local: first conjunct `IsLocalRing (integralClosure R Ω)`. Its canonical
  `IsLocalRing.maximalIdeal` is the unique maximal ideal n.
- n contracts to m: the next conjunct is the exact `Ideal.comap ... = ...`
  equality. The `IsLocalHom` conjunct is the equivalent local-map formulation,
  used to expose Mathlib's canonical kappa-algebra structure on the residue field.
- kappa-bar = B/n is an algebraic closure of kappa: `IsAlgClosure
  (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField (integralClosure R Ω))`.
  `IsLocalRing.ResidueField` is literally the quotient by the maximal ideal.
- Every sigma preserves B: the group homomorphism `a` restricts each
  `Ω ≃ₐ[K] Ω` to an R-algebra automorphism of B, with the equality
  `((a σ b : B) : Ω) = σ (b : Ω)` for every b. Since `a σ` is an equivalence,
  this states preservation in both directions, not just an inclusion.
- Every sigma preserves n: `Ideal.comap (a σ).toRingHom n = n`, for every sigma.
- Reduction induces a continuous homomorphism r of the specified Galois groups:
  `r : (Ω ≃ₐ[K] Ω) →* (kappa-bar ≃ₐ[kappa] kappa-bar)` and `Continuous r`.
  Mathlib's `krullTopology` is the actual topology on both automorphism groups;
  for algebraic closures its finite-subextension basis is equivalently the
  pointwise stabilizer basis on finite sets in the node.
- Its characterization: `r σ (IsLocalRing.residue B b) =
  IsLocalRing.residue B (a σ b)`, for every sigma and b. Combined with the
  preceding equality for a, this is exactly reduction of sigma(b). The residue
  map is surjective, so this formula determines r on every element.
- k' is the subfield of algebraic constants: existing `algebraicClosure k0 Ω`.
  `mem_algebraicClosure_iff` identifies its elements as algebraic over k0.
- k' is contained in B: the k0-algebra homomorphism `c` has ambient value
  `(c x : Ω) = (x : Ω)` for every constant. Thus c is precisely the inclusion,
  determined by that equality.
- Reduction restricts to a k0-isomorphism t: the witness is a full
  `algebraicClosure k0 Ω ≃ₐ[k0] IsLocalRing.ResidueField B`, and its formula on
  every constant is `t x = IsLocalRing.residue B (c x)`. This determines t.
- Equivariance for every sigma: for each constant x the final clause supplies a
  constant y with `(y : Ω) = σ (x : Ω)` and `t y = r σ (t x)`. The inclusion
  into Omega is injective, so y is exactly sigma restricted to k' applied to x.
  This is the whole commuting-square assertion, and also explicitly records
  stability of k' under sigma. No choice of a different action is admitted.

The two `∀ [instance]` binders occur in the conclusion, after locality and the
local-map property have been asserted. They make the canonical dependent residue
objects available to typeclass elaboration without a `let` in the statement.
They are not hypotheses: the preceding conjunct supplies the respective class.
Both classes are propositions, so proof irrelevance makes these binders independent
of the chosen evidence. The full conclusion therefore asserts every clause even
when no local instance has been supplied by a consumer.

Dependency declarations read and used:

- def-weil-finite-field-q-elements: `GaloisField` in
  `Mathlib.FieldTheory.Finite.GaloisField`; used through its equivalent arbitrary
  finite-field presentation, with no cardinality restriction beyond finiteness.
- def-weil-pbc-henselian-terminology: `HenselianLocalRing`, inherited from
  `Mathlib.RingTheory.Henselian` by the recorded module
  `WeilConjectures.Mathlib.RingTheory.Henselian`. The recorded strict henselian
  class is not needed because this node asks only for henselianity.
- def-weil-algebraic-closure: `IsAlgClosure` from
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, imported with the recorded
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`.
- def-weil-pbc-integral-closure: `integralClosure` from its recorded
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`.
- def-real-boundary-absolute-galois-group: `AlgEquiv.aut` from
  `Mathlib.Algebra.Algebra.Equiv`; its specialization is exactly `Ω ≃ₐ[K] Ω`
  and the corresponding residue automorphism group, as the dependency states.
- The stated proof dependencies are imported without public: the recorded
  `WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct` (read using
  `scompile.py --source`), `Mathlib.RingTheory.LocalRing.ResidueField.Instances`,
  `Mathlib.RingTheory.Ideal.GoingUp`, and
  `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`. The remaining
  integral/algebraic-closure facts are already in the public imports needed
  for the statement. The docstring records all ten proof steps and the named
  DAG inputs.

Edge cases checked before the statement:

- R = K = k0 finite: B = Omega is a field, n = 0, its residue is Omega, and t
  is the reduction identification. No positive-dimensional restriction occurs.
- A henselian DVR with finite residue and K its fraction field: B is the usual
  local integral closure and the statement gives the expected residue action.
- R -> K kills m, for example R = k0[epsilon]/(epsilon^2), K = k0: B is the
  algebraic closure of the image field; contraction of 0 is m. No injectivity
  or reducedness of R was introduced.
- K may be transcendental over the image of R, for example R = k0 and
  K = k0(T): B is the algebraic constants inside Omega, not all of Omega.
  The statement uses the integral closure rather than identifying B with Omega.
- All positive characteristics and finite field cardinalities are included.
  The zero ring R is already excluded by the source's local-ring convention
  and by the unital map to the nonzero field K.

Searches performed (2026-10-18):

- msearch.py leansearch: "Integral closure of a henselian local ring in an
  algebraically closed field is local with algebraically closed residue field
  and equivariant Galois reduction". Eight results include `integralClosure`,
  its integral-closure instance, and henselian-to-local inheritance; no full
  theorem or residue/constant comparison.
- msearch.py leanfinder: "Integral closure of a henselian local ring in an
  algebraic closure is local and reduction gives a continuous Galois action
  equivariant with algebraic constants". Results include `galRestrict`,
  `galLift`, `IsIntegralClosure.MulSemiringAction`, and `Field.henselian`.
  Read `IntegralRestrict.lean`: the equivalence galRestrict assumes a fraction
  field; it is not the present theorem, which allows noninjective R -> K.
- msearch.py loogle: `IsLocalRing.ResidueField, AlgEquiv`. Results include
  `IsLocalRing.ResidueField.mapAlgEquiv`, `mapAlgEquiv'`, and their reduction
  formulas. They act on an already local algebra and do not give locality,
  algebraic closedness, continuity, or the constants comparison.
- msearch.py grep: `residue.*[Gg]alois|[Gg]alois.*residue|integralClosure.*[Ll]ocal`.
  Results concern ramification, invariant rings, and localizations, not this
  entire statement.
- rg searches of upstream WeilConjectures and side lean/Sheaf for the item id,
  `residueGalois|residue_galois|henselian.*[Gg]alois|[Gg]alois.*[Rr]esidue` found
  no declaration of this statement. The other residue-Galois mentions concern
  finite normalization residue degrees.
- rg of upstream, side Lean, and dag/lean_names_upstream.json for the proposed
  declaration name found no clash. No declaration already says this node.

Validation: scompile.py compiled the module both as the isolated sandbox file
and with its library module path; both passed with no diagnostics. A direct
recorded-module source request initially retried an SSH multiplexing refusal
and then succeeded. No tool was modified or bypassed.

## Second reading by NH

A separate rereading by the same worker compared the complete node text, its
source places, the module, and the JSON signature. There was no second agent;
the dispatch brief explicitly prohibits starting agents, and the maintainer's
independent review remains the delivery review.

Checked every hypothesis and conclusion against the mapping above. In particular,
R -> K is not assumed local or injective; the quotient is the residue of the actual
integral closure; the target Galois group fixes kappa and both topologies are Krull;
the constants map and isomorphism are forced by ambient inclusion and reduction;
and the last existential is exactly restriction to constants, not an arbitrary
action. The universally exposed instance evidence follows asserted conjuncts,
so there is no vacuity from an unavailable local instance. No universe is equated
with another. The proof remains solely sorry. Added the explicit import of the
recorded integralClosure module during this reading. No node statement change
or STATEMENT-DISPUTED issue was found.
