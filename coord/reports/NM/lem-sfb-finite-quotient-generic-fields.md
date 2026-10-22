## Worker report

The delivery states `AlgebraicGeometry.finiteQuotient_genericFields` in
`Sheaf.AlgebraicGeometry.FiniteQuotientGenericFields`. Its sole proof is `sorry`.
There are no definitions, auxiliary assertions, new nodes, dependency repairs, or statement
corrections. The original node is unchanged except for `lean`. The theorem docstring carries
all eight original proof steps, including their dependency citations and denominator calculation.

Source read: `literature/stacks-project/groupoids.tex`, lemma-invariants-base-change,
Tag 03BK, especially part (3) and its kernel/flat-base-change proof. The source identifies
invariants after flat localization; the node's explicit component-product and denominator
argument provides the claimed generic-field consequence. This is an agent-formulated consequence,
not a claim that Tag 03BK states the full geometric theorem verbatim.

Hypothesis-by-hypothesis correspondence:

- Schemes X and Z: `{X Z : Scheme.{u}}`; both may be empty or disconnected.
- Noetherian means a finite affine cover with Noetherian rings: `[IsNoetherian X]` and
  `[IsNoetherian Z]`. Mathlib's definition is locally Noetherian plus compact, and
  `isNoetherian_iff_of_finite_iSup_eq_top` gives precisely the finite-affine-cover criterion.
- Normal means all local rings are integrally closed domains: `hXnormal` and `hZnormal`
  quantify `IsDomain` and `IsIntegrallyClosed` on every structure-sheaf stalk. The upstream
  `IsNormalScheme` also requires integrality and is deliberately not used: it would exclude
  the disconnected case. These inline stalk conditions are the node's stated meaning of normality.
- A finite group H acting on X: `{H : Type v} [Group H] [Finite H] (a : H →* Aut X)`.
  The monoid homomorphism supplies the action laws and automorphisms. No injectivity or
  faithfulness is imposed. The group universe is independent of the scheme universe.
- Finite surjective morphism: `(q : X ⟶ Z) [IsFinite q] [Surjective q]`.
- Invariance: `hinvariant : ∀ h, (a h).hom ≫ q = q`.
- Geometric fibres are H-orbits: `hgeometric` quantifies every algebraically closed field
  `Ω : Type u` and two field-valued points x,y with equal image; it supplies an h with
  `x ≫ (a h).hom = y`. Invariance supplies the reverse implication. Finiteness and
  surjectivity ensure nonempty geometric fibres, including lifting the base geometric
  point along a finite nonzero fibre algebra. The field universe equals the scheme
  universe, so algebraic closures of residue fields and their finite composita are included;
  no independent smaller test-field universe can make this condition vacuous.
- The structure-sheaf identity through the structural map: for every Zariski open U,
  `hsheaf` makes `(q.app U).hom` injective and its image exactly the invariant sections.
  Invariance is expressed by equality of actual pullback and restriction maps on every
  common subopen W of `q ⁻¹ᵁ U` and `(a h).hom ⁻¹ᵁ (q ⁻¹ᵁ U)`. Since q is invariant,
  the full preimage is stable, so this is exactly the fixed-section condition. As the maps
  are q's own sheaf maps, restriction compatibility is already present. An arbitrary
  section-ring isomorphism, or an arbitrary embedding, is not substituted for this map.

Conclusion-by-conclusion correspondence:

- For every component C and its generic point η, the first conjunct gives
  `IsGenericPoint (q η) (q '' C)` and `q '' C ∈ irreducibleComponents Z`.
- The next conjunct makes every component E of Z equal to `q '' C` for a component C of X.
- The third conjunct says `q '' C = q '' C' ↔ ∃ h, (a h).hom '' C = C'`.
  Together these give exactly a bijection from H-orbits of components to components of Z.
  Generic points exist for every component by scheme sobriety, so the first conjunct
  supplies the image-component assertion for every component; it is not a conditional
  assertion missing components without a chosen point. No arbitrary quotient-set bijection
  is introduced: it is the one induced by q.
- For every generic η of any C, the last conjunct gives injectivity of the canonical
  `(q.residueFieldMap η).hom : κ(q η) →+* κ(η)` and characterizes its image elementwise.
  For `eh : (a h).hom η = η`, `(X.residueFieldCongr eh).inv` maps κ(η) to κ(hη),
  followed by `(a h).hom.residueFieldMap η` back to κ(η). Thus the displayed equality
  is precisely fixedness under the stabilizer, with canonical point-equality transport.
  Pullbacks by h give a right action; fixedness for all h is identical to fixedness for
  the conventional inverse-pullback left action since the stabilizer is closed under inversion.
  Quantifying h and its equality proof is equivalent to quantifying the subgroup
  `D = {h | hη = η}`. No arbitrary action on the residue field is supplied as data.
- Nonfaithful D-action and disconnected/non-generically-free X: there is no injectivity
  assumption on a, no uniqueness in `hgeometric`, no irreducibility assumption, and no
  restriction on the characteristic. These sentences of the node describe allowed cases,
  not additional conclusions needing a separate propositional conjunct.

Statement-dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `Scheme.Hom` (underlying locally ringed spaces and their morphisms).
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed`, with `IsDomain`. The node explicitly defines normality on scheme
  stalks; no alternative global normality predicate is introduced.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`;
  used through `IsNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian` and its affine criterion.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`. Only the finite branch of the dependency is needed here.
- `def-weil-surjective-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `AlgebraicGeometry.Surjective`, which is surjectivity of the underlying point map.
- `def-weil-irreducible-components`: its mathlib_match `irreducibleComponents` in
  `Mathlib.Topology.Irreducible`; the record is a Mathlib leaf without a lean record.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`, closure of a singleton.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.residueField`, `Scheme.Hom.residueFieldMap`, and `Scheme.residueFieldCongr`.

The modules for all recorded proof dependencies are imported privately, including
`NormalTopologicallyNoetherianComponents`, `AffineGroupoidOrbitFibres`, the finite-coproduct
spectrum API in Mathlib Limits, Proper/UniversallyClosed/QuasiFinite, Properties/Sober,
PrimeSpectrum.Topology, AffineScheme, FunctionField, and OpenImmersion. The normal-components
and affine-groupoid theorem signatures and docstrings were read. Nothing is proved by these
imports in this stage; they preserve the stage-3 plan.

Edge cases checked before drafting and on the completed statement:

- Empty X: surjectivity forces empty Z; there are no components or generic points, and
  the empty orbit set maps bijectively to the empty component set. No Nonempty is imposed.
- Trivial H: the sheaf condition identifies the canonical sheaf map with the full section
  ring, and the residue-field clause states surjectivity onto the full residue field.
- A permutation action on two disjoint copies of an integral normal scheme: components
  have a single orbit, and the point stabilizer sees the field of one copy.
- A trivial action of a nontrivial finite H on X, q the identity: the stabilizer is all H,
  its residue action can be completely nonfaithful, and the fixed field is unchanged.
- Ramified finite quotients are allowed: geometric transitivity has existence, not uniqueness.
- Characteristic dividing |H|: there is no invertibility or division-by-|H| assumption;
  the source proof uses the product of conjugate denominators instead of averaging.

Searches actually run:

- LeanFinder: "Finite group quotient of a normal Noetherian scheme generic points
  irreducible component orbits residue fields stabilizer invariants". Eight hits, notably
  `IsFractionRing.stabilizerHom_surjective` and `Ideal.Quotient.stabilizerHom_surjective`.
  These are algebraic stabilizer statements, not the node's full geometric statement.
- Loogle: `Scheme.Hom.residueFieldMap, MulAction`. Zero hits; the service reported the
  short identifier `Scheme.Hom.residueFieldMap` unknown. This result was not treated as
  evidence that the residue-field map is absent; its fully qualified definition was read.
- Mathlib grep through msearch: `quotient|invariant|stabilizer` in AlgebraicGeometry.
  Twenty-five hits, including unrelated Proj quotient rings, connected base-change
  quotient maps, and constant-sheaf maps; no full match.
- LeanSearch: "For a finite quotient of normal Noetherian schemes the generic residue
  field is the fixed field under the stabilizer and irreducible components correspond
  to group orbits". Eight hits, including `finite_irreducibleComponents_of_isNoetherian`,
  `Scheme.residueField`, `IsGalois.of_fixed_field`, and algebraic stabilizer results;
  none states the full conclusion for this finite scheme quotient.
- Project ripgrep of WeilConjectures and Sheaf for finite quotients, generic fields,
  geometric orbits, invariant sheaves, and exact proposed theorem names; plus exact
  node-id search in WeilConjectures. No duplicate of the theorem was found.
  `IsAdmissibleFiniteSchemeQuotient` was read: its invariant-section spelling is reusable,
  but its orbit-neighbourhood/admissibility and ordinary quotient-topology conditions
  are not this node's list of assumptions. It was not used as a stronger bundled hypothesis.
  `NormalScheme.lean` was also read; its integral normality predicate is unsuitable here.
  `dag/lean_names_upstream.json` has no finite-quotient-generic-field name match.

No statement dispute or node fault was found. All variables and both universes are
explicitly bound; `autoImplicit false` is set. No line exceeds 100 characters.

Validation: prescribed scompile.py compiled both its sandbox view and the final library
module with exit code zero and no diagnostics (3.2 s and 2.5 s respectively).

## Second reading by NM

A second pass by this dispatched worker compared the delivered node copy and module.
The independent review is the maintainer's review after delivery; no second worker was
started, as the dispatcher explicitly forbids starting other agents.

The critical checks on this pass were the distinction between normal and integral,
the two directions of the sheaf image iff, and the directions of residue-field transport.
The transport starts in κ(η), goes by the inverse of the equality-induced isomorphism
to κ(hη), and then by the actual automorphism's residue map to κ(η). The domain of
q's residue map is κ(qη), as required. The component clauses use actual set images
under q and actual translates under a, so their surjectivity and equality criterion
express the canonical component-orbit bijection. Geometric transitivity retains repeated
stabilizers and is not strengthened to freeness. This pass found no mismatch and made
no statement changes. The original JSON fields other than lean were compared and agree.
