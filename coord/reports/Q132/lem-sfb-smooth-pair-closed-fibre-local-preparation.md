## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothPairClosedFibreLocalPreparation` states
`AlgebraicGeometry.smooth_pair_closed_fibre_local_preparation`. Its sole theorem
has `sorry` as its whole proof. No definitions, helper theorems, dependency repairs,
new nodes, or statement corrections are needed. The node changes only in `lean`.

Source read: the online English EGA IV4 translation, Proposition 21.14.3(ii),
including the entire final paragraph beginning “Let y be a closed point”. The
source explicitly chooses y specializing from the original point, obtains actual
preadic formal smoothness, strict dimension inequality, the prime corresponding
to the original point and finite residue extension. The inherited DAG proof makes
the generic/nongeneric dimension distinction explicit. Its eight proof steps and
all 24 proof-dependency records were read and reproduced in the theorem docstring.
The current blueprint unit was read at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`.
This item is a supporting lemma, not the unit statement. No source correction is
proposed: in particular, the dimension is the dimension of the actual local ring,
not the topological local dimension at a nonclosed fibre point.

Hypothesis and conclusion correspondence (every clause):

- A₀ and B₀ are `Type u` with `CommRing`; `[IsNoetherianRing A₀]`,
  `[IsDomain A₀]`, and `[IsIntegrallyClosed A₀]` say exactly Noetherian normal
  domain. A common ambient universe allows both rings without any size restriction.
- T and V are literally `Spec (CommRingCat.of A₀)` and
  `Spec (CommRingCat.of B₀)`. `g` is their actual scheme morphism and `[Smooth g]`
  is recorded Mathlib smoothness. Finite presentation follows from smoothness
  (locally of finite presentation) and affineness of this morphism between affines
  (quasi-compact and quasi-separated); no finite-type hypothesis is omitted.
- `Z` is a set of points of V and `hZ : IsClosed Z` is the closed-subset hypothesis.
- `hcomponents` quantifies over every base point s and every
  `C ∈ irreducibleComponents (g.fiber s)`, and asserts
  `¬ C ⊆ (g.fiberι s) ⁻¹' Z`. Thus no fibre component is contained in Z_s.
- `η` and `hη : IsGenericPoint η Set.univ` introduce the generic base point.
  `hgeneric` quantifies over every point w of that actual scheme fibre whose image
  lies in Z, requiring `2 ≤ ringKrullDim ((g.fiber η).presheaf.stalk w)`.
- `z` with `hz : z ∈ Z` is arbitrary. The conclusion chooses `y ∈ Z` and
  `hy : g y = g z`, hence y lies in Z at the same fibre s. `hzy : z ⤳ y`
  expresses specialization. With the equality `hy`, `fiberHomeo` places y in
  `g.fiber (g z)`. Membership in that fibre's `closedPoints` says closed in the
  whole fibre. Specialization in V between two points of the fibre is equivalent
  to specialization in the fibre because `fiberHomeo` identifies its topology
  with the subspace topology. No strict specialization is required: y=z is allowed.
- A is the actual base stalk at `g y`; `hy` identifies this with the stalk at s=g z.
  B is the actual V stalk at y. The four `IsNoetherianRing` / `IsLocalRing`
  conjuncts explicitly state that both are Noetherian local rings.
- `IsLocalHom (g.stalkMap y).hom` explicitly states locality of the actual stalk
  map. `@Algebra.FormallySmoothAdic ... (g.stalkMap y).hom.toAlgebra ...`
  uses exactly that map for the algebra structure, with the actual maximal ideal
  of B as the adic ideal. No arbitrary algebra structure or map is quantified over.
- `(g.residueFieldMap y).hom.Finite` is finite-dimensionality of κ(y) over κ(g y),
  using the actual induced residue map. Mathlib's `RingHom.Finite` is precisely
  `Module.Finite` for the algebra structure of that ring map. Via `hy`, this is
  κ(y)/κ(s), including inseparable extensions.
- The strict `ringKrullDim A < ringKrullDim B` conjunct is exactly dim B > dim A.
- `((IsLocalRing.maximalIdeal A).map (g.stalkMap y).hom).IsPrime` states that
  p=m_A B is prime, using ideal extension along the actual stalk map.
- The existential `q : PrimeSpectrum B` supplies a prime q_z. Its equality with
  `(IsLocalRing.maximalIdeal (V.presheaf.stalk z)).comap
  (V.presheaf.stalkSpecializes hzy).hom` identifies the prime defined by z,
  rather than merely asserting an unspecified prime exists. Under the affine
  stalk description this is Q_z B, as in proof step 7.
- `(IsLocalRing.maximalIdeal A).map (g.stalkMap y).hom < q.asIdeal` is the strict
  containment p ⊊ q_z, with `<` on ideals meaning strict inclusion.
- `e : Localization.AtPrime q.asIdeal ≃+* V.presheaf.stalk z` is the local-ring
  isomorphism. An isomorphism of these local rings is automatically local.
  The clause for every b of B,
  `e (algebraMap _ (Localization.AtPrime q.asIdeal) b) =
  (V.presheaf.stalkSpecializes hzy).hom b`, specifies the canonical localization
  map on all original germs. This determines the isomorphism uniquely by the
  localization universal property, rather than choosing an arbitrary ring iso.
- The final `2 ≤ ringKrullDim (Localization.AtPrime q.asIdeal)` states exactly
  dim B_q_z ≥ 2. No dimension conclusion is replaced by a weaker vanishing claim.

Dependency declarations used, with signatures/docstrings read in the sources:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsDomain` and
  `IsIntegrallyClosed` (the recorded normal-domain encoding).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and actual stalk maps.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  its `LocallyOfFinitePresentation` instance is used in the affine interpretation.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`; these underlie
  the actual `Scheme.Hom.fiber` and `fiberι` from `Mathlib.AlgebraicGeometry.Fiber`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` (mathlib_match).
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints` (mathlib_match).
- `WeilConjectures.RingTheory.FormallySmoothAdic`: `Algebra.FormallySmoothAdic`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.RingTheory.Finiteness.Defs`: `RingHom.Finite`, the ring-map encoding
  of finiteness for the actual residue-field extension.
- `TopCat.Presheaf.stalkSpecializes` from Mathlib's stalk API gives the genuine
  specialization ring map, whose germ formula was also read.

Every available proof-dependency module is imported without `public` unless it
already appears among statement imports. In particular, the proof uses
`Algebra.smooth_fibre_regular_local` (upstream),
`Scheme.Hom.fiberStalkMap_surjective_ker_quotientEquiv`
(`Sheaf.AlgebraicGeometry.FibreStalkQuotient`), and the published upstream
localization-prime/residue-field interface. No private copies of notions occur.

Edge cases checked before writing:

- Z empty and V empty give no z; the theorem is correctly vacuous. B₀ is allowed
  to be the zero ring. A₀ is nonzero because it is a domain, as in the node.
- A field as base is allowed. For k→k[u,v], Z=V(u,v), choose y=z=(u,v):
  p=0, q is maximal and dim B_q=2. This checks the generic-only case and reflexive
  specialization; the statement does not force a strict specialization z→y.
- For k[t]→k[t,u] and Z=V(t,u), all generic-fibre hypotheses are vacuous,
  and at z=(t,u) the local dimensions are 1 and 2, p=(t) is prime and
  q=(t,u) strictly contains it, with localization dimension 2.
- For k→k[u] and Z=V(u), the generic dimension hypothesis fails, so the false
  dimension-two conclusion cannot be inferred. For an identity morphism any
  nonempty Z violates the fibre-component hypothesis. No hidden positive
  relative-dimension or excellence assumption is added.
- No perfectness, separability or algebraic closedness is imposed on residue
  fields. Krull dimensions use `WithBot ℕ∞`, retaining the zero-ring convention.

Searches actually run:

- `msearch.py ... leanfinder`: “For a smooth affine scheme over a noetherian
  normal domain choose a closed specialization in a fibre with finite residue
  extension, prime fibre ideal, and local dimension at least two”. Eight hits:
  IsIntegral, fibre Jacobson-space instance, residue-field/preimmersion interfaces,
  and field-valued points. No theorem states the combined assertion.
- `msearch.py ... loogle`: “AlgebraicGeometry.Scheme.Hom.fiber,
  AlgebraicGeometry.Scheme.stalkSpecializes, ringKrullDim”. Zero hits; the service
  reports unknown identifier `AlgebraicGeometry.Scheme.stalkSpecializes`.
  Source search found the correct `TopCat.Presheaf.stalkSpecializes` interface.
- `msearch.py ... grep`: `closed.*(fibre|fiber)|smooth.*[Ll]ocal.*[Pp]reparation`
  in Mathlib/AlgebraicGeometry: three unrelated hits in QuasiFinite, Etale and
  UniversallyClosed. No whole-item match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`: searched FormallySmoothAdic,
  stalkSpecializes/localization, the full item id, the proposed declaration and
  module names, closed-fibre preparation, and 21.14.3. Found reusable adic and
  fibre interfaces, plus the parent SmoothNongenericPuncturedLineTriviality and
  RamanujamSamuelPrimeDivisor; no existing theorem for this item.
- The item-id search in upstream Lean found no declaration. The name search in
  `dag/lean_names_upstream.json` also found no existing proposed name.

No STATEMENT-DISPUTED issue, node fault or missing interface was found.
Server compilation through the prescribed `scompile.py` passed for both the
sandbox and public module environments (1.9 s and 1.8 s in the first check).

## Second reading by Q132

Author's separate rereading with the node and complete module open; no independent
agent was started, as the dispatch brief prohibits it. The maintainer supplies
independent review. Matched all hypotheses and conjuncts using the correspondence
above. Checked especially that the chosen point is closed in the entire fibre,
that its residue extension and adic algebra structure use the actual stalk map,
that q is the prime associated to z, and that the isomorphism is normalized on
all elements of B. The only wording fix was to correct the direction of the
contraction in proof step 7's docstring: q is the contraction of the maximal ideal
at z along B→O_{V,z}. The theorem signature needed no change after compilation.
The affineness makes the finite-presentation condition automatic from smoothness;
the fibre-homeomorphism makes total-space and fibre specialization equivalent.
The generic-point binder retains the generic case rather than excluding it.
