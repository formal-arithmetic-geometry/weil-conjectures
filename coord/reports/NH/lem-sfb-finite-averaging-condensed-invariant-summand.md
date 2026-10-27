## Worker report

The module `Sheaf.Paper.FiniteAveragingCondensedInvariantSummand` states the item as
`Profinite.CondensedAction.PrimeToEll.FiniteAveraging.finite_averaging_condensed_invariant_summand`.
Its only theorem has the required whole-proof `sorry`. All helpers have real data:
functor composition, the existing inclusion, the Mathlib ordinary average, or transparent
Prop abbreviations of the clauses. No new node or dependency repair is needed.

Hypotheses and clauses, checked against the unchanged node:

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`. The coefficient closure is `Ω : Type u`,
  `[NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]`, encoding its
  extended norm. The finite intermediate field is `E : IntermediateField ℚ_[ℓ] Ω`
  with `[FiniteDimensional ℚ_[ℓ] E]`; its norm and topology are inherited.
- The small coherent profinite site uses explicit `universe u`, `Profinite.{u}`, and
  the dependency's internal modules with coefficients in `AddCommGrpCat.{u+1}`.
  Vector carriers are `Type (u+1)`. No independent smaller test universe is imposed.
- Coefficients F=E and F=Omega occur in the two `InternalAssertion` and
  `RepresentationAssertion` clauses. `normContinuousRing` is exactly the already
  recorded all-continuous coefficient ring, based on `continuousMapRingObjOfUniverse`.
- Finite discrete Q is `[Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Fintype Q]`.
  A Fintype specifies the finite enumeration needed for its sum without restricting
  finite groups. `L : ProfiniteGrp.{u}` supplies the residual profinite group.
  `_horder : Nat.Coprime (Fintype.card Q) ℓ` is the prime-to-ell hypothesis.
- `invariants F Q L d` inflates along `ContinuousMonoidHom.swap L Q` and applies
  the existing `ProductInvariants (normContinuousRing F) L Q`. This fixes exactly Q
  in the original Q times L action. Its existing injective inclusion, image,
  residual-action and adjunction formulas are inherited, rather than redefined.
- `InternalAssertion` states existence of p for EVERY internal action module M.
  The composite `p ≫ inclusion.app M` is the actual internal averaging endomorphism;
  its section formula is the constant `ULift.up (ContinuousMap.const S (card Q)⁻¹)`
  acting on the finite sum of `M.act S (ContinuousMap.const S (q,1)) x`.
  The scalar is elaborated before being specialized to its constant section, to keep
  the recorded transported section-module scalar structure. It is not a new action.
- `inclusion.app M ≫ p = 𝟙 _` states identity on invariants and the splitting.
  The displayed idempotence equation states e squared equals e. The image equation
  is exactly `Fixed M (ContinuousMonoidHom.snd Q L) S x`, quantifying through the
  dependency over every base change and every generalized kernel element. These
  formulas identify the image as the actual invariant subsheaf. The last quantified
  equation on p states residual L-equivariance; the inclusion has that property by d.
- Exactness is `Additive`, `PreservesFiniteLimits`, and `PreservesFiniteColimits`.
  Two additional implications preserve epic action maps and epic underlying internal
  module maps respectively. There is no assertion of sectionwise surjectivity.
- V has `AddCommGroup`, `Module E`, `FiniteDimensional E`, a Hausdorff vector topology
  with continuous addition and scalar action, and `_hρ` is joint continuity of its
  E-linear `Representation E (Q × L) V`. This expresses the norm-topological
  finite-dimensional E-space; no norm on an incomplete scalar extension is assumed.
- `average` reuses `Representation.averageMap` for `ρ.comp (MonoidHom.inl Q L)`.
  An explicit `invertibleOfNonzero` instance supplies Mathlib's required inverse.
  The total helper has a zero branch when the cardinality vanishes in an arbitrary
  field; that branch cannot occur over the theorem's characteristic-zero fields.
  The theorem explicitly equates this helper to the node's inverse-cardinality sum.
- The existential `p : V →L[E] fixedSpace Q L ρ`, its underlying-average formula,
  identity on that subspace, and residual-action formula express the continuous
  L-equivariant splitting. Its image is all of `fixedSpace`, since p is a retraction;
  the composite with inclusion is e_W, and hence has that image and is idempotent.
- `fixedSpace` is the dependency's Mathlib `Representation.invariants`, with its
  induced subspace topology and `fixedRepresentation` residual L-action.
  `Extended E F` is the actual tensor product with its recorded finite-dimensional
  module topology, not a completion or replacement space.
- `RepresentationAssertion` gives a `ContinuousLinearEquiv` onto the actual extended
  representation's `fixedSpace`. Its underlying map is precisely `fixedInclusion`;
  its other equation states L-equivariance. Thus it is the asserted homeomorphism
  of invariant subspaces, with their specified topologies.
- Realization existence is included for both V_F and (V^Q)_F. For EVERY such pair
  of section presentations, `∃! e` and `RepresentsComparison` give theta_F as an
  actual isomorphism in the residual action category. The section equation says
  theta followed by the invariant inclusion is postcomposition by `fixedInclusion`.
  Consequently it is the specified actual invariant-inclusion map.
- `NaturalityAssertion` quantifies over continuous equivariant E-linear f, target
  representations, both realization pairs and normalized theta isomorphisms.
  `RepresentsMap` fixes the morphisms a and b as the actual tensor extension of f
  and of its recorded `fixedMap`. The equality is theta naturality. No assumption
  that f is invertible, nonzero or injective is present.
- `CoefficientAssertion` uses exactly `coefficientRingMap E (algebraMap E Ω) hφ`,
  the recorded postcomposition C_E to C_Omega, and every normalized `ScalarAction`.
  `RepresentsScalarMap` specifies a and b by the actual `scalarInsertion` on the
  two tensor products. The unique c is normalized by its square with the invariant
  inclusions; its theta square is then asserted, rather than assumed. The theorem
  also displays the tensor inclusion square and the requested explicit identity
  `average ... ((1 : Ω) ⊗ₜ[E] v) = (1 : Ω) ⊗ₜ[E] average ... v`.
- There is no `CompleteSpace Ω` assumption. The theorem's twelve-step docstring
  includes the full node proof, using completeness only for E and finite matrix
  continuity over Omega.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CondensedActionModule`: `ActionModule`, `Modules`,
  `sectionModule`, `inflate`, `forgetAction`, `Fixed`, `ProductInvariants` and its
  inclusion, image, injectivity and residual-action specifications.
- `Sheaf.Paper.ContinuousRepresentationCondensation`: `Realization`, `RepresentsMap`,
  `coefficientRingMap`, `RepresentsScalarMap`; `PrimeToEll.Extended`,
  `extendedRepresentation`, `fixedSpace`, `fixedRepresentation`, `fixedInclusion`,
  `fixedMap`, `scalarInsertion`. Their full signatures/docstrings were read.
- `Sheaf.Topology.ContinuousMapCondensedRing`: `continuousMapRingSheafOfUniverse`,
  `continuousMapRingObjOfUniverse`, its ring-object structure, through
  `AlgebraicGeometry.ProEtale.normContinuousRing`.
- `Sheaf.Topology.ContinuousMapCondensedRingMap`: the postcomposition sheaf and
  ring-object maps through `ContinuousRepresentation.coefficientRingMap`.
- `def-weil-size-convention` is explicitly a metatheoretic convention, not an
  additional definition. Its universe convention is rendered as above.
- Proof imports include `Sheaf.CategoryTheory.SheafActionGrothendieckInflation`,
  `Mathlib.Algebra.Homology.ShortComplex.Exact`,
  `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`, and finite-dimensional topology.
  Mathlib's `Representation.averageMap` and invariants were read in full.

Edge cases checked: a group is nonempty, so card Q is never zero as a natural number;
Q trivial makes the average and splitting identities; L trivial removes only residual
equivariance. V=0 and V^Q=0 are allowed: there are no positivity/nonzero hypotheses,
and continuous linear equivalences between zero modules are included. The empty
profinite test set is included by all universal section quantifiers, with its unique
continuous section. Generalized Q-elements are handled by `Fixed`, not only constant
q. Cardinality divisible by ell is excluded exactly as in the node, although finite
averaging over these characteristic-zero fields would still make sense.

Searches (msearch.py NH item, plus direct source inspection):

- LeanFinder, "Finite group averaging idempotent projects onto invariants, exact
  invariants functor for internal condensed modules and scalar extension of continuous
  finite dimensional representations": 8 hits including `Representation.isProj_averageMap`,
  `averageMap_id`, `Rep.invariantsFunctor`, `invariantsAdjunction`, and `Rep.normNatTrans`.
  These concern ordinary representations; none states the internal condensed result.
- LeanSearch, "finite group invariants averaging exact functor and continuous tensor
  base change": 8 hits, the same ordinary average/invariants API and
  `ContinuousCohomology.invariants`; no exact match for this statement.
- Loogle, "Representation.invariants, LinearMap.isIdempotentElem_iff,
  Functor.PreservesFiniteLimits": no hit; the middle identifier is unknown.
- Mathlib grep, `averag|Reynolds`, RepresentationTheory: 11 hits; read
  `Mathlib/RepresentationTheory/Invariants.lean` and reused its `averageMap`.
- `rg` in lean/WeilConjectures and lean/Sheaf for averaging, PrimeToEll and invariant
  summands: found the continuous-representation dependency and the consuming
  `PrimeToEllDerivedInvariantsReduction` module; its continuous maps have distinct
  owning nodes, so no helper was copied. Other hits concern discrete modules,
  Artin-Schreier averaging or unrelated tame geometry.
- `grep -rn` for this item id in lean/WeilConjectures: no result.
  `dag/lean_names_upstream.json` was included in the name/concept search. No exact
  existing declaration was found.

Source read: `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3).
It supplies the direct-image context; the node correctly marks its auxiliary
finite-average proof as agent-formulated with an exact external reference WANTED.
No mathematical node correction, disputed statement, or missing notion was found.

Validation: scompile.py compiled the full module in module mode, both the sandbox
and its intended library path, with no errors or warnings. All variables and universes
are explicit; the only postponed result is the owning node's main theorem.

## Second reading by NH

Author's separate second pass; the maintainer's independent review remains external to
this worker, as the dispatch brief specifies. Reopened the unchanged node, the full
module and the dependency specifications. Checked each match above, particularly:
Q occupies the first original factor while ProductInvariants fixes the second;
the swap therefore precedes d.functor. Checked composition order in i then p,
p then i, both naturality squares and the underlying scalar-restriction square.
The inverse-cardinality scalar initially failed type inference after unfolding the
transported ring; specializing a lambda with the recorded section-ring binder fixed
elaboration without changing the scalar action. The explicit normalizations prevent
an arbitrary isomorphism from satisfying the assertion. Added actual realization
existence, naturality and coefficient-square clauses during this rereading so no
part of the node is merely left in prose. The statement does not rely on a hypothetical
sectionwise surjectivity of epic maps and does not assume Omega complete.
