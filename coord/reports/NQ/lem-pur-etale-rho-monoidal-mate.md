## Worker report

The module `Sheaf.Paper.EtaleRhoMonoidalMate` specifies the actual inverse-twist
projection mate by its unique counit equation and states its normalization and compatibility with the normalized
etale exceptional comparison. Definitions have real data; the four named theorems
have `sorry` proofs. No statement correction or new notion is proposed.

Hypotheses and clauses:

* `P : WeilConjectures.PurityFiniteSetting` is the existing finite-field and finite
  coefficient datum, with positive level and ell different from the field characteristic.
* The `Over`, `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` instances for
  the structure maps express separated finite-type schemes over the fixed field.
  The corresponding instances and `IsOver` for `h` give the specified morphism.
* `K,N : Etale.DerivedCategoryModule P.Coefficient T`, with the recorded
  `FiniteEtaleNormalization.domain P T` predicates, quantify over every etale
  origin whose comparison image belongs to the original pro-etale Dctf category.
  This is precisely the coordinate convention of the supplied rho declaration;
  it does not choose one representative or replace constructibility by origin.
  Bounded constructible origin and fully faithful comparison identify this with
  the original small pro-etale statement. The canonical tensor, pullback, support,
  and exceptional comparisons used for this identification are those recorded
  in the dependency nodes, not arbitrary endpoint isomorphisms.
* `TensorInvertibleData` is the dependency's existing chosen inverse `d.inverse`
  and evaluation `d.iso`. Its inverse is required to be in the same domain.
* `OperationData` is a package of the actual operations, with no additional
  hypothesis in the finite theorem. `operations` fills its tensor bifunctors with
  `Etale.derivedTensor`, its unit with `coefficientUnit`, F and G with the existing
  compact-support and exceptional functors, Q with derived upperStar, and its
  counit, projection, and mu with the specified existing transformations.
* `finiteDataWitness` has real data: the specialization of `operations` to
  `ModuleCat P.Coefficient` and the same Nagata compactification used by the
  normalization dependency. Its subtype property stores equality to this exact
  construction, not just an isomorphism of endpoints. `finiteData` is its value;
  `finiteData_eq` exposes its property (a stage-2 postponed theorem whose proof
  is this property projection). Opacity keeps kernel checking from expanding
  the underlying derived-functor implementations; it hides no mathematical data.
* Consequently `d : TensorInvertibleData` for the packaged tensor/unit is exactly
  the recorded tensor invertibility, not a new tensor structure. `finiteRho`
  transports the actual `FiniteEtaleNormalization.rho` along the G and Q field
  equalities of `finiteData_eq`. It chooses no comparison.
* `IsFiniteKappa` is precisely PF(GK,N), followed by F(kappa) and the exceptional
  counit at K tensor N, equals epsilon(K) tensor id(N). Step 2 of the node's own
  proof derives exactly this equation from the displayed inverse-twist composite,
  using PF invertibility and the tensor-adjunction triangle.
* `finiteKappa_existsUnique` states that this equation has a unique solution on
  the node's domains. Its docstring supplies the full argument: cancel the inverse
  twist using the tensor-action/unit laws, obtain q = (epsilon tensor id) PF inverse,
  then apply the exceptional Hom bijection. It explicitly identifies the solution
  with the original displayed composite and its adjunction unit normalization.
* `finiteKappa` takes the uniquely determined morphism from that theorem. This is
  permitted proof postponement: the theorem fixes the actual morphism, not merely
  the isomorphism class of its endpoints. It introduces neither an arbitrary map
  nor a choice from a bare Nonempty statement. Its compactification is the very
  same Nagata compactification as the recorded normalization functors.
* `finiteKappa_normalization` states independence of every other inverse datum
  in the domain. For a closed immersion its isomorphism `c` has inverse
  `finiteKappa` and obeys exactly
  the counit/projection equation of `purityCoprojectionProperty` in etale-origin
  coordinates. For a closed immersion this identifies it with the dependency's
  canonical co-projection. The unique counit equation is equivalent to the inverse-twist
  conjugation described in the node, by the calculation in its Step 2.
* `[Etale h]` adds precisely the etaleness hypothesis of the final assertion.
  The first conjunction in `finite_etale_rho_monoidal_mate` is
  kappa followed by rho at K tensor N = rho at K tensor identity followed by
  mu inverse. The existential isomorphism `c` has inverse exactly kappa, so
  asserts invertibility. Its final equation is rho followed by mu = c followed
  by rho tensor identity, the node's equivalent co-projection identity.

Dependency interfaces read and used:

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Ring`, `.Coefficient`, the finite coefficient part of `sk-def-purity-conv`.
  The Kummer, normal-cone and deformation clauses of `PurityConventions` are
  irrelevant to this node; no second finite coefficient datum is introduced.
* `Sheaf.Paper.DerivedPullbackTensorHom`: the intrinsic finite operations and
  their canonical fixed-coefficient realization; its imported etale tensors and
  canonical pullbacks are used in the origin coordinates.
* `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`: `sfFiniteExceptionalAt`
  realizes the finite part of the recorded exceptional inverse image; the
  supplied normalization's `.exceptional` is its etale-origin coordinate.
* `Sheaf.Paper.Pur9Invertible`: `AlgebraicGeometry.TensorInvertibleData` and
  `Etale.DerivedCategory.etaleDerivedTensor`.
* `Sheaf.Paper.StandingExceptionalComposition`: `standingExceptionalHomEquiv`
  was read in full; on origins this is the ordinary etale Hom bijection used
  by `kappa`, with canonical support/site comparison on either side.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `compactificationProjectionFromData` and `ExchangeProjectionStage.projection`.
  The actual finite map is `Etale.projectionMap`, proper counit mate followed
  by the open tensor comparison, as specified in the recorded finite formula.
* `Sheaf.Paper.PurityCoprojection`: `purityCoprojectionProperty` and
  `purity_coprojection`, in particular the inverse's counit equation.
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
* `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization`: `.compactification`,
  `.exceptional`, `.lower`, `.counit`, `.pull`, `.coefficientUnit`, `.rho`, `.domain`
  and `finite_etale_dualizing_normalization`. The very same rho is used here.

Proof import compatibility: importing both legacy and FiniteCoefficient pro-etale
lower-shriek modules is rejected with a duplicate declaration of
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`.
The direct imports of StandingExceptionalComposition, PurityCoprojection,
FiniteProjectionActionLaws and ProjectionComparisonEtaleOrigin were therefore
omitted. Their required mathematical interfaces and proof uses are documented
above and in the proof docstrings; no declaration was copied or renamed. The
normalized-origin interface already imports its canonical support comparisons,
origin, compact-support, comparison-unit and ringed projection-mate tools.
The remaining compatible stated proof dependencies are imported privately.

Edge cases checked before writing: identity h; the tensor unit N; zero K; empty
source or target; open immersions; the finite etale fold T disjoint-union T to T;
and N equal to the coefficient unit shifted by one. No nonemptiness, positive
codimension or even-shift assumption is imposed. The odd shift in particular
requires the adjointified unit rather than symmetry followed by inverse evaluation.
For identity h the counit equation gives kappa = identity, including the odd shift;
zero inputs and empty sites give the unique zero morphism. For the fold, all formulas
are componentwise tensor identities and the counit is the fold sum. For an open
immersion the support normalization is extension by zero and its usual restriction
counit, with no surjectivity requirement.
Universes are explicit, with schemes in u and coefficient modules in u+1 as in
both recorded small-site encodings.

Searches for an existing statement:

* msearch leanfinder, `normalized etale exceptional inverse image comparison
  preserves projection formula mates`: eight unrelated normalization hits,
  no matching theorem.
* msearch loogle, `Adjunction.homEquiv, MonoidalCategory.tensorRight`: no hits;
  the service reported unknown identifier Adjunction.homEquiv.
* msearch grep, `projection.*[Mm]ate|[Mm]onoidal.*[Mm]ate`, CategoryTheory:
  no hits.
* rg of the upstream WeilConjectures and project Sheaf trees for this node id,
  `etale.*rho.*monoidal`, and `etaleRhoMonoidal`: no matching declaration.
* Source search for co-projection found the general upstream tensor/upper-shriek
  isomorphism and the recorded PurityCoprojection statement, neither of which
  states the normalized rho compatibility. Searches also found Mathlib tensor
  functors and tensor equivalences, but those do not state this specified identity.

No STATEMENT-DISPUTED flag: the source, the DAG proof and the odd-shift check agree
when the tensor adjunction is normalized as specified.

## Second reading by NQ

No second worker was started: the dispatcher brief prohibits other agents and
requires direct delivery. The maintainer's independent review is the second reading.

Implementation choice: the module packages the existing operations with a stored
equality specification and uses the uniquely determining counit equation, as the
existing PurityCoprojection interface does. This is an equivalent rendering
of the original kappa, established in Steps 1-3 of the node's existing proof; it
is not a change to the node's statement. Direct expansion of derived functor implementations caused kernel timeouts; the
opaque package carries the fully specified construction and its equality proof,
so the final interface retains the normalization while keeping type checking small.

Validation: scompile.py compiled the complete delivered file both as a sandbox module
and at its library module path under default options (5.9 s and 6.8 s), with no errors
or warnings. Every variable and universe is explicitly bound; no diagnostic options
or temporary Lean files remain.
