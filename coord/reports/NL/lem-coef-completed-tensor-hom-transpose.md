## Worker report

The module `Sheaf.Paper.CompletedTensorHomTranspose` states
`WeilConjectures.completedTensorHomTranspose`, with its sole proof `sorry`.
`CoefficientTransposeLaws` is a transparent Prop structure packaging the three
specific equations in this node. It is not an alternative coefficient category,
tensor, internal Hom, evaluation, braiding, or adjunction construction.

Hypothesis and conclusion correspondence:

- The global finite-field and coefficient datum is `(D : FiniteFieldDatum.{u})`
  and `(C : D.CoefficientDatum)`. In particular C contains the prime, its inequality
  with D.p, and the fixed algebraic closure. The finite coefficient field is
  `(E : Type u) [Field E] [Algebra ℚ_[C.l] E] [FiniteDimensional ℚ_[C.l] E]`;
  R is exactly `Padic.coefficientExtensionIntegers C.l E`.
- The scheme is `X : Scheme.{u}`, with `X.Over (Spec (.of D.k))` and the structure
  map instances `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`. Locally of
  finite type plus quasi-compact is the finite-type convention. No properness,
  smoothness, finite Tor, or perfectness hypothesis is introduced.
- `L : sfIntegralConstructibleCategory C.l E X` is the specified derived-complete
  bounded constructible category. A permitted pair
  `P : (constructibleIntegralHomPairs C.l E X).FullSubcategory` has first object
  `P.obj.1.unop` (the paper's P) and second object `P.obj.2` (the paper's Q).
  Its sole property says that the ambient internal Hom is constructible. Thus
  this is exactly the node's additional Hom-output condition, with no stronger
  objectwise closure assumption. All L and all permitted P,Q are quantified.
- The integral `tau` is a family of `≃ₗ[R]` from `Hom(L,H(P,Q))` to the Hom from
  `constructibleIntegralTensor.obj (P,L)` to Q. It expresses both R-linearity and
  bijectivity for the actual completed tensor and actual ambient internal Hom.
- `CoefficientTransposeLaws.evaluation` fixes its forward function to
  `T.map (Prod.mkHom (𝟙 P) phi) ≫ beta(P,H).hom ≫ S.evaluation`.
  Here the last two factors are precisely argument-first evaluation e_{P,Q}:
  the normalized Hom-first counit preceded by signed symmetry.
- `CoefficientTransposeLaws.naturality` quantifies over every `f : L' ⟶ L` and
  every permitted-pair arrow g, and reads
  `tau (f ≫ phi ≫ H.map g) = T.map (g.first.unop,f) ≫ tau phi ≫ g.second`.
  Pair arrows encode arbitrary P'→P and Q→Q'. This is simultaneous naturality
  in all three variables on exactly the indicated domain.
- `CoefficientTransposeLaws.symmetry` identifies tau phi with the already
  normalized Hom-first inverse transpose precomposed with `beta(P,L).hom`.
  The beta here is `pullbackTensorIntegralBraiding`, whose normalization is the
  recorded coherent Koszul signed symmetry, not an arbitrary braiding.
- Rational objects and Hom-pairs use `sfRationalConstructibleCategory` and
  `constructibleRationalHomPairs`; these are the raw scalar localization with
  unchanged integral objects. Tensor and Hom are `rationalDerivedTensor` and
  `rationalDerivedInternalHom`, with exactly the prescribed scalar extensions.
- The rational tau is an additive equivalence of the actual rational Hom groups.
  Its additional equation quantifies over every `phi` in that Hom group and
  every `c : E` and preserves multiplication by
  `(sfRationalCoefficientEquiv C.l E).symm c`. This is precisely E-linearity:
  the library presents its native scalars as Localization.Away(varpi), and
  this canonical algebra equivalence identifies that field with E. No
  restriction to pure tensors or lattice-preserving rational maps occurs.
- The rational evaluation, naturality, and symmetry equations are the same
  three laws, using `podRationalClosed` and `pullbackTensorRationalBraiding`.
  The former is uniquely normalized as the scalar extension of the integral
  data on pure tensors and their sums; the latter is the actual localization
  of the integral symmetry. Thus these are the images of the stated integral
  operations, and the laws apply to arbitrary rational arrows.

The node's statement is unchanged. Its stmt_deps gains two already landed
nodes needed to name their published normalized interfaces, as permitted by
brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED NODES). There are no new nodes or
dependency repairs. The two additions have no path back to this item through
stmt_deps or proof_deps (checked by read-only DAG traversal).

Dependency declarations used:

- `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum` and its
  publicly imported `FiniteFieldDatum`, `FiniteFieldDatum.CoefficientDatum`.
  The theorem fixes the field/coefficient setting, without adding an arbitrary
  supplied choice of operations to the already canonical constructions.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`. The predicate consists of derived
  completeness and positive constructible reductions in one common interval.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralTensor`,
  `constructibleIntegralHomPairs`, `constructibleIntegralHom`,
  `constructibleRationalHomPairs`, `rationalDerivedTensor`,
  `rationalDerivedInternalHom`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalCoefficientEquiv`; inherited R-linear structure from the public
  `SfIntegralConstructibleLinear` module.
- `Sheaf.Paper.DerivedAutomorphismHomEvaluation` (landed node
  lem-pod-derived-automorphism-hom-evaluation): `PodPartialClosed`,
  `PodPartialClosed.evaluation`, `podIntegralClosed`, `podRationalClosed`.
  Read their full signatures and docstrings: these are uniquely normalized
  by the actual ordinary-to-completed tensor unit and raw scalar extension.
  No pullback/isomorphism hypothesis is required for these closed interfaces.
- `Sheaf.Paper.DerivedPullbackTensorIso` (landed node
  lem-pur-derived-pullback-tensor-iso): `pullbackTensorIntegralBraiding`,
  `pullbackTensorRationalBraiding`, read with their unique normalization
  theorems. They supply precisely the signed coherent and localized symmetries.
- `Sheaf.Paper.DirectImagesConstructible`: `finiteFieldDatumPrimeUnit`.
  At each residue field the statement supplies the inverse inline: map this
  base-field unit along the structure morphism's `residueFieldAlgebraMap`,
  simplify its natural-number cast, and apply `IsUnit.invertible`. Every tensor,
  braiding and closed structure receives this same term explicitly. This adds
  no residue-invertibility hypothesis and cites no Verdier-duality theorem.
- The remaining proof-dependency imports are exactly the recorded modules of
  the node's eleven proof dependencies, including independent-universe global
  Hom, restriction, constant-completion comparison and the Koszul reflector.
  The proof docstring explains each of the four DAG proof steps.

Edge cases checked before writing: X empty (all maps and laws remain in the
zero category); P,L,Q zero; torsion objects that rationalize to zero; E=Q_l;
shifted inputs of degrees a,b, giving the same (-1)^(ab) under the two symmetry
normalizations; the exact permitted-pair domain, including arrows between pairs
without extra constructibility assumptions on intermediary Hom objects; and
sums of arbitrary rational morphisms. There is no characteristic-ell case
because C explicitly requires ell different from the base characteristic.
Site object and morphism universes remain u+1 and u in the imported intrinsic
construction; no equality or extra smallness assumption is imposed.

Searches for an existing statement (all read-only):

- msearch.py leanfinder, query `completed derived tensor internal Hom transpose
  evaluation linear bijection natural signed symmetry`: eight generic hits,
  including ModuleCat.ihom_ev_app, ModuleCat.monoidalClosedHomEquiv and rigid
  tensor-Hom equivalences. None states the completed constructible and raw
  rational claim with these operations and domain.
- msearch.py loogle, query `CategoryTheory.Adjunction,
  CategoryTheory.MonoidalClosed`: twelve generic closed/reflection hits,
  including MonoidalClosed.ofEquiv and Monoidal.Reflective.monoidalClosed;
  none is this coefficient statement.
- msearch.py grep, query `completed.*[Tt]ensor|[Tt]ensor.*[Hh]om.*[Ee]quiv`:
  25 generic module tensor/rigid-category hits; no completed constructible claim.
- rg in both lean/WeilConjectures and lean/Sheaf, queries for completed/integral
  evaluation and transposition, integral braiding and symmetry; upstream node-id
  grep returns no hit. Project hits include AdicClosed.transpose_existsUnique
  (Hom-first, stronger all-pair closure assumptions) and podIntegralClosed /
  podRationalClosed (the reusable exact permitted-pair interfaces). Neither
  states the requested R/E linear, three-variable, signed-symmetry assertion.
- rg for `CompletedTensorHomTranspose|completedTensorHomTranspose` in both
  source trees and dag/lean_names_upstream.json found no name collision.

Source read: the current main-20261015 blueprint equivariance proof, especially
its second paragraph: evaluation and transposition apply to a rational Weil
structure itself, without preserving a chosen integral lattice. The four-step
node proof gives its explicit Stacks 08J9/08JA and 099B/099M completion argument;
these exact normalization interfaces are used here.

Validation: scompile.py compiled the delivered file in both sandbox and library
module contexts without errors or warnings (5.3 s and 6.1 s). All variables and
universes are explicit, with autoImplicit and relaxedAutoImplicit disabled.

## Second reading by NL

The dispatched worker reread the node and module after compilation; no second
agent was started, as required by the dispatcher. The maintainer supplies the
independent delivery review. This self-check verified the first-vs-second
argument order of every tensor, the opposite first component of pair arrows,
and the evaluation counit's Hom-first convention. The signed beta in both
fields converts that convention to the displayed argument-first formula.
The naturality field includes all three variables, and the rational scalar
field quantifies over arbitrary actual localized arrows, not just generators.
No mismatch was found in this rereading and no source statement was corrected.

## Returned-delivery repair

Repaired the maintainer's H2/theorem-stmt_dep point on returned head e14dc47dccd7.
Removed `thm-coef-rational-verdier` from `stmt_deps` and removed its module import.
Replaced all six uses of `RationalVerdier.units` by its explicit residue-field
inverse construction from `finiteFieldDatumPrimeUnit`; no `Invertible` binder
or new helper declaration was added. The mathematical statement and every
hypothesis and conclusion are unchanged. The `lean.statement` field is copied
verbatim from the revised theorem signature. The other two added theorem
statement dependencies remain: their closed data and signed braidings are
chosen from those nodes' own uniquely normalized existence theorems.

The saved pre-repair packet passed the required initial dry run (ea666a75a0);
that dry run was inspected before changing the retained packet. The repaired
packet is compiled and dry-run again before delivery. A self-check confirms
that all six inline terms are identical and exactly unfold the old definition.
