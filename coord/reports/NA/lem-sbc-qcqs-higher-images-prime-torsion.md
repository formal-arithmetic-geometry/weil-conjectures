## Worker report

The module `Sheaf.AlgebraicGeometry.QcqsHigherImagesPrimeTorsion` states
`AlgebraicGeometry.Etale.qcqs_higherDirectImages_prime_torsion`, with the sole proof
`sorry`. No definitions, additional hypotheses, new nodes, dependency replacements,
or statement corrections are needed. The seven-step proof from the DAG is included
in the theorem docstring. Source read: Stacks Project, etale-cohomology.tex,
Tags 0DDC (1) and 0DDD (1), including both proofs. The fixed-prime refinement
uses exactly the restricted positive annihilator indices described by the node.

Clause-by-clause correspondence:

- Schemes U and V and their morphism: `{U V : Scheme.{u}} (f : U ⟶ V)`.
- Quasi-compact and quasi-separated morphism: `[QuasiCompact f] [QuasiSeparated f]`.
  These are properties of f, not assumptions that U or V themselves are qcqs.
- Any set of primes: `P : Set ℕ`, used only through
  `∀ p : ℕ, p.Prime → p ∣ n → p ∈ P`. This is the upstream convention:
  nonprime members are immaterial, and every actual set of primes has this encoding.
- Abelian etale sheaf: `F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- Every geometric point of U: the binders inside hF are
  `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U)`.
- Every element of its geometric stalk: x belongs to
  `((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F`.
- A positive annihilator depending on the element: `∃ n : ℕ, 0 < n ∧ n • x = 0`.
- All prime divisors allowed: the final conjunct in hF is
  `∀ p : ℕ, p.Prime → p ∣ n → p ∈ P`.
- Every integer q >= 0: `(q : ℕ)`, cast to ℤ in the homology functor.
  This parametrizes exactly the nonnegative integers, including zero.
- Every geometric point of V: `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`
  and `(s : Spec (.of Ω) ⟶ V)`.
- R^q f_* F: apply `DerivedCategory.Plus.singleFunctor` in degree zero to F,
  then `rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f`, then
  `DerivedCategory.Plus.homologyFunctor` in degree `(q : ℤ)`.
- Every element y of that sheaf's stalk: y is bound in the object obtained by
  applying the same geometric-point sheafFiber to this cohomology sheaf.
- Positive annihilator and allowed prime divisors for y: the conclusion is
  `∃ m : ℕ, 0 < m ∧ m • y = 0 ∧ ∀ p : ℕ, p.Prime → p ∣ m → p ∈ P`.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` is explicitly a convention-only node, with
  no module or declaration. Its relevant Mathlib notions are
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, and
  `AlgebraicGeometry.QuasiSeparated` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `def-weil-pbc-abelian-etale-sheaves`: `CategoryTheory.Sheaf` from
  `Mathlib.CategoryTheory.Sites.Sheaf`, specialized using
  `AlgebraicGeometry.Scheme.smallEtaleTopology` from
  `Mathlib.AlgebraicGeometry.Sites.Etale` and `AddCommGrpCat`.
- `def-weil-pbc-geometric-stalks`: `CategoryTheory.GrothendieckTopology.Point.sheafFiber`
  from `Mathlib.CategoryTheory.Sites.Point.Basic`, and
  `AlgebraicGeometry.Scheme.pointSmallEtale` from
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`. Algebraically closed fields supply
  the separably closed instance required by pointSmallEtale. The point's fibre
  is the lifts of Spec Ω into an etale object; sheafFiber is the colimit over
  their opposite category of elements, exactly the node's pointed-neighbourhood stalk.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar` from
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` and
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`, whose definition is in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
  Both modules are public imports. The record's module provides lowerStar;
  the second recorded declaration is imported from its actual definition module.
  The derived functor is applied to exactly the abelian category in the node.
- Proof-only imports include every recorded proof module (Stalk,
  GeometricStalkColimits, EtaleDirectedCohomologyColimit,
  RightDerivedUniversalDeltaFunctor, AbelianHigherDirectImagePresheaf,
  the upstream EtalePoint module and Mathlib sheaf cohomology), plus the
  Mathlib modules for the proof leaves. They are ordinary imports. The
  concrete-coefficient module supplies the standard abelian-group instances.

Edge cases checked mathematically: q = 0 is included. The zero sheaf and zero
stalk element allow annihilator 1. If P is empty, only annihilator 1 is possible,
so the hypothesis says every stalk vanishes and the conclusion correctly says
this of the higher images. If P includes all primes the statement is ordinary
torsion preservation. Unbounded element orders are allowed: n depends on Ω, s,
and x. Empty source or target schemes are included; geometric-point quantifiers
then become empty as appropriate. No restriction on residue characteristics,
no invertibility assumption, and no global qcqs hypotheses occur. Schemes and
geometric-point fields use the same arbitrary universe u, the recorded site
encoding; abelian coefficients use u+1. No auto-bound variable is used.

Searches for an existing statement:

- msearch LeanFinder: "Higher direct images under quasi compact quasi separated
  scheme morphisms preserve etale sheaf torsion with prime divisors in a fixed set".
  Eight hits concerned qcqs structure-sheaf sections, affine limits, or ring etaleness;
  none states fixed-prime torsion preservation for higher direct images.
- msearch Loogle: `CategoryTheory.Sheaf, "torsion"`: zero hits.
- msearch grep: `torsion|annihilat` in `AlgebraicGeometry/Sites`: zero hits.
- msearch LeanSearch: "Higher direct images preserve torsion etale sheaves supported
  on a fixed set of primes": UNAVAILABLE, Internal Server Error; other searches used.
- rg over upstream WeilConjectures and this project's lean/Sheaf for
  `prime.*torsion|torsion.*prime|higher.*torsion` found the existing module-coefficient
  torsion predicates and unrelated devissage results, but no such preservation theorem.
  The upstream predicate uses P : Set ℕ with only prime divisors tested, as here.
- Exact node-id search over upstream WeilConjectures and dag/lean_names_upstream.json
  returned no existing declaration. Name search for the chosen theorem name likewise
  returned no collision. No existing declaration states this abelian-sheaf assertion.

Validation uses only scompile.py on the server, nice 19, two threads, 60 seconds
per file. Final compile and delivery dry-run results are recorded below.

Final server compile: clean, 1.5 seconds, nice 19, two threads, 60-second limit.
The signature in the node matches the file verbatim; maximum line width is 97.
`deliver2.py NA lem-sbc-qcqs-higher-images-prime-torsion --no-push` printed
`OK (dry run)`: compiles and passes preflight except for the second reading,
which the independent second reader supplies. Nothing was pushed.


## Second reading by NA

Read independently with the sandbox node and Lean module open, then the Stacks
source etale-cohomology.tex, section Torsion sheaves, Tags 0DDC and 0DDD,
including their proofs and the section introduction. Tag 0DDD assumes only a
qcqs morphism; 0DDC assumes a qcqs scheme when used on an affine test object's
pullback. There is no standing Noetherian, characteristic, or invertibility
hypothesis. Restricting the annihilator indices in 0DDC to positive integers
whose prime divisors lie in P gives precisely this node's refinement.

My statement inventory and clause-by-clause verdicts:

1. Objects U and V are arbitrary schemes: `{U V : Scheme.{u}}`. Correct.
2. A morphism u from U to V: `(f : U ⟶ V)`. Correct; renaming only.
3. Quasi-compactness of that morphism: `[QuasiCompact f]`. Correct; opened
   Mathlib's class, which requires compact preimages of compact opens.
4. Quasi-separatedness of that morphism: `[QuasiSeparated f]`. Correct;
   opened its class, requiring the diagonal to be quasi-compact. Neither
   property is replaced by a global property of U or V.
5. An arbitrary set of primes: `(P : Set ℕ)`, with membership tested only
   after `p.Prime`. Correct: nonprime members cannot affect the statement,
   and any set of primes has this representation.
6. An abelian sheaf F on U's small etale site:
   `(F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})`. Correct.
7. Every geometric point of U: the `Ω`, `Field Ω`, `IsAlgClosed Ω`, and
   `s : Spec (.of Ω) ⟶ U` binders inside hF. Correct.
8. Every element of its stalk: the `x` binder in
   `((Scheme.pointSmallEtale s).sheafFiber ...).obj F`. Correct.
9. A positive annihilator for each such element:
   `∃ n : ℕ, 0 < n ∧ n • x = 0`. Correct, with n inside the point/element
   quantifiers, so no uniform annihilator has been assumed.
10. All prime divisors of that annihilator lie in P:
    `∀ p : ℕ, p.Prime → p ∣ n → p ∈ P`. Correct.
11. Every nonnegative integer q: `(q : ℕ)`, with `(q : ℤ)` used for
    cohomological degree. Correct, including q = 0.
12. Every geometric point of V: the subsequent `Ω`, field, algebraic closure,
    and `s : Spec (.of Ω) ⟶ V` binders. Correct, independently of hF's points.
13. The higher direct image R^q f_* F: `singleFunctor ... 0` places F in
    degree zero, `rightDerivedLowerStarPlus ... f` applies Rf_*, and
    `homologyFunctor ... (q : ℤ)` extracts its qth cohomology sheaf. Correct.
14. Every element of its geometric stalk: the final `y` binder applies the
    target point's `sheafFiber` to exactly the sheaf in clause 13. Correct.
15. A positive annihilator m of y, with all its prime divisors in P:
    `∃ m : ℕ, 0 < m ∧ m • y = 0 ∧
      ∀ p : ℕ, p.Prime → p ∣ m → p ∈ P`. Correct, and m depends on y.

Opened each of the four statement dependency nodes and read their signatures
and implementations, rather than trusting their names. The convention-only
scheme node has no declaration to import. The abelian-sheaf node uses Mathlib
Sheaf, the full subcategory of presheaves satisfying IsSheaf, specialized to
smallEtaleTopology and AddCommGrpCat. The geometric-stalk node uses pointSmallEtale
and Point.sheafFiber: their bodies are the lift functor on etale neighbourhoods
and its opposite-elements colimit, restricted to sheaves. IsAlgClosed supplies
the IsSepClosed needed there. The direct-image node uses lowerStar, objectwise
precomposition with etale base change, and rightDerivedLowerStarPlus, whose body
is that functor's rightDerivedFunctorPlus. The latter is defined in the imported
Derived.UpperLowerStarCoherence module, even though the node's primary module
records UpperLowerStar.Defs. Opened Mathlib DerivedCategory.Plus.singleFunctor
and homologyFunctor as well: these give the degree-zero complex and ordinary
cohomology through the inclusion into the derived category. No dependency
replacement or missing definition is required. Checked proof-dependency records
against the ordinary proof imports; the seven docstring steps retain the node's
entire proof, including the restricted directed union, injectivity on stalks,
additivity, and affine shrinking.

Edge cases: P empty forces annihilator 1 and zero stalks; P all primes gives
ordinary torsion. Zero elements and the zero sheaf admit annihilator 1. The
restricted annihilator index is never empty since 1 is allowed, even for empty
P. The theorem includes empty schemes and q = 0. It permits varying unbounded
orders and every residue characteristic, including characteristic zero and
primes belonging to P. All schemes and geometric fields use the arbitrary
universe u of the recorded pointSmallEtale interface; coefficients have universe
u+1 as required by the site's derived functor. These are the dependency nodes'
shared universe conventions, with no independent smaller test universe or
additional instance hypothesis. All variables and the universe are explicit.

Independent searches with different wording from the first reader:

- LeanFinder via msearch: "Derived pushforward of an abelian sheaf preserves
  primary torsion for quasi compact quasi separated maps". Eight results about
  module pushforward, its additivity, and Grothendieck categories; no match.
- Loogle via msearch: `"torsion", "Sheaf"`. Zero hits.
- LeanSearch via msearch: "Higher pushforward etale abelian sheaf elements
  annihilated by integers with specified prime factors". Service unavailable
  (Internal Server Error); no mathematical verdict drawn from that failure.
- Independent rg in Mathlib algebraic geometry and sites, upstream
  WeilConjectures, and project lean/Sheaf for primary torsion, allowed primes,
  and torsion together with lowerStar/direct image. Results concern curve
  coefficient torsion, finite pushforwards, open-extension exchange, or
  principal-open section torsion; none states the present arbitrary-q qcqs
  fixed-prime preservation theorem. Exact node-id and declaration-name searches
  in upstream sources and dag/lean_names_upstream.json found no collision.

No mathematical or formatting mismatch was found. No Lean, dependency, or node
statement changed; only this independent second-reading record was appended.
There are no new nodes, dependency modules, statement corrections, private
notions, hollow definitions, or proofs beyond the single named theorem's sorry.
The source/blueprint docstrings, namespace, public statement imports, ordinary
proof imports, and line widths satisfy H5–H9. The recorded lean.statement was
checked verbatim against the file's complete signature.

Server validation with scompile.py succeeded cleanly: 1.5 seconds, nice 19,
two threads, 60-second per-file limit. No local Lean compiler or global build
was run. Delivery dry-run and push are performed by deliver2.py.
